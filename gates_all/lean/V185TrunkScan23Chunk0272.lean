import V185TrunkScan23Chunk0271

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1608995 : List Nat := [1, 1, 1, 4, 2, 5, 1, 2, 2, 1, 3]
def baseStart_1608995 : Nat := 118140960795 + 1608995 * 2 ^ 59
def prefixEnd_1608995 : Nat := 4983230072969 + 3 ^ 40 * 1608995 * 2
def baseEnd_1608995 : Nat := 826187805681037533362873

theorem tailTrace_1608995 : CollatzResearch.WordTrace tailWord_1608995 prefixEnd_1608995 826187805681037533362873 := by
  unfold tailWord_1608995
  simp only [CollatzResearch.WordTrace]
  refine ⟨58684868805893384313604439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39123245870595589542402959 58684868805893384313604439)
  ·
    refine ⟨88027303208840076470406659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58684868805893384313604439 88027303208840076470406659)
    ·
      refine ⟨132040954813260114705609989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88027303208840076470406659 132040954813260114705609989)
      ·
        refine ⟨24757679027486271507301873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132040954813260114705609989 24757679027486271507301873)
        ·
          refine ⟨18568259270614703630476405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24757679027486271507301873 18568259270614703630476405)
          ·
            refine ⟨1740774306620128465357163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18568259270614703630476405 1740774306620128465357163)
            ·
              refine ⟨2611161459930192698035745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1740774306620128465357163 2611161459930192698035745)
              ·
                refine ⟨1958371094947644523526809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2611161459930192698035745 1958371094947644523526809)
                ·
                  refine ⟨1468778321210733392645107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1958371094947644523526809 1468778321210733392645107)
                  ·
                    refine ⟨2203167481816100088967661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1468778321210733392645107 2203167481816100088967661)
                    ·
                      refine ⟨826187805681037533362873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2203167481816100088967661 826187805681037533362873)
                      ·
                        rfl

theorem cell23_1608995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2, 1, 3].length) (baseStart_1608995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1608995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1608995 prefixEnd_1608995 := by exact prefixLift 1608995
  have htrace : WordTrace (prefixWord ++ tailWord_1608995) baseStart_1608995 baseEnd_1608995 := by
    simpa [prefixWord, tailWord_1608995, baseEnd_1608995] using wordTrace_append hprefix tailTrace_1608995
  have hstable : (prefixWord ++ tailWord_1608995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1608995).length < 2 ^ (prefixWord ++ tailWord_1608995).sum := by decide
  have hdescent : baseEnd_1608995 < baseStart_1608995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1608995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609004 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 5]
def baseStart_1609004 : Nat := 118140960795 + 1609004 * 2 ^ 59
def prefixEnd_1609004 : Nat := 4983230072969 + 3 ^ 40 * 1609004 * 2
def baseEnd_1609004 : Nat := 826192427006927998150331

theorem tailTrace_1609004 : CollatzResearch.WordTrace tailWord_1609004 prefixEnd_1609004 826192427006927998150331 := by
  unfold tailWord_1609004
  simp only [CollatzResearch.WordTrace]
  refine ⟨29342598531430389425341033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39123464708573852567121377 29342598531430389425341033)
  ·
    refine ⟨22006948898572792069005775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29342598531430389425341033 22006948898572792069005775)
    ·
      refine ⟨33010423347859188103508663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22006948898572792069005775 33010423347859188103508663)
      ·
        refine ⟨49515635021788782155262995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33010423347859188103508663 49515635021788782155262995)
        ·
          refine ⟨74273452532683173232894493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49515635021788782155262995 74273452532683173232894493)
          ·
            refine ⟨27852544699756189962335435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74273452532683173232894493 27852544699756189962335435)
            ·
              refine ⟨41778817049634284943503153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27852544699756189962335435 41778817049634284943503153)
              ·
                refine ⟨31334112787225713707627365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41778817049634284943503153 31334112787225713707627365)
                ·
                  refine ⟨5875146147604821320180131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31334112787225713707627365 5875146147604821320180131)
                  ·
                    refine ⟨8812719221407231980270197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5875146147604821320180131 8812719221407231980270197)
                    ·
                      refine ⟨826192427006927998150331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8812719221407231980270197 826192427006927998150331)
                      ·
                        rfl

theorem cell23_1609004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_1609004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609004 prefixEnd_1609004 := by exact prefixLift 1609004
  have htrace : WordTrace (prefixWord ++ tailWord_1609004) baseStart_1609004 baseEnd_1609004 := by
    simpa [prefixWord, tailWord_1609004, baseEnd_1609004] using wordTrace_append hprefix tailTrace_1609004
  have hstable : (prefixWord ++ tailWord_1609004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609004).length < 2 ^ (prefixWord ++ tailWord_1609004).sum := by decide
  have hdescent : baseEnd_1609004 < baseStart_1609004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609012 : List Nat := [2, 5, 1, 1, 1, 1, 5, 1, 2, 1, 3]
def baseStart_1609012 : Nat := 118140960795 + 1609012 * 2 ^ 59
def prefixEnd_1609012 : Nat := 4983230072969 + 3 ^ 40 * 1609012 * 2
def baseEnd_1609012 : Nat := 826196534852163966850295

theorem tailTrace_1609012 : CollatzResearch.WordTrace tailWord_1609012 prefixEnd_1609012 826196534852163966850295 := by
  unfold tailWord_1609012
  simp only [CollatzResearch.WordTrace]
  refine ⟨29342744423415898108486645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39123659231221197477982193 29342744423415898108486645)
  ·
    refine ⟨2750882289695240447670623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29342744423415898108486645 2750882289695240447670623)
    ·
      refine ⟨4126323434542860671505935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2750882289695240447670623 4126323434542860671505935)
      ·
        refine ⟨6189485151814291007258903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4126323434542860671505935 6189485151814291007258903)
        ·
          refine ⟨9284227727721436510888355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6189485151814291007258903 9284227727721436510888355)
          ·
            refine ⟨13926341591582154766332533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9284227727721436510888355 13926341591582154766332533)
            ·
              refine ⟨1305594524210827009343675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13926341591582154766332533 1305594524210827009343675)
              ·
                refine ⟨1958391786316240514015513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1305594524210827009343675 1958391786316240514015513)
                ·
                  refine ⟨1468793839737180385511635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1958391786316240514015513 1468793839737180385511635)
                  ·
                    refine ⟨2203190759605770578267453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1468793839737180385511635 2203190759605770578267453)
                    ·
                      refine ⟨826196534852163966850295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2203190759605770578267453 826196534852163966850295)
                      ·
                        rfl

theorem cell23_1609012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_1609012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609012 prefixEnd_1609012 := by exact prefixLift 1609012
  have htrace : WordTrace (prefixWord ++ tailWord_1609012) baseStart_1609012 baseEnd_1609012 := by
    simpa [prefixWord, tailWord_1609012, baseEnd_1609012] using wordTrace_append hprefix tailTrace_1609012
  have hstable : (prefixWord ++ tailWord_1609012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609012).length < 2 ^ (prefixWord ++ tailWord_1609012).sum := by decide
  have hdescent : baseEnd_1609012 < baseStart_1609012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609024 : List Nat := [2, 1, 1, 2, 2, 1, 3, 4, 7]
def baseStart_1609024 : Nat := 118140960795 + 1609024 * 2 ^ 59
def prefixEnd_1609024 : Nat := 4983230072969 + 3 ^ 40 * 1609024 * 2
def baseEnd_1609024 : Nat := 91800299624446435544471

theorem tailTrace_1609024 : CollatzResearch.WordTrace tailWord_1609024 prefixEnd_1609024 91800299624446435544471 := by
  unfold tailWord_1609024
  simp only [CollatzResearch.WordTrace]
  refine ⟨29342963261394161133205063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39123951015192214844273417 29342963261394161133205063)
  ·
    refine ⟨44014444892091241699807595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29342963261394161133205063 44014444892091241699807595)
    ·
      refine ⟨66021667338136862549711393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44014444892091241699807595 66021667338136862549711393)
      ·
        refine ⟨49516250503602646912283545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66021667338136862549711393 49516250503602646912283545)
        ·
          refine ⟨37137187877701985184212659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49516250503602646912283545 37137187877701985184212659)
          ·
            refine ⟨55705781816552977776318989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37137187877701985184212659 55705781816552977776318989)
            ·
              refine ⟨20889668181207366666119621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55705781816552977776318989 20889668181207366666119621)
              ·
                refine ⟨3916812783976381249897429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20889668181207366666119621 3916812783976381249897429)
                ·
                  refine ⟨91800299624446435544471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3916812783976381249897429 91800299624446435544471)
                  ·
                    rfl

theorem cell23_1609024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 7].length) (baseStart_1609024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609024 prefixEnd_1609024 := by exact prefixLift 1609024
  have htrace : WordTrace (prefixWord ++ tailWord_1609024) baseStart_1609024 baseEnd_1609024 := by
    simpa [prefixWord, tailWord_1609024, baseEnd_1609024] using wordTrace_append hprefix tailTrace_1609024
  have hstable : (prefixWord ++ tailWord_1609024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609024).length < 2 ^ (prefixWord ++ tailWord_1609024).sum := by decide
  have hdescent : baseEnd_1609024 < baseStart_1609024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609030 : List Nat := [6, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2]
def baseStart_1609030 : Nat := 118140960795 + 1609030 * 2 ^ 59
def prefixEnd_1609030 : Nat := 4983230072969 + 3 ^ 40 * 1609030 * 2
def baseEnd_1609030 : Nat := 826205777503944896425213

theorem tailTrace_1609030 : CollatzResearch.WordTrace tailWord_1609030 prefixEnd_1609030 826205777503944896425213 := by
  unfold tailWord_1609030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1833942042523955790347767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39124096907177723527419029 1833942042523955790347767)
  ·
    refine ⟨2750913063785933685521651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1833942042523955790347767 2750913063785933685521651)
    ·
      refine ⟨4126369595678900528282477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2750913063785933685521651 4126369595678900528282477)
      ·
        refine ⟨1547388598379587698105929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4126369595678900528282477 1547388598379587698105929)
        ·
          refine ⟨1160541448784690773579447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1547388598379587698105929 1160541448784690773579447)
          ·
            refine ⟨1740812173177036160369171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160541448784690773579447 1740812173177036160369171)
            ·
              refine ⟨2611218259765554240553757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1740812173177036160369171 2611218259765554240553757)
              ·
                refine ⟨979206847412082840207659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2611218259765554240553757 979206847412082840207659)
                ·
                  refine ⟨1468810271118124260311489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 979206847412082840207659 1468810271118124260311489)
                  ·
                    refine ⟨1101607703338593195233617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1468810271118124260311489 1101607703338593195233617)
                    ·
                      refine ⟨826205777503944896425213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1101607703338593195233617 826205777503944896425213)
                      ·
                        rfl

theorem cell23_1609030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_1609030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609030 prefixEnd_1609030 := by exact prefixLift 1609030
  have htrace : WordTrace (prefixWord ++ tailWord_1609030) baseStart_1609030 baseEnd_1609030 := by
    simpa [prefixWord, tailWord_1609030, baseEnd_1609030] using wordTrace_append hprefix tailTrace_1609030
  have hstable : (prefixWord ++ tailWord_1609030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609030).length < 2 ^ (prefixWord ++ tailWord_1609030).sum := by decide
  have hdescent : baseEnd_1609030 < baseStart_1609030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609069 : List Nat := [1, 5, 1, 1, 1, 5, 2, 1, 2, 2, 2]
def baseStart_1609069 : Nat := 118140960795 + 1609069 * 2 ^ 59
def prefixEnd_1609069 : Nat := 4983230072969 + 3 ^ 40 * 1609069 * 2
def baseEnd_1609069 : Nat := 826225803249470243837533

theorem tailTrace_1609069 : CollatzResearch.WordTrace tailWord_1609069 prefixEnd_1609069 826225803249470243837533 := by
  unfold tailWord_1609069
  simp only [CollatzResearch.WordTrace]
  refine ⟨58687567807625294951798261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39125045205083529967865507 58687567807625294951798261)
  ·
    refine ⟨5501959481964871401731087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58687567807625294951798261 5501959481964871401731087)
    ·
      refine ⟨8252939222947307102596631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5501959481964871401731087 8252939222947307102596631)
      ·
        refine ⟨12379408834420960653894947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8252939222947307102596631 12379408834420960653894947)
        ·
          refine ⟨18569113251631440980842421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12379408834420960653894947 18569113251631440980842421)
          ·
            refine ⟨1740854367340447591953977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18569113251631440980842421 1740854367340447591953977)
            ·
              refine ⟨1305640775505335693965483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1740854367340447591953977 1305640775505335693965483)
              ·
                refine ⟨1958461163258003540948225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1305640775505335693965483 1958461163258003540948225)
                ·
                  refine ⟨1468845872443502655711169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1958461163258003540948225 1468845872443502655711169)
                  ·
                    refine ⟨1101634404332626991783377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1468845872443502655711169 1101634404332626991783377)
                    ·
                      refine ⟨826225803249470243837533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1101634404332626991783377 826225803249470243837533)
                      ·
                        rfl

theorem cell23_1609069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_1609069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609069 prefixEnd_1609069 := by exact prefixLift 1609069
  have htrace : WordTrace (prefixWord ++ tailWord_1609069) baseStart_1609069 baseEnd_1609069 := by
    simpa [prefixWord, tailWord_1609069, baseEnd_1609069] using wordTrace_append hprefix tailTrace_1609069
  have hstable : (prefixWord ++ tailWord_1609069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609069).length < 2 ^ (prefixWord ++ tailWord_1609069).sum := by decide
  have hdescent : baseEnd_1609069 < baseStart_1609069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609111 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 3, 4, 3]
def baseStart_1609111 : Nat := 118140960795 + 1609111 * 2 ^ 59
def prefixEnd_1609111 : Nat := 4983230072969 + 3 ^ 40 * 1609111 * 2
def baseEnd_1609111 : Nat := 826247369436959079512339

theorem tailTrace_1609111 : CollatzResearch.WordTrace tailWord_1609111 prefixEnd_1609111 826247369436959079512339 := by
  unfold tailWord_1609111
  simp only [CollatzResearch.WordTrace]
  refine ⟨58689099673473136124827187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39126066448982090749884791 58689099673473136124827187)
  ·
    refine ⟨88033649510209704187240781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58689099673473136124827187 88033649510209704187240781)
    ·
      refine ⟨33012618566328639070215293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88033649510209704187240781 33012618566328639070215293)
      ·
        refine ⟨12379731962373239651330735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33012618566328639070215293 12379731962373239651330735)
        ·
          refine ⟨18569597943559859476996103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12379731962373239651330735 18569597943559859476996103)
          ·
            refine ⟨27854396915339789215494155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18569597943559859476996103 27854396915339789215494155)
            ·
              refine ⟨41781595373009683823241233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27854396915339789215494155 41781595373009683823241233)
              ·
                refine ⟨31336196529757262867430925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41781595373009683823241233 31336196529757262867430925)
                ·
                  refine ⟨11751073698658973575286597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31336196529757262867430925 11751073698658973575286597)
                  ·
                    refine ⟨2203326318498557545366237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11751073698658973575286597 2203326318498557545366237)
                    ·
                      refine ⟨826247369436959079512339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2203326318498557545366237 826247369436959079512339)
                      ·
                        rfl

theorem cell23_1609111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_1609111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609111 prefixEnd_1609111 := by exact prefixLift 1609111
  have htrace : WordTrace (prefixWord ++ tailWord_1609111) baseStart_1609111 baseEnd_1609111 := by
    simpa [prefixWord, tailWord_1609111, baseEnd_1609111] using wordTrace_append hprefix tailTrace_1609111
  have hstable : (prefixWord ++ tailWord_1609111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609111).length < 2 ^ (prefixWord ++ tailWord_1609111).sum := by decide
  have hdescent : baseEnd_1609111 < baseStart_1609111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609208 : List Nat := [2, 1, 2, 1, 1, 5, 1, 2, 4, 4]
def baseStart_1609208 : Nat := 118140960795 + 1609208 * 2 ^ 59
def prefixEnd_1609208 : Nat := 4983230072969 + 3 ^ 40 * 1609208 * 2
def baseEnd_1609208 : Nat := 275432392353481733333131

theorem tailTrace_1609208 : CollatzResearch.WordTrace tailWord_1609208 prefixEnd_1609208 275432392353481733333131 := by
  unfold tailWord_1609208
  simp only [CollatzResearch.WordTrace]
  refine ⟨29346318777060860845554139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39128425036081147794072185 29346318777060860845554139)
  ·
    refine ⟨44019478165591291268331209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29346318777060860845554139 44019478165591291268331209)
    ·
      refine ⟨33014608624193468451248407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44019478165591291268331209 33014608624193468451248407)
      ·
        refine ⟨49521912936290202676872611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33014608624193468451248407 49521912936290202676872611)
        ·
          refine ⟨74282869404435304015308917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49521912936290202676872611 74282869404435304015308917)
          ·
            refine ⟨6964019006665809751435211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74282869404435304015308917 6964019006665809751435211)
            ·
              refine ⟨10446028509998714627152817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6964019006665809751435211 10446028509998714627152817)
              ·
                refine ⟨7834521382499035970364613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10446028509998714627152817 7834521382499035970364613)
                ·
                  refine ⟨1468972759218569244443365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7834521382499035970364613 1468972759218569244443365)
                  ·
                    refine ⟨275432392353481733333131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1468972759218569244443365 275432392353481733333131)
                    ·
                      rfl

theorem cell23_1609208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 4, 4].length) (baseStart_1609208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609208 prefixEnd_1609208 := by exact prefixLift 1609208
  have htrace : WordTrace (prefixWord ++ tailWord_1609208) baseStart_1609208 baseEnd_1609208 := by
    simpa [prefixWord, tailWord_1609208, baseEnd_1609208] using wordTrace_append hprefix tailTrace_1609208
  have hstable : (prefixWord ++ tailWord_1609208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609208).length < 2 ^ (prefixWord ++ tailWord_1609208).sum := by decide
  have hdescent : baseEnd_1609208 < baseStart_1609208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609298 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 1, 8]
def baseStart_1609298 : Nat := 118140960795 + 1609298 * 2 ^ 59
def prefixEnd_1609298 : Nat := 4983230072969 + 3 ^ 40 * 1609298 * 2
def baseEnd_1609298 : Nat := 275447796773116615957993

theorem tailTrace_1609298 : CollatzResearch.WordTrace tailWord_1609298 prefixEnd_1609298 275447796773116615957993 := by
  unfold tailWord_1609298
  simp only [CollatzResearch.WordTrace]
  refine ⟨14673980030948916765471137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39130613415863778041256365 14673980030948916765471137)
  ·
    refine ⟨11005485023211687574103353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14673980030948916765471137 11005485023211687574103353)
    ·
      refine ⟨8254113767408765680577515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11005485023211687574103353 8254113767408765680577515)
      ·
        refine ⟨12381170651113148520866273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8254113767408765680577515 12381170651113148520866273)
        ·
          refine ⟨9285877988334861390649705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12381170651113148520866273 9285877988334861390649705)
          ·
            refine ⟨6964408491251146042987279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9285877988334861390649705 6964408491251146042987279)
            ·
              refine ⟨10446612736876719064480919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6964408491251146042987279 10446612736876719064480919)
              ·
                refine ⟨15669919105315078596721379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10446612736876719064480919 15669919105315078596721379)
                ·
                  refine ⟨23504878657972617895082069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15669919105315078596721379 23504878657972617895082069)
                  ·
                    refine ⟨275447796773116615957993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23504878657972617895082069 275447796773116615957993)
                    ·
                      rfl

theorem cell23_1609298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_1609298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609298 prefixEnd_1609298 := by exact prefixLift 1609298
  have htrace : WordTrace (prefixWord ++ tailWord_1609298) baseStart_1609298 baseEnd_1609298 := by
    simpa [prefixWord, tailWord_1609298, baseEnd_1609298] using wordTrace_append hprefix tailTrace_1609298
  have hstable : (prefixWord ++ tailWord_1609298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609298).length < 2 ^ (prefixWord ++ tailWord_1609298).sum := by decide
  have hdescent : baseEnd_1609298 < baseStart_1609298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609322 : List Nat := [3, 1, 3, 2, 1, 2, 2, 2, 1, 4, 2]
def baseStart_1609322 : Nat := 118140960795 + 1609322 * 2 ^ 59
def prefixEnd_1609322 : Nat := 4983230072969 + 3 ^ 40 * 1609322 * 2
def baseEnd_1609322 : Nat := 826355713855057753973869

theorem tailTrace_1609322 : CollatzResearch.WordTrace tailWord_1609322 prefixEnd_1609322 826355713855057753973869 := by
  unfold tailWord_1609322
  simp only [CollatzResearch.WordTrace]
  refine ⟨14674198868927179790189555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39131196983805812773838813 14674198868927179790189555)
  ·
    refine ⟨22011298303390769685284333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14674198868927179790189555 22011298303390769685284333)
    ·
      refine ⟨8254236863771538631981625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22011298303390769685284333 8254236863771538631981625)
      ·
        refine ⟨6190677647828653973986219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8254236863771538631981625 6190677647828653973986219)
        ·
          refine ⟨9286016471742980960979329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6190677647828653973986219 9286016471742980960979329)
          ·
            refine ⟨6964512353807235720734497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9286016471742980960979329 6964512353807235720734497)
            ·
              refine ⟨5223384265355426790550873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6964512353807235720734497 5223384265355426790550873)
              ·
                refine ⟨3917538199016570092913155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5223384265355426790550873 3917538199016570092913155)
                ·
                  refine ⟨5876307298524855139369733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3917538199016570092913155 5876307298524855139369733)
                  ·
                    refine ⟨1101807618473410338631825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5876307298524855139369733 1101807618473410338631825)
                    ·
                      refine ⟨826355713855057753973869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1101807618473410338631825 826355713855057753973869)
                      ·
                        rfl

theorem cell23_1609322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_1609322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609322 prefixEnd_1609322 := by exact prefixLift 1609322
  have htrace : WordTrace (prefixWord ++ tailWord_1609322) baseStart_1609322 baseEnd_1609322 := by
    simpa [prefixWord, tailWord_1609322, baseEnd_1609322] using wordTrace_append hprefix tailTrace_1609322
  have hstable : (prefixWord ++ tailWord_1609322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609322).length < 2 ^ (prefixWord ++ tailWord_1609322).sum := by decide
  have hdescent : baseEnd_1609322 < baseStart_1609322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609345 : List Nat := [1, 2, 4, 2, 1, 3, 2, 1, 7]
def baseStart_1609345 : Nat := 118140960795 + 1609345 * 2 ^ 59
def prefixEnd_1609345 : Nat := 4983230072969 + 3 ^ 40 * 1609345 * 2
def baseEnd_1609345 : Nat := 91818613767790129331807

theorem tailTrace_1609345 : CollatzResearch.WordTrace tailWord_1609345 prefixEnd_1609345 91818613767790129331807 := by
  unfold tailWord_1609345
  simp only [CollatzResearch.WordTrace]
  refine ⟨58697634354625394088845489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39131756236416929392563659 58697634354625394088845489)
  ·
    refine ⟨44023225765969045566634117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58697634354625394088845489 44023225765969045566634117)
    ·
      refine ⟨8254354831119196043743897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44023225765969045566634117 8254354831119196043743897)
      ·
        refine ⟨6190766123339397032807923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8254354831119196043743897 6190766123339397032807923)
        ·
          refine ⟨9286149185009095549211885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6190766123339397032807923 9286149185009095549211885)
          ·
            refine ⟨3482305944378410830954457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9286149185009095549211885 3482305944378410830954457)
            ·
              refine ⟨2611729458283808123215843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3482305944378410830954457 2611729458283808123215843)
              ·
                refine ⟨3917594187425712184823765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2611729458283808123215843 3917594187425712184823765)
                ·
                  refine ⟨91818613767790129331807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3917594187425712184823765 91818613767790129331807)
                  ·
                    rfl

theorem cell23_1609345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 7].length) (baseStart_1609345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609345 prefixEnd_1609345 := by exact prefixLift 1609345
  have htrace : WordTrace (prefixWord ++ tailWord_1609345) baseStart_1609345 baseEnd_1609345 := by
    simpa [prefixWord, tailWord_1609345, baseEnd_1609345] using wordTrace_append hprefix tailTrace_1609345
  have hstable : (prefixWord ++ tailWord_1609345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609345).length < 2 ^ (prefixWord ++ tailWord_1609345).sum := by decide
  have hdescent : baseEnd_1609345 < baseStart_1609345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609365 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 2, 5, 2]
def baseStart_1609365 : Nat := 118140960795 + 1609365 * 2 ^ 59
def prefixEnd_1609365 : Nat := 4983230072969 + 3 ^ 40 * 1609365 * 2
def baseEnd_1609365 : Nat := 826377793523201085736171

theorem tailTrace_1609365 : CollatzResearch.WordTrace tailWord_1609365 prefixEnd_1609365 826377793523201085736171 := by
  unfold tailWord_1609365
  simp only [CollatzResearch.WordTrace]
  refine ⟨58698363814552937504573549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39132242543035291669715699 58698363814552937504573549)
  ·
    refine ⟨22011886430457351564215081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58698363814552937504573549 22011886430457351564215081)
    ·
      refine ⟨16508914822843013673161311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22011886430457351564215081 16508914822843013673161311)
      ·
        refine ⟨24763372234264520509741967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16508914822843013673161311 24763372234264520509741967)
        ·
          refine ⟨37145058351396780764612951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24763372234264520509741967 37145058351396780764612951)
          ·
            refine ⟨55717587527095171146919427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37145058351396780764612951 55717587527095171146919427)
            ·
              refine ⟨83576381290642756720379141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55717587527095171146919427 83576381290642756720379141)
              ·
                refine ⟨15670571491995516885071089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83576381290642756720379141 15670571491995516885071089)
                ·
                  refine ⟨11752928618996637663803317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15670571491995516885071089 11752928618996637663803317)
                  ·
                    refine ⟨1101837058030934780981561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11752928618996637663803317 1101837058030934780981561)
                    ·
                      refine ⟨826377793523201085736171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1101837058030934780981561 826377793523201085736171)
                      ·
                        rfl

theorem cell23_1609365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 5, 2].length) (baseStart_1609365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609365 prefixEnd_1609365 := by exact prefixLift 1609365
  have htrace : WordTrace (prefixWord ++ tailWord_1609365) baseStart_1609365 baseEnd_1609365 := by
    simpa [prefixWord, tailWord_1609365, baseEnd_1609365] using wordTrace_append hprefix tailTrace_1609365
  have hstable : (prefixWord ++ tailWord_1609365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609365).length < 2 ^ (prefixWord ++ tailWord_1609365).sum := by decide
  have hdescent : baseEnd_1609365 < baseStart_1609365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609395 : List Nat := [1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 4]
def baseStart_1609395 : Nat := 118140960795 + 1609395 * 2 ^ 59
def prefixEnd_1609395 : Nat := 4983230072969 + 3 ^ 40 * 1609395 * 2
def baseEnd_1609395 : Nat := 826393197942835968361033

theorem tailTrace_1609395 : CollatzResearch.WordTrace tailWord_1609395 prefixEnd_1609395 826393197942835968361033 := by
  unfold tailWord_1609395
  simp only [CollatzResearch.WordTrace]
  refine ⟨58699458004444252628165639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39132972002962835085443759 58699458004444252628165639)
  ·
    refine ⟨88049187006666378942248459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58699458004444252628165639 88049187006666378942248459)
    ·
      refine ⟨132073780509999568413372689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88049187006666378942248459 132073780509999568413372689)
      ·
        refine ⟨99055335382499676310029517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132073780509999568413372689 99055335382499676310029517)
        ·
          refine ⟨37145750768437378616261069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99055335382499676310029517 37145750768437378616261069)
          ·
            refine ⟨13929656538164016981097901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37145750768437378616261069 13929656538164016981097901)
            ·
              refine ⟨5223621201811506367911713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13929656538164016981097901 5223621201811506367911713)
              ·
                refine ⟨3917715901358629775933785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5223621201811506367911713 3917715901358629775933785)
                ·
                  refine ⟨2938286926018972331950339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3917715901358629775933785 2938286926018972331950339)
                  ·
                    refine ⟨4407430389028458497925509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2938286926018972331950339 4407430389028458497925509)
                    ·
                      refine ⟨826393197942835968361033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4407430389028458497925509 826393197942835968361033)
                      ·
                        rfl

theorem cell23_1609395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 2, 2, 1, 4].length) (baseStart_1609395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609395 prefixEnd_1609395 := by exact prefixLift 1609395
  have htrace : WordTrace (prefixWord ++ tailWord_1609395) baseStart_1609395 baseEnd_1609395 := by
    simpa [prefixWord, tailWord_1609395, baseEnd_1609395] using wordTrace_append hprefix tailTrace_1609395
  have hstable : (prefixWord ++ tailWord_1609395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609395).length < 2 ^ (prefixWord ++ tailWord_1609395).sum := by decide
  have hdescent : baseEnd_1609395 < baseStart_1609395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609412 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 1, 6, 2]
def baseStart_1609412 : Nat := 118140960795 + 1609412 * 2 ^ 59
def prefixEnd_1609412 : Nat := 4983230072969 + 3 ^ 40 * 1609412 * 2
def baseEnd_1609412 : Nat := 826401927113962401848455

theorem tailTrace_1609412 : CollatzResearch.WordTrace tailWord_1609412 prefixEnd_1609412 826401927113962401848455 := by
  unfold tailWord_1609412
  simp only [CollatzResearch.WordTrace]
  refine ⟨29350039022691332265767245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39133385363588443021022993 29350039022691332265767245)
  ·
    refine ⟨11006264633509249599662717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29350039022691332265767245 11006264633509249599662717)
    ·
      refine ⟨4127349237565968599873519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11006264633509249599662717 4127349237565968599873519)
      ·
        refine ⟨6191023856348952899810279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4127349237565968599873519 6191023856348952899810279)
        ·
          refine ⟨9286535784523429349715419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6191023856348952899810279 9286535784523429349715419)
          ·
            refine ⟨13929803676785144024573129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9286535784523429349715419 13929803676785144024573129)
            ·
              refine ⟨10447352757588858018429847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13929803676785144024573129 10447352757588858018429847)
              ·
                refine ⟨15671029136383287027644771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10447352757588858018429847 15671029136383287027644771)
                ·
                  refine ⟨23506543704574930541467157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15671029136383287027644771 23506543704574930541467157)
                  ·
                    refine ⟨1101869236151949869131273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23506543704574930541467157 1101869236151949869131273)
                    ·
                      refine ⟨826401927113962401848455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1101869236151949869131273 826401927113962401848455)
                      ·
                        rfl

theorem cell23_1609412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_1609412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609412 prefixEnd_1609412 := by exact prefixLift 1609412
  have htrace : WordTrace (prefixWord ++ tailWord_1609412) baseStart_1609412 baseEnd_1609412 := by
    simpa [prefixWord, tailWord_1609412, baseEnd_1609412] using wordTrace_append hprefix tailTrace_1609412
  have hstable : (prefixWord ++ tailWord_1609412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609412).length < 2 ^ (prefixWord ++ tailWord_1609412).sum := by decide
  have hdescent : baseEnd_1609412 < baseStart_1609412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609415 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 4, 2, 3]
def baseStart_1609415 : Nat := 118140960795 + 1609415 * 2 ^ 59
def prefixEnd_1609415 : Nat := 4983230072969 + 3 ^ 40 * 1609415 * 2
def baseEnd_1609415 : Nat := 826403467555925890110941

theorem tailTrace_1609415 : CollatzResearch.WordTrace tailWord_1609415 prefixEnd_1609415 826403467555925890110941 := by
  unfold tailWord_1609415
  simp only [CollatzResearch.WordTrace]
  refine ⟨58700187464371796043893699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39133458309581197362595799 58700187464371796043893699)
  ·
    refine ⟨88050281196557694065840549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58700187464371796043893699 88050281196557694065840549)
    ·
      refine ⟨16509427724354567637345103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88050281196557694065840549 16509427724354567637345103)
      ·
        refine ⟨24764141586531851456017655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16509427724354567637345103 24764141586531851456017655)
        ·
          refine ⟨37146212379797777184026483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24764141586531851456017655 37146212379797777184026483)
          ·
            refine ⟨55719318569696665776039725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37146212379797777184026483 55719318569696665776039725)
            ·
              refine ⟨20894744463636249666014897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55719318569696665776039725 20894744463636249666014897)
              ·
                refine ⟨15671058347727187249511173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20894744463636249666014897 15671058347727187249511173)
                ·
                  refine ⟨2938323440198847609283345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15671058347727187249511173 2938323440198847609283345)
                  ·
                    refine ⟨2203742580149135706962509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2938323440198847609283345 2203742580149135706962509)
                    ·
                      refine ⟨826403467555925890110941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2203742580149135706962509 826403467555925890110941)
                      ·
                        rfl

theorem cell23_1609415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_1609415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609415 prefixEnd_1609415 := by exact prefixLift 1609415
  have htrace : WordTrace (prefixWord ++ tailWord_1609415) baseStart_1609415 baseEnd_1609415 := by
    simpa [prefixWord, tailWord_1609415, baseEnd_1609415] using wordTrace_append hprefix tailTrace_1609415
  have hstable : (prefixWord ++ tailWord_1609415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609415).length < 2 ^ (prefixWord ++ tailWord_1609415).sum := by decide
  have hdescent : baseEnd_1609415 < baseStart_1609415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609432 : List Nat := [2, 1, 2, 2, 3, 1, 4, 1, 2, 2, 3]
def baseStart_1609432 : Nat := 118140960795 + 1609432 * 2 ^ 59
def prefixEnd_1609432 : Nat := 4983230072969 + 3 ^ 40 * 1609432 * 2
def baseEnd_1609432 : Nat := 826412196727052323598363

theorem tailTrace_1609432 : CollatzResearch.WordTrace tailWord_1609432 prefixEnd_1609432 826412196727052323598363 := by
  unfold tailWord_1609432
  simp only [CollatzResearch.WordTrace]
  refine ⟨29350403752655103973631275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39133871670206805298175033 29350403752655103973631275)
  ·
    refine ⟨44025605628982655960446913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29350403752655103973631275 44025605628982655960446913)
    ·
      refine ⟨33019204221736991970335185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44025605628982655960446913 33019204221736991970335185)
      ·
        refine ⟨24764403166302743977751389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33019204221736991970335185 24764403166302743977751389)
        ·
          refine ⟨9286651187363528991656771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24764403166302743977751389 9286651187363528991656771)
          ·
            refine ⟨13929976781045293487485157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9286651187363528991656771 13929976781045293487485157)
            ·
              refine ⟨2611870646445992528903467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13929976781045293487485157 2611870646445992528903467)
              ·
                refine ⟨3917805969668988793355201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2611870646445992528903467 3917805969668988793355201)
                ·
                  refine ⟨2938354477251741595016401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3917805969668988793355201 2938354477251741595016401)
                  ·
                    refine ⟨2203765857938806196262301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2938354477251741595016401 2203765857938806196262301)
                    ·
                      refine ⟨826412196727052323598363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2203765857938806196262301 826412196727052323598363)
                      ·
                        rfl

theorem cell23_1609432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_1609432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609432 prefixEnd_1609432 := by exact prefixLift 1609432
  have htrace : WordTrace (prefixWord ++ tailWord_1609432) baseStart_1609432 baseEnd_1609432 := by
    simpa [prefixWord, tailWord_1609432, baseEnd_1609432] using wordTrace_append hprefix tailTrace_1609432
  have hstable : (prefixWord ++ tailWord_1609432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609432).length < 2 ^ (prefixWord ++ tailWord_1609432).sum := by decide
  have hdescent : baseEnd_1609432 < baseStart_1609432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609522 : List Nat := [3, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5]
def baseStart_1609522 : Nat := 118140960795 + 1609522 * 2 ^ 59
def prefixEnd_1609522 : Nat := 4983230072969 + 3 ^ 40 * 1609522 * 2
def baseEnd_1609522 : Nat := 826458409985956971472949

theorem tailTrace_1609522 : CollatzResearch.WordTrace tailWord_1609522 prefixEnd_1609522 826458409985956971472949 := by
  unfold tailWord_1609522
  simp only [CollatzResearch.WordTrace]
  refine ⟨14676022518746038329509705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39136060049989435545359213 14676022518746038329509705)
  ·
    refine ⟨11007016889059528747132279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14676022518746038329509705 11007016889059528747132279)
    ·
      refine ⟨16510525333589293120698419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11007016889059528747132279 16510525333589293120698419)
      ·
        refine ⟨24765788000383939681047629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16510525333589293120698419 24765788000383939681047629)
        ·
          refine ⟨9287170500143977380392861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24765788000383939681047629 9287170500143977380392861)
          ·
            refine ⟨3482688937553991517647323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9287170500143977380392861 3482688937553991517647323)
            ·
              refine ⟨5224033406330987276470985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3482688937553991517647323 5224033406330987276470985)
              ·
                refine ⟨3918025054748240457353239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5224033406330987276470985 3918025054748240457353239)
                ·
                  refine ⟨5877037582122360686029859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3918025054748240457353239 5877037582122360686029859)
                  ·
                    refine ⟨8815556373183541029044789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5877037582122360686029859 8815556373183541029044789)
                    ·
                      refine ⟨826458409985956971472949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8815556373183541029044789 826458409985956971472949)
                      ·
                        rfl

theorem cell23_1609522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_1609522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609522 prefixEnd_1609522 := by exact prefixLift 1609522
  have htrace : WordTrace (prefixWord ++ tailWord_1609522) baseStart_1609522 baseEnd_1609522 := by
    simpa [prefixWord, tailWord_1609522, baseEnd_1609522] using wordTrace_append hprefix tailTrace_1609522
  have hstable : (prefixWord ++ tailWord_1609522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609522).length < 2 ^ (prefixWord ++ tailWord_1609522).sum := by decide
  have hdescent : baseEnd_1609522 < baseStart_1609522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609532 : List Nat := [2, 2, 2, 2, 1, 1, 5, 1, 1, 2, 4]
def baseStart_1609532 : Nat := 118140960795 + 1609532 * 2 ^ 59
def prefixEnd_1609532 : Nat := 4983230072969 + 3 ^ 40 * 1609532 * 2
def baseEnd_1609532 : Nat := 826463544792501932347903

theorem tailTrace_1609532 : CollatzResearch.WordTrace tailWord_1609532 prefixEnd_1609532 826463544792501932347903 := by
  unfold tailWord_1609532
  simp only [CollatzResearch.WordTrace]
  refine ⟨29352227402473962512951425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39136303203298616683935233 29352227402473962512951425)
  ·
    refine ⟨22014170551855471884713569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29352227402473962512951425 22014170551855471884713569)
    ·
      refine ⟨16510627913891603913535177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22014170551855471884713569 16510627913891603913535177)
      ·
        refine ⟨12382970935418702935151383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16510627913891603913535177 12382970935418702935151383)
        ·
          refine ⟨18574456403128054402727075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12382970935418702935151383 18574456403128054402727075)
          ·
            refine ⟨27861684604692081604090613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18574456403128054402727075 27861684604692081604090613)
            ·
              refine ⟨2612032931689882650383495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27861684604692081604090613 2612032931689882650383495)
              ·
                refine ⟨3918049397534823975575243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2612032931689882650383495 3918049397534823975575243)
                ·
                  refine ⟨5877074096302235963362865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3918049397534823975575243 5877074096302235963362865)
                  ·
                    refine ⟨4407805572226676972522149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5877074096302235963362865 4407805572226676972522149)
                    ·
                      refine ⟨826463544792501932347903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4407805572226676972522149 826463544792501932347903)
                      ·
                        rfl

theorem cell23_1609532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_1609532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609532 prefixEnd_1609532 := by exact prefixLift 1609532
  have htrace : WordTrace (prefixWord ++ tailWord_1609532) baseStart_1609532 baseEnd_1609532 := by
    simpa [prefixWord, tailWord_1609532, baseEnd_1609532] using wordTrace_append hprefix tailTrace_1609532
  have hstable : (prefixWord ++ tailWord_1609532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609532).length < 2 ^ (prefixWord ++ tailWord_1609532).sum := by decide
  have hdescent : baseEnd_1609532 < baseStart_1609532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609539 : List Nat := [1, 1, 1, 3, 1, 6, 2, 2, 1, 2, 3]
def baseStart_1609539 : Nat := 118140960795 + 1609539 * 2 ^ 59
def prefixEnd_1609539 : Nat := 4983230072969 + 3 ^ 40 * 1609539 * 2
def baseEnd_1609539 : Nat := 826467139157083404960371

theorem tailTrace_1609539 : CollatzResearch.WordTrace tailWord_1609539 prefixEnd_1609539 826467139157083404960371 := by
  unfold tailWord_1609539
  simp only [CollatzResearch.WordTrace]
  refine ⟨58704710115922565221407671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39136473410615043480938447 58704710115922565221407671)
  ·
    refine ⟨88057065173883847832111507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58704710115922565221407671 88057065173883847832111507)
    ·
      refine ⟨132085597760825771748167261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88057065173883847832111507 132085597760825771748167261)
      ·
        refine ⟨49532099160309664405562723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132085597760825771748167261 49532099160309664405562723)
        ·
          refine ⟨74298148740464496608344085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49532099160309664405562723 74298148740464496608344085)
          ·
            refine ⟨3482725722209273278516129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 74298148740464496608344085 3482725722209273278516129)
            ·
              refine ⟨2612044291656954958887097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3482725722209273278516129 2612044291656954958887097)
              ·
                refine ⟨1959033218742716219165323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2612044291656954958887097 1959033218742716219165323)
                ·
                  refine ⟨2938549828114074328747985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1959033218742716219165323 2938549828114074328747985)
                  ·
                    refine ⟨2203912371085555746560989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2938549828114074328747985 2203912371085555746560989)
                    ·
                      refine ⟨826467139157083404960371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2203912371085555746560989 826467139157083404960371)
                      ·
                        rfl

theorem cell23_1609539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 2, 3].length) (baseStart_1609539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609539 prefixEnd_1609539 := by exact prefixLift 1609539
  have htrace : WordTrace (prefixWord ++ tailWord_1609539) baseStart_1609539 baseEnd_1609539 := by
    simpa [prefixWord, tailWord_1609539, baseEnd_1609539] using wordTrace_append hprefix tailTrace_1609539
  have hstable : (prefixWord ++ tailWord_1609539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609539).length < 2 ^ (prefixWord ++ tailWord_1609539).sum := by decide
  have hdescent : baseEnd_1609539 < baseStart_1609539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609553 : List Nat := [1, 2, 2, 1, 5, 1, 3, 3, 1, 2, 2]
def baseStart_1609553 : Nat := 118140960795 + 1609553 * 2 ^ 59
def prefixEnd_1609553 : Nat := 4983230072969 + 3 ^ 40 * 1609553 * 2
def baseEnd_1609553 : Nat := 826474327886246350185307

theorem tailTrace_1609553 : CollatzResearch.WordTrace tailWord_1609553 prefixEnd_1609553 826474327886246350185307 := by
  unfold tailWord_1609553
  simp only [CollatzResearch.WordTrace]
  refine ⟨58705220737871845612417313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39136813825247897074944875 58705220737871845612417313)
  ·
    refine ⟨44028915553403884209312985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58705220737871845612417313 44028915553403884209312985)
    ·
      refine ⟨33021686665052913156984739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44028915553403884209312985 33021686665052913156984739)
      ·
        refine ⟨49532529997579369735477109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33021686665052913156984739 49532529997579369735477109)
        ·
          refine ⟨4643674687273065912700979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49532529997579369735477109 4643674687273065912700979)
          ·
            refine ⟨6965512030909598869051469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4643674687273065912700979 6965512030909598869051469)
            ·
              refine ⟨2612067011591099575894301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6965512030909598869051469 2612067011591099575894301)
              ·
                refine ⟨979525129346662340960363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2612067011591099575894301 979525129346662340960363)
                ·
                  refine ⟨1469287694019993511440545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 979525129346662340960363 1469287694019993511440545)
                  ·
                    refine ⟨1101965770514995133580409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1469287694019993511440545 1101965770514995133580409)
                    ·
                      refine ⟨826474327886246350185307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1101965770514995133580409 826474327886246350185307)
                      ·
                        rfl

theorem cell23_1609553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3, 1, 2, 2].length) (baseStart_1609553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609553 prefixEnd_1609553 := by exact prefixLift 1609553
  have htrace : WordTrace (prefixWord ++ tailWord_1609553) baseStart_1609553 baseEnd_1609553 := by
    simpa [prefixWord, tailWord_1609553, baseEnd_1609553] using wordTrace_append hprefix tailTrace_1609553
  have hstable : (prefixWord ++ tailWord_1609553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609553).length < 2 ^ (prefixWord ++ tailWord_1609553).sum := by decide
  have hdescent : baseEnd_1609553 < baseStart_1609553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609569 : List Nat := [1, 2, 3, 1, 1, 1, 4, 4, 2, 1, 3]
def baseStart_1609569 : Nat := 118140960795 + 1609569 * 2 ^ 59
def prefixEnd_1609569 : Nat := 4983230072969 + 3 ^ 40 * 1609569 * 2
def baseEnd_1609569 : Nat := 826482543576718287585233

theorem tailTrace_1609569 : CollatzResearch.WordTrace tailWord_1609569 prefixEnd_1609569 826482543576718287585233 := by
  unfold tailWord_1609569
  simp only [CollatzResearch.WordTrace]
  refine ⟨58705804305813880344999761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39137202870542586896666507 58705804305813880344999761)
  ·
    refine ⟨44029353229360410258749821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58705804305813880344999761 44029353229360410258749821)
    ·
      refine ⟨16511007461010153847031183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44029353229360410258749821 16511007461010153847031183)
      ·
        refine ⟨24766511191515230770546775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16511007461010153847031183 24766511191515230770546775)
        ·
          refine ⟨37149766787272846155820163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24766511191515230770546775 37149766787272846155820163)
          ·
            refine ⟨55724650180909269233730245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37149766787272846155820163 55724650180909269233730245)
            ·
              refine ⟨10448371908920487981324421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55724650180909269233730245 10448371908920487981324421)
              ·
                refine ⟨1959069732922591496498329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10448371908920487981324421 1959069732922591496498329)
                ·
                  refine ⟨1469302299691943622373747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1959069732922591496498329 1469302299691943622373747)
                  ·
                    refine ⟨2203953449537915433560621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1469302299691943622373747 2203953449537915433560621)
                    ·
                      refine ⟨826482543576718287585233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2203953449537915433560621 826482543576718287585233)
                      ·
                        rfl

theorem cell23_1609569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_1609569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609569 prefixEnd_1609569 := by exact prefixLift 1609569
  have htrace : WordTrace (prefixWord ++ tailWord_1609569) baseStart_1609569 baseEnd_1609569 := by
    simpa [prefixWord, tailWord_1609569, baseEnd_1609569] using wordTrace_append hprefix tailTrace_1609569
  have hstable : (prefixWord ++ tailWord_1609569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609569).length < 2 ^ (prefixWord ++ tailWord_1609569).sum := by decide
  have hdescent : baseEnd_1609569 < baseStart_1609569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609585 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 1, 8]
def baseStart_1609585 : Nat := 118140960795 + 1609585 * 2 ^ 59
def prefixEnd_1609585 : Nat := 4983230072969 + 3 ^ 40 * 1609585 * 2
def baseEnd_1609585 : Nat := 275496919755730074995053

theorem tailTrace_1609585 : CollatzResearch.WordTrace tailWord_1609585 prefixEnd_1609585 275496919755730074995053 := by
  unfold tailWord_1609585
  simp only [CollatzResearch.WordTrace]
  refine ⟨58706387873755915077582209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39137591915837276718388139 58706387873755915077582209)
  ·
    refine ⟨44029790905316936308186657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58706387873755915077582209 44029790905316936308186657)
    ·
      refine ⟨33022343178987702231139993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44029790905316936308186657 33022343178987702231139993)
      ·
        refine ⟨24766757384240776673354995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33022343178987702231139993 24766757384240776673354995)
        ·
          refine ⟨37150136076361165010032493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24766757384240776673354995 37150136076361165010032493)
          ·
            refine ⟨13931301028635436878762185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37150136076361165010032493 13931301028635436878762185)
            ·
              refine ⟨10448475771476577659071639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13931301028635436878762185 10448475771476577659071639)
              ·
                refine ⟨15672713657214866488607459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10448475771476577659071639 15672713657214866488607459)
                ·
                  refine ⟨23509070485822299732911189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15672713657214866488607459 23509070485822299732911189)
                  ·
                    refine ⟨275496919755730074995053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23509070485822299732911189 275496919755730074995053)
                    ·
                      rfl

theorem cell23_1609585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_1609585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609585 prefixEnd_1609585 := by exact prefixLift 1609585
  have htrace : WordTrace (prefixWord ++ tailWord_1609585) baseStart_1609585 baseEnd_1609585 := by
    simpa [prefixWord, tailWord_1609585, baseEnd_1609585] using wordTrace_append hprefix tailTrace_1609585
  have hstable : (prefixWord ++ tailWord_1609585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609585).length < 2 ^ (prefixWord ++ tailWord_1609585).sum := by decide
  have hdescent : baseEnd_1609585 < baseStart_1609585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609590 : List Nat := [5, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3]
def baseStart_1609590 : Nat := 118140960795 + 1609590 * 2 ^ 59
def prefixEnd_1609590 : Nat := 4983230072969 + 3 ^ 40 * 1609590 * 2
def baseEnd_1609590 : Nat := 826493326670462705422637

theorem tailTrace_1609590 : CollatzResearch.WordTrace tailWord_1609590 prefixEnd_1609590 826493326670462705422637 := by
  unfold tailWord_1609590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3669160639921112558219639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39137713492491867287676149 3669160639921112558219639)
  ·
    refine ⟨5503740959881668837329459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3669160639921112558219639 5503740959881668837329459)
    ·
      refine ⟨8255611439822503255994189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5503740959881668837329459 8255611439822503255994189)
      ·
        refine ⟨3095854289933438720997821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8255611439822503255994189 3095854289933438720997821)
        ·
          refine ⟨1160945358725039520374183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3095854289933438720997821 1160945358725039520374183)
          ·
            refine ⟨1741418038087559280561275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160945358725039520374183 1741418038087559280561275)
            ·
              refine ⟨2612127057131338920841913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1741418038087559280561275 2612127057131338920841913)
              ·
                refine ⟨1959095292848504190631435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2612127057131338920841913 1959095292848504190631435)
                ·
                  refine ⟨2938642939272756285947153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1959095292848504190631435 2938642939272756285947153)
                  ·
                    refine ⟨2203982204454567214460365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2938642939272756285947153 2203982204454567214460365)
                    ·
                      refine ⟨826493326670462705422637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2203982204454567214460365 826493326670462705422637)
                      ·
                        rfl

theorem cell23_1609590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_1609590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609590 prefixEnd_1609590 := by exact prefixLift 1609590
  have htrace : WordTrace (prefixWord ++ tailWord_1609590) baseStart_1609590 baseEnd_1609590 := by
    simpa [prefixWord, tailWord_1609590, baseEnd_1609590] using wordTrace_append hprefix tailTrace_1609590
  have hstable : (prefixWord ++ tailWord_1609590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609590).length < 2 ^ (prefixWord ++ tailWord_1609590).sum := by decide
  have hdescent : baseEnd_1609590 < baseStart_1609590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609609 : List Nat := [1, 2, 1, 1, 5, 1, 3, 2, 1, 4, 2]
def baseStart_1609609 : Nat := 118140960795 + 1609609 * 2 ^ 59
def prefixEnd_1609609 : Nat := 4983230072969 + 3 ^ 40 * 1609609 * 2
def baseEnd_1609609 : Nat := 826503082802898131085049

theorem tailTrace_1609609 : CollatzResearch.WordTrace tailWord_1609609 prefixEnd_1609609 826503082802898131085049 := by
  unfold tailWord_1609609
  simp only [CollatzResearch.WordTrace]
  refine ⟨58707263225668967176455881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39138175483779311450970587 58707263225668967176455881)
  ·
    refine ⟨44030447419251725382341911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58707263225668967176455881 44030447419251725382341911)
    ·
      refine ⟨66045671128877588073512867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44030447419251725382341911 66045671128877588073512867)
      ·
        refine ⟨99068506693316382110269301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66045671128877588073512867 99068506693316382110269301)
        ·
          refine ⟨9287672502498410822837747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99068506693316382110269301 9287672502498410822837747)
          ·
            refine ⟨13931508753747616234256621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9287672502498410822837747 13931508753747616234256621)
            ·
              refine ⟨5224315782655356087846233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13931508753747616234256621 5224315782655356087846233)
              ·
                refine ⟨3918236836991517065884675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5224315782655356087846233 3918236836991517065884675)
                ·
                  refine ⟨5877355255487275598827013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3918236836991517065884675 5877355255487275598827013)
                  ·
                    refine ⟨1102004110403864174780065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5877355255487275598827013 1102004110403864174780065)
                    ·
                      refine ⟨826503082802898131085049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1102004110403864174780065 826503082802898131085049)
                      ·
                        rfl

theorem cell23_1609609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 4, 2].length) (baseStart_1609609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609609 prefixEnd_1609609 := by exact prefixLift 1609609
  have htrace : WordTrace (prefixWord ++ tailWord_1609609) baseStart_1609609 baseEnd_1609609 := by
    simpa [prefixWord, tailWord_1609609, baseEnd_1609609] using wordTrace_append hprefix tailTrace_1609609
  have hstable : (prefixWord ++ tailWord_1609609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609609).length < 2 ^ (prefixWord ++ tailWord_1609609).sum := by decide
  have hdescent : baseEnd_1609609 < baseStart_1609609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609625 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 1, 2, 7]
def baseStart_1609625 : Nat := 118140960795 + 1609625 * 2 ^ 59
def prefixEnd_1609625 : Nat := 4983230072969 + 3 ^ 40 * 1609625 * 2
def baseEnd_1609625 : Nat := 826511298493370068484975

theorem tailTrace_1609625 : CollatzResearch.WordTrace tailWord_1609625 prefixEnd_1609625 826511298493370068484975 := by
  unfold tailWord_1609625
  simp only [CollatzResearch.WordTrace]
  refine ⟨58707846793611001909038329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39138564529074001272692219 58707846793611001909038329)
  ·
    refine ⟨44030885095208251431778747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58707846793611001909038329 44030885095208251431778747)
    ·
      refine ⟨66046327642812377147668121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44030885095208251431778747 66046327642812377147668121)
      ·
        refine ⟨49534745732109282860751091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66046327642812377147668121 49534745732109282860751091)
        ·
          refine ⟨74302118598163924291126637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49534745732109282860751091 74302118598163924291126637)
          ·
            refine ⟨27863294474311471609172489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74302118598163924291126637 27863294474311471609172489)
            ·
              refine ⟨20897470855733603706879367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27863294474311471609172489 20897470855733603706879367)
              ·
                refine ⟨31346206283600405560319051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20897470855733603706879367 31346206283600405560319051)
                ·
                  refine ⟨47019309425400608340478577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31346206283600405560319051 47019309425400608340478577)
                  ·
                    refine ⟨35264482069050456255358933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47019309425400608340478577 35264482069050456255358933)
                    ·
                      refine ⟨826511298493370068484975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35264482069050456255358933 826511298493370068484975)
                      ·
                        rfl

theorem cell23_1609625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_1609625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609625 prefixEnd_1609625 := by exact prefixLift 1609625
  have htrace : WordTrace (prefixWord ++ tailWord_1609625) baseStart_1609625 baseEnd_1609625 := by
    simpa [prefixWord, tailWord_1609625, baseEnd_1609625] using wordTrace_append hprefix tailTrace_1609625
  have hstable : (prefixWord ++ tailWord_1609625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609625).length < 2 ^ (prefixWord ++ tailWord_1609625).sum := by decide
  have hdescent : baseEnd_1609625 < baseStart_1609625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609635 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 8]
def baseStart_1609635 : Nat := 118140960795 + 1609635 * 2 ^ 59
def prefixEnd_1609635 : Nat := 4983230072969 + 3 ^ 40 * 1609635 * 2
def baseEnd_1609635 : Nat := 826516433299915029359929

theorem tailTrace_1609635 : CollatzResearch.WordTrace tailWord_1609635 prefixEnd_1609635 826516433299915029359929 := by
  unfold tailWord_1609635
  simp only [CollatzResearch.WordTrace]
  refine ⟨58708211523574773616902359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39138807682383182411268239 58708211523574773616902359)
  ·
    refine ⟨88062317285362160425353539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58708211523574773616902359 88062317285362160425353539)
    ·
      refine ⟨132093475928043240638030309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88062317285362160425353539 132093475928043240638030309)
      ·
        refine ⟨24767526736508107619630683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132093475928043240638030309 24767526736508107619630683)
        ·
          refine ⟨37151290104762161429446025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24767526736508107619630683 37151290104762161429446025)
          ·
            refine ⟨27863467578571621072084519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37151290104762161429446025 27863467578571621072084519)
            ·
              refine ⟨41795201367857431608126779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27863467578571621072084519 41795201367857431608126779)
              ·
                refine ⟨62692802051786147412190169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41795201367857431608126779 62692802051786147412190169)
                ·
                  refine ⟨47019601538839610559142627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62692802051786147412190169 47019601538839610559142627)
                  ·
                    refine ⟨70529402308259415838713941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47019601538839610559142627 70529402308259415838713941)
                    ·
                      refine ⟨826516433299915029359929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 70529402308259415838713941 826516433299915029359929)
                      ·
                        rfl

theorem cell23_1609635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_1609635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609635 prefixEnd_1609635 := by exact prefixLift 1609635
  have htrace : WordTrace (prefixWord ++ tailWord_1609635) baseStart_1609635 baseEnd_1609635 := by
    simpa [prefixWord, tailWord_1609635, baseEnd_1609635] using wordTrace_append hprefix tailTrace_1609635
  have hstable : (prefixWord ++ tailWord_1609635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609635).length < 2 ^ (prefixWord ++ tailWord_1609635).sum := by decide
  have hdescent : baseEnd_1609635 < baseStart_1609635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609639 : List Nat := [1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_1609639 : Nat := 118140960795 + 1609639 * 2 ^ 59
def prefixEnd_1609639 : Nat := 4983230072969 + 3 ^ 40 * 1609639 * 2
def baseEnd_1609639 : Nat := 826518487222533013709911

theorem tailTrace_1609639 : CollatzResearch.WordTrace tailWord_1609639 prefixEnd_1609639 826518487222533013709911 := by
  unfold tailWord_1609639
  simp only [CollatzResearch.WordTrace]
  refine ⟨58708357415560282300047971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39138904943706854866698647 58708357415560282300047971)
  ·
    refine ⟨88062536123340423450071957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58708357415560282300047971 88062536123340423450071957)
    ·
      refine ⟨4127931380781582349222123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 88062536123340423450071957 4127931380781582349222123)
      ·
        refine ⟨6191897071172373523833185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4127931380781582349222123 6191897071172373523833185)
        ·
          refine ⟨4643922803379280142874889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6191897071172373523833185 4643922803379280142874889)
          ·
            refine ⟨3482942102534460107156167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4643922803379280142874889 3482942102534460107156167)
            ·
              refine ⟨5224413153801690160734251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3482942102534460107156167 5224413153801690160734251)
              ·
                refine ⟨7836619730702535241101377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5224413153801690160734251 7836619730702535241101377)
                ·
                  refine ⟨5877464798026901430826033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7836619730702535241101377 5877464798026901430826033)
                  ·
                    refine ⟨4408098598520176073119525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5877464798026901430826033 4408098598520176073119525)
                    ·
                      refine ⟨826518487222533013709911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4408098598520176073119525 826518487222533013709911)
                      ·
                        rfl

theorem cell23_1609639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_1609639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609639 prefixEnd_1609639 := by exact prefixLift 1609639
  have htrace : WordTrace (prefixWord ++ tailWord_1609639) baseStart_1609639 baseEnd_1609639 := by
    simpa [prefixWord, tailWord_1609639, baseEnd_1609639] using wordTrace_append hprefix tailTrace_1609639
  have hstable : (prefixWord ++ tailWord_1609639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609639).length < 2 ^ (prefixWord ++ tailWord_1609639).sum := by decide
  have hdescent : baseEnd_1609639 < baseStart_1609639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609734 : List Nat := [6, 2, 1, 2, 1, 1, 3, 2, 5]
def baseStart_1609734 : Nat := 118140960795 + 1609734 * 2 ^ 59
def prefixEnd_1609734 : Nat := 4983230072969 + 3 ^ 40 * 1609734 * 2
def baseEnd_1609734 : Nat := 91840807542745571335775

theorem tailTrace_1609734 : CollatzResearch.WordTrace tailWord_1609734 prefixEnd_1609734 91840807542745571335775 := by
  unfold tailWord_1609734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1834744448444253547648633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39141214900144075683170837 1834744448444253547648633)
  ·
    refine ⟨1376058336333190160736475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1834744448444253547648633 1376058336333190160736475)
    ·
      refine ⟨2064087504499785241104713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1376058336333190160736475 2064087504499785241104713)
      ·
        refine ⟨1548065628374838930828535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2064087504499785241104713 1548065628374838930828535)
        ·
          refine ⟨2322098442562258396242803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1548065628374838930828535 2322098442562258396242803)
          ·
            refine ⟨3483147663843387594364205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2322098442562258396242803 3483147663843387594364205)
            ·
              refine ⟨1306180373941270347886577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3483147663843387594364205 1306180373941270347886577)
              ·
                refine ⟨979635280455952760914933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1306180373941270347886577 979635280455952760914933)
                ·
                  refine ⟨91840807542745571335775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 979635280455952760914933 91840807542745571335775)
                  ·
                    rfl

theorem cell23_1609734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_1609734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609734 prefixEnd_1609734 := by exact prefixLift 1609734
  have htrace : WordTrace (prefixWord ++ tailWord_1609734) baseStart_1609734 baseEnd_1609734 := by
    simpa [prefixWord, tailWord_1609734, baseEnd_1609734] using wordTrace_append hprefix tailTrace_1609734
  have hstable : (prefixWord ++ tailWord_1609734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609734).length < 2 ^ (prefixWord ++ tailWord_1609734).sum := by decide
  have hdescent : baseEnd_1609734 < baseStart_1609734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609756 : List Nat := [2, 2, 3, 1, 3, 1, 4, 1, 6]
def baseStart_1609756 : Nat := 118140960795 + 1609756 * 2 ^ 59
def prefixEnd_1609756 : Nat := 4983230072969 + 3 ^ 40 * 1609756 * 2
def baseEnd_1609756 : Nat := 91842062717678783994097

theorem tailTrace_1609756 : CollatzResearch.WordTrace tailWord_1609756 prefixEnd_1609756 91842062717678783994097 := by
  unfold tailWord_1609756
  simp only [CollatzResearch.WordTrace]
  refine ⟨29356312378068205641028561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39141749837424274188038081 29356312378068205641028561)
  ·
    refine ⟨22017234283551154230771421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29356312378068205641028561 22017234283551154230771421)
    ·
      refine ⟨8256462856331682836539283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22017234283551154230771421 8256462856331682836539283)
      ·
        refine ⟨12384694284497524254808925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8256462856331682836539283 12384694284497524254808925)
        ·
          refine ⟨4644260356686571595553347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12384694284497524254808925 4644260356686571595553347)
          ·
            refine ⟨6966390535029857393330021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4644260356686571595553347 6966390535029857393330021)
            ·
              refine ⟨1306198225318098261249379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6966390535029857393330021 1306198225318098261249379)
              ·
                refine ⟨1959297337977147391874069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1306198225318098261249379 1959297337977147391874069)
                ·
                  refine ⟨91842062717678783994097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1959297337977147391874069 91842062717678783994097)
                  ·
                    rfl

theorem cell23_1609756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 1, 6].length) (baseStart_1609756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609756 prefixEnd_1609756 := by exact prefixLift 1609756
  have htrace : WordTrace (prefixWord ++ tailWord_1609756) baseStart_1609756 baseEnd_1609756 := by
    simpa [prefixWord, tailWord_1609756, baseEnd_1609756] using wordTrace_append hprefix tailTrace_1609756
  have hstable : (prefixWord ++ tailWord_1609756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609756).length < 2 ^ (prefixWord ++ tailWord_1609756).sum := by decide
  have hdescent : baseEnd_1609756 < baseStart_1609756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609776 : List Nat := [2, 1, 1, 1, 2, 5, 1, 3, 2, 3, 2]
def baseStart_1609776 : Nat := 118140960795 + 1609776 * 2 ^ 59
def prefixEnd_1609776 : Nat := 4983230072969 + 3 ^ 40 * 1609776 * 2
def baseEnd_1609776 : Nat := 826588834072198977696781

theorem tailTrace_1609776 : CollatzResearch.WordTrace tailWord_1609776 prefixEnd_1609776 826588834072198977696781 := by
  unfold tailWord_1609776
  simp only [CollatzResearch.WordTrace]
  refine ⟨29356677108031977348892591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39142236144042636465190121 29356677108031977348892591)
  ·
    refine ⟨44035015662047966023338887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29356677108031977348892591 44035015662047966023338887)
    ·
      refine ⟨66052523493071949035008331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44035015662047966023338887 66052523493071949035008331)
      ·
        refine ⟨99078785239607923552512497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66052523493071949035008331 99078785239607923552512497)
        ·
          refine ⟨74309088929705942664384373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99078785239607923552512497 74309088929705942664384373)
          ·
            refine ⟨6966477087159932124786035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74309088929705942664384373 6966477087159932124786035)
            ·
              refine ⟨10449715630739898187179053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6966477087159932124786035 10449715630739898187179053)
              ·
                refine ⟨3918643361527461820192145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10449715630739898187179053 3918643361527461820192145)
                ·
                  refine ⟨2938982521145596365144109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3918643361527461820192145 2938982521145596365144109)
                  ·
                    refine ⟨1102118445429598636929041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2938982521145596365144109 1102118445429598636929041)
                    ·
                      refine ⟨826588834072198977696781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1102118445429598636929041 826588834072198977696781)
                      ·
                        rfl

theorem cell23_1609776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 2, 3, 2].length) (baseStart_1609776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609776 prefixEnd_1609776 := by exact prefixLift 1609776
  have htrace : WordTrace (prefixWord ++ tailWord_1609776) baseStart_1609776 baseEnd_1609776 := by
    simpa [prefixWord, tailWord_1609776, baseEnd_1609776] using wordTrace_append hprefix tailTrace_1609776
  have hstable : (prefixWord ++ tailWord_1609776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609776).length < 2 ^ (prefixWord ++ tailWord_1609776).sum := by decide
  have hdescent : baseEnd_1609776 < baseStart_1609776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609793 : List Nat := [1, 2, 5, 1, 2, 1, 2, 2, 2, 3, 2]
def baseStart_1609793 : Nat := 118140960795 + 1609793 * 2 ^ 59
def prefixEnd_1609793 : Nat := 4983230072969 + 3 ^ 40 * 1609793 * 2
def baseEnd_1609793 : Nat := 826597563243325411184203

theorem tailTrace_1609793 : CollatzResearch.WordTrace tailWord_1609793 prefixEnd_1609793 826597563243325411184203 := by
  unfold tailWord_1609793
  simp only [CollatzResearch.WordTrace]
  refine ⟨58713974257002366601154033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39142649504668244400769355 58713974257002366601154033)
  ·
    refine ⟨44035480692751774950865525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58713974257002366601154033 44035480692751774950865525)
    ·
      refine ⟨4128326314945478901643643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44035480692751774950865525 4128326314945478901643643)
      ·
        refine ⟨6192489472418218352465465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4128326314945478901643643 6192489472418218352465465)
        ·
          refine ⟨4644367104313663764349099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6192489472418218352465465 4644367104313663764349099)
          ·
            refine ⟨6966550656470495646523649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4644367104313663764349099 6966550656470495646523649)
            ·
              refine ⟨5224912992352871734892737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6966550656470495646523649 5224912992352871734892737)
              ·
                refine ⟨3918684744264653801169553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5224912992352871734892737 3918684744264653801169553)
                ·
                  refine ⟨2939013558198490350877165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3918684744264653801169553 2939013558198490350877165)
                  ·
                    refine ⟨1102130084324433881578937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2939013558198490350877165 1102130084324433881578937)
                    ·
                      refine ⟨826597563243325411184203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1102130084324433881578937 826597563243325411184203)
                      ·
                        rfl

theorem cell23_1609793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_1609793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609793 prefixEnd_1609793 := by exact prefixLift 1609793
  have htrace : WordTrace (prefixWord ++ tailWord_1609793) baseStart_1609793 baseEnd_1609793 := by
    simpa [prefixWord, tailWord_1609793, baseEnd_1609793] using wordTrace_append hprefix tailTrace_1609793
  have hstable : (prefixWord ++ tailWord_1609793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609793).length < 2 ^ (prefixWord ++ tailWord_1609793).sum := by decide
  have hdescent : baseEnd_1609793 < baseStart_1609793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609816 : List Nat := [2, 1, 2, 2, 1, 4, 2, 3, 2, 4]
def baseStart_1609816 : Nat := 118140960795 + 1609816 * 2 ^ 59
def prefixEnd_1609816 : Nat := 4983230072969 + 3 ^ 40 * 1609816 * 2
def baseEnd_1609816 : Nat := 275536457766126273732199

theorem tailTrace_1609816 : CollatzResearch.WordTrace tailWord_1609816 prefixEnd_1609816 275536457766126273732199 := by
  unfold tailWord_1609816
  simp only [CollatzResearch.WordTrace]
  refine ⟨29357406567959520764620651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39143208757279361019494201 29357406567959520764620651)
  ·
    refine ⟨44036109851939281146930977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29357406567959520764620651 44036109851939281146930977)
    ·
      refine ⟨33027082388954460860198233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44036109851939281146930977 33027082388954460860198233)
      ·
        refine ⟨24770311791715845645148675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33027082388954460860198233 24770311791715845645148675)
        ·
          refine ⟨37155467687573768467723013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24770311791715845645148675 37155467687573768467723013)
          ·
            refine ⟨6966650191420081587698065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37155467687573768467723013 6966650191420081587698065)
            ·
              refine ⟨5224987643565061190773549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6966650191420081587698065 5224987643565061190773549)
              ·
                refine ⟨1959370366336897946540081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5224987643565061190773549 1959370366336897946540081)
                ·
                  refine ⟨1469527774752673459905061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1959370366336897946540081 1469527774752673459905061)
                  ·
                    refine ⟨275536457766126273732199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1469527774752673459905061 275536457766126273732199)
                    ·
                      rfl

theorem cell23_1609816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 2, 4].length) (baseStart_1609816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609816 prefixEnd_1609816 := by exact prefixLift 1609816
  have htrace : WordTrace (prefixWord ++ tailWord_1609816) baseStart_1609816 baseEnd_1609816 := by
    simpa [prefixWord, tailWord_1609816, baseEnd_1609816] using wordTrace_append hprefix tailTrace_1609816
  have hstable : (prefixWord ++ tailWord_1609816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609816).length < 2 ^ (prefixWord ++ tailWord_1609816).sum := by decide
  have hdescent : baseEnd_1609816 < baseStart_1609816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609840 : List Nat := [2, 1, 1, 1, 5, 2, 1, 5, 1, 2, 2]
def baseStart_1609840 : Nat := 118140960795 + 1609840 * 2 ^ 59
def prefixEnd_1609840 : Nat := 4983230072969 + 3 ^ 40 * 1609840 * 2
def baseEnd_1609840 : Nat := 826621696834086727296487

theorem tailTrace_1609840 : CollatzResearch.WordTrace tailWord_1609840 prefixEnd_1609840 826621696834086727296487 := by
  unfold tailWord_1609840
  simp only [CollatzResearch.WordTrace]
  refine ⟨29357844243916046814057487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39143792325221395752076649 29357844243916046814057487)
  ·
    refine ⟨44036766365874070221086231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29357844243916046814057487 44036766365874070221086231)
    ·
      refine ⟨66055149548811105331629347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44036766365874070221086231 66055149548811105331629347)
      ·
        refine ⟨99082724323216657997444021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66055149548811105331629347 99082724323216657997444021)
        ·
          refine ⟨9289005405301561687260377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99082724323216657997444021 9289005405301561687260377)
          ·
            refine ⟨6966754053976171265445283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9289005405301561687260377 6966754053976171265445283)
            ·
              refine ⟨10450131080964256898167925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6966754053976171265445283 10450131080964256898167925)
              ·
                refine ⟨979699788840399084203243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10450131080964256898167925 979699788840399084203243)
                ·
                  refine ⟨1469549683260598626304865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 979699788840399084203243 1469549683260598626304865)
                  ·
                    refine ⟨1102162262445448969728649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1469549683260598626304865 1102162262445448969728649)
                    ·
                      refine ⟨826621696834086727296487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1102162262445448969728649 826621696834086727296487)
                      ·
                        rfl

theorem cell23_1609840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5, 1, 2, 2].length) (baseStart_1609840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609840 prefixEnd_1609840 := by exact prefixLift 1609840
  have htrace : WordTrace (prefixWord ++ tailWord_1609840) baseStart_1609840 baseEnd_1609840 := by
    simpa [prefixWord, tailWord_1609840, baseEnd_1609840] using wordTrace_append hprefix tailTrace_1609840
  have hstable : (prefixWord ++ tailWord_1609840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609840).length < 2 ^ (prefixWord ++ tailWord_1609840).sum := by decide
  have hdescent : baseEnd_1609840 < baseStart_1609840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609870 : List Nat := [4, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4]
def baseStart_1609870 : Nat := 118140960795 + 1609870 * 2 ^ 59
def prefixEnd_1609870 : Nat := 4983230072969 + 3 ^ 40 * 1609870 * 2
def baseEnd_1609870 : Nat := 826637101253721609921349

theorem tailTrace_1609870 : CollatzResearch.WordTrace tailWord_1609870 prefixEnd_1609870 826637101253721609921349 := by
  unfold tailWord_1609870
  simp only [CollatzResearch.WordTrace]
  refine ⟨7339597834715426093963383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39144521785148939167804709 7339597834715426093963383)
  ·
    refine ⟨11009396752073139140945075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7339597834715426093963383 11009396752073139140945075)
    ·
      refine ⟨16514095128109708711417613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11009396752073139140945075 16514095128109708711417613)
      ·
        refine ⟨6192785673041140766781605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16514095128109708711417613 6192785673041140766781605)
        ·
          refine ⟨1161147313695213893771551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6192785673041140766781605 1161147313695213893771551)
          ·
            refine ⟨1741720970542820840657327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1161147313695213893771551 1741720970542820840657327)
            ·
              refine ⟨2612581455814231260985991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1741720970542820840657327 2612581455814231260985991)
              ·
                refine ⟨3918872183721346891478987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2612581455814231260985991 3918872183721346891478987)
                ·
                  refine ⟨5878308275582020337218481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3918872183721346891478987 5878308275582020337218481)
                  ·
                    refine ⟨4408731206686515252913861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5878308275582020337218481 4408731206686515252913861)
                    ·
                      refine ⟨826637101253721609921349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4408731206686515252913861 826637101253721609921349)
                      ·
                        rfl

theorem cell23_1609870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_1609870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609870 prefixEnd_1609870 := by exact prefixLift 1609870
  have htrace : WordTrace (prefixWord ++ tailWord_1609870) baseStart_1609870 baseEnd_1609870 := by
    simpa [prefixWord, tailWord_1609870, baseEnd_1609870] using wordTrace_append hprefix tailTrace_1609870
  have hstable : (prefixWord ++ tailWord_1609870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609870).length < 2 ^ (prefixWord ++ tailWord_1609870).sum := by decide
  have hdescent : baseEnd_1609870 < baseStart_1609870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609908 : List Nat := [2, 5, 3, 1, 2, 1, 1, 1, 3, 2, 2]
def baseStart_1609908 : Nat := 118140960795 + 1609908 * 2 ^ 59
def prefixEnd_1609908 : Nat := 4983230072969 + 3 ^ 40 * 1609908 * 2
def baseEnd_1609908 : Nat := 826656613518592461246175

theorem tailTrace_1609908 : CollatzResearch.WordTrace tailWord_1609908 prefixEnd_1609908 826656613518592461246175 := by
  unfold tailWord_1609908
  simp only [CollatzResearch.WordTrace]
  refine ⟨29359084325792870620795189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39145445767723827494393585 29359084325792870620795189)
  ·
    refine ⟨2752414155543081620699549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29359084325792870620795189 2752414155543081620699549)
    ·
      refine ⟨1032155308328655607762331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2752414155543081620699549 1032155308328655607762331)
      ·
        refine ⟨1548232962492983411643497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1032155308328655607762331 1548232962492983411643497)
        ·
          refine ⟨1161174721869737558732623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1548232962492983411643497 1161174721869737558732623)
          ·
            refine ⟨1741762082804606338098935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1161174721869737558732623 1741762082804606338098935)
            ·
              refine ⟨2612643124206909507148403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1741762082804606338098935 2612643124206909507148403)
              ·
                refine ⟨3918964686310364260722605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2612643124206909507148403 3918964686310364260722605)
                ·
                  refine ⟨1469611757366386597770977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3918964686310364260722605 1469611757366386597770977)
                  ·
                    refine ⟨1102208818024789948328233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1469611757366386597770977 1102208818024789948328233)
                    ·
                      refine ⟨826656613518592461246175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1102208818024789948328233 826656613518592461246175)
                      ·
                        rfl

theorem cell23_1609908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_1609908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609908 prefixEnd_1609908 := by exact prefixLift 1609908
  have htrace : WordTrace (prefixWord ++ tailWord_1609908) baseStart_1609908 baseEnd_1609908 := by
    simpa [prefixWord, tailWord_1609908, baseEnd_1609908] using wordTrace_append hprefix tailTrace_1609908
  have hstable : (prefixWord ++ tailWord_1609908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609908).length < 2 ^ (prefixWord ++ tailWord_1609908).sum := by decide
  have hdescent : baseEnd_1609908 < baseStart_1609908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609913 : List Nat := [1, 2, 1, 4, 1, 2, 1, 3, 4, 2, 2]
def baseStart_1609913 : Nat := 118140960795 + 1609913 * 2 ^ 59
def prefixEnd_1609913 : Nat := 4983230072969 + 3 ^ 40 * 1609913 * 2
def baseEnd_1609913 : Nat := 826659180921864941683651

theorem tailTrace_1609913 : CollatzResearch.WordTrace tailWord_1609913 prefixEnd_1609913 826659180921864941683651 := by
  unfold tailWord_1609913
  simp only [CollatzResearch.WordTrace]
  refine ⟨58718351016567627095522393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39145567344378418063681595 58718351016567627095522393)
  ·
    refine ⟨44038763262425720321641795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58718351016567627095522393 44038763262425720321641795)
    ·
      refine ⟨66058144893638580482462693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44038763262425720321641795 66058144893638580482462693)
      ·
        refine ⟨12385902167557233840461755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66058144893638580482462693 12385902167557233840461755)
        ·
          refine ⟨18578853251335850760692633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12385902167557233840461755 18578853251335850760692633)
          ·
            refine ⟨13934139938501888070519475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18578853251335850760692633 13934139938501888070519475)
            ·
              refine ⟨20901209907752832105779213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13934139938501888070519475 20901209907752832105779213)
              ·
                refine ⟨7837953715407312039667205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20901209907752832105779213 7837953715407312039667205)
                ·
                  refine ⟨1469616321638871007437601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7837953715407312039667205 1469616321638871007437601)
                  ·
                    refine ⟨1102212241229153255578201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1469616321638871007437601 1102212241229153255578201)
                    ·
                      refine ⟨826659180921864941683651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1102212241229153255578201 826659180921864941683651)
                      ·
                        rfl

theorem cell23_1609913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_1609913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609913 prefixEnd_1609913 := by exact prefixLift 1609913
  have htrace : WordTrace (prefixWord ++ tailWord_1609913) baseStart_1609913 baseEnd_1609913 := by
    simpa [prefixWord, tailWord_1609913, baseEnd_1609913] using wordTrace_append hprefix tailTrace_1609913
  have hstable : (prefixWord ++ tailWord_1609913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609913).length < 2 ^ (prefixWord ++ tailWord_1609913).sum := by decide
  have hdescent : baseEnd_1609913 < baseStart_1609913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609930 : List Nat := [3, 1, 2, 1, 3, 1, 3, 3, 2, 2, 2]
def baseStart_1609930 : Nat := 118140960795 + 1609930 * 2 ^ 59
def prefixEnd_1609930 : Nat := 4983230072969 + 3 ^ 40 * 1609930 * 2
def baseEnd_1609930 : Nat := 826667910092991375171073

theorem tailTrace_1609930 : CollatzResearch.WordTrace tailWord_1609930 prefixEnd_1609930 826667910092991375171073 := by
  unfold tailWord_1609930
  simp only [CollatzResearch.WordTrace]
  refine ⟨14679742764376509749722811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39145980705004025999260829 14679742764376509749722811)
  ·
    refine ⟨22019614146564764624584217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14679742764376509749722811 22019614146564764624584217)
    ·
      refine ⟨16514710609923573468438163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22019614146564764624584217 16514710609923573468438163)
      ·
        refine ⟨24772065914885360202657245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16514710609923573468438163 24772065914885360202657245)
        ·
          refine ⟨9289524718082010075996467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24772065914885360202657245 9289524718082010075996467)
          ·
            refine ⟨13934287077123015113994701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9289524718082010075996467 13934287077123015113994701)
            ·
              refine ⟨5225357653921130667748013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13934287077123015113994701 5225357653921130667748013)
              ·
                refine ⟨1959509120220424000405505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5225357653921130667748013 1959509120220424000405505)
                ·
                  refine ⟨1469631840165318000304129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1959509120220424000405505 1469631840165318000304129)
                  ·
                    refine ⟨1102223880123988500228097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1469631840165318000304129 1102223880123988500228097)
                    ·
                      refine ⟨826667910092991375171073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1102223880123988500228097 826667910092991375171073)
                      ·
                        rfl

theorem cell23_1609930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 2, 2, 2].length) (baseStart_1609930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609930 prefixEnd_1609930 := by exact prefixLift 1609930
  have htrace : WordTrace (prefixWord ++ tailWord_1609930) baseStart_1609930 baseEnd_1609930 := by
    simpa [prefixWord, tailWord_1609930, baseEnd_1609930] using wordTrace_append hprefix tailTrace_1609930
  have hstable : (prefixWord ++ tailWord_1609930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609930).length < 2 ^ (prefixWord ++ tailWord_1609930).sum := by decide
  have hdescent : baseEnd_1609930 < baseStart_1609930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609970 : List Nat := [3, 2, 1, 3, 2, 1, 4, 2, 5]
def baseStart_1609970 : Nat := 118140960795 + 1609970 * 2 ^ 59
def prefixEnd_1609970 : Nat := 4983230072969 + 3 ^ 40 * 1609970 * 2
def baseEnd_1609970 : Nat := 91854272146574579852321

theorem tailTrace_1609970 : CollatzResearch.WordTrace tailWord_1609970 prefixEnd_1609970 91854272146574579852321 := by
  unfold tailWord_1609970
  simp only [CollatzResearch.WordTrace]
  refine ⟨14680107494340281457586841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39146953318240750553564909 14680107494340281457586841)
  ·
    refine ⟨11010080620755211093190131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14680107494340281457586841 11010080620755211093190131)
    ·
      refine ⟨16515120931132816639785197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11010080620755211093190131 16515120931132816639785197)
      ·
        refine ⟨6193170349174806239919449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16515120931132816639785197 6193170349174806239919449)
        ·
          refine ⟨4644877761881104679939587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6193170349174806239919449 4644877761881104679939587)
          ·
            refine ⟨6967316642821657019909381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4644877761881104679939587 6967316642821657019909381)
            ·
              refine ⟨1306371870529060691233009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6967316642821657019909381 1306371870529060691233009)
              ·
                refine ⟨979778902896795518424757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1306371870529060691233009 979778902896795518424757)
                ·
                  refine ⟨91854272146574579852321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 979778902896795518424757 91854272146574579852321)
                  ·
                    rfl

theorem cell23_1609970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2, 5].length) (baseStart_1609970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609970 prefixEnd_1609970 := by exact prefixLift 1609970
  have htrace : WordTrace (prefixWord ++ tailWord_1609970) baseStart_1609970 baseEnd_1609970 := by
    simpa [prefixWord, tailWord_1609970, baseEnd_1609970] using wordTrace_append hprefix tailTrace_1609970
  have hstable : (prefixWord ++ tailWord_1609970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609970).length < 2 ^ (prefixWord ++ tailWord_1609970).sum := by decide
  have hdescent : baseEnd_1609970 < baseStart_1609970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1609999 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 6]
def baseStart_1609999 : Nat := 118140960795 + 1609999 * 2 ^ 59
def prefixEnd_1609999 : Nat := 4983230072969 + 3 ^ 40 * 1609999 * 2
def baseEnd_1609999 : Nat := 826703340258151605208255

theorem tailTrace_1609999 : CollatzResearch.WordTrace tailWord_1609999 prefixEnd_1609999 826703340258151605208255 := by
  unfold tailWord_1609999
  simp only [CollatzResearch.WordTrace]
  refine ⟨58721487694256063783153051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39147658462837375855435367 58721487694256063783153051)
  ·
    refine ⟨88082231541384095674729577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58721487694256063783153051 88082231541384095674729577)
    ·
      refine ⟨66061673656038071756047183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88082231541384095674729577 66061673656038071756047183)
      ·
        refine ⟨99092510484057107634070775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66061673656038071756047183 99092510484057107634070775)
        ·
          refine ⟨148638765726085661451106163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99092510484057107634070775 148638765726085661451106163)
          ·
            refine ⟨222958148589128492176659245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148638765726085661451106163 222958148589128492176659245)
            ·
              refine ⟨83609305720923184566247217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222958148589128492176659245 83609305720923184566247217)
              ·
                refine ⟨62706979290692388424685413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83609305720923184566247217 62706979290692388424685413)
                ·
                  refine ⟨11757558617004822829628515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62706979290692388424685413 11757558617004822829628515)
                  ·
                    refine ⟨17636337925507234244442773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11757558617004822829628515 17636337925507234244442773)
                    ·
                      refine ⟨826703340258151605208255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17636337925507234244442773 826703340258151605208255)
                      ·
                        rfl

theorem cell23_1609999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 6].length) (baseStart_1609999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1609999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1609999 prefixEnd_1609999 := by exact prefixLift 1609999
  have htrace : WordTrace (prefixWord ++ tailWord_1609999) baseStart_1609999 baseEnd_1609999 := by
    simpa [prefixWord, tailWord_1609999, baseEnd_1609999] using wordTrace_append hprefix tailTrace_1609999
  have hstable : (prefixWord ++ tailWord_1609999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1609999).length < 2 ^ (prefixWord ++ tailWord_1609999).sum := by decide
  have hdescent : baseEnd_1609999 < baseStart_1609999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1609999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610016 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 6]
def baseStart_1610016 : Nat := 118140960795 + 1610016 * 2 ^ 59
def prefixEnd_1610016 : Nat := 4983230072969 + 3 ^ 40 * 1610016 * 2
def baseEnd_1610016 : Nat := 826712069429278038695677

theorem tailTrace_1610016 : CollatzResearch.WordTrace tailWord_1610016 prefixEnd_1610016 826712069429278038695677 := by
  unfold tailWord_1610016
  simp only [CollatzResearch.WordTrace]
  refine ⟨29361053867597237843260951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39148071823462983791014601 29361053867597237843260951)
  ·
    refine ⟨44041580801395856764891427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29361053867597237843260951 44041580801395856764891427)
    ·
      refine ⟨66062371202093785147337141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44041580801395856764891427 66062371202093785147337141)
      ·
        refine ⟨6193347300196292357562857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66062371202093785147337141 6193347300196292357562857)
        ·
          refine ⟨4645010475147219268172143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6193347300196292357562857 4645010475147219268172143)
          ·
            refine ⟨6967515712720828902258215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4645010475147219268172143 6967515712720828902258215)
            ·
              refine ⟨10451273569081243353387323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6967515712720828902258215 10451273569081243353387323)
              ·
                refine ⟨15676910353621865030080985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10451273569081243353387323 15676910353621865030080985)
                ·
                  refine ⟨11757682765216398772560739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15676910353621865030080985 11757682765216398772560739)
                  ·
                    refine ⟨17636524147824598158841109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11757682765216398772560739 17636524147824598158841109)
                    ·
                      refine ⟨826712069429278038695677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17636524147824598158841109 826712069429278038695677)
                      ·
                        rfl

theorem cell23_1610016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_1610016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610016 prefixEnd_1610016 := by exact prefixLift 1610016
  have htrace : WordTrace (prefixWord ++ tailWord_1610016) baseStart_1610016 baseEnd_1610016 := by
    simpa [prefixWord, tailWord_1610016, baseEnd_1610016] using wordTrace_append hprefix tailTrace_1610016
  have hstable : (prefixWord ++ tailWord_1610016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610016).length < 2 ^ (prefixWord ++ tailWord_1610016).sum := by decide
  have hdescent : baseEnd_1610016 < baseStart_1610016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610056 : List Nat := [2, 1, 3, 1, 1, 2, 2, 3, 3, 5]
def baseStart_1610056 : Nat := 118140960795 + 1610056 * 2 ^ 59
def prefixEnd_1610056 : Nat := 4983230072969 + 3 ^ 40 * 1610056 * 2
def baseEnd_1610056 : Nat := 275577536218485960731831

theorem tailTrace_1610056 : CollatzResearch.WordTrace tailWord_1610056 prefixEnd_1610056 275577536218485960731831 := by
  unfold tailWord_1610056
  simp only [CollatzResearch.WordTrace]
  refine ⟨29361783327524781258989011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39149044436699708345318681 29361783327524781258989011)
  ·
    refine ⟨44042674991287171888483517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29361783327524781258989011 44042674991287171888483517)
    ·
      refine ⟨16516003121732689458181319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44042674991287171888483517 16516003121732689458181319)
      ·
        refine ⟨24774004682599034187271979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16516003121732689458181319 24774004682599034187271979)
        ·
          refine ⟨37161007023898551280907969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24774004682599034187271979 37161007023898551280907969)
          ·
            refine ⟨27870755267923913460680977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37161007023898551280907969 27870755267923913460680977)
            ·
              refine ⟨20903066450942935095510733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27870755267923913460680977 20903066450942935095510733)
              ·
                refine ⟨7838649919103600660816525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20903066450942935095510733 7838649919103600660816525)
                ·
                  refine ⟨2939493719663850247806197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7838649919103600660816525 2939493719663850247806197)
                  ·
                    refine ⟨275577536218485960731831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2939493719663850247806197 275577536218485960731831)
                    ·
                      rfl

theorem cell23_1610056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_1610056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610056 prefixEnd_1610056 := by exact prefixLift 1610056
  have htrace : WordTrace (prefixWord ++ tailWord_1610056) baseStart_1610056 baseEnd_1610056 := by
    simpa [prefixWord, tailWord_1610056, baseEnd_1610056] using wordTrace_append hprefix tailTrace_1610056
  have hstable : (prefixWord ++ tailWord_1610056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610056).length < 2 ^ (prefixWord ++ tailWord_1610056).sum := by decide
  have hdescent : baseEnd_1610056 < baseStart_1610056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610087 : List Nat := [1, 1, 5, 1, 3, 3, 1, 1, 3, 1, 3]
def baseStart_1610087 : Nat := 118140960795 + 1610087 * 2 ^ 59
def prefixEnd_1610087 : Nat := 4983230072969 + 3 ^ 40 * 1610087 * 2
def baseEnd_1610087 : Nat := 826748526555747260907851

theorem tailTrace_1610087 : CollatzResearch.WordTrace tailWord_1610087 prefixEnd_1610087 826748526555747260907851 := by
  unfold tailWord_1610087
  simp only [CollatzResearch.WordTrace]
  refine ⟨58724697317937254812356515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39149798211958169874904343 58724697317937254812356515)
  ·
    refine ⟨88087045976905882218534773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58724697317937254812356515 88087045976905882218534773)
    ·
      refine ⟨8258160560334926457987635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88087045976905882218534773 8258160560334926457987635)
      ·
        refine ⟨12387240840502389686981453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8258160560334926457987635 12387240840502389686981453)
        ·
          refine ⟨4645215315188396132618045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12387240840502389686981453 4645215315188396132618045)
          ·
            refine ⟨1741955743195648549731767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4645215315188396132618045 1741955743195648549731767)
            ·
              refine ⟨2612933614793472824597651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1741955743195648549731767 2612933614793472824597651)
              ·
                refine ⟨3919400422190209236896477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2612933614793472824597651 3919400422190209236896477)
                ·
                  refine ⟨1469775158321328463836179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3919400422190209236896477 1469775158321328463836179)
                  ·
                    refine ⟨2204662737481992695754269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1469775158321328463836179 2204662737481992695754269)
                    ·
                      refine ⟨826748526555747260907851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2204662737481992695754269 826748526555747260907851)
                      ·
                        rfl

theorem cell23_1610087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_1610087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610087 prefixEnd_1610087 := by exact prefixLift 1610087
  have htrace : WordTrace (prefixWord ++ tailWord_1610087) baseStart_1610087 baseEnd_1610087 := by
    simpa [prefixWord, tailWord_1610087, baseEnd_1610087] using wordTrace_append hprefix tailTrace_1610087
  have hstable : (prefixWord ++ tailWord_1610087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610087).length < 2 ^ (prefixWord ++ tailWord_1610087).sum := by decide
  have hdescent : baseEnd_1610087 < baseStart_1610087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610093 : List Nat := [1, 5, 1, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_1610093 : Nat := 118140960795 + 1610093 * 2 ^ 59
def prefixEnd_1610093 : Nat := 4983230072969 + 3 ^ 40 * 1610093 * 2
def baseEnd_1610093 : Nat := 826751607439674237432823

theorem tailTrace_1610093 : CollatzResearch.WordTrace tailWord_1610093 prefixEnd_1610093 826751607439674237432823 := by
  unfold tailWord_1610093
  simp only [CollatzResearch.WordTrace]
  refine ⟨58724916155915517837074933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39149944103943678558049955 58724916155915517837074933)
  ·
    refine ⟨5505460889617079797225775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58724916155915517837074933 5505460889617079797225775)
    ·
      refine ⟨8258191334425619695838663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5505460889617079797225775 8258191334425619695838663)
      ·
        refine ⟨12387287001638429543757995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8258191334425619695838663 12387287001638429543757995)
        ·
          refine ⟨18580930502457644315636993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12387287001638429543757995 18580930502457644315636993)
          ·
            refine ⟨13935697876843233236727745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18580930502457644315636993 13935697876843233236727745)
            ·
              refine ⟨10451773407632424927545809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13935697876843233236727745 10451773407632424927545809)
              ·
                refine ⟨7838830055724318695659357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10451773407632424927545809 7838830055724318695659357)
                ·
                  refine ⟨2939561270896619510872259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7838830055724318695659357 2939561270896619510872259)
                  ·
                    refine ⟨4409341906344929266308389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2939561270896619510872259 4409341906344929266308389)
                    ·
                      refine ⟨826751607439674237432823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4409341906344929266308389 826751607439674237432823)
                      ·
                        rfl

theorem cell23_1610093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_1610093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610093 prefixEnd_1610093 := by exact prefixLift 1610093
  have htrace : WordTrace (prefixWord ++ tailWord_1610093) baseStart_1610093 baseEnd_1610093 := by
    simpa [prefixWord, tailWord_1610093, baseEnd_1610093] using wordTrace_append hprefix tailTrace_1610093
  have hstable : (prefixWord ++ tailWord_1610093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610093).length < 2 ^ (prefixWord ++ tailWord_1610093).sum := by decide
  have hdescent : baseEnd_1610093 < baseStart_1610093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610116 : List Nat := [2, 3, 2, 1, 1, 2, 1, 11]
def baseStart_1610116 : Nat := 118140960795 + 1610116 * 2 ^ 59
def prefixEnd_1610116 : Nat := 4983230072969 + 3 ^ 40 * 1610116 * 2
def baseEnd_1610116 : Nat := 30620867314619542497971

theorem tailTrace_1610116 : CollatzResearch.WordTrace tailWord_1610116 prefixEnd_1610116 30620867314619542497971 := by
  unfold tailWord_1610116
  simp only [CollatzResearch.WordTrace]
  refine ⟨29362877517416096382581101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39150503356554795176774801 29362877517416096382581101)
  ·
    refine ⟨11011079069031036143467913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29362877517416096382581101 11011079069031036143467913)
    ·
      refine ⟨8258309301773277107600935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11011079069031036143467913 8258309301773277107600935)
      ·
        refine ⟨12387463952659915661401403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8258309301773277107600935 12387463952659915661401403)
        ·
          refine ⟨18581195928989873492102105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12387463952659915661401403 18581195928989873492102105)
          ·
            refine ⟨13935896946742405119076579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18581195928989873492102105 13935896946742405119076579)
            ·
              refine ⟨20903845420113607678614869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13935896946742405119076579 20903845420113607678614869)
              ·
                refine ⟨30620867314619542497971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 20903845420113607678614869 30620867314619542497971)
                ·
                  rfl

theorem cell23_1610116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 11].length) (baseStart_1610116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610116 prefixEnd_1610116 := by exact prefixLift 1610116
  have htrace : WordTrace (prefixWord ++ tailWord_1610116) baseStart_1610116 baseEnd_1610116 := by
    simpa [prefixWord, tailWord_1610116, baseEnd_1610116] using wordTrace_append hprefix tailTrace_1610116
  have hstable : (prefixWord ++ tailWord_1610116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610116).length < 2 ^ (prefixWord ++ tailWord_1610116).sum := by decide
  have hdescent : baseEnd_1610116 < baseStart_1610116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610123 : List Nat := [1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 4]
def baseStart_1610123 : Nat := 118140960795 + 1610123 * 2 ^ 59
def prefixEnd_1610123 : Nat := 4983230072969 + 3 ^ 40 * 1610123 * 2
def baseEnd_1610123 : Nat := 826767011859309120057685

theorem tailTrace_1610123 : CollatzResearch.WordTrace tailWord_1610123 prefixEnd_1610123 826767011859309120057685 := by
  unfold tailWord_1610123
  simp only [CollatzResearch.WordTrace]
  refine ⟨58726010345806832960667023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39150673563871221973778015 58726010345806832960667023)
  ·
    refine ⟨88089015518710249441000535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58726010345806832960667023 88089015518710249441000535)
    ·
      refine ⟨132133523278065374161500803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88089015518710249441000535 132133523278065374161500803)
      ·
        refine ⟨198200284917098061242251205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132133523278065374161500803 198200284917098061242251205)
        ·
          refine ⟨37162553421955886482922101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198200284917098061242251205 37162553421955886482922101)
          ·
            refine ⟨3483989383308364357773947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37162553421955886482922101 3483989383308364357773947)
            ·
              refine ⟨5225984074962546536660921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3483989383308364357773947 5225984074962546536660921)
              ·
                refine ⟨3919488056221909902495691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5225984074962546536660921 3919488056221909902495691)
                ·
                  refine ⟨5879232084332864853743537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3919488056221909902495691 5879232084332864853743537)
                  ·
                    refine ⟨4409424063249648640307653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5879232084332864853743537 4409424063249648640307653)
                    ·
                      refine ⟨826767011859309120057685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4409424063249648640307653 826767011859309120057685)
                      ·
                        rfl

theorem cell23_1610123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 4].length) (baseStart_1610123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610123 prefixEnd_1610123 := by exact prefixLift 1610123
  have htrace : WordTrace (prefixWord ++ tailWord_1610123) baseStart_1610123 baseEnd_1610123 := by
    simpa [prefixWord, tailWord_1610123, baseEnd_1610123] using wordTrace_append hprefix tailTrace_1610123
  have hstable : (prefixWord ++ tailWord_1610123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610123).length < 2 ^ (prefixWord ++ tailWord_1610123).sum := by decide
  have hdescent : baseEnd_1610123 < baseStart_1610123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610143 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 3, 3, 3]
def baseStart_1610143 : Nat := 118140960795 + 1610143 * 2 ^ 59
def prefixEnd_1610143 : Nat := 4983230072969 + 3 ^ 40 * 1610143 * 2
def baseEnd_1610143 : Nat := 826777281472399041807593

theorem tailTrace_1610143 : CollatzResearch.WordTrace tailWord_1610143 prefixEnd_1610143 826777281472399041807593 := by
  unfold tailWord_1610143
  simp only [CollatzResearch.WordTrace]
  refine ⟨58726739805734376376395083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39151159870489584250930055 58726739805734376376395083)
  ·
    refine ⟨88090109708601564564592625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58726739805734376376395083 88090109708601564564592625)
    ·
      refine ⟨66067582281451173423444469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88090109708601564564592625 66067582281451173423444469)
      ·
        refine ⟨6193835838886047508447919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66067582281451173423444469 6193835838886047508447919)
        ·
          refine ⟨9290753758329071262671879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6193835838886047508447919 9290753758329071262671879)
          ·
            refine ⟨13936130637493606894007819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9290753758329071262671879 13936130637493606894007819)
            ·
              refine ⟨20904195956240410341011729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13936130637493606894007819 20904195956240410341011729)
              ·
                refine ⟨15678146967180307755758797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20904195956240410341011729 15678146967180307755758797)
                ·
                  refine ⟨5879305112692615408409549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15678146967180307755758797 5879305112692615408409549)
                  ·
                    refine ⟨2204739417259730778153581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5879305112692615408409549 2204739417259730778153581)
                    ·
                      refine ⟨826777281472399041807593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2204739417259730778153581 826777281472399041807593)
                      ·
                        rfl

theorem cell23_1610143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_1610143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610143 prefixEnd_1610143 := by exact prefixLift 1610143
  have htrace : WordTrace (prefixWord ++ tailWord_1610143) baseStart_1610143 baseEnd_1610143 := by
    simpa [prefixWord, tailWord_1610143, baseEnd_1610143] using wordTrace_append hprefix tailTrace_1610143
  have hstable : (prefixWord ++ tailWord_1610143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610143).length < 2 ^ (prefixWord ++ tailWord_1610143).sum := by decide
  have hdescent : baseEnd_1610143 < baseStart_1610143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610144 : List Nat := [2, 1, 1, 4, 1, 4, 1, 4, 1, 2, 2]
def baseStart_1610144 : Nat := 118140960795 + 1610144 * 2 ^ 59
def prefixEnd_1610144 : Nat := 4983230072969 + 3 ^ 40 * 1610144 * 2
def baseEnd_1610144 : Nat := 826777794953053537895089

theorem tailTrace_1610144 : CollatzResearch.WordTrace tailWord_1610144 prefixEnd_1610144 826777794953053537895089 := by
  unfold tailWord_1610144
  simp only [CollatzResearch.WordTrace]
  refine ⟨29363388139365376773590743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39151184185820502364787657 29363388139365376773590743)
  ·
    refine ⟨44045082209048065160386115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29363388139365376773590743 44045082209048065160386115)
    ·
      refine ⟨66067623313572097740579173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44045082209048065160386115 66067623313572097740579173)
      ·
        refine ⟨12387679371294768326358595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66067623313572097740579173 12387679371294768326358595)
        ·
          refine ⟨18581519056942152489537893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12387679371294768326358595 18581519056942152489537893)
          ·
            refine ⟨3484034823176653591788355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18581519056942152489537893 3484034823176653591788355)
            ·
              refine ⟨5226052234764980387682533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3484034823176653591788355 5226052234764980387682533)
              ·
                refine ⟨979884794018433822690475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5226052234764980387682533 979884794018433822690475)
                ·
                  refine ⟨1469827191027650734035713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 979884794018433822690475 1469827191027650734035713)
                  ·
                    refine ⟨1102370393270738050526785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1469827191027650734035713 1102370393270738050526785)
                    ·
                      refine ⟨826777794953053537895089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1102370393270738050526785 826777794953053537895089)
                      ·
                        rfl

theorem cell23_1610144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_1610144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610144 prefixEnd_1610144 := by exact prefixLift 1610144
  have htrace : WordTrace (prefixWord ++ tailWord_1610144) baseStart_1610144 baseEnd_1610144 := by
    simpa [prefixWord, tailWord_1610144, baseEnd_1610144] using wordTrace_append hprefix tailTrace_1610144
  have hstable : (prefixWord ++ tailWord_1610144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610144).length < 2 ^ (prefixWord ++ tailWord_1610144).sum := by decide
  have hdescent : baseEnd_1610144 < baseStart_1610144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610154 : List Nat := [3, 1, 6, 1, 1, 1, 2, 1, 1, 6]
def baseStart_1610154 : Nat := 118140960795 + 1610154 * 2 ^ 59
def prefixEnd_1610154 : Nat := 4983230072969 + 3 ^ 40 * 1610154 * 2
def baseEnd_1610154 : Nat := 275594309919866166256681

theorem tailTrace_1610154 : CollatzResearch.WordTrace tailWord_1610154 prefixEnd_1610154 275594309919866166256681 := by
  unfold tailWord_1610154
  simp only [CollatzResearch.WordTrace]
  refine ⟨14681785252173631313761379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39151427339129683503363677 14681785252173631313761379)
  ·
    refine ⟨22022677878260446970642069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14681785252173631313761379 22022677878260446970642069)
    ·
      refine ⟨1032313025543458451748847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22022677878260446970642069 1032313025543458451748847)
      ·
        refine ⟨1548469538315187677623271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1032313025543458451748847 1548469538315187677623271)
        ·
          refine ⟨2322704307472781516434907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1548469538315187677623271 2322704307472781516434907)
          ·
            refine ⟨3484056461209172274652361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2322704307472781516434907 3484056461209172274652361)
            ·
              refine ⟨2613042345906879205989271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3484056461209172274652361 2613042345906879205989271)
              ·
                refine ⟨3919563518860318808983907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2613042345906879205989271 3919563518860318808983907)
                ·
                  refine ⟨5879345278290478213475861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3919563518860318808983907 5879345278290478213475861)
                  ·
                    refine ⟨275594309919866166256681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5879345278290478213475861 275594309919866166256681)
                    ·
                      rfl

theorem cell23_1610154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_1610154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610154 prefixEnd_1610154 := by exact prefixLift 1610154
  have htrace : WordTrace (prefixWord ++ tailWord_1610154) baseStart_1610154 baseEnd_1610154 := by
    simpa [prefixWord, tailWord_1610154, baseEnd_1610154] using wordTrace_append hprefix tailTrace_1610154
  have hstable : (prefixWord ++ tailWord_1610154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610154).length < 2 ^ (prefixWord ++ tailWord_1610154).sum := by decide
  have hdescent : baseEnd_1610154 < baseStart_1610154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610156 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 5]
def baseStart_1610156 : Nat := 118140960795 + 1610156 * 2 ^ 59
def prefixEnd_1610156 : Nat := 4983230072969 + 3 ^ 40 * 1610156 * 2
def baseEnd_1610156 : Nat := 826783956720907490945033

theorem tailTrace_1610156 : CollatzResearch.WordTrace tailWord_1610156 prefixEnd_1610156 826783956720907490945033 := by
  unfold tailWord_1610156
  simp only [CollatzResearch.WordTrace]
  refine ⟨29363606977343639798309161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39151475969791519731078881 29363606977343639798309161)
  ·
    refine ⟨22022705233007729848731871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29363606977343639798309161 22022705233007729848731871)
    ·
      refine ⟨33034057849511594773097807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22022705233007729848731871 33034057849511594773097807)
      ·
        refine ⟨49551086774267392159646711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33034057849511594773097807 49551086774267392159646711)
        ·
          refine ⟨74326630161401088239470067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49551086774267392159646711 74326630161401088239470067)
          ·
            refine ⟨111489945242101632359205101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74326630161401088239470067 111489945242101632359205101)
            ·
              refine ⟨41808729465788112134701913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111489945242101632359205101 41808729465788112134701913)
              ·
                refine ⟨31356547099341084101026435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41808729465788112134701913 31356547099341084101026435)
                ·
                  refine ⟨47034820649011626151539653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31356547099341084101026435 47034820649011626151539653)
                  ·
                    refine ⟨8819028871689679903413685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47034820649011626151539653 8819028871689679903413685)
                    ·
                      refine ⟨826783956720907490945033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8819028871689679903413685 826783956720907490945033)
                      ·
                        rfl

theorem cell23_1610156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_1610156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610156 prefixEnd_1610156 := by exact prefixLift 1610156
  have htrace : WordTrace (prefixWord ++ tailWord_1610156) baseStart_1610156 baseEnd_1610156 := by
    simpa [prefixWord, tailWord_1610156, baseEnd_1610156] using wordTrace_append hprefix tailTrace_1610156
  have hstable : (prefixWord ++ tailWord_1610156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610156).length < 2 ^ (prefixWord ++ tailWord_1610156).sum := by decide
  have hdescent : baseEnd_1610156 < baseStart_1610156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610157 : List Nat := [1, 5, 2, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_1610157 : Nat := 118140960795 + 1610157 * 2 ^ 59
def prefixEnd_1610157 : Nat := 4983230072969 + 3 ^ 40 * 1610157 * 2
def baseEnd_1610157 : Nat := 826784470201561987032529

theorem tailTrace_1610157 : CollatzResearch.WordTrace tailWord_1610157 prefixEnd_1610157 826784470201561987032529 := by
  unfold tailWord_1610157
  simp only [CollatzResearch.WordTrace]
  refine ⟨58727250427683656767404725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39151500285122437844936483 58727250427683656767404725)
  ·
    refine ⟨5505679727595342821944193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58727250427683656767404725 5505679727595342821944193)
    ·
      refine ⟨4129259795696507116458145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5505679727595342821944193 4129259795696507116458145)
      ·
        refine ⟨3096944846772380337343609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4129259795696507116458145 3096944846772380337343609)
        ·
          refine ⟨2322708635079285253007707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3096944846772380337343609 2322708635079285253007707)
          ·
            refine ⟨3484062952618927879511561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2322708635079285253007707 3484062952618927879511561)
            ·
              refine ⟨2613047214464195909633671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3484062952618927879511561 2613047214464195909633671)
              ·
                refine ⟨3919570821696293864450507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2613047214464195909633671 3919570821696293864450507)
                ·
                  refine ⟨5879356232544440796675761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3919570821696293864450507 5879356232544440796675761)
                  ·
                    refine ⟨4409517174408330597506821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5879356232544440796675761 4409517174408330597506821)
                    ·
                      refine ⟨826784470201561987032529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4409517174408330597506821 826784470201561987032529)
                      ·
                        rfl

theorem cell23_1610157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_1610157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610157 prefixEnd_1610157 := by exact prefixLift 1610157
  have htrace : WordTrace (prefixWord ++ tailWord_1610157) baseStart_1610157 baseEnd_1610157 := by
    simpa [prefixWord, tailWord_1610157, baseEnd_1610157] using wordTrace_append hprefix tailTrace_1610157
  have hstable : (prefixWord ++ tailWord_1610157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610157).length < 2 ^ (prefixWord ++ tailWord_1610157).sum := by decide
  have hdescent : baseEnd_1610157 < baseStart_1610157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610176 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 3, 8]
def baseStart_1610176 : Nat := 118140960795 + 1610176 * 2 ^ 59
def prefixEnd_1610176 : Nat := 4983230072969 + 3 ^ 40 * 1610176 * 2
def baseEnd_1610176 : Nat := 275598075444665804231647

theorem tailTrace_1610176 : CollatzResearch.WordTrace tailWord_1610176 prefixEnd_1610176 275598075444665804231647 := by
  unfold tailWord_1610176
  simp only [CollatzResearch.WordTrace]
  refine ⟨29363971707307411506173191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39151962276409882008230921 29363971707307411506173191)
  ·
    refine ⟨44045957560961117259259787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29363971707307411506173191 44045957560961117259259787)
    ·
      refine ⟨66068936341441675888889681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44045957560961117259259787 66068936341441675888889681)
      ·
        refine ⟨49551702256081256916667261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66068936341441675888889681 49551702256081256916667261)
        ·
          refine ⟨18581888346030471343750223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49551702256081256916667261 18581888346030471343750223)
          ·
            refine ⟨27872832519045707015625335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18581888346030471343750223 27872832519045707015625335)
            ·
              refine ⟨41809248778568560523438003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27872832519045707015625335 41809248778568560523438003)
              ·
                refine ⟨62713873167852840785157005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41809248778568560523438003 62713873167852840785157005)
                ·
                  refine ⟨23517702437944815294433877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62713873167852840785157005 23517702437944815294433877)
                  ·
                    refine ⟨275598075444665804231647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23517702437944815294433877 275598075444665804231647)
                    ·
                      rfl

theorem cell23_1610176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 8].length) (baseStart_1610176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610176 prefixEnd_1610176 := by exact prefixLift 1610176
  have htrace : WordTrace (prefixWord ++ tailWord_1610176) baseStart_1610176 baseEnd_1610176 := by
    simpa [prefixWord, tailWord_1610176, baseEnd_1610176] using wordTrace_append hprefix tailTrace_1610176
  have hstable : (prefixWord ++ tailWord_1610176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610176).length < 2 ^ (prefixWord ++ tailWord_1610176).sum := by decide
  have hdescent : baseEnd_1610176 < baseStart_1610176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610194 : List Nat := [3, 2, 2, 4, 1, 1, 1, 1, 4, 1, 3]
def baseStart_1610194 : Nat := 118140960795 + 1610194 * 2 ^ 59
def prefixEnd_1610194 : Nat := 4983230072969 + 3 ^ 40 * 1610194 * 2
def baseEnd_1610194 : Nat := 826803468985778342269859

theorem tailTrace_1610194 : CollatzResearch.WordTrace tailWord_1610194 prefixEnd_1610194 826803468985778342269859 := by
  unfold tailWord_1610194
  simp only [CollatzResearch.WordTrace]
  refine ⟨14682149982137403021625409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39152399952366408057667757 14682149982137403021625409)
  ·
    refine ⟨11011612486603052266219057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14682149982137403021625409 11011612486603052266219057)
    ·
      refine ⟨8258709364952289199664293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11011612486603052266219057 8258709364952289199664293)
      ·
        refine ⟨1548508005928554224937055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8258709364952289199664293 1548508005928554224937055)
        ·
          refine ⟨2322762008892831337405583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1548508005928554224937055 2322762008892831337405583)
          ·
            refine ⟨3484143013339247006108375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2322762008892831337405583 3484143013339247006108375)
            ·
              refine ⟨5226214520008870509162563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3484143013339247006108375 5226214520008870509162563)
              ·
                refine ⟨7839321780013305763743845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5226214520008870509162563 7839321780013305763743845)
                ·
                  refine ⟨1469872833752494830701971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7839321780013305763743845 1469872833752494830701971)
                  ·
                    refine ⟨2204809250628742246052957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1469872833752494830701971 2204809250628742246052957)
                    ·
                      refine ⟨826803468985778342269859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2204809250628742246052957 826803468985778342269859)
                      ·
                        rfl

theorem cell23_1610194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_1610194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610194 prefixEnd_1610194 := by exact prefixLift 1610194
  have htrace : WordTrace (prefixWord ++ tailWord_1610194) baseStart_1610194 baseEnd_1610194 := by
    simpa [prefixWord, tailWord_1610194, baseEnd_1610194] using wordTrace_append hprefix tailTrace_1610194
  have hstable : (prefixWord ++ tailWord_1610194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610194).length < 2 ^ (prefixWord ++ tailWord_1610194).sum := by decide
  have hdescent : baseEnd_1610194 < baseStart_1610194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610233 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 1, 5, 3]
def baseStart_1610233 : Nat := 118140960795 + 1610233 * 2 ^ 59
def prefixEnd_1610233 : Nat := 4983230072969 + 3 ^ 40 * 1610233 * 2
def baseEnd_1610233 : Nat := 826823494731303689682179

theorem tailTrace_1610233 : CollatzResearch.WordTrace tailWord_1610233 prefixEnd_1610233 826823494731303689682179 := by
  unfold tailWord_1610233
  simp only [CollatzResearch.WordTrace]
  refine ⟨58730022375408321747171353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39153348250272214498114235 58730022375408321747171353)
  ·
    refine ⟨44047516781556241310378515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58730022375408321747171353 44047516781556241310378515)
    ·
      refine ⟨66071275172334361965567773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44047516781556241310378515 66071275172334361965567773)
      ·
        refine ⟨24776728189625385737087915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66071275172334361965567773 24776728189625385737087915)
        ·
          refine ⟨37165092284438078605631873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24776728189625385737087915 37165092284438078605631873)
          ·
            refine ⟨27873819213328558954223905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37165092284438078605631873 27873819213328558954223905)
            ·
              refine ⟨20905364409996419215667929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27873819213328558954223905 20905364409996419215667929)
              ·
                refine ⟨15679023307497314411750947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20905364409996419215667929 15679023307497314411750947)
                ·
                  refine ⟨23518534961245971617626421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15679023307497314411750947 23518534961245971617626421)
                  ·
                    refine ⟨2204862652616809839152477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23518534961245971617626421 2204862652616809839152477)
                    ·
                      refine ⟨826823494731303689682179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2204862652616809839152477 826823494731303689682179)
                      ·
                        rfl

theorem cell23_1610233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_1610233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610233 prefixEnd_1610233 := by exact prefixLift 1610233
  have htrace : WordTrace (prefixWord ++ tailWord_1610233) baseStart_1610233 baseEnd_1610233 := by
    simpa [prefixWord, tailWord_1610233, baseEnd_1610233] using wordTrace_append hprefix tailTrace_1610233
  have hstable : (prefixWord ++ tailWord_1610233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610233).length < 2 ^ (prefixWord ++ tailWord_1610233).sum := by decide
  have hdescent : baseEnd_1610233 < baseStart_1610233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610290 : List Nat := [3, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4]
def baseStart_1610290 : Nat := 118140960795 + 1610290 * 2 ^ 59
def prefixEnd_1610290 : Nat := 4983230072969 + 3 ^ 40 * 1610290 * 2
def baseEnd_1610290 : Nat := 826852763128609966669417

theorem tailTrace_1610290 : CollatzResearch.WordTrace tailWord_1610290 prefixEnd_1610290 826852763128609966669417 := by
  unfold tailWord_1610290
  simp only [CollatzResearch.WordTrace]
  refine ⟨14683025334050455120499081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39154734224134546987997549 14683025334050455120499081)
  ·
    refine ⟨11012269000537841340374311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14683025334050455120499081 11012269000537841340374311)
    ·
      refine ⟨16518403500806762010561467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11012269000537841340374311 16518403500806762010561467)
      ·
        refine ⟨24777605251210143015842201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16518403500806762010561467 24777605251210143015842201)
        ·
          refine ⟨18583203938407607261881651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24777605251210143015842201 18583203938407607261881651)
          ·
            refine ⟨27874805907611410892822477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18583203938407607261881651 27874805907611410892822477)
            ·
              refine ⟨10453052215354279084808429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27874805907611410892822477 10453052215354279084808429)
              ·
                refine ⟨3919894580757854656803161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10453052215354279084808429 3919894580757854656803161)
                ·
                  refine ⟨2939920935568390992602371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3919894580757854656803161 2939920935568390992602371)
                  ·
                    refine ⟨4409881403352586488903557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2939920935568390992602371 4409881403352586488903557)
                    ·
                      refine ⟨826852763128609966669417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4409881403352586488903557 826852763128609966669417)
                      ·
                        rfl

theorem cell23_1610290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_1610290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610290 prefixEnd_1610290 := by exact prefixLift 1610290
  have htrace : WordTrace (prefixWord ++ tailWord_1610290) baseStart_1610290 baseEnd_1610290 := by
    simpa [prefixWord, tailWord_1610290, baseEnd_1610290] using wordTrace_append hprefix tailTrace_1610290
  have hstable : (prefixWord ++ tailWord_1610290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610290).length < 2 ^ (prefixWord ++ tailWord_1610290).sum := by decide
  have hdescent : baseEnd_1610290 < baseStart_1610290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610303 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 6]
def baseStart_1610303 : Nat := 118140960795 + 1610303 * 2 ^ 59
def prefixEnd_1610303 : Nat := 4983230072969 + 3 ^ 40 * 1610303 * 2
def baseEnd_1610303 : Nat := 826859438377118415806857

theorem tailTrace_1610303 : CollatzResearch.WordTrace tailWord_1610303 prefixEnd_1610303 826859438377118415806857 := by
  unfold tailWord_1610303
  simp only [CollatzResearch.WordTrace]
  refine ⟨58732575485154723702219563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39155050323436482468146375 58732575485154723702219563)
  ·
    refine ⟨88098863227732085553329345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58732575485154723702219563 88098863227732085553329345)
    ·
      refine ⟨66074147420799064164997009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88098863227732085553329345 66074147420799064164997009)
      ·
        refine ⟨49555610565599298123747757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66074147420799064164997009 49555610565599298123747757)
        ·
          refine ⟨18583353962099736796405409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49555610565599298123747757 18583353962099736796405409)
          ·
            refine ⟨13937515471574802597304057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18583353962099736796405409 13937515471574802597304057)
            ·
              refine ⟨10453136603681101947978043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13937515471574802597304057 10453136603681101947978043)
              ·
                refine ⟨15679704905521652921967065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10453136603681101947978043 15679704905521652921967065)
                ·
                  refine ⟨11759778679141239691475299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15679704905521652921967065 11759778679141239691475299)
                  ·
                    refine ⟨17639668018711859537212949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11759778679141239691475299 17639668018711859537212949)
                    ·
                      refine ⟨826859438377118415806857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17639668018711859537212949 826859438377118415806857)
                      ·
                        rfl

theorem cell23_1610303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_1610303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610303 prefixEnd_1610303 := by exact prefixLift 1610303
  have htrace : WordTrace (prefixWord ++ tailWord_1610303) baseStart_1610303 baseEnd_1610303 := by
    simpa [prefixWord, tailWord_1610303, baseEnd_1610303] using wordTrace_append hprefix tailTrace_1610303
  have hstable : (prefixWord ++ tailWord_1610303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610303).length < 2 ^ (prefixWord ++ tailWord_1610303).sum := by decide
  have hdescent : baseEnd_1610303 < baseStart_1610303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610353 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 1, 6, 5]
def baseStart_1610353 : Nat := 118140960795 + 1610353 * 2 ^ 59
def prefixEnd_1610353 : Nat := 4983230072969 + 3 ^ 40 * 1610353 * 2
def baseEnd_1610353 : Nat := 826885112409843220181627

theorem tailTrace_1610353 : CollatzResearch.WordTrace tailWord_1610353 prefixEnd_1610353 826885112409843220181627 := by
  unfold tailWord_1610353
  simp only [CollatzResearch.WordTrace]
  refine ⟨58734399134973582241539713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39156266089982388161026475 58734399134973582241539713)
  ·
    refine ⟨44050799351230186681154785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58734399134973582241539713 44050799351230186681154785)
    ·
      refine ⟨33038099513422640010866089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44050799351230186681154785 33038099513422640010866089)
      ·
        refine ⟨24778574635066980008149567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33038099513422640010866089 24778574635066980008149567)
        ·
          refine ⟨37167861952600470012224351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24778574635066980008149567 37167861952600470012224351)
          ·
            refine ⟨55751792928900705018336527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37167861952600470012224351 55751792928900705018336527)
            ·
              refine ⟨83627689393351057527504791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55751792928900705018336527 83627689393351057527504791)
              ·
                refine ⟨125441534090026586291257187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83627689393351057527504791 125441534090026586291257187)
                ·
                  refine ⟨188162301135039879436885781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125441534090026586291257187 188162301135039879436885781)
                  ·
                    refine ⟨8820107865704994348604021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 188162301135039879436885781 8820107865704994348604021)
                    ·
                      refine ⟨826885112409843220181627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8820107865704994348604021 826885112409843220181627)
                      ·
                        rfl

theorem cell23_1610353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_1610353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610353 prefixEnd_1610353 := by exact prefixLift 1610353
  have htrace : WordTrace (prefixWord ++ tailWord_1610353) baseStart_1610353 baseEnd_1610353 := by
    simpa [prefixWord, tailWord_1610353, baseEnd_1610353] using wordTrace_append hprefix tailTrace_1610353
  have hstable : (prefixWord ++ tailWord_1610353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610353).length < 2 ^ (prefixWord ++ tailWord_1610353).sum := by decide
  have hdescent : baseEnd_1610353 < baseStart_1610353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610360 : List Nat := [2, 1, 2, 1, 1, 1, 2, 7, 1, 5]
def baseStart_1610360 : Nat := 118140960795 + 1610360 * 2 ^ 59
def prefixEnd_1610360 : Nat := 4983230072969 + 3 ^ 40 * 1610360 * 2
def baseEnd_1610360 : Nat := 275629568924808230931365

theorem tailTrace_1610360 : CollatzResearch.WordTrace tailWord_1610360 prefixEnd_1610360 275629568924808230931365 := by
  unfold tailWord_1610360
  simp only [CollatzResearch.WordTrace]
  refine ⟨29367327222974111218522267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39156436297298814958029689 29367327222974111218522267)
  ·
    refine ⟨44050990834461166827783401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29367327222974111218522267 44050990834461166827783401)
    ·
      refine ⟨33038243125845875120837551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44050990834461166827783401 33038243125845875120837551)
      ·
        refine ⟨49557364688768812681256327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33038243125845875120837551 49557364688768812681256327)
        ·
          refine ⟨74336047033153219021884491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49557364688768812681256327 74336047033153219021884491)
          ·
            refine ⟨111504070549729828532826737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74336047033153219021884491 111504070549729828532826737)
            ·
              refine ⟨83628052912297371399620053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111504070549729828532826737 83628052912297371399620053)
              ·
                refine ⟨1960032490131969642178595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 83628052912297371399620053 1960032490131969642178595)
                ·
                  refine ⟨2940048735197954463267893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1960032490131969642178595 2940048735197954463267893)
                  ·
                    refine ⟨275629568924808230931365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2940048735197954463267893 275629568924808230931365)
                    ·
                      rfl

theorem cell23_1610360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 1, 5].length) (baseStart_1610360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610360 prefixEnd_1610360 := by exact prefixLift 1610360
  have htrace : WordTrace (prefixWord ++ tailWord_1610360) baseStart_1610360 baseEnd_1610360 := by
    simpa [prefixWord, tailWord_1610360, baseEnd_1610360] using wordTrace_append hprefix tailTrace_1610360
  have hstable : (prefixWord ++ tailWord_1610360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610360).length < 2 ^ (prefixWord ++ tailWord_1610360).sum := by decide
  have hdescent : baseEnd_1610360 < baseStart_1610360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610380 : List Nat := [2, 2, 1, 2, 1, 1, 2, 4, 3, 1, 4]
def baseStart_1610380 : Nat := 118140960795 + 1610380 * 2 ^ 59
def prefixEnd_1610380 : Nat := 4983230072969 + 3 ^ 40 * 1610380 * 2
def baseEnd_1610380 : Nat := 826898976387514614544003

theorem tailTrace_1610380 : CollatzResearch.WordTrace tailWord_1610380 prefixEnd_1610380 826898976387514614544003 := by
  unfold tailWord_1610380
  simp only [CollatzResearch.WordTrace]
  refine ⟨29367691952937882926386297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39156922603917177235181729 29367691952937882926386297)
  ·
    refine ⟨22025768964703412194789723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29367691952937882926386297 22025768964703412194789723)
    ·
      refine ⟨33038653447055118292184585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22025768964703412194789723 33038653447055118292184585)
      ·
        refine ⟨24778990085291338719138439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33038653447055118292184585 24778990085291338719138439)
        ·
          refine ⟨37168485127937008078707659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24778990085291338719138439 37168485127937008078707659)
          ·
            refine ⟨55752727691905512118061489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37168485127937008078707659 55752727691905512118061489)
            ·
              refine ⟨41814545768929134088546117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55752727691905512118061489 41814545768929134088546117)
              ·
                refine ⟨7840227331674212641602397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41814545768929134088546117 7840227331674212641602397)
                ·
                  refine ⟨2940085249377829740600899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7840227331674212641602397 2940085249377829740600899)
                  ·
                    refine ⟨4410127874066744610901349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2940085249377829740600899 4410127874066744610901349)
                    ·
                      refine ⟨826898976387514614544003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4410127874066744610901349 826898976387514614544003)
                      ·
                        rfl

theorem cell23_1610380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_1610380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610380 prefixEnd_1610380 := by exact prefixLift 1610380
  have htrace : WordTrace (prefixWord ++ tailWord_1610380) baseStart_1610380 baseEnd_1610380 := by
    simpa [prefixWord, tailWord_1610380, baseEnd_1610380] using wordTrace_append hprefix tailTrace_1610380
  have hstable : (prefixWord ++ tailWord_1610380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610380).length < 2 ^ (prefixWord ++ tailWord_1610380).sum := by decide
  have hdescent : baseEnd_1610380 < baseStart_1610380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610397 : List Nat := [1, 4, 2, 1, 1, 1, 3, 4, 1, 1, 4]
def baseStart_1610397 : Nat := 118140960795 + 1610397 * 2 ^ 59
def prefixEnd_1610397 : Nat := 4983230072969 + 3 ^ 40 * 1610397 * 2
def baseEnd_1610397 : Nat := 826907705558641048031425

theorem tailTrace_1610397 : CollatzResearch.WordTrace tailWord_1610397 prefixEnd_1610397 826907705558641048031425 := by
  unfold tailWord_1610397
  simp only [CollatzResearch.WordTrace]
  refine ⟨58736003946814177756141445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39157335964542785170760963 58736003946814177756141445)
  ·
    refine ⟨11013000740027658329276521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58736003946814177756141445 11013000740027658329276521)
    ·
      refine ⟨8259750555020743746957391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11013000740027658329276521 8259750555020743746957391)
      ·
        refine ⟨12389625832531115620436087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8259750555020743746957391 12389625832531115620436087)
        ·
          refine ⟨18584438748796673430654131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12389625832531115620436087 18584438748796673430654131)
          ·
            refine ⟨27876658123195010145981197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18584438748796673430654131 27876658123195010145981197)
            ·
              refine ⟨10453746796198128804742949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27876658123195010145981197 10453746796198128804742949)
              ·
                refine ⟨1960077524287149150889303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10453746796198128804742949 1960077524287149150889303)
                ·
                  refine ⟨2940116286430723726333955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1960077524287149150889303 2940116286430723726333955)
                  ·
                    refine ⟨4410174429646085589500933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2940116286430723726333955 4410174429646085589500933)
                    ·
                      refine ⟨826907705558641048031425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4410174429646085589500933 826907705558641048031425)
                      ·
                        rfl

theorem cell23_1610397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_1610397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610397 prefixEnd_1610397 := by exact prefixLift 1610397
  have htrace : WordTrace (prefixWord ++ tailWord_1610397) baseStart_1610397 baseEnd_1610397 := by
    simpa [prefixWord, tailWord_1610397, baseEnd_1610397] using wordTrace_append hprefix tailTrace_1610397
  have hstable : (prefixWord ++ tailWord_1610397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610397).length < 2 ^ (prefixWord ++ tailWord_1610397).sum := by decide
  have hdescent : baseEnd_1610397 < baseStart_1610397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610431 : List Nat := [1, 1, 2, 2, 2, 6, 1, 1, 3, 2, 2]
def baseStart_1610431 : Nat := 118140960795 + 1610431 * 2 ^ 59
def prefixEnd_1610431 : Nat := 4983230072969 + 3 ^ 40 * 1610431 * 2
def baseEnd_1610431 : Nat := 826925163900893915006269

theorem tailTrace_1610431 : CollatzResearch.WordTrace tailWord_1610431 prefixEnd_1610431 826925163900893915006269 := by
  unfold tailWord_1610431
  simp only [CollatzResearch.WordTrace]
  refine ⟨58737244028691001562879147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39158162685794001041919431 58737244028691001562879147)
  ·
    refine ⟨88105866043036502344318721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58737244028691001562879147 88105866043036502344318721)
    ·
      refine ⟨66079399532277376758239041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88105866043036502344318721 66079399532277376758239041)
      ·
        refine ⟨49559549649208032568679281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66079399532277376758239041 49559549649208032568679281)
        ·
          refine ⟨37169662236906024426509461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49559549649208032568679281 37169662236906024426509461)
          ·
            refine ⟨1742327917354969894992631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37169662236906024426509461 1742327917354969894992631)
            ·
              refine ⟨2613491876032454842488947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1742327917354969894992631 2613491876032454842488947)
              ·
                refine ⟨3920237814048682263733421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2613491876032454842488947 3920237814048682263733421)
                ·
                  refine ⟨1470089180268255848900033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3920237814048682263733421 1470089180268255848900033)
                  ·
                    refine ⟨1102566885201191886675025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1470089180268255848900033 1102566885201191886675025)
                    ·
                      refine ⟨826925163900893915006269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1102566885201191886675025 826925163900893915006269)
                      ·
                        rfl

theorem cell23_1610431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 3, 2, 2].length) (baseStart_1610431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610431 prefixEnd_1610431 := by exact prefixLift 1610431
  have htrace : WordTrace (prefixWord ++ tailWord_1610431) baseStart_1610431 baseEnd_1610431 := by
    simpa [prefixWord, tailWord_1610431, baseEnd_1610431] using wordTrace_append hprefix tailTrace_1610431
  have hstable : (prefixWord ++ tailWord_1610431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610431).length < 2 ^ (prefixWord ++ tailWord_1610431).sum := by decide
  have hdescent : baseEnd_1610431 < baseStart_1610431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610480 : List Nat := [2, 1, 1, 1, 3, 1, 4, 2, 2, 6]
def baseStart_1610480 : Nat := 118140960795 + 1610480 * 2 ^ 59
def prefixEnd_1610480 : Nat := 4983230072969 + 3 ^ 40 * 1610480 * 2
def baseEnd_1610480 : Nat := 275650108150988074431181

theorem tailTrace_1610480 : CollatzResearch.WordTrace tailWord_1610480 prefixEnd_1610480 275650108150988074431181 := by
  unfold tailWord_1610480
  simp only [CollatzResearch.WordTrace]
  refine ⟨29369515602756741465706447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39159354137008988620941929 29369515602756741465706447)
  ·
    refine ⟨44054273404135112198559671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29369515602756741465706447 44054273404135112198559671)
    ·
      refine ⟨66081410106202668297839507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44054273404135112198559671 66081410106202668297839507)
      ·
        refine ⟨99122115159304002446759261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66081410106202668297839507 99122115159304002446759261)
        ·
          refine ⟨37170793184739000917534723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99122115159304002446759261 37170793184739000917534723)
          ·
            refine ⟨55756189777108501376302085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37170793184739000917534723 55756189777108501376302085)
            ·
              refine ⟨10454285583207844008056641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55756189777108501376302085 10454285583207844008056641)
              ·
                refine ⟨7840714187405883006042481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10454285583207844008056641 7840714187405883006042481)
                ·
                  refine ⟨5880535640554412254531861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7840714187405883006042481 5880535640554412254531861)
                  ·
                    refine ⟨275650108150988074431181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5880535640554412254531861 275650108150988074431181)
                    ·
                      rfl

theorem cell23_1610480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 2, 6].length) (baseStart_1610480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610480 prefixEnd_1610480 := by exact prefixLift 1610480
  have htrace : WordTrace (prefixWord ++ tailWord_1610480) baseStart_1610480 baseEnd_1610480 := by
    simpa [prefixWord, tailWord_1610480, baseEnd_1610480] using wordTrace_append hprefix tailTrace_1610480
  have hstable : (prefixWord ++ tailWord_1610480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610480).length < 2 ^ (prefixWord ++ tailWord_1610480).sum := by decide
  have hdescent : baseEnd_1610480 < baseStart_1610480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610487 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 5, 4, 2]
def baseStart_1610487 : Nat := 118140960795 + 1610487 * 2 ^ 59
def prefixEnd_1610487 : Nat := 4983230072969 + 3 ^ 40 * 1610487 * 2
def baseEnd_1610487 : Nat := 826953918817545695906011

theorem tailTrace_1610487 : CollatzResearch.WordTrace tailWord_1610487 prefixEnd_1610487 826953918817545695906011 := by
  unfold tailWord_1610487
  simp only [CollatzResearch.WordTrace]
  refine ⟨58739286516488123126917715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39159524344325415417945143 58739286516488123126917715)
  ·
    refine ⟨88108929774732184690376573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58739286516488123126917715 88108929774732184690376573)
    ·
      refine ⟨33040848665524569258891215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88108929774732184690376573 33040848665524569258891215)
      ·
        refine ⟨49561272998286853888336823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33040848665524569258891215 49561272998286853888336823)
        ·
          refine ⟨74341909497430280832505235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49561272998286853888336823 74341909497430280832505235)
          ·
            refine ⟨111512864246145421248757853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74341909497430280832505235 111512864246145421248757853)
            ·
              refine ⟨41817324092304532968284195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111512864246145421248757853 41817324092304532968284195)
              ·
                refine ⟨62725986138456799452426293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41817324092304532968284195 62725986138456799452426293)
                ·
                  refine ⟨5880561200480324948664965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62725986138456799452426293 5880561200480324948664965)
                  ·
                    refine ⟨1102605225090060927874681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5880561200480324948664965 1102605225090060927874681)
                    ·
                      refine ⟨826953918817545695906011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1102605225090060927874681 826953918817545695906011)
                      ·
                        rfl

theorem cell23_1610487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 4, 2].length) (baseStart_1610487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610487 prefixEnd_1610487 := by exact prefixLift 1610487
  have htrace : WordTrace (prefixWord ++ tailWord_1610487) baseStart_1610487 baseEnd_1610487 := by
    simpa [prefixWord, tailWord_1610487, baseEnd_1610487] using wordTrace_append hprefix tailTrace_1610487
  have hstable : (prefixWord ++ tailWord_1610487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610487).length < 2 ^ (prefixWord ++ tailWord_1610487).sum := by decide
  have hdescent : baseEnd_1610487 < baseStart_1610487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610490 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5]
def baseStart_1610490 : Nat := 118140960795 + 1610490 * 2 ^ 59
def prefixEnd_1610490 : Nat := 4983230072969 + 3 ^ 40 * 1610490 * 2
def baseEnd_1610490 : Nat := 826955459259509184168497

theorem tailTrace_1610490 : CollatzResearch.WordTrace tailWord_1610490 prefixEnd_1610490 826955459259509184168497 := by
  unfold tailWord_1610490
  simp only [CollatzResearch.WordTrace]
  refine ⟨14684848983869313659819231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39159597290318169759517949 14684848983869313659819231)
  ·
    refine ⟨22027273475803970489728847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14684848983869313659819231 22027273475803970489728847)
    ·
      refine ⟨33040910213705955734593271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22027273475803970489728847 33040910213705955734593271)
      ·
        refine ⟨49561365320558933601889907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33040910213705955734593271 49561365320558933601889907)
        ·
          refine ⟨74342047980838400402834861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49561365320558933601889907 74342047980838400402834861)
          ·
            refine ⟨27878267992814400151063073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74342047980838400402834861 27878267992814400151063073)
            ·
              refine ⟨20908700994610800113297305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27878267992814400151063073 20908700994610800113297305)
              ·
                refine ⟨15681525745958100084972979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20908700994610800113297305 15681525745958100084972979)
                ·
                  refine ⟨23522288618937150127459469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15681525745958100084972979 23522288618937150127459469)
                  ·
                    refine ⟨8820858232101431297797301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23522288618937150127459469 8820858232101431297797301)
                    ·
                      refine ⟨826955459259509184168497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8820858232101431297797301 826955459259509184168497)
                      ·
                        rfl

theorem cell23_1610490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_1610490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610490 prefixEnd_1610490 := by exact prefixLift 1610490
  have htrace : WordTrace (prefixWord ++ tailWord_1610490) baseStart_1610490 baseEnd_1610490 := by
    simpa [prefixWord, tailWord_1610490, baseEnd_1610490] using wordTrace_append hprefix tailTrace_1610490
  have hstable : (prefixWord ++ tailWord_1610490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610490).length < 2 ^ (prefixWord ++ tailWord_1610490).sum := by decide
  have hdescent : baseEnd_1610490 < baseStart_1610490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610504 : List Nat := [2, 1, 3, 2, 2, 2, 1, 3, 1, 4, 2]
def baseStart_1610504 : Nat := 118140960795 + 1610504 * 2 ^ 59
def prefixEnd_1610504 : Nat := 4983230072969 + 3 ^ 40 * 1610504 * 2
def baseEnd_1610504 : Nat := 826962647988672129393433

theorem tailTrace_1610504 : CollatzResearch.WordTrace tailWord_1610504 prefixEnd_1610504 826962647988672129393433 := by
  unfold tailWord_1610504
  simp only [CollatzResearch.WordTrace]
  refine ⟨29369953278713267515143283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39159937704951023353524377 29369953278713267515143283)
  ·
    refine ⟨44054929918069901272714925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29369953278713267515143283 44054929918069901272714925)
    ·
      refine ⟨16520598719276212977268097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44054929918069901272714925 16520598719276212977268097)
      ·
        refine ⟨12390449039457159732951073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16520598719276212977268097 12390449039457159732951073)
        ·
          refine ⟨9292836779592869799713305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12390449039457159732951073 9292836779592869799713305)
          ·
            refine ⟨6969627584694652349784979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9292836779592869799713305 6969627584694652349784979)
            ·
              refine ⟨10454441377041978524677469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6969627584694652349784979 10454441377041978524677469)
              ·
                refine ⟨3920415516390741946754051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10454441377041978524677469 3920415516390741946754051)
                ·
                  refine ⟨5880623274586112920131077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3920415516390741946754051 5880623274586112920131077)
                  ·
                    refine ⟨1102616863984896172524577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5880623274586112920131077 1102616863984896172524577)
                    ·
                      refine ⟨826962647988672129393433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1102616863984896172524577 826962647988672129393433)
                      ·
                        rfl

theorem cell23_1610504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_1610504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610504 prefixEnd_1610504 := by exact prefixLift 1610504
  have htrace : WordTrace (prefixWord ++ tailWord_1610504) baseStart_1610504 baseEnd_1610504 := by
    simpa [prefixWord, tailWord_1610504, baseEnd_1610504] using wordTrace_append hprefix tailTrace_1610504
  have hstable : (prefixWord ++ tailWord_1610504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610504).length < 2 ^ (prefixWord ++ tailWord_1610504).sum := by decide
  have hdescent : baseEnd_1610504 < baseStart_1610504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610520 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 1, 2, 7]
def baseStart_1610520 : Nat := 118140960795 + 1610520 * 2 ^ 59
def prefixEnd_1610520 : Nat := 4983230072969 + 3 ^ 40 * 1610520 * 2
def baseEnd_1610520 : Nat := 826970863679144066793359

theorem tailTrace_1610520 : CollatzResearch.WordTrace tailWord_1610520 prefixEnd_1610520 826970863679144066793359 := by
  unfold tailWord_1610520
  simp only [CollatzResearch.WordTrace]
  refine ⟨29370245062684284881434507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39160326750245713175246009 29370245062684284881434507)
  ·
    refine ⟨44055367594026427322151761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29370245062684284881434507 44055367594026427322151761)
    ·
      refine ⟨33041525695519820491613821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44055367594026427322151761 33041525695519820491613821)
      ·
        refine ⟨12390572135819932684355183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33041525695519820491613821 12390572135819932684355183)
        ·
          refine ⟨18585858203729899026532775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12390572135819932684355183 18585858203729899026532775)
          ·
            refine ⟨27878787305594848539799163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18585858203729899026532775 27878787305594848539799163)
            ·
              refine ⟨41818180958392272809698745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27878787305594848539799163 41818180958392272809698745)
              ·
                refine ⟨31363635718794204607274059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41818180958392272809698745 31363635718794204607274059)
                ·
                  refine ⟨47045453578191306910911089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31363635718794204607274059 47045453578191306910911089)
                  ·
                    refine ⟨35284090183643480183183317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47045453578191306910911089 35284090183643480183183317)
                    ·
                      refine ⟨826970863679144066793359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35284090183643480183183317 826970863679144066793359)
                      ·
                        rfl

theorem cell23_1610520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_1610520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610520 prefixEnd_1610520 := by exact prefixLift 1610520
  have htrace : WordTrace (prefixWord ++ tailWord_1610520) baseStart_1610520 baseEnd_1610520 := by
    simpa [prefixWord, tailWord_1610520, baseEnd_1610520] using wordTrace_append hprefix tailTrace_1610520
  have hstable : (prefixWord ++ tailWord_1610520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610520).length < 2 ^ (prefixWord ++ tailWord_1610520).sum := by decide
  have hdescent : baseEnd_1610520 < baseStart_1610520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610631 : List Nat := [1, 1, 4, 2, 3, 2, 2, 1, 2, 2, 3]
def baseStart_1610631 : Nat := 118140960795 + 1610631 * 2 ^ 59
def prefixEnd_1610631 : Nat := 4983230072969 + 3 ^ 40 * 1610631 * 2
def baseEnd_1610631 : Nat := 827027860031793132505349

theorem tailTrace_1610631 : CollatzResearch.WordTrace tailWord_1610631 prefixEnd_1610631 827027860031793132505349 := by
  unfold tailWord_1610631
  simp only [CollatzResearch.WordTrace]
  refine ⟨58744538627966435720159747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39163025751977623813439831 58744538627966435720159747)
  ·
    refine ⟨88116807941949653580239621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58744538627966435720159747 88116807941949653580239621)
    ·
      refine ⟨16521901489115560046294929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88116807941949653580239621 16521901489115560046294929)
      ·
        refine ⟨12391426116836670034721197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16521901489115560046294929 12391426116836670034721197)
        ·
          refine ⟨4646784793813751263020449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12391426116836670034721197 4646784793813751263020449)
          ·
            refine ⟨3485088595360313447265337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4646784793813751263020449 3485088595360313447265337)
            ·
              refine ⟨2613816446520235085449003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3485088595360313447265337 2613816446520235085449003)
              ·
                refine ⟨3920724669780352628173505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2613816446520235085449003 3920724669780352628173505)
                ·
                  refine ⟨2940543502335264471130129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3920724669780352628173505 2940543502335264471130129)
                  ·
                    refine ⟨2205407626751448353347597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2940543502335264471130129 2205407626751448353347597)
                    ·
                      refine ⟨827027860031793132505349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2205407626751448353347597 827027860031793132505349)
                      ·
                        rfl

theorem cell23_1610631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_1610631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610631 prefixEnd_1610631 := by exact prefixLift 1610631
  have htrace : WordTrace (prefixWord ++ tailWord_1610631) baseStart_1610631 baseEnd_1610631 := by
    simpa [prefixWord, tailWord_1610631, baseEnd_1610631] using wordTrace_append hprefix tailTrace_1610631
  have hstable : (prefixWord ++ tailWord_1610631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610631).length < 2 ^ (prefixWord ++ tailWord_1610631).sum := by decide
  have hdescent : baseEnd_1610631 < baseStart_1610631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610655 : List Nat := [1, 1, 2, 5, 2, 3, 2, 2, 1, 4]
def baseStart_1610655 : Nat := 118140960795 + 1610655 * 2 ^ 59
def prefixEnd_1610655 : Nat := 4983230072969 + 3 ^ 40 * 1610655 * 2
def baseEnd_1610655 : Nat := 275680061189167012868413

theorem tailTrace_1610655 : CollatzResearch.WordTrace tailWord_1610655 prefixEnd_1610655 275680061189167012868413 := by
  unfold tailWord_1610655
  simp only [CollatzResearch.WordTrace]
  refine ⟨58745413979879487819033419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39163609319919658546022279 58745413979879487819033419)
  ·
    refine ⟨88118120969819231728550129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58745413979879487819033419 88118120969819231728550129)
    ·
      refine ⟨66088590727364423796412597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88118120969819231728550129 66088590727364423796412597)
      ·
        refine ⟨6195805380690414730913681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66088590727364423796412597 6195805380690414730913681)
        ·
          refine ⟨4646854035517811048185261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6195805380690414730913681 4646854035517811048185261)
          ·
            refine ⟨1742570263319179143069473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4646854035517811048185261 1742570263319179143069473)
            ·
              refine ⟨1306927697489384357302105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1742570263319179143069473 1306927697489384357302105)
              ·
                refine ⟨980195773117038267976579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1306927697489384357302105 980195773117038267976579)
                ·
                  refine ⟨1470293659675557401964869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 980195773117038267976579 1470293659675557401964869)
                  ·
                    refine ⟨275680061189167012868413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1470293659675557401964869 275680061189167012868413)
                    ·
                      rfl

theorem cell23_1610655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2, 1, 4].length) (baseStart_1610655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610655 prefixEnd_1610655 := by exact prefixLift 1610655
  have htrace : WordTrace (prefixWord ++ tailWord_1610655) baseStart_1610655 baseEnd_1610655 := by
    simpa [prefixWord, tailWord_1610655, baseEnd_1610655] using wordTrace_append hprefix tailTrace_1610655
  have hstable : (prefixWord ++ tailWord_1610655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610655).length < 2 ^ (prefixWord ++ tailWord_1610655).sum := by decide
  have hdescent : baseEnd_1610655 < baseStart_1610655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610687 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 5]
def baseStart_1610687 : Nat := 118140960795 + 1610687 * 2 ^ 59
def prefixEnd_1610687 : Nat := 4983230072969 + 3 ^ 40 * 1610687 * 2
def baseEnd_1610687 : Nat := 827056614948444913405091

theorem tailTrace_1610687 : CollatzResearch.WordTrace tailWord_1610687 prefixEnd_1610687 827056614948444913405091 := by
  unfold tailWord_1610687
  simp only [CollatzResearch.WordTrace]
  refine ⟨58746581115763557284198315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39164387410509038189465543 58746581115763557284198315)
  ·
    refine ⟨88119871673645335926297473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58746581115763557284198315 88119871673645335926297473)
    ·
      refine ⟨66089903755234001944723105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88119871673645335926297473 66089903755234001944723105)
      ·
        refine ⟨49567427816425501458542329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66089903755234001944723105 49567427816425501458542329)
        ·
          refine ⟨37175570862319126093906747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49567427816425501458542329 37175570862319126093906747)
          ·
            refine ⟨55763356293478689140860121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37175570862319126093906747 55763356293478689140860121)
            ·
              refine ⟨41822517220109016855645091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55763356293478689140860121 41822517220109016855645091)
              ·
                refine ⟨62733775830163525283467637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41822517220109016855645091 62733775830163525283467637)
                ·
                  refine ⟨5881291484077830495325091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62733775830163525283467637 5881291484077830495325091)
                  ·
                    refine ⟨8821937226116745742987637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5881291484077830495325091 8821937226116745742987637)
                    ·
                      refine ⟨827056614948444913405091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8821937226116745742987637 827056614948444913405091)
                      ·
                        rfl

theorem cell23_1610687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_1610687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610687 prefixEnd_1610687 := by exact prefixLift 1610687
  have htrace : WordTrace (prefixWord ++ tailWord_1610687) baseStart_1610687 baseEnd_1610687 := by
    simpa [prefixWord, tailWord_1610687, baseEnd_1610687] using wordTrace_append hprefix tailTrace_1610687
  have hstable : (prefixWord ++ tailWord_1610687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610687).length < 2 ^ (prefixWord ++ tailWord_1610687).sum := by decide
  have hdescent : baseEnd_1610687 < baseStart_1610687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610688 : List Nat := [2, 1, 1, 2, 3, 5, 1, 1, 2, 3, 2]
def baseStart_1610688 : Nat := 118140960795 + 1610688 * 2 ^ 59
def prefixEnd_1610688 : Nat := 4983230072969 + 3 ^ 40 * 1610688 * 2
def baseEnd_1610688 : Nat := 827057128429099409492587

theorem tailTrace_1610688 : CollatzResearch.WordTrace tailWord_1610688 prefixEnd_1610688 827057128429099409492587 := by
  unfold tailWord_1610688
  simp only [CollatzResearch.WordTrace]
  refine ⟨29373308794379967227492359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39164411725839956303323145 29373308794379967227492359)
  ·
    refine ⟨44059963191569950841238539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29373308794379967227492359 44059963191569950841238539)
    ·
      refine ⟨66089944787354926261857809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44059963191569950841238539 66089944787354926261857809)
      ·
        refine ⟨49567458590516194696393357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66089944787354926261857809 49567458590516194696393357)
        ·
          refine ⟨18587796971443573011147509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49567458590516194696393357 18587796971443573011147509)
          ·
            refine ⟨1742605966072834969795079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18587796971443573011147509 1742605966072834969795079)
            ·
              refine ⟨2613908949109252454692619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1742605966072834969795079 2613908949109252454692619)
              ·
                refine ⟨3920863423663878682038929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2613908949109252454692619 3920863423663878682038929)
                ·
                  refine ⟨2940647567747909011529197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3920863423663878682038929 2940647567747909011529197)
                  ·
                    refine ⟨1102742837905465879323449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2940647567747909011529197 1102742837905465879323449)
                    ·
                      refine ⟨827057128429099409492587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1102742837905465879323449 827057128429099409492587)
                      ·
                        rfl

theorem cell23_1610688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 2, 3, 2].length) (baseStart_1610688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610688 prefixEnd_1610688 := by exact prefixLift 1610688
  have htrace : WordTrace (prefixWord ++ tailWord_1610688) baseStart_1610688 baseEnd_1610688 := by
    simpa [prefixWord, tailWord_1610688, baseEnd_1610688] using wordTrace_append hprefix tailTrace_1610688
  have hstable : (prefixWord ++ tailWord_1610688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610688).length < 2 ^ (prefixWord ++ tailWord_1610688).sum := by decide
  have hdescent : baseEnd_1610688 < baseStart_1610688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610767 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 5, 8]
def baseStart_1610767 : Nat := 118140960795 + 1610767 * 2 ^ 59
def prefixEnd_1610767 : Nat := 4983230072969 + 3 ^ 40 * 1610767 * 2
def baseEnd_1610767 : Nat := 275699231133601533468241

theorem tailTrace_1610767 : CollatzResearch.WordTrace tailWord_1610767 prefixEnd_1610767 275699231133601533468241 := by
  unfold tailWord_1610767
  simp only [CollatzResearch.WordTrace]
  refine ⟨58749498955473730947110555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39166332636982487298073703 58749498955473730947110555)
  ·
    refine ⟨88124248433210596420665833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58749498955473730947110555 88124248433210596420665833)
    ·
      refine ⟨66093186324907947315499375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88124248433210596420665833 66093186324907947315499375)
      ·
        refine ⟨99139779487361920973249063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66093186324907947315499375 99139779487361920973249063)
        ·
          refine ⟨148709669231042881459873595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99139779487361920973249063 148709669231042881459873595)
          ·
            refine ⟨223064503846564322189810393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148709669231042881459873595 223064503846564322189810393)
            ·
              refine ⟨167298377884923241642357795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223064503846564322189810393 167298377884923241642357795)
              ·
                refine ⟨250947566827384862463536693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167298377884923241642357795 250947566827384862463536693)
                ·
                  refine ⟨23526334390067330855956565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 250947566827384862463536693 23526334390067330855956565)
                  ·
                    refine ⟨275699231133601533468241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 23526334390067330855956565 275699231133601533468241)
                    ·
                      rfl

theorem cell23_1610767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 8].length) (baseStart_1610767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610767 prefixEnd_1610767 := by exact prefixLift 1610767
  have htrace : WordTrace (prefixWord ++ tailWord_1610767) baseStart_1610767 baseEnd_1610767 := by
    simpa [prefixWord, tailWord_1610767, baseEnd_1610767] using wordTrace_append hprefix tailTrace_1610767
  have hstable : (prefixWord ++ tailWord_1610767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610767).length < 2 ^ (prefixWord ++ tailWord_1610767).sum := by decide
  have hdescent : baseEnd_1610767 < baseStart_1610767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610785 : List Nat := [1, 2, 3, 2, 3, 1, 4, 1, 2, 1, 3]
def baseStart_1610785 : Nat := 118140960795 + 1610785 * 2 ^ 59
def prefixEnd_1610785 : Nat := 4983230072969 + 3 ^ 40 * 1610785 * 2
def baseEnd_1610785 : Nat := 827106936052585529979641

theorem tailTrace_1610785 : CollatzResearch.WordTrace tailWord_1610785 prefixEnd_1610785 827106936052585529979641 := by
  unfold tailWord_1610785
  simp only [CollatzResearch.WordTrace]
  refine ⟨58750155469408520021265809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39166770312939013347510539 58750155469408520021265809)
  ·
    refine ⟨44062616602056390015949357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58750155469408520021265809 44062616602056390015949357)
    ·
      refine ⟨16523481225771146255981009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44062616602056390015949357 16523481225771146255981009)
      ·
        refine ⟨12392610919328359691985757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16523481225771146255981009 12392610919328359691985757)
        ·
          refine ⟨4647229094748134884494659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12392610919328359691985757 4647229094748134884494659)
          ·
            refine ⟨6970843642122202326741989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4647229094748134884494659 6970843642122202326741989)
            ·
              refine ⟨1307033182897912936264123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6970843642122202326741989 1307033182897912936264123)
              ·
                refine ⟨1960549774346869404396185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1307033182897912936264123 1960549774346869404396185)
                ·
                  refine ⟨1470412330760152053297139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1960549774346869404396185 1470412330760152053297139)
                  ·
                    refine ⟨2205618496140228079945709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1470412330760152053297139 2205618496140228079945709)
                    ·
                      refine ⟨827106936052585529979641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2205618496140228079945709 827106936052585529979641)
                      ·
                        rfl

theorem cell23_1610785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_1610785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610785 prefixEnd_1610785 := by exact prefixLift 1610785
  have htrace : WordTrace (prefixWord ++ tailWord_1610785) baseStart_1610785 baseEnd_1610785 := by
    simpa [prefixWord, tailWord_1610785, baseEnd_1610785] using wordTrace_append hprefix tailTrace_1610785
  have hstable : (prefixWord ++ tailWord_1610785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610785).length < 2 ^ (prefixWord ++ tailWord_1610785).sum := by decide
  have hdescent : baseEnd_1610785 < baseStart_1610785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610808 : List Nat := [2, 1, 2, 1, 5, 2, 1, 2, 1, 4, 2]
def baseStart_1610808 : Nat := 118140960795 + 1610808 * 2 ^ 59
def prefixEnd_1610808 : Nat := 4983230072969 + 3 ^ 40 * 1610808 * 2
def baseEnd_1610808 : Nat := 827118746107638939992035

theorem tailTrace_1610808 : CollatzResearch.WordTrace tailWord_1610808 prefixEnd_1610808 827118746107638939992035 := by
  unfold tailWord_1610808
  simp only [CollatzResearch.WordTrace]
  refine ⟨29375497174162597474676539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39167329565550129966235385 29375497174162597474676539)
  ·
    refine ⟨44063245761243896212014809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29375497174162597474676539 44063245761243896212014809)
    ·
      refine ⟨33047434320932922159011107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44063245761243896212014809 33047434320932922159011107)
      ·
        refine ⟨49571151481399383238516661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33047434320932922159011107 49571151481399383238516661)
        ·
          refine ⟨4647295451381192178610937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49571151481399383238516661 4647295451381192178610937)
          ·
            refine ⟨3485471588535894133958203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4647295451381192178610937 3485471588535894133958203)
            ·
              refine ⟨5228207382803841200937305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3485471588535894133958203 5228207382803841200937305)
              ·
                refine ⟨3921155537102880900702979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5228207382803841200937305 3921155537102880900702979)
                ·
                  refine ⟨5881733305654321351054469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3921155537102880900702979 5881733305654321351054469)
                  ·
                    refine ⟨1102824994810185253322713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5881733305654321351054469 1102824994810185253322713)
                    ·
                      refine ⟨827118746107638939992035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1102824994810185253322713 827118746107638939992035)
                      ·
                        rfl

theorem cell23_1610808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 1, 4, 2].length) (baseStart_1610808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610808 prefixEnd_1610808 := by exact prefixLift 1610808
  have htrace : WordTrace (prefixWord ++ tailWord_1610808) baseStart_1610808 baseEnd_1610808 := by
    simpa [prefixWord, tailWord_1610808, baseEnd_1610808] using wordTrace_append hprefix tailTrace_1610808
  have hstable : (prefixWord ++ tailWord_1610808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610808).length < 2 ^ (prefixWord ++ tailWord_1610808).sum := by decide
  have hdescent : baseEnd_1610808 < baseStart_1610808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610851 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 4, 5, 2]
def baseStart_1610851 : Nat := 118140960795 + 1610851 * 2 ^ 59
def prefixEnd_1610851 : Nat := 4983230072969 + 3 ^ 40 * 1610851 * 2
def baseEnd_1610851 : Nat := 827140825775782271754337

theorem tailTrace_1610851 : CollatzResearch.WordTrace tailWord_1610851 prefixEnd_1610851 827140825775782271754337 := by
  unfold tailWord_1610851
  simp only [CollatzResearch.WordTrace]
  refine ⟨58752562687169413293168407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39168375124779608862112271 58752562687169413293168407)
  ·
    refine ⟨88128844030754119939752611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58752562687169413293168407 88128844030754119939752611)
    ·
      refine ⟨132193266046131179909628917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88128844030754119939752611 132193266046131179909628917)
      ·
        refine ⟨12393118691824798116527711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132193266046131179909628917 12393118691824798116527711)
        ·
          refine ⟨18589678037737197174791567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12393118691824798116527711 18589678037737197174791567)
          ·
            refine ⟨27884517056605795762187351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18589678037737197174791567 27884517056605795762187351)
            ·
              refine ⟨41826775584908693643281027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27884517056605795762187351 41826775584908693643281027)
              ·
                refine ⟨62740163377363040464921541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41826775584908693643281027 62740163377363040464921541)
                ·
                  refine ⟨11763780633255570087172789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62740163377363040464921541 11763780633255570087172789)
                  ·
                    refine ⟨1102854434367709695672449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11763780633255570087172789 1102854434367709695672449)
                    ·
                      refine ⟨827140825775782271754337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1102854434367709695672449 827140825775782271754337)
                      ·
                        rfl

theorem cell23_1610851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 5, 2].length) (baseStart_1610851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610851 prefixEnd_1610851 := by exact prefixLift 1610851
  have htrace : WordTrace (prefixWord ++ tailWord_1610851) baseStart_1610851 baseEnd_1610851 := by
    simpa [prefixWord, tailWord_1610851, baseEnd_1610851] using wordTrace_append hprefix tailTrace_1610851
  have hstable : (prefixWord ++ tailWord_1610851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610851).length < 2 ^ (prefixWord ++ tailWord_1610851).sum := by decide
  have hdescent : baseEnd_1610851 < baseStart_1610851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610861 : List Nat := [1, 5, 1, 1, 2, 3, 1, 1, 1, 7]
def baseStart_1610861 : Nat := 118140960795 + 1610861 * 2 ^ 59
def prefixEnd_1610861 : Nat := 4983230072969 + 3 ^ 40 * 1610861 * 2
def baseEnd_1610861 : Nat := 275715320194109077543097

theorem tailTrace_1610861 : CollatzResearch.WordTrace tailWord_1610861 prefixEnd_1610861 275715320194109077543097 := by
  unfold tailWord_1610861
  simp only [CollatzResearch.WordTrace]
  refine ⟨58752927417133185001032437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39168618278088790000688291 58752927417133185001032437)
  ·
    refine ⟨5508086945356236093846791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58752927417133185001032437 5508086945356236093846791)
    ·
      refine ⟨8262130418034354140770187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5508086945356236093846791 8262130418034354140770187)
      ·
        refine ⟨12393195627051531211155281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8262130418034354140770187 12393195627051531211155281)
        ·
          refine ⟨9294896720288648408366461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12393195627051531211155281 9294896720288648408366461)
          ·
            refine ⟨3485586270108243153137423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9294896720288648408366461 3485586270108243153137423)
            ·
              refine ⟨5228379405162364729706135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3485586270108243153137423 5228379405162364729706135)
              ·
                refine ⟨7842569107743547094559203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5228379405162364729706135 7842569107743547094559203)
                ·
                  refine ⟨11763853661615320641838805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7842569107743547094559203 11763853661615320641838805)
                  ·
                    refine ⟨275715320194109077543097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11763853661615320641838805 275715320194109077543097)
                    ·
                      rfl

theorem cell23_1610861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_1610861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610861 prefixEnd_1610861 := by exact prefixLift 1610861
  have htrace : WordTrace (prefixWord ++ tailWord_1610861) baseStart_1610861 baseEnd_1610861 := by
    simpa [prefixWord, tailWord_1610861, baseEnd_1610861] using wordTrace_append hprefix tailTrace_1610861
  have hstable : (prefixWord ++ tailWord_1610861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610861).length < 2 ^ (prefixWord ++ tailWord_1610861).sum := by decide
  have hdescent : baseEnd_1610861 < baseStart_1610861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610901 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 6, 2, 3]
def baseStart_1610901 : Nat := 118140960795 + 1610901 * 2 ^ 59
def prefixEnd_1610901 : Nat := 4983230072969 + 3 ^ 40 * 1610901 * 2
def baseEnd_1610901 : Nat := 827166499808507076129107

theorem tailTrace_1610901 : CollatzResearch.WordTrace tailWord_1610901 prefixEnd_1610901 827166499808507076129107 := by
  unfold tailWord_1610901
  simp only [CollatzResearch.WordTrace]
  refine ⟨58754386336988271832488557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39169590891325514554992371 58754386336988271832488557)
  ·
    refine ⟨22032894876370601937183209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58754386336988271832488557 22032894876370601937183209)
    ·
      refine ⟨16524671157277951452887407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22032894876370601937183209 16524671157277951452887407)
      ·
        refine ⟨24787006735916927179331111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16524671157277951452887407 24787006735916927179331111)
        ·
          refine ⟨37180510103875390768996667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24787006735916927179331111 37180510103875390768996667)
          ·
            refine ⟨55770765155813086153495001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37180510103875390768996667 55770765155813086153495001)
            ·
              refine ⟨41828073866859814615121251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55770765155813086153495001 41828073866859814615121251)
              ·
                refine ⟨62742110800289721922681877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41828073866859814615121251 62742110800289721922681877)
                ·
                  refine ⟨2941036443763580715125713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62742110800289721922681877 2941036443763580715125713)
                  ·
                    refine ⟨2205777332822685536344285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2941036443763580715125713 2205777332822685536344285)
                    ·
                      refine ⟨827166499808507076129107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2205777332822685536344285 827166499808507076129107)
                      ·
                        rfl

theorem cell23_1610901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_1610901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610901 prefixEnd_1610901 := by exact prefixLift 1610901
  have htrace : WordTrace (prefixWord ++ tailWord_1610901) baseStart_1610901 baseEnd_1610901 := by
    simpa [prefixWord, tailWord_1610901, baseEnd_1610901] using wordTrace_append hprefix tailTrace_1610901
  have hstable : (prefixWord ++ tailWord_1610901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610901).length < 2 ^ (prefixWord ++ tailWord_1610901).sum := by decide
  have hdescent : baseEnd_1610901 < baseStart_1610901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610908 : List Nat := [2, 2, 3, 2, 1, 2, 2, 2, 3, 4]
def baseStart_1610908 : Nat := 118140960795 + 1610908 * 2 ^ 59
def prefixEnd_1610908 : Nat := 4983230072969 + 3 ^ 40 * 1610908 * 2
def baseEnd_1610908 : Nat := 275723364724362849580525

theorem tailTrace_1610908 : CollatzResearch.WordTrace tailWord_1610908 prefixEnd_1610908 275723364724362849580525 := by
  unfold tailWord_1610908
  simp only [CollatzResearch.WordTrace]
  refine ⟨29377320823981456013996689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39169761098641941351995585 29377320823981456013996689)
  ·
    refine ⟨22032990617986092010497517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29377320823981456013996689 22032990617986092010497517)
    ·
      refine ⟨8262371481744784503936569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22032990617986092010497517 8262371481744784503936569)
      ·
        refine ⟨6196778611308588377952427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8262371481744784503936569 6196778611308588377952427)
        ·
          refine ⟨9295167916962882566928641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6196778611308588377952427 9295167916962882566928641)
          ·
            refine ⟨6971375937722161925196481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9295167916962882566928641 6971375937722161925196481)
            ·
              refine ⟨5228531953291621443897361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6971375937722161925196481 5228531953291621443897361)
              ·
                refine ⟨3921398964968716082923021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5228531953291621443897361 3921398964968716082923021)
                ·
                  refine ⟨1470524611863268531096133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3921398964968716082923021 1470524611863268531096133)
                  ·
                    refine ⟨275723364724362849580525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1470524611863268531096133 275723364724362849580525)
                    ·
                      rfl

theorem cell23_1610908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_1610908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610908 prefixEnd_1610908 := by exact prefixLift 1610908
  have htrace : WordTrace (prefixWord ++ tailWord_1610908) baseStart_1610908 baseEnd_1610908 := by
    simpa [prefixWord, tailWord_1610908, baseEnd_1610908] using wordTrace_append hprefix tailTrace_1610908
  have hstable : (prefixWord ++ tailWord_1610908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610908).length < 2 ^ (prefixWord ++ tailWord_1610908).sum := by decide
  have hdescent : baseEnd_1610908 < baseStart_1610908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610924 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 8]
def baseStart_1610924 : Nat := 118140960795 + 1610924 * 2 ^ 59
def prefixEnd_1610924 : Nat := 4983230072969 + 3 ^ 40 * 1610924 * 2
def baseEnd_1610924 : Nat := 827178309863560486141501

theorem tailTrace_1610924 : CollatzResearch.WordTrace tailWord_1610924 prefixEnd_1610924 827178309863560486141501 := by
  unfold tailWord_1610924
  simp only [CollatzResearch.WordTrace]
  refine ⟨29377612607952473380287913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39170150143936631173717217 29377612607952473380287913)
  ·
    refine ⟨22033209455964355035215935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29377612607952473380287913 22033209455964355035215935)
    ·
      refine ⟨33049814183946532552823903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22033209455964355035215935 33049814183946532552823903)
      ·
        refine ⟨49574721275919798829235855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33049814183946532552823903 49574721275919798829235855)
        ·
          refine ⟨74362081913879698243853783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49574721275919798829235855 74362081913879698243853783)
          ·
            refine ⟨111543122870819547365780675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74362081913879698243853783 111543122870819547365780675)
            ·
              refine ⟨167314684306229321048671013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111543122870819547365780675 167314684306229321048671013)
              ·
                refine ⟨31371503307417997696625815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167314684306229321048671013 31371503307417997696625815)
                ·
                  refine ⟨47057254961126996544938723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31371503307417997696625815 47057254961126996544938723)
                  ·
                    refine ⟨70585882441690494817408085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47057254961126996544938723 70585882441690494817408085)
                    ·
                      refine ⟨827178309863560486141501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 70585882441690494817408085 827178309863560486141501)
                      ·
                        rfl

theorem cell23_1610924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_1610924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610924 prefixEnd_1610924 := by exact prefixLift 1610924
  have htrace : WordTrace (prefixWord ++ tailWord_1610924) baseStart_1610924 baseEnd_1610924 := by
    simpa [prefixWord, tailWord_1610924, baseEnd_1610924] using wordTrace_append hprefix tailTrace_1610924
  have hstable : (prefixWord ++ tailWord_1610924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610924).length < 2 ^ (prefixWord ++ tailWord_1610924).sum := by decide
  have hdescent : baseEnd_1610924 < baseStart_1610924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1610968 : List Nat := [2, 1, 2, 2, 5, 1, 1, 1, 3, 5]
def baseStart_1610968 : Nat := 118140960795 + 1610968 * 2 ^ 59
def prefixEnd_1610968 : Nat := 4983230072969 + 3 ^ 40 * 1610968 * 2
def baseEnd_1610968 : Nat := 275733634337452771330433

theorem tailTrace_1610968 : CollatzResearch.WordTrace tailWord_1610968 prefixEnd_1610968 275733634337452771330433 := by
  unfold tailWord_1610968
  simp only [CollatzResearch.WordTrace]
  refine ⟨29378415013872771137588779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39171220018497028183451705 29378415013872771137588779)
  ·
    refine ⟨44067622520809156706383169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29378415013872771137588779 44067622520809156706383169)
    ·
      refine ⟨33050716890606867529787377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44067622520809156706383169 33050716890606867529787377)
      ·
        refine ⟨24788037667955150647340533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33050716890606867529787377 24788037667955150647340533)
        ·
          refine ⟨2323878531370795373188175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24788037667955150647340533 2323878531370795373188175)
          ·
            refine ⟨3485817797056193059782263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2323878531370795373188175 3485817797056193059782263)
            ·
              refine ⟨5228726695584289589673395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3485817797056193059782263 5228726695584289589673395)
              ·
                refine ⟨7843090043376434384510093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5228726695584289589673395 7843090043376434384510093)
                ·
                  refine ⟨2941158766266162894191285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7843090043376434384510093 2941158766266162894191285)
                  ·
                    refine ⟨275733634337452771330433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2941158766266162894191285 275733634337452771330433)
                    ·
                      rfl

theorem cell23_1610968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 3, 5].length) (baseStart_1610968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1610968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1610968 prefixEnd_1610968 := by exact prefixLift 1610968
  have htrace : WordTrace (prefixWord ++ tailWord_1610968) baseStart_1610968 baseEnd_1610968 := by
    simpa [prefixWord, tailWord_1610968, baseEnd_1610968] using wordTrace_append hprefix tailTrace_1610968
  have hstable : (prefixWord ++ tailWord_1610968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1610968).length < 2 ^ (prefixWord ++ tailWord_1610968).sum := by decide
  have hdescent : baseEnd_1610968 < baseStart_1610968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1610968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611001 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 3, 2, 4]
def baseStart_1611001 : Nat := 118140960795 + 1611001 * 2 ^ 59
def prefixEnd_1611001 : Nat := 4983230072969 + 3 ^ 40 * 1611001 * 2
def baseEnd_1611001 : Nat := 827217847873956684878647

theorem tailTrace_1611001 : CollatzResearch.WordTrace tailWord_1611001 prefixEnd_1611001 827217847873956684878647 := by
  unfold tailWord_1611001
  simp only [CollatzResearch.WordTrace]
  refine ⟨58758033636625988911128857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39172022424417325940752571 58758033636625988911128857)
  ·
    refine ⟨44068525227469491683346643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58758033636625988911128857 44068525227469491683346643)
    ·
      refine ⟨66102787841204237525019965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44068525227469491683346643 66102787841204237525019965)
      ·
        refine ⟨24788545440451589071882487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66102787841204237525019965 24788545440451589071882487)
        ·
          refine ⟨37182818160677383607823731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24788545440451589071882487 37182818160677383607823731)
          ·
            refine ⟨55774227241016075411735597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37182818160677383607823731 55774227241016075411735597)
            ·
              refine ⟨20915335215381028279400849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55774227241016075411735597 20915335215381028279400849)
              ·
                refine ⟨15686501411535771209550637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20915335215381028279400849 15686501411535771209550637)
                ·
                  refine ⟨5882438029325914203581489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15686501411535771209550637 5882438029325914203581489)
                  ·
                    refine ⟨4411828521994435652686117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5882438029325914203581489 4411828521994435652686117)
                    ·
                      refine ⟨827217847873956684878647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4411828521994435652686117 827217847873956684878647)
                      ·
                        rfl

theorem cell23_1611001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_1611001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611001 prefixEnd_1611001 := by exact prefixLift 1611001
  have htrace : WordTrace (prefixWord ++ tailWord_1611001) baseStart_1611001 baseEnd_1611001 := by
    simpa [prefixWord, tailWord_1611001, baseEnd_1611001] using wordTrace_append hprefix tailTrace_1611001
  have hstable : (prefixWord ++ tailWord_1611001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611001).length < 2 ^ (prefixWord ++ tailWord_1611001).sum := by decide
  have hdescent : baseEnd_1611001 < baseStart_1611001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611011 : List Nat := [1, 1, 1, 3, 2, 4, 3, 8]
def baseStart_1611011 : Nat := 118140960795 + 1611011 * 2 ^ 59
def prefixEnd_1611011 : Nat := 4983230072969 + 3 ^ 40 * 1611011 * 2
def baseEnd_1611011 : Nat := 30637888247425986879763

theorem tailTrace_1611011 : CollatzResearch.WordTrace tailWord_1611011 prefixEnd_1611011 30637888247425986879763 := by
  unfold tailWord_1611011
  simp only [CollatzResearch.WordTrace]
  refine ⟨58758398366589760618992887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39172265577726507079328591 58758398366589760618992887)
  ·
    refine ⟨88137597549884640928489331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58758398366589760618992887 88137597549884640928489331)
    ·
      refine ⟨132206396324826961392733997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88137597549884640928489331 132206396324826961392733997)
      ·
        refine ⟨49577398621810110522275249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132206396324826961392733997 49577398621810110522275249)
        ·
          refine ⟨37183048966357582891706437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49577398621810110522275249 37183048966357582891706437)
          ·
            refine ⟨6971821681192046792194957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37183048966357582891706437 6971821681192046792194957)
            ·
              refine ⟨2614433130447017547073109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6971821681192046792194957 2614433130447017547073109)
              ·
                refine ⟨30637888247425986879763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2614433130447017547073109 30637888247425986879763)
                ·
                  rfl

theorem cell23_1611011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 8].length) (baseStart_1611011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611011 prefixEnd_1611011 := by exact prefixLift 1611011
  have htrace : WordTrace (prefixWord ++ tailWord_1611011) baseStart_1611011 baseEnd_1611011 := by
    simpa [prefixWord, tailWord_1611011, baseEnd_1611011] using wordTrace_append hprefix tailTrace_1611011
  have hstable : (prefixWord ++ tailWord_1611011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611011).length < 2 ^ (prefixWord ++ tailWord_1611011).sum := by decide
  have hdescent : baseEnd_1611011 < baseStart_1611011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611022 : List Nat := [4, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2]
def baseStart_1611022 : Nat := 118140960795 + 1611022 * 2 ^ 59
def prefixEnd_1611022 : Nat := 4983230072969 + 3 ^ 40 * 1611022 * 2
def baseEnd_1611022 : Nat := 827228630967701102716051

theorem tailTrace_1611022 : CollatzResearch.WordTrace tailWord_1611022 prefixEnd_1611022 827228630967701102716051 := by
  unfold tailWord_1611022
  simp only [CollatzResearch.WordTrace]
  refine ⟨7344849946193738687205415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39172533046366606331762213 7344849946193738687205415)
  ·
    refine ⟨11017274919290608030808123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7344849946193738687205415 11017274919290608030808123)
    ·
      refine ⟨16525912378935912046212185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11017274919290608030808123 16525912378935912046212185)
      ·
        refine ⟨12394434284201934034659139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16525912378935912046212185 12394434284201934034659139)
        ·
          refine ⟨18591651426302901051988709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12394434284201934034659139 18591651426302901051988709)
          ·
            refine ⟨3485934642431793947247883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18591651426302901051988709 3485934642431793947247883)
            ·
              refine ⟨5228901963647690920871825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3485934642431793947247883 5228901963647690920871825)
              ·
                refine ⟨3921676472735768190653869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5228901963647690920871825 3921676472735768190653869)
                ·
                  refine ⟨1470628677275913071495201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3921676472735768190653869 1470628677275913071495201)
                  ·
                    refine ⟨1102971507956934803621401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1470628677275913071495201 1102971507956934803621401)
                    ·
                      refine ⟨827228630967701102716051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1102971507956934803621401 827228630967701102716051)
                      ·
                        rfl

theorem cell23_1611022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_1611022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611022 prefixEnd_1611022 := by exact prefixLift 1611022
  have htrace : WordTrace (prefixWord ++ tailWord_1611022) baseStart_1611022 baseEnd_1611022 := by
    simpa [prefixWord, tailWord_1611022, baseEnd_1611022] using wordTrace_append hprefix tailTrace_1611022
  have hstable : (prefixWord ++ tailWord_1611022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611022).length < 2 ^ (prefixWord ++ tailWord_1611022).sum := by decide
  have hdescent : baseEnd_1611022 < baseStart_1611022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611026 : List Nat := [3, 2, 4, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_1611026 : Nat := 118140960795 + 1611026 * 2 ^ 59
def prefixEnd_1611026 : Nat := 4983230072969 + 3 ^ 40 * 1611026 * 2
def baseEnd_1611026 : Nat := 827230684890319087066033

theorem tailTrace_1611026 : CollatzResearch.WordTrace tailWord_1611026 prefixEnd_1611026 827230684890319087066033 := by
  unfold tailWord_1611026
  simp only [CollatzResearch.WordTrace]
  refine ⟨14689736365383854545197233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39172630307690278787192621 14689736365383854545197233)
  ·
    refine ⟨11017302274037890908897925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14689736365383854545197233 11017302274037890908897925)
    ·
      refine ⟨2065744176382104545418361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11017302274037890908897925 2065744176382104545418361)
      ·
        refine ⟨1549308132286578409063771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2065744176382104545418361 1549308132286578409063771)
        ·
          refine ⟨2323962198429867613595657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1549308132286578409063771 2323962198429867613595657)
          ·
            refine ⟨1742971648822400710196743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2323962198429867613595657 1742971648822400710196743)
            ·
              refine ⟨2614457473233601065295115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1742971648822400710196743 2614457473233601065295115)
              ·
                refine ⟨3921686209850401597942673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2614457473233601065295115 3921686209850401597942673)
                ·
                  refine ⟨2941264657387801198457005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3921686209850401597942673 2941264657387801198457005)
                  ·
                    refine ⟨1102974246520425449421377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2941264657387801198457005 1102974246520425449421377)
                    ·
                      refine ⟨827230684890319087066033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1102974246520425449421377 827230684890319087066033)
                      ·
                        rfl

theorem cell23_1611026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_1611026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611026 prefixEnd_1611026 := by exact prefixLift 1611026
  have htrace : WordTrace (prefixWord ++ tailWord_1611026) baseStart_1611026 baseEnd_1611026 := by
    simpa [prefixWord, tailWord_1611026, baseEnd_1611026] using wordTrace_append hprefix tailTrace_1611026
  have hstable : (prefixWord ++ tailWord_1611026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611026).length < 2 ^ (prefixWord ++ tailWord_1611026).sum := by decide
  have hdescent : baseEnd_1611026 < baseStart_1611026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611039 : List Nat := [1, 1, 2, 4, 5, 1, 2, 1, 1, 1, 4]
def baseStart_1611039 : Nat := 118140960795 + 1611039 * 2 ^ 59
def prefixEnd_1611039 : Nat := 4983230072969 + 3 ^ 40 * 1611039 * 2
def baseEnd_1611039 : Nat := 827237360138827536203473

theorem tailTrace_1611039 : CollatzResearch.WordTrace tailWord_1611039 prefixEnd_1611039 827237360138827536203473 := by
  unfold tailWord_1611039
  simp only [CollatzResearch.WordTrace]
  refine ⟨58759419610488321401012171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39172946406992214267341447 58759419610488321401012171)
  ·
    refine ⟨88139129415732482101518257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58759419610488321401012171 88139129415732482101518257)
    ·
      refine ⟨66104347061799361576138693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88139129415732482101518257 66104347061799361576138693)
      ·
        refine ⟨12394565074087380295526005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66104347061799361576138693 12394565074087380295526005)
        ·
          refine ⟨1161990475695691902705563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12394565074087380295526005 1161990475695691902705563)
          ·
            refine ⟨1742985713543537854058345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1161990475695691902705563 1742985713543537854058345)
            ·
              refine ⟨1307239285157653390543759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1742985713543537854058345 1307239285157653390543759)
              ·
                refine ⟨1960858927736480085815639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1307239285157653390543759 1960858927736480085815639)
                ·
                  refine ⟨2941288391604720128723459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1960858927736480085815639 2941288391604720128723459)
                  ·
                    refine ⟨4411932587407080193085189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2941288391604720128723459 4411932587407080193085189)
                    ·
                      refine ⟨827237360138827536203473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4411932587407080193085189 827237360138827536203473)
                      ·
                        rfl

theorem cell23_1611039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_1611039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611039 prefixEnd_1611039 := by exact prefixLift 1611039
  have htrace : WordTrace (prefixWord ++ tailWord_1611039) baseStart_1611039 baseEnd_1611039 := by
    simpa [prefixWord, tailWord_1611039, baseEnd_1611039] using wordTrace_append hprefix tailTrace_1611039
  have hstable : (prefixWord ++ tailWord_1611039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611039).length < 2 ^ (prefixWord ++ tailWord_1611039).sum := by decide
  have hdescent : baseEnd_1611039 < baseStart_1611039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611042 : List Nat := [3, 3, 1, 1, 4, 1, 1, 3, 1, 2, 3]
def baseStart_1611042 : Nat := 118140960795 + 1611042 * 2 ^ 59
def prefixEnd_1611042 : Nat := 4983230072969 + 3 ^ 40 * 1611042 * 2
def baseEnd_1611042 : Nat := 827238900580791024465959

theorem tailTrace_1611042 : CollatzResearch.WordTrace tailWord_1611042 prefixEnd_1611042 827238900580791024465959 := by
  unfold tailWord_1611042
  simp only [CollatzResearch.WordTrace]
  refine ⟨14689882257369363228342845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39173019352984968608914253 14689882257369363228342845)
  ·
    refine ⟨5508705846513511210628567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14689882257369363228342845 5508705846513511210628567)
    ·
      refine ⟨8263058769770266815942851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5508705846513511210628567 8263058769770266815942851)
      ·
        refine ⟨12394588154655400223914277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8263058769770266815942851 12394588154655400223914277)
        ·
          refine ⟨2323985278997887541983927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12394588154655400223914277 2323985278997887541983927)
          ·
            refine ⟨3485977918496831312975891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2323985278997887541983927 3485977918496831312975891)
            ·
              refine ⟨5228966877745246969463837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3485977918496831312975891 5228966877745246969463837)
              ·
                refine ⟨1960862579154467613548939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5228966877745246969463837 1960862579154467613548939)
                ·
                  refine ⟨2941293868731701420323409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1960862579154467613548939 2941293868731701420323409)
                  ·
                    refine ⟨2205970401548776065242557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2941293868731701420323409 2205970401548776065242557)
                    ·
                      refine ⟨827238900580791024465959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2205970401548776065242557 827238900580791024465959)
                      ·
                        rfl

theorem cell23_1611042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_1611042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611042 prefixEnd_1611042 := by exact prefixLift 1611042
  have htrace : WordTrace (prefixWord ++ tailWord_1611042) baseStart_1611042 baseEnd_1611042 := by
    simpa [prefixWord, tailWord_1611042, baseEnd_1611042] using wordTrace_append hprefix tailTrace_1611042
  have hstable : (prefixWord ++ tailWord_1611042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611042).length < 2 ^ (prefixWord ++ tailWord_1611042).sum := by decide
  have hdescent : baseEnd_1611042 < baseStart_1611042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611069 : List Nat := [1, 4, 1, 5, 2, 1, 1, 1, 1, 2, 4]
def baseStart_1611069 : Nat := 118140960795 + 1611069 * 2 ^ 59
def prefixEnd_1611069 : Nat := 4983230072969 + 3 ^ 40 * 1611069 * 2
def baseEnd_1611069 : Nat := 827252764558462418828335

theorem tailTrace_1611069 : CollatzResearch.WordTrace tailWord_1611069 prefixEnd_1611069 827252764558462418828335 := by
  unfold tailWord_1611069
  simp only [CollatzResearch.WordTrace]
  refine ⟨58760513800379636524604261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39173675866919757683069507 58760513800379636524604261)
  ·
    refine ⟨11017596337571181848363299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58760513800379636524604261 11017596337571181848363299)
    ·
      refine ⟨16526394506356772772544949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11017596337571181848363299 16526394506356772772544949)
      ·
        refine ⟨1549349484970947447426089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16526394506356772772544949 1549349484970947447426089)
        ·
          refine ⟨1162012113728210585569567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1549349484970947447426089 1162012113728210585569567)
          ·
            refine ⟨1743018170592315878354351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162012113728210585569567 1743018170592315878354351)
            ·
              refine ⟨2614527255888473817531527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1743018170592315878354351 2614527255888473817531527)
              ·
                refine ⟨3921790883832710726297291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2614527255888473817531527 3921790883832710726297291)
                ·
                  refine ⟨5882686325749066089445937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3921790883832710726297291 5882686325749066089445937)
                  ·
                    refine ⟨4412014744311799567084453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5882686325749066089445937 4412014744311799567084453)
                    ·
                      refine ⟨827252764558462418828335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4412014744311799567084453 827252764558462418828335)
                      ·
                        rfl

theorem cell23_1611069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_1611069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611069 prefixEnd_1611069 := by exact prefixLift 1611069
  have htrace : WordTrace (prefixWord ++ tailWord_1611069) baseStart_1611069 baseEnd_1611069 := by
    simpa [prefixWord, tailWord_1611069, baseEnd_1611069] using wordTrace_append hprefix tailTrace_1611069
  have hstable : (prefixWord ++ tailWord_1611069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611069).length < 2 ^ (prefixWord ++ tailWord_1611069).sum := by decide
  have hdescent : baseEnd_1611069 < baseStart_1611069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611072 : List Nat := [2, 1, 1, 2, 2, 1, 7, 1, 2, 1, 3]
def baseStart_1611072 : Nat := 118140960795 + 1611072 * 2 ^ 59
def prefixEnd_1611072 : Nat := 4983230072969 + 3 ^ 40 * 1611072 * 2
def baseEnd_1611072 : Nat := 827254305000425907090821

theorem tailTrace_1611072 : CollatzResearch.WordTrace tailWord_1611072 prefixEnd_1611072 827254305000425907090821 := by
  unfold tailWord_1611072
  simp only [CollatzResearch.WordTrace]
  refine ⟨29380311609684384018481735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39173748812912512024642313 29380311609684384018481735)
  ·
    refine ⟨44070467414526576027722603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29380311609684384018481735 44070467414526576027722603)
    ·
      refine ⟨66105701121789864041583905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44070467414526576027722603 66105701121789864041583905)
      ·
        refine ⟨49579275841342398031187929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66105701121789864041583905 49579275841342398031187929)
        ·
          refine ⟨37184456881006798523390947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49579275841342398031187929 37184456881006798523390947)
          ·
            refine ⟨55776685321510197785086421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37184456881006798523390947 55776685321510197785086421)
            ·
              refine ⟨1307266062222895260587963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 55776685321510197785086421 1307266062222895260587963)
              ·
                refine ⟨1960899093334342890881945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1307266062222895260587963 1960899093334342890881945)
                ·
                  refine ⟨1470674320000757168161459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1960899093334342890881945 1470674320000757168161459)
                  ·
                    refine ⟨2206011480001135752242189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1470674320000757168161459 2206011480001135752242189)
                    ·
                      refine ⟨827254305000425907090821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2206011480001135752242189 827254305000425907090821)
                      ·
                        rfl

theorem cell23_1611072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 2, 1, 3].length) (baseStart_1611072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611072 prefixEnd_1611072 := by exact prefixLift 1611072
  have htrace : WordTrace (prefixWord ++ tailWord_1611072) baseStart_1611072 baseEnd_1611072 := by
    simpa [prefixWord, tailWord_1611072, baseEnd_1611072] using wordTrace_append hprefix tailTrace_1611072
  have hstable : (prefixWord ++ tailWord_1611072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611072).length < 2 ^ (prefixWord ++ tailWord_1611072).sum := by decide
  have hdescent : baseEnd_1611072 < baseStart_1611072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611129 : List Nat := [1, 2, 1, 3, 2, 1, 6, 1, 2, 2, 2]
def baseStart_1611129 : Nat := 118140960795 + 1611129 * 2 ^ 59
def prefixEnd_1611129 : Nat := 4983230072969 + 3 ^ 40 * 1611129 * 2
def baseEnd_1611129 : Nat := 827283573397732184078059

theorem tailTrace_1611129 : CollatzResearch.WordTrace tailWord_1611129 prefixEnd_1611129 827283573397732184078059 := by
  unfold tailWord_1611129
  simp only [CollatzResearch.WordTrace]
  refine ⟨58762702180162266771788441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39175134786774844514525627 58762702180162266771788441)
  ·
    refine ⟨44072026635121700078841331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58762702180162266771788441 44072026635121700078841331)
    ·
      refine ⟨66108039952682550118261997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44072026635121700078841331 66108039952682550118261997)
      ·
        refine ⟨24790514982255956294348249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66108039952682550118261997 24790514982255956294348249)
        ·
          refine ⟨18592886236691967220761187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24790514982255956294348249 18592886236691967220761187)
          ·
            refine ⟨27889329355037950831141781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18592886236691967220761187 27889329355037950831141781)
            ·
              refine ⟨1307312313517403945209771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27889329355037950831141781 1307312313517403945209771)
              ·
                refine ⟨1960968470276105917814657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1307312313517403945209771 1960968470276105917814657)
                ·
                  refine ⟨1470726352707079438360993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1960968470276105917814657 1470726352707079438360993)
                  ·
                    refine ⟨1103044764530309578770745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1470726352707079438360993 1103044764530309578770745)
                    ·
                      refine ⟨827283573397732184078059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1103044764530309578770745 827283573397732184078059)
                      ·
                        rfl

theorem cell23_1611129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 2, 2, 2].length) (baseStart_1611129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611129 prefixEnd_1611129 := by exact prefixLift 1611129
  have htrace : WordTrace (prefixWord ++ tailWord_1611129) baseStart_1611129 baseEnd_1611129 := by
    simpa [prefixWord, tailWord_1611129, baseEnd_1611129] using wordTrace_append hprefix tailTrace_1611129
  have hstable : (prefixWord ++ tailWord_1611129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611129).length < 2 ^ (prefixWord ++ tailWord_1611129).sum := by decide
  have hdescent : baseEnd_1611129 < baseStart_1611129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611165 : List Nat := [1, 4, 2, 1, 3, 1, 2, 2, 2, 5]
def baseStart_1611165 : Nat := 118140960795 + 1611165 * 2 ^ 59
def prefixEnd_1611165 : Nat := 4983230072969 + 3 ^ 40 * 1611165 * 2
def baseEnd_1611165 : Nat := 275767352900431347742631

theorem tailTrace_1611165 : CollatzResearch.WordTrace tailWord_1611165 prefixEnd_1611165 275767352900431347742631 := by
  unfold tailWord_1611165
  simp only [CollatzResearch.WordTrace]
  refine ⟨58764015208031844920098949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39176010138687896613399299 58764015208031844920098949)
  ·
    refine ⟨11018252851505970922518553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58764015208031844920098949 11018252851505970922518553)
    ·
      refine ⟨8263689638629478191888915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11018252851505970922518553 8263689638629478191888915)
      ·
        refine ⟨12395534457944217287833373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8263689638629478191888915 12395534457944217287833373)
        ·
          refine ⟨4648325421729081482937515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12395534457944217287833373 4648325421729081482937515)
          ·
            refine ⟨6972488132593622224406273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4648325421729081482937515 6972488132593622224406273)
            ·
              refine ⟨5229366099445216668304705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6972488132593622224406273 5229366099445216668304705)
              ·
                refine ⟨3922024574583912501228529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5229366099445216668304705 3922024574583912501228529)
                ·
                  refine ⟨2941518430937934375921397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3922024574583912501228529 2941518430937934375921397)
                  ·
                    refine ⟨275767352900431347742631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2941518430937934375921397 275767352900431347742631)
                    ·
                      rfl

theorem cell23_1611165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_1611165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611165 prefixEnd_1611165 := by exact prefixLift 1611165
  have htrace : WordTrace (prefixWord ++ tailWord_1611165) baseStart_1611165 baseEnd_1611165 := by
    simpa [prefixWord, tailWord_1611165, baseEnd_1611165] using wordTrace_append hprefix tailTrace_1611165
  have hstable : (prefixWord ++ tailWord_1611165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611165).length < 2 ^ (prefixWord ++ tailWord_1611165).sum := by decide
  have hdescent : baseEnd_1611165 < baseStart_1611165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611208 : List Nat := [2, 1, 3, 1, 3, 1, 2, 2, 8]
def baseStart_1611208 : Nat := 118140960795 + 1611208 * 2 ^ 59
def prefixEnd_1611208 : Nat := 4983230072969 + 3 ^ 40 * 1611208 * 2
def baseEnd_1611208 : Nat := 91924904263270819443355

theorem tailTrace_1611208 : CollatzResearch.WordTrace tailWord_1611208 prefixEnd_1611208 91924904263270819443355 := by
  unfold tailWord_1611208
  simp only [CollatzResearch.WordTrace]
  refine ⟨29382791773438031631957139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39177055697917375509276185 29382791773438031631957139)
  ·
    refine ⟨44074187660157047447935709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29382791773438031631957139 44074187660157047447935709)
    ·
      refine ⟨16527820372558892792975891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44074187660157047447935709 16527820372558892792975891)
      ·
        refine ⟨24791730558838339189463837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16527820372558892792975891 24791730558838339189463837)
        ·
          refine ⟨9296898959564377196048939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24791730558838339189463837 9296898959564377196048939)
          ·
            refine ⟨13945348439346565794073409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9296898959564377196048939 13945348439346565794073409)
            ·
              refine ⟨10459011329509924345555057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13945348439346565794073409 10459011329509924345555057)
              ·
                refine ⟨7844258497132443259166293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10459011329509924345555057 7844258497132443259166293)
                ·
                  refine ⟨91924904263270819443355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7844258497132443259166293 91924904263270819443355)
                  ·
                    rfl

theorem cell23_1611208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 8].length) (baseStart_1611208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611208 prefixEnd_1611208 := by exact prefixLift 1611208
  have htrace : WordTrace (prefixWord ++ tailWord_1611208) baseStart_1611208 baseEnd_1611208 := by
    simpa [prefixWord, tailWord_1611208, baseEnd_1611208] using wordTrace_append hprefix tailTrace_1611208
  have hstable : (prefixWord ++ tailWord_1611208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611208).length < 2 ^ (prefixWord ++ tailWord_1611208).sum := by decide
  have hdescent : baseEnd_1611208 < baseStart_1611208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611225 : List Nat := [1, 2, 1, 2, 4, 2, 3, 2, 6]
def baseStart_1611225 : Nat := 118140960795 + 1611225 * 2 ^ 59
def prefixEnd_1611225 : Nat := 4983230072969 + 3 ^ 40 * 1611225 * 2
def baseEnd_1611225 : Nat := 91925874171173756497513

theorem tailTrace_1611225 : CollatzResearch.WordTrace tailWord_1611225 prefixEnd_1611225 91925874171173756497513 := by
  unfold tailWord_1611225
  simp only [CollatzResearch.WordTrace]
  refine ⟨58766203587814475167283129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39177469058542983444855419 58766203587814475167283129)
  ·
    refine ⟨44074652690860856375462347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58766203587814475167283129 44074652690860856375462347)
    ·
      refine ⟨66111979036291284563193521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44074652690860856375462347 66111979036291284563193521)
      ·
        refine ⟨49583984277218463422395141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66111979036291284563193521 49583984277218463422395141)
        ·
          refine ⟨9296997051978461891699089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49583984277218463422395141 9296997051978461891699089)
          ·
            refine ⟨6972747788983846418774317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9296997051978461891699089 6972747788983846418774317)
            ·
              refine ⟨2614780420868942407040369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6972747788983846418774317 2614780420868942407040369)
              ·
                refine ⟨1961085315651706805280277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2614780420868942407040369 1961085315651706805280277)
                ·
                  refine ⟨91925874171173756497513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1961085315651706805280277 91925874171173756497513)
                  ·
                    rfl

theorem cell23_1611225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 6].length) (baseStart_1611225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611225 prefixEnd_1611225 := by exact prefixLift 1611225
  have htrace : WordTrace (prefixWord ++ tailWord_1611225) baseStart_1611225 baseEnd_1611225 := by
    simpa [prefixWord, tailWord_1611225, baseEnd_1611225] using wordTrace_append hprefix tailTrace_1611225
  have hstable : (prefixWord ++ tailWord_1611225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611225).length < 2 ^ (prefixWord ++ tailWord_1611225).sum := by decide
  have hdescent : baseEnd_1611225 < baseStart_1611225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611229 : List Nat := [1, 4, 3, 1, 1, 2, 2, 4, 1, 4]
def baseStart_1611229 : Nat := 118140960795 + 1611229 * 2 ^ 59
def prefixEnd_1611229 : Nat := 4983230072969 + 3 ^ 40 * 1611229 * 2
def baseEnd_1611229 : Nat := 275778307154393930942533

theorem tailTrace_1611229 : CollatzResearch.WordTrace tailWord_1611229 prefixEnd_1611229 275778307154393930942533 := by
  unfold tailWord_1611229
  simp only [CollatzResearch.WordTrace]
  refine ⟨58766349479799983850428741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39177566319866655900285827 58766349479799983850428741)
  ·
    refine ⟨11018690527462496971955389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58766349479799983850428741 11018690527462496971955389)
    ·
      refine ⟨4132008947798436364483271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11018690527462496971955389 4132008947798436364483271)
      ·
        refine ⟨6198013421697654546724907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4132008947798436364483271 6198013421697654546724907)
        ·
          refine ⟨9297020132546481820087361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6198013421697654546724907 9297020132546481820087361)
          ·
            refine ⟨6972765099409861365065521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9297020132546481820087361 6972765099409861365065521)
            ·
              refine ⟨5229573824557396023799141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6972765099409861365065521 5229573824557396023799141)
              ·
                refine ⟨980545092104511754462339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5229573824557396023799141 980545092104511754462339)
                ·
                  refine ⟨1470817638156767631693509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 980545092104511754462339 1470817638156767631693509)
                  ·
                    refine ⟨275778307154393930942533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1470817638156767631693509 275778307154393930942533)
                    ·
                      rfl

theorem cell23_1611229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_1611229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611229 prefixEnd_1611229 := by exact prefixLift 1611229
  have htrace : WordTrace (prefixWord ++ tailWord_1611229) baseStart_1611229 baseEnd_1611229 := by
    simpa [prefixWord, tailWord_1611229, baseEnd_1611229] using wordTrace_append hprefix tailTrace_1611229
  have hstable : (prefixWord ++ tailWord_1611229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611229).length < 2 ^ (prefixWord ++ tailWord_1611229).sum := by decide
  have hdescent : baseEnd_1611229 < baseStart_1611229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611295 : List Nat := [1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 5]
def baseStart_1611295 : Nat := 118140960795 + 1611295 * 2 ^ 59
def prefixEnd_1611295 : Nat := 4983230072969 + 3 ^ 40 * 1611295 * 2
def baseEnd_1611295 : Nat := 827368811186378534602295

theorem tailTrace_1611295 : CollatzResearch.WordTrace tailWord_1611295 prefixEnd_1611295 827368811186378534602295 := by
  unfold tailWord_1611295
  simp only [CollatzResearch.WordTrace]
  refine ⟨58768756697560877122331339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39179171131707251414887559 58768756697560877122331339)
  ·
    refine ⟨88153135046341315683497009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58768756697560877122331339 88153135046341315683497009)
    ·
      refine ⟨66114851284755986762622757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88153135046341315683497009 66114851284755986762622757)
      ·
        refine ⟨12396534615891747517991767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66114851284755986762622757 12396534615891747517991767)
        ·
          refine ⟨18594801923837621276987651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12396534615891747517991767 18594801923837621276987651)
          ·
            refine ⟨27892202885756431915481477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18594801923837621276987651 27892202885756431915481477)
            ·
              refine ⟨5229788041079330984152777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27892202885756431915481477 5229788041079330984152777)
              ·
                refine ⟨3922341030809498238114583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5229788041079330984152777 3922341030809498238114583)
                ·
                  refine ⟨5883511546214247357171875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3922341030809498238114583 5883511546214247357171875)
                  ·
                    refine ⟨8825267319321371035757813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5883511546214247357171875 8825267319321371035757813)
                    ·
                      refine ⟨827368811186378534602295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8825267319321371035757813 827368811186378534602295)
                      ·
                        rfl

theorem cell23_1611295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_1611295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611295 prefixEnd_1611295 := by exact prefixLift 1611295
  have htrace : WordTrace (prefixWord ++ tailWord_1611295) baseStart_1611295 baseEnd_1611295 := by
    simpa [prefixWord, tailWord_1611295, baseEnd_1611295] using wordTrace_append hprefix tailTrace_1611295
  have hstable : (prefixWord ++ tailWord_1611295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611295).length < 2 ^ (prefixWord ++ tailWord_1611295).sum := by decide
  have hdescent : baseEnd_1611295 < baseStart_1611295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611385 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 1, 3, 5]
def baseStart_1611385 : Nat := 118140960795 + 1611385 * 2 ^ 59
def prefixEnd_1611385 : Nat := 4983230072969 + 3 ^ 40 * 1611385 * 2
def baseEnd_1611385 : Nat := 827415024445283182476881

theorem tailTrace_1611385 : CollatzResearch.WordTrace tailWord_1611385 prefixEnd_1611385 827415024445283182476881 := by
  unfold tailWord_1611385
  simp only [CollatzResearch.WordTrace]
  refine ⟨58772039267234822493107609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39181359511489881662071739 58772039267234822493107609)
  ·
    refine ⟨44079029450426116869830707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58772039267234822493107609 44079029450426116869830707)
    ·
      refine ⟨66118544175639175304746061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44079029450426116869830707 66118544175639175304746061)
      ·
        refine ⟨24794454065864690739279773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66118544175639175304746061 24794454065864690739279773)
        ·
          refine ⟨9297920274699259027229915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24794454065864690739279773 9297920274699259027229915)
          ·
            refine ⟨13946880412048888540844873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9297920274699259027229915 13946880412048888540844873)
            ·
              refine ⟨10460160309036666405633655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13946880412048888540844873 10460160309036666405633655)
              ·
                refine ⟨15690240463554999608450483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10460160309036666405633655 15690240463554999608450483)
                ·
                  refine ⟨23535360695332499412675725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15690240463554999608450483 23535360695332499412675725)
                  ·
                    refine ⟨8825760260749687279753397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23535360695332499412675725 8825760260749687279753397)
                    ·
                      refine ⟨827415024445283182476881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8825760260749687279753397 827415024445283182476881)
                      ·
                        rfl

theorem cell23_1611385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_1611385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611385 prefixEnd_1611385 := by exact prefixLift 1611385
  have htrace : WordTrace (prefixWord ++ tailWord_1611385) baseStart_1611385 baseEnd_1611385 := by
    simpa [prefixWord, tailWord_1611385, baseEnd_1611385] using wordTrace_append hprefix tailTrace_1611385
  have hstable : (prefixWord ++ tailWord_1611385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611385).length < 2 ^ (prefixWord ++ tailWord_1611385).sum := by decide
  have hdescent : baseEnd_1611385 < baseStart_1611385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611416 : List Nat := [2, 1, 2, 4, 1, 4, 1, 1, 1, 4, 2]
def baseStart_1611416 : Nat := 118140960795 + 1611416 * 2 ^ 59
def prefixEnd_1611416 : Nat := 4983230072969 + 3 ^ 40 * 1611416 * 2
def baseEnd_1611416 : Nat := 827430942345572561189239

theorem tailTrace_1611416 : CollatzResearch.WordTrace tailWord_1611416 prefixEnd_1611416 827430942345572561189239 := by
  unfold tailWord_1611416
  simp only [CollatzResearch.WordTrace]
  refine ⟨29386584965061257393743051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39182113286748343191657401 29386584965061257393743051)
  ·
    refine ⟨44079877447591886090614577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29386584965061257393743051 44079877447591886090614577)
    ·
      refine ⟨33059908085693914567960933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44079877447591886090614577 33059908085693914567960933)
      ·
        refine ⟨6198732766067608981492675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33059908085693914567960933 6198732766067608981492675)
        ·
          refine ⟨9298099149101413472239013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6198732766067608981492675 9298099149101413472239013)
          ·
            refine ⟨1743393590456515026044815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9298099149101413472239013 1743393590456515026044815)
            ·
              refine ⟨2615090385684772539067223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1743393590456515026044815 2615090385684772539067223)
              ·
                refine ⟨3922635578527158808600835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2615090385684772539067223 3922635578527158808600835)
                ·
                  refine ⟨5883953367790738212901253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3922635578527158808600835 5883953367790738212901253)
                  ·
                    refine ⟨1103241256460763414918985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5883953367790738212901253 1103241256460763414918985)
                    ·
                      refine ⟨827430942345572561189239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1103241256460763414918985 827430942345572561189239)
                      ·
                        rfl

theorem cell23_1611416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_1611416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611416 prefixEnd_1611416 := by exact prefixLift 1611416
  have htrace : WordTrace (prefixWord ++ tailWord_1611416) baseStart_1611416 baseEnd_1611416 := by
    simpa [prefixWord, tailWord_1611416, baseEnd_1611416] using wordTrace_append hprefix tailTrace_1611416
  have hstable : (prefixWord ++ tailWord_1611416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611416).length < 2 ^ (prefixWord ++ tailWord_1611416).sum := by decide
  have hdescent : baseEnd_1611416 < baseStart_1611416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611452 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 4, 5]
def baseStart_1611452 : Nat := 118140960795 + 1611452 * 2 ^ 59
def prefixEnd_1611452 : Nat := 4983230072969 + 3 ^ 40 * 1611452 * 2
def baseEnd_1611452 : Nat := 275816475883044806779691

theorem tailTrace_1611452 : CollatzResearch.WordTrace tailWord_1611452 prefixEnd_1611452 275816475883044806779691 := by
  unfold tailWord_1611452
  simp only [CollatzResearch.WordTrace]
  refine ⟨29387241478996046467898305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39182988638661395290531073 29387241478996046467898305)
  ·
    refine ⟨22040431109247034850923729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29387241478996046467898305 22040431109247034850923729)
    ·
      refine ⟨16530323331935276138192797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22040431109247034850923729 16530323331935276138192797)
      ·
        refine ⟨6198871249475728551822299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16530323331935276138192797 6198871249475728551822299)
        ·
          refine ⟨9298306874213592827733449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6198871249475728551822299 9298306874213592827733449)
          ·
            refine ⟨6973730155660194620800087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9298306874213592827733449 6973730155660194620800087)
            ·
              refine ⟨10460595233490291931200131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6973730155660194620800087 10460595233490291931200131)
              ·
                refine ⟨15690892850235437896800197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10460595233490291931200131 15690892850235437896800197)
                ·
                  refine ⟨2942042409419144605650037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15690892850235437896800197 2942042409419144605650037)
                  ·
                    refine ⟨275816475883044806779691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2942042409419144605650037 275816475883044806779691)
                    ·
                      rfl

theorem cell23_1611452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_1611452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611452 prefixEnd_1611452 := by exact prefixLift 1611452
  have htrace : WordTrace (prefixWord ++ tailWord_1611452) baseStart_1611452 baseEnd_1611452 := by
    simpa [prefixWord, tailWord_1611452, baseEnd_1611452] using wordTrace_append hprefix tailTrace_1611452
  have hstable : (prefixWord ++ tailWord_1611452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611452).length < 2 ^ (prefixWord ++ tailWord_1611452).sum := by decide
  have hdescent : baseEnd_1611452 < baseStart_1611452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611502 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_1611502 : Nat := 118140960795 + 1611502 * 2 ^ 59
def prefixEnd_1611502 : Nat := 4983230072969 + 3 ^ 40 * 1611502 * 2
def baseEnd_1611502 : Nat := 827475101681859224713843

theorem tailTrace_1611502 : CollatzResearch.WordTrace tailWord_1611502 prefixEnd_1611502 827475101681859224713843 := by
  unfold tailWord_1611502
  simp only [CollatzResearch.WordTrace]
  refine ⟨7347038325976368934389595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39184204405207300983411173 7347038325976368934389595)
  ·
    refine ⟨11020557488964553401584393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7347038325976368934389595 11020557488964553401584393)
    ·
      refine ⟨8265418116723415051188295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11020557488964553401584393 8265418116723415051188295)
      ·
        refine ⟨12398127175085122576782443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8265418116723415051188295 12398127175085122576782443)
        ·
          refine ⟨18597190762627683865173665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12398127175085122576782443 18597190762627683865173665)
          ·
            refine ⟨13947893071970762898880249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18597190762627683865173665 13947893071970762898880249)
            ·
              refine ⟨10460919803978072174160187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13947893071970762898880249 10460919803978072174160187)
              ·
                refine ⟨15691379705967108261240281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10460919803978072174160187 15691379705967108261240281)
                ·
                  refine ⟨11768534779475331195930211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15691379705967108261240281 11768534779475331195930211)
                  ·
                    refine ⟨17652802169212996793895317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11768534779475331195930211 17652802169212996793895317)
                    ·
                      refine ⟨827475101681859224713843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17652802169212996793895317 827475101681859224713843)
                      ·
                        rfl

theorem cell23_1611502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_1611502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611502 prefixEnd_1611502 := by exact prefixLift 1611502
  have htrace : WordTrace (prefixWord ++ tailWord_1611502) baseStart_1611502 baseEnd_1611502 := by
    simpa [prefixWord, tailWord_1611502, baseEnd_1611502] using wordTrace_append hprefix tailTrace_1611502
  have hstable : (prefixWord ++ tailWord_1611502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611502).length < 2 ^ (prefixWord ++ tailWord_1611502).sum := by decide
  have hdescent : baseEnd_1611502 < baseStart_1611502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611516 : List Nat := [2, 2, 2, 1, 3, 1, 3, 4, 1, 4]
def baseStart_1611516 : Nat := 118140960795 + 1611516 * 2 ^ 59
def prefixEnd_1611516 : Nat := 4983230072969 + 3 ^ 40 * 1611516 * 2
def baseEnd_1611516 : Nat := 275827430137007389979593

theorem tailTrace_1611516 : CollatzResearch.WordTrace tailWord_1611516 prefixEnd_1611516 275827430137007389979593 := by
  unfold tailWord_1611516
  simp only [CollatzResearch.WordTrace]
  refine ⟨29388408614880115933063201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39184544819840154577417601 29388408614880115933063201)
  ·
    refine ⟨22041306461160086949797401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29388408614880115933063201 22041306461160086949797401)
    ·
      refine ⟨16530979845870065212348051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22041306461160086949797401 16530979845870065212348051)
      ·
        refine ⟨24796469768805097818522077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16530979845870065212348051 24796469768805097818522077)
        ·
          refine ⟨9298676163301911681945779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24796469768805097818522077 9298676163301911681945779)
          ·
            refine ⟨13948014244952867522918669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9298676163301911681945779 13948014244952867522918669)
            ·
              refine ⟨5230505341857325321094501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13948014244952867522918669 5230505341857325321094501)
              ·
                refine ⟨980719751598248497705219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5230505341857325321094501 980719751598248497705219)
                ·
                  refine ⟨1471079627397372746557829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 980719751598248497705219 1471079627397372746557829)
                  ·
                    refine ⟨275827430137007389979593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1471079627397372746557829 275827430137007389979593)
                    ·
                      rfl

theorem cell23_1611516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_1611516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611516 prefixEnd_1611516 := by exact prefixLift 1611516
  have htrace : WordTrace (prefixWord ++ tailWord_1611516) baseStart_1611516 baseEnd_1611516 := by
    simpa [prefixWord, tailWord_1611516, baseEnd_1611516] using wordTrace_append hprefix tailTrace_1611516
  have hstable : (prefixWord ++ tailWord_1611516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611516).length < 2 ^ (prefixWord ++ tailWord_1611516).sum := by decide
  have hdescent : baseEnd_1611516 < baseStart_1611516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611573 : List Nat := [1, 3, 3, 1, 4, 1, 2, 1, 3, 1, 3]
def baseStart_1611573 : Nat := 118140960795 + 1611573 * 2 ^ 59
def prefixEnd_1611573 : Nat := 4983230072969 + 3 ^ 40 * 1611573 * 2
def baseEnd_1611573 : Nat := 827511558808328446926017

theorem tailTrace_1611573 : CollatzResearch.WordTrace tailWord_1611573 prefixEnd_1611573 827511558808328446926017 := by
  unfold tailWord_1611573
  simp only [CollatzResearch.WordTrace]
  refine ⟨58778896190553730600951373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39185930793702487067300915 58778896190553730600951373)
  ·
    refine ⟨22042086071457648975356765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58778896190553730600951373 22042086071457648975356765)
    ·
      refine ⟨8265782276796618365758787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22042086071457648975356765 8265782276796618365758787)
      ·
        refine ⟨12398673415194927548638181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8265782276796618365758787 12398673415194927548638181)
        ·
          refine ⟨2324751265349048915369659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12398673415194927548638181 2324751265349048915369659)
          ·
            refine ⟨3487126898023573373054489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2324751265349048915369659 3487126898023573373054489)
            ·
              refine ⟨2615345173517680029790867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3487126898023573373054489 2615345173517680029790867)
              ·
                refine ⟨3923017760276520044686301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2615345173517680029790867 3923017760276520044686301)
                ·
                  refine ⟨1471131660103695016757363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3923017760276520044686301 1471131660103695016757363)
                  ·
                    refine ⟨2206697490155542525136045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1471131660103695016757363 2206697490155542525136045)
                    ·
                      refine ⟨827511558808328446926017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2206697490155542525136045 827511558808328446926017)
                      ·
                        rfl

theorem cell23_1611573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_1611573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611573 prefixEnd_1611573 := by exact prefixLift 1611573
  have htrace : WordTrace (prefixWord ++ tailWord_1611573) baseStart_1611573 baseEnd_1611573 := by
    simpa [prefixWord, tailWord_1611573, baseEnd_1611573] using wordTrace_append hprefix tailTrace_1611573
  have hstable : (prefixWord ++ tailWord_1611573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611573).length < 2 ^ (prefixWord ++ tailWord_1611573).sum := by decide
  have hdescent : baseEnd_1611573 < baseStart_1611573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611590 : List Nat := [6, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_1611590 : Nat := 118140960795 + 1611590 * 2 ^ 59
def prefixEnd_1611590 : Nat := 4983230072969 + 3 ^ 40 * 1611590 * 2
def baseEnd_1611590 : Nat := 827520287979454880413439

theorem tailTrace_1611590 : CollatzResearch.WordTrace tailWord_1611590 prefixEnd_1611590 827520287979454880413439 := by
  unfold tailWord_1611590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1836859882234129453260007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39186344154328095002880149 1836859882234129453260007)
  ·
    refine ⟨2755289823351194179890011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1836859882234129453260007 2755289823351194179890011)
    ·
      refine ⟨4132934735026791269835017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2755289823351194179890011 4132934735026791269835017)
      ·
        refine ⟨3099701051270093452376263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4132934735026791269835017 3099701051270093452376263)
        ·
          refine ⟨4649551576905140178564395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3099701051270093452376263 4649551576905140178564395)
          ·
            refine ⟨6974327365357710267846593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4649551576905140178564395 6974327365357710267846593)
            ·
              refine ⟨5230745524018282700884945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6974327365357710267846593 5230745524018282700884945)
              ·
                refine ⟨3923059143013712025663709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5230745524018282700884945 3923059143013712025663709)
                ·
                  refine ⟨1471147178630142009623891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3923059143013712025663709 1471147178630142009623891)
                  ·
                    refine ⟨2206720767945213014435837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1471147178630142009623891 2206720767945213014435837)
                    ·
                      refine ⟨827520287979454880413439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2206720767945213014435837 827520287979454880413439)
                      ·
                        rfl

theorem cell23_1611590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_1611590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611590 prefixEnd_1611590 := by exact prefixLift 1611590
  have htrace : WordTrace (prefixWord ++ tailWord_1611590) baseStart_1611590 baseEnd_1611590 := by
    simpa [prefixWord, tailWord_1611590, baseEnd_1611590] using wordTrace_append hprefix tailTrace_1611590
  have hstable : (prefixWord ++ tailWord_1611590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611590).length < 2 ^ (prefixWord ++ tailWord_1611590).sum := by decide
  have hdescent : baseEnd_1611590 < baseStart_1611590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611607 : List Nat := [1, 1, 3, 2, 6, 1, 1, 3, 1, 1, 3]
def baseStart_1611607 : Nat := 118140960795 + 1611607 * 2 ^ 59
def prefixEnd_1611607 : Nat := 4983230072969 + 3 ^ 40 * 1611607 * 2
def baseEnd_1611607 : Nat := 827529017150581313900861

theorem tailTrace_1611607 : CollatzResearch.WordTrace tailWord_1611607 prefixEnd_1611607 827529017150581313900861 := by
  unfold tailWord_1611607
  simp only [CollatzResearch.WordTrace]
  refine ⟨58780136272430554407689075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39186757514953702938459383 58780136272430554407689075)
  ·
    refine ⟨88170204408645831611533613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58780136272430554407689075 88170204408645831611533613)
    ·
      refine ⟨33063826653242186854325105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88170204408645831611533613 33063826653242186854325105)
      ·
        refine ⟨24797869989931640140743829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33063826653242186854325105 24797869989931640140743829)
        ·
          refine ⟨1162400155778045631597367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24797869989931640140743829 1162400155778045631597367)
          ·
            refine ⟨1743600233667068447396051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162400155778045631597367 1743600233667068447396051)
            ·
              refine ⟨2615400350500602671094077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1743600233667068447396051 2615400350500602671094077)
              ·
                refine ⟨980775131437726001660279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2615400350500602671094077 980775131437726001660279)
                ·
                  refine ⟨1471162697156589002490419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 980775131437726001660279 1471162697156589002490419)
                  ·
                    refine ⟨2206744045734883503735629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1471162697156589002490419 2206744045734883503735629)
                    ·
                      refine ⟨827529017150581313900861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2206744045734883503735629 827529017150581313900861)
                      ·
                        rfl

theorem cell23_1611607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3, 1, 1, 3].length) (baseStart_1611607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611607 prefixEnd_1611607 := by exact prefixLift 1611607
  have htrace : WordTrace (prefixWord ++ tailWord_1611607) baseStart_1611607 baseEnd_1611607 := by
    simpa [prefixWord, tailWord_1611607, baseEnd_1611607] using wordTrace_append hprefix tailTrace_1611607
  have hstable : (prefixWord ++ tailWord_1611607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611607).length < 2 ^ (prefixWord ++ tailWord_1611607).sum := by decide
  have hdescent : baseEnd_1611607 < baseStart_1611607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611616 : List Nat := [2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 3]
def baseStart_1611616 : Nat := 118140960795 + 1611616 * 2 ^ 59
def prefixEnd_1611616 : Nat := 4983230072969 + 3 ^ 40 * 1611616 * 2
def baseEnd_1611616 : Nat := 827533638476471778688319

theorem tailTrace_1611616 : CollatzResearch.WordTrace tailWord_1611616 prefixEnd_1611616 827533638476471778688319 := by
  unfold tailWord_1611616
  simp only [CollatzResearch.WordTrace]
  refine ⟨29390232264698974472383351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39186976352931965963177801 29390232264698974472383351)
  ·
    refine ⟨44085348397048461708575027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29390232264698974472383351 44085348397048461708575027)
    ·
      refine ⟨66128022595572692562862541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44085348397048461708575027 66128022595572692562862541)
      ·
        refine ⟨24798008473339759711073453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66128022595572692562862541 24798008473339759711073453)
        ·
          refine ⟨9299253177502409891652545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24798008473339759711073453 9299253177502409891652545)
          ·
            refine ⟨6974439883126807418739409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9299253177502409891652545 6974439883126807418739409)
            ·
              refine ⟨5230829912345105564054557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6974439883126807418739409 5230829912345105564054557)
              ·
                refine ⟨1961561217129414586520459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5230829912345105564054557 1961561217129414586520459)
                ·
                  refine ⟨2942341825694121879780689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1961561217129414586520459 2942341825694121879780689)
                  ·
                    refine ⟨2206756369270591409835517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2942341825694121879780689 2206756369270591409835517)
                    ·
                      refine ⟨827533638476471778688319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2206756369270591409835517 827533638476471778688319)
                      ·
                        rfl

theorem cell23_1611616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_1611616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611616 prefixEnd_1611616 := by exact prefixLift 1611616
  have htrace : WordTrace (prefixWord ++ tailWord_1611616) baseStart_1611616 baseEnd_1611616 := by
    simpa [prefixWord, tailWord_1611616, baseEnd_1611616] using wordTrace_append hprefix tailTrace_1611616
  have hstable : (prefixWord ++ tailWord_1611616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611616).length < 2 ^ (prefixWord ++ tailWord_1611616).sum := by decide
  have hdescent : baseEnd_1611616 < baseStart_1611616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611619 : List Nat := [1, 1, 1, 5, 4, 2, 9]
def baseStart_1611619 : Nat := 118140960795 + 1611619 * 2 ^ 59
def prefixEnd_1611619 : Nat := 4983230072969 + 3 ^ 40 * 1611619 * 2
def baseEnd_1611619 : Nat := 10216483690351052678405

theorem tailTrace_1611619 : CollatzResearch.WordTrace tailWord_1611619 prefixEnd_1611619 10216483690351052678405 := by
  unfold tailWord_1611619
  simp only [CollatzResearch.WordTrace]
  refine ⟨58780573948387080457125911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39187049298924720304750607 58780573948387080457125911)
  ·
    refine ⟨88170860922580620685688867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58780573948387080457125911 88170860922580620685688867)
    ·
      refine ⟨132256291383870931028533301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88170860922580620685688867 132256291383870931028533301)
      ·
        refine ⟨12399027317237899783924997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132256291383870931028533301 12399027317237899783924997)
        ·
          refine ⟨2324817621982106209485937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12399027317237899783924997 2324817621982106209485937)
          ·
            refine ⟨1743613216486579657114453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2324817621982106209485937 1743613216486579657114453)
            ·
              refine ⟨10216483690351052678405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1743613216486579657114453 10216483690351052678405)
              ·
                rfl

theorem cell23_1611619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 9].length) (baseStart_1611619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611619 prefixEnd_1611619 := by exact prefixLift 1611619
  have htrace : WordTrace (prefixWord ++ tailWord_1611619) baseStart_1611619 baseEnd_1611619 := by
    simpa [prefixWord, tailWord_1611619, baseEnd_1611619] using wordTrace_append hprefix tailTrace_1611619
  have hstable : (prefixWord ++ tailWord_1611619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611619).length < 2 ^ (prefixWord ++ tailWord_1611619).sum := by decide
  have hdescent : baseEnd_1611619 < baseStart_1611619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611630 : List Nat := [4, 1, 2, 3, 1, 1, 3, 1, 3, 2, 2]
def baseStart_1611630 : Nat := 118140960795 + 1611630 * 2 ^ 59
def prefixEnd_1611630 : Nat := 4983230072969 + 3 ^ 40 * 1611630 * 2
def baseEnd_1611630 : Nat := 827540827205634723913255

theorem tailTrace_1611630 : CollatzResearch.WordTrace tailWord_1611630 prefixEnd_1611630 827540827205634723913255 := by
  unfold tailWord_1611630
  simp only [CollatzResearch.WordTrace]
  refine ⟨7347621893918403666972043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39187316767564819557184229 7347621893918403666972043)
  ·
    refine ⟨11021432840877605500458065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7347621893918403666972043 11021432840877605500458065)
    ·
      refine ⟨8266074630658204125343549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11021432840877605500458065 8266074630658204125343549)
      ·
        refine ⟨3099777986496826547003831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8266074630658204125343549 3099777986496826547003831)
        ·
          refine ⟨4649666979745239820505747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3099777986496826547003831 4649666979745239820505747)
          ·
            refine ⟨6974500469617859730758621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4649666979745239820505747 6974500469617859730758621)
            ·
              refine ⟨2615437676106697399034483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6974500469617859730758621 2615437676106697399034483)
              ·
                refine ⟨3923156514160046098551725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2615437676106697399034483 3923156514160046098551725)
                ·
                  refine ⟨1471183692810017286956897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3923156514160046098551725 1471183692810017286956897)
                  ·
                    refine ⟨1103387769607512965217673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1471183692810017286956897 1103387769607512965217673)
                    ·
                      refine ⟨827540827205634723913255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1103387769607512965217673 827540827205634723913255)
                      ·
                        rfl

theorem cell23_1611630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_1611630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611630 prefixEnd_1611630 := by exact prefixLift 1611630
  have htrace : WordTrace (prefixWord ++ tailWord_1611630) baseStart_1611630 baseEnd_1611630 := by
    simpa [prefixWord, tailWord_1611630, baseEnd_1611630] using wordTrace_append hprefix tailTrace_1611630
  have hstable : (prefixWord ++ tailWord_1611630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611630).length < 2 ^ (prefixWord ++ tailWord_1611630).sum := by decide
  have hdescent : baseEnd_1611630 < baseStart_1611630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611632 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 2, 7]
def baseStart_1611632 : Nat := 118140960795 + 1611632 * 2 ^ 59
def prefixEnd_1611632 : Nat := 4983230072969 + 3 ^ 40 * 1611632 * 2
def baseEnd_1611632 : Nat := 275847284722314572029415

theorem tailTrace_1611632 : CollatzResearch.WordTrace tailWord_1611632 prefixEnd_1611632 275847284722314572029415 := by
  unfold tailWord_1611632
  simp only [CollatzResearch.WordTrace]
  refine ⟨29390524048669991838674575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39187365398226655784899433 29390524048669991838674575)
  ·
    refine ⟨44085786073004987758011863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29390524048669991838674575 44085786073004987758011863)
    ·
      refine ⟨66128679109507481637017795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44085786073004987758011863 66128679109507481637017795)
      ·
        refine ⟨99193018664261222455526693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66128679109507481637017795 99193018664261222455526693)
        ·
          refine ⟨18598690999548979210411255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99193018664261222455526693 18598690999548979210411255)
          ·
            refine ⟨27898036499323468815616883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18598690999548979210411255 27898036499323468815616883)
            ·
              refine ⟨41847054748985203223425325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27898036499323468815616883 41847054748985203223425325)
              ·
                refine ⟨15692645530869451208784497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41847054748985203223425325 15692645530869451208784497)
                ·
                  refine ⟨11769484148152088406588373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15692645530869451208784497 11769484148152088406588373)
                  ·
                    refine ⟨275847284722314572029415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11769484148152088406588373 275847284722314572029415)
                    ·
                      rfl

theorem cell23_1611632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 2, 7].length) (baseStart_1611632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611632 prefixEnd_1611632 := by exact prefixLift 1611632
  have htrace : WordTrace (prefixWord ++ tailWord_1611632) baseStart_1611632 baseEnd_1611632 := by
    simpa [prefixWord, tailWord_1611632, baseEnd_1611632] using wordTrace_append hprefix tailTrace_1611632
  have hstable : (prefixWord ++ tailWord_1611632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611632).length < 2 ^ (prefixWord ++ tailWord_1611632).sum := by decide
  have hdescent : baseEnd_1611632 < baseStart_1611632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611639 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 1, 9, 2]
def baseStart_1611639 : Nat := 118140960795 + 1611639 * 2 ^ 59
def prefixEnd_1611639 : Nat := 4983230072969 + 3 ^ 40 * 1611639 * 2
def baseEnd_1611639 : Nat := 827545448531525188700713

theorem tailTrace_1611639 : CollatzResearch.WordTrace tailWord_1611639 prefixEnd_1611639 827545448531525188700713 := by
  unfold tailWord_1611639
  simp only [CollatzResearch.WordTrace]
  refine ⟨58781303408314623872853971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39187535605543082581902647 58781303408314623872853971)
  ·
    refine ⟨88171955112471935809280957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58781303408314623872853971 88171955112471935809280957)
    ·
      refine ⟨33064483167176975928480359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88171955112471935809280957 33064483167176975928480359)
      ·
        refine ⟨49596724750765463892720539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33064483167176975928480359 49596724750765463892720539)
        ·
          refine ⟨74395087126148195839080809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49596724750765463892720539 74395087126148195839080809)
          ·
            refine ⟨55796315344611146879310607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74395087126148195839080809 55796315344611146879310607)
            ·
              refine ⟨83694473016916720318965911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55796315344611146879310607 83694473016916720318965911)
              ·
                refine ⟨125541709525375080478448867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83694473016916720318965911 125541709525375080478448867)
                ·
                  refine ⟨188312564288062620717673301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125541709525375080478448867 188312564288062620717673301)
                  ·
                    refine ⟨1103393931375366918267617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 188312564288062620717673301 1103393931375366918267617)
                    ·
                      refine ⟨827545448531525188700713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1103393931375366918267617 827545448531525188700713)
                      ·
                        rfl

theorem cell23_1611639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 9, 2].length) (baseStart_1611639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611639 prefixEnd_1611639 := by exact prefixLift 1611639
  have htrace : WordTrace (prefixWord ++ tailWord_1611639) baseStart_1611639 baseEnd_1611639 := by
    simpa [prefixWord, tailWord_1611639, baseEnd_1611639] using wordTrace_append hprefix tailTrace_1611639
  have hstable : (prefixWord ++ tailWord_1611639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611639).length < 2 ^ (prefixWord ++ tailWord_1611639).sum := by decide
  have hdescent : baseEnd_1611639 < baseStart_1611639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611681 : List Nat := [1, 2, 3, 4, 3, 1, 2, 2, 1, 2, 2]
def baseStart_1611681 : Nat := 118140960795 + 1611681 * 2 ^ 59
def prefixEnd_1611681 : Nat := 4983230072969 + 3 ^ 40 * 1611681 * 2
def baseEnd_1611681 : Nat := 827567014719014024375521

theorem tailTrace_1611681 : CollatzResearch.WordTrace tailWord_1611681 prefixEnd_1611681 827567014719014024375521 := by
  unfold tailWord_1611681
  simp only [CollatzResearch.WordTrace]
  refine ⟨58782835274162465045882897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39188556849441643363921931 58782835274162465045882897)
  ·
    refine ⟨44087126455621848784412173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58782835274162465045882897 44087126455621848784412173)
    ·
      refine ⟨16532672420858193294154565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44087126455621848784412173 16532672420858193294154565)
      ·
        refine ⟨3099876078910911242653981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16532672420858193294154565 3099876078910911242653981)
        ·
          refine ⟨1162453529591591715995243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3099876078910911242653981 1162453529591591715995243)
          ·
            refine ⟨1743680294387387573992865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1162453529591591715995243 1743680294387387573992865)
            ·
              refine ⟨1307760220790540680494649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1743680294387387573992865 1307760220790540680494649)
              ·
                refine ⟨980820165592905510370987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1307760220790540680494649 980820165592905510370987)
                ·
                  refine ⟨1471230248389358265556481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 980820165592905510370987 1471230248389358265556481)
                  ·
                    refine ⟨1103422686292018699167361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1471230248389358265556481 1103422686292018699167361)
                    ·
                      refine ⟨827567014719014024375521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1103422686292018699167361 827567014719014024375521)
                      ·
                        rfl

theorem cell23_1611681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_1611681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611681 prefixEnd_1611681 := by exact prefixLift 1611681
  have htrace : WordTrace (prefixWord ++ tailWord_1611681) baseStart_1611681 baseEnd_1611681 := by
    simpa [prefixWord, tailWord_1611681, baseEnd_1611681] using wordTrace_append hprefix tailTrace_1611681
  have hstable : (prefixWord ++ tailWord_1611681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611681).length < 2 ^ (prefixWord ++ tailWord_1611681).sum := by decide
  have hdescent : baseEnd_1611681 < baseStart_1611681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611699 : List Nat := [1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 4]
def baseStart_1611699 : Nat := 118140960795 + 1611699 * 2 ^ 59
def prefixEnd_1611699 : Nat := 4983230072969 + 3 ^ 40 * 1611699 * 2
def baseEnd_1611699 : Nat := 827576257370794953950437

theorem tailTrace_1611699 : CollatzResearch.WordTrace tailWord_1611699 prefixEnd_1611699 827576257370794953950437 := by
  unfold tailWord_1611699
  simp only [CollatzResearch.WordTrace]
  refine ⟨58783491788097254120038151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39188994525398169413358767 58783491788097254120038151)
  ·
    refine ⟨88175237682145881180057227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58783491788097254120038151 88175237682145881180057227)
    ·
      refine ⟨132262856523218821770085841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88175237682145881180057227 132262856523218821770085841)
      ·
        refine ⟨99197142392414116327564381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132262856523218821770085841 99197142392414116327564381)
        ·
          refine ⟨37198928397155293622836643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99197142392414116327564381 37198928397155293622836643)
          ·
            refine ⟨55798392595732940434254965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37198928397155293622836643 55798392595732940434254965)
            ·
              refine ⟨5231099305849963165711403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55798392595732940434254965 5231099305849963165711403)
              ·
                refine ⟨7846648958774944748567105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5231099305849963165711403 7846648958774944748567105)
                ·
                  refine ⟨5884986719081208561425329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7846648958774944748567105 5884986719081208561425329)
                  ·
                    refine ⟨4413740039310906421068997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5884986719081208561425329 4413740039310906421068997)
                    ·
                      refine ⟨827576257370794953950437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4413740039310906421068997 827576257370794953950437)
                      ·
                        rfl

theorem cell23_1611699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 4].length) (baseStart_1611699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611699 prefixEnd_1611699 := by exact prefixLift 1611699
  have htrace : WordTrace (prefixWord ++ tailWord_1611699) baseStart_1611699 baseEnd_1611699 := by
    simpa [prefixWord, tailWord_1611699, baseEnd_1611699] using wordTrace_append hprefix tailTrace_1611699
  have hstable : (prefixWord ++ tailWord_1611699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611699).length < 2 ^ (prefixWord ++ tailWord_1611699).sum := by decide
  have hdescent : baseEnd_1611699 < baseStart_1611699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611709 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 9]
def baseStart_1611709 : Nat := 118140960795 + 1611709 * 2 ^ 59
def prefixEnd_1611709 : Nat := 4983230072969 + 3 ^ 40 * 1611709 * 2
def baseEnd_1611709 : Nat := 91953488019704434980599

theorem tailTrace_1611709 : CollatzResearch.WordTrace tailWord_1611709 prefixEnd_1611709 91953488019704434980599 := by
  unfold tailWord_1611709
  simp only [CollatzResearch.WordTrace]
  refine ⟨58783856518061025827902181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39189237678707350551934787 58783856518061025827902181)
  ·
    refine ⟨11021973097136442342731659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58783856518061025827902181 11021973097136442342731659)
    ·
      refine ⟨16532959645704663514097489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11021973097136442342731659 16532959645704663514097489)
      ·
        refine ⟨12399719734278497635573117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16532959645704663514097489 12399719734278497635573117)
        ·
          refine ⟨4649894900354436613339919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12399719734278497635573117 4649894900354436613339919)
          ·
            refine ⟨6974842350531654920009879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4649894900354436613339919 6974842350531654920009879)
            ·
              refine ⟨10462263525797482380014819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6974842350531654920009879 10462263525797482380014819)
              ·
                refine ⟨15693395288696223570022229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10462263525797482380014819 15693395288696223570022229)
                ·
                  refine ⟨91953488019704434980599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15693395288696223570022229 91953488019704434980599)
                  ·
                    rfl

theorem cell23_1611709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_1611709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611709 prefixEnd_1611709 := by exact prefixLift 1611709
  have htrace : WordTrace (prefixWord ++ tailWord_1611709) baseStart_1611709 baseEnd_1611709 := by
    simpa [prefixWord, tailWord_1611709, baseEnd_1611709] using wordTrace_append hprefix tailTrace_1611709
  have hstable : (prefixWord ++ tailWord_1611709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611709).length < 2 ^ (prefixWord ++ tailWord_1611709).sum := by decide
  have hdescent : baseEnd_1611709 < baseStart_1611709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611719 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 3, 5, 3]
def baseStart_1611719 : Nat := 118140960795 + 1611719 * 2 ^ 59
def prefixEnd_1611719 : Nat := 4983230072969 + 3 ^ 40 * 1611719 * 2
def baseEnd_1611719 : Nat := 827586526983884875700345

theorem tailTrace_1611719 : CollatzResearch.WordTrace tailWord_1611719 prefixEnd_1611719 827586526983884875700345 := by
  unfold tailWord_1611719
  simp only [CollatzResearch.WordTrace]
  refine ⟨58784221248024797535766211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39189480832016531690510807 58784221248024797535766211)
  ·
    refine ⟨88176331872037196303649317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58784221248024797535766211 88176331872037196303649317)
    ·
      refine ⟨16533062226006974306934247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88176331872037196303649317 16533062226006974306934247)
      ·
        refine ⟨24799593339010461460401371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16533062226006974306934247 24799593339010461460401371)
        ·
          refine ⟨37199390008515692190602057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24799593339010461460401371 37199390008515692190602057)
          ·
            refine ⟨27899542506386769142951543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37199390008515692190602057 27899542506386769142951543)
            ·
              refine ⟨41849313759580153714427315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27899542506386769142951543 41849313759580153714427315)
              ·
                refine ⟨62773970639370230571640973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41849313759580153714427315 62773970639370230571640973)
                ·
                  refine ⟨23540238989763836464365365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62773970639370230571640973 23540238989763836464365365)
                  ·
                    refine ⟨2206897405290359668534253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23540238989763836464365365 2206897405290359668534253)
                    ·
                      refine ⟨827586526983884875700345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2206897405290359668534253 827586526983884875700345)
                      ·
                        rfl

theorem cell23_1611719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_1611719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611719 prefixEnd_1611719 := by exact prefixLift 1611719
  have htrace : WordTrace (prefixWord ++ tailWord_1611719) baseStart_1611719 baseEnd_1611719 := by
    simpa [prefixWord, tailWord_1611719, baseEnd_1611719] using wordTrace_append hprefix tailTrace_1611719
  have hstable : (prefixWord ++ tailWord_1611719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611719).length < 2 ^ (prefixWord ++ tailWord_1611719).sum := by decide
  have hdescent : baseEnd_1611719 < baseStart_1611719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611737 : List Nat := [1, 2, 1, 2, 6, 2, 1, 2, 2, 2, 2]
def baseStart_1611737 : Nat := 118140960795 + 1611737 * 2 ^ 59
def prefixEnd_1611737 : Nat := 4983230072969 + 3 ^ 40 * 1611737 * 2
def baseEnd_1611737 : Nat := 827595769635665805275263

theorem tailTrace_1611737 : CollatzResearch.WordTrace tailWord_1611737 prefixEnd_1611737 827595769635665805275263 := by
  unfold tailWord_1611737
  simp only [CollatzResearch.WordTrace]
  refine ⟨58784877761959586609921465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39189918507973057739947643 58784877761959586609921465)
  ·
    refine ⟨44088658321469689957441099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58784877761959586609921465 44088658321469689957441099)
    ·
      refine ⟨66132987482204534936161649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44088658321469689957441099 66132987482204534936161649)
      ·
        refine ⟨49599740611653401202121237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66132987482204534936161649 49599740611653401202121237)
        ·
          refine ⟨2324987841171253181349433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49599740611653401202121237 2324987841171253181349433)
          ·
            refine ⟨1743740880878439886012075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2324987841171253181349433 1743740880878439886012075)
            ·
              refine ⟨2615611321317659829018113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1743740880878439886012075 2615611321317659829018113)
              ·
                refine ⟨1961708490988244871763585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2615611321317659829018113 1961708490988244871763585)
                ·
                  refine ⟨1471281368241183653822689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1961708490988244871763585 1471281368241183653822689)
                  ·
                    refine ⟨1103461026180887740367017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1471281368241183653822689 1103461026180887740367017)
                    ·
                      refine ⟨827595769635665805275263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1103461026180887740367017 827595769635665805275263)
                      ·
                        rfl

theorem cell23_1611737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2, 2, 2].length) (baseStart_1611737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611737 prefixEnd_1611737 := by exact prefixLift 1611737
  have htrace : WordTrace (prefixWord ++ tailWord_1611737) baseStart_1611737 baseEnd_1611737 := by
    simpa [prefixWord, tailWord_1611737, baseEnd_1611737] using wordTrace_append hprefix tailTrace_1611737
  have hstable : (prefixWord ++ tailWord_1611737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611737).length < 2 ^ (prefixWord ++ tailWord_1611737).sum := by decide
  have hdescent : baseEnd_1611737 < baseStart_1611737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611759 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 4]
def baseStart_1611759 : Nat := 118140960795 + 1611759 * 2 ^ 59
def prefixEnd_1611759 : Nat := 4983230072969 + 3 ^ 40 * 1611759 * 2
def baseEnd_1611759 : Nat := 827607066210064719200161

theorem tailTrace_1611759 : CollatzResearch.WordTrace tailWord_1611759 prefixEnd_1611759 827607066210064719200161 := by
  unfold tailWord_1611759
  simp only [CollatzResearch.WordTrace]
  refine ⟨58785680167879884367222331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39190453445253256244814887 58785680167879884367222331)
  ·
    refine ⟨88178520251819826550833497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58785680167879884367222331 88178520251819826550833497)
    ·
      refine ⟨66133890188864869913125123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88178520251819826550833497 66133890188864869913125123)
      ·
        refine ⟨99200835283297304869687685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66133890188864869913125123 99200835283297304869687685)
        ·
          refine ⟨18600156615618244663066441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99200835283297304869687685 18600156615618244663066441)
          ·
            refine ⟨13950117461713683497299831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18600156615618244663066441 13950117461713683497299831)
            ·
              refine ⟨20925176192570525245949747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13950117461713683497299831 20925176192570525245949747)
              ·
                refine ⟨31387764288855787868924621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20925176192570525245949747 31387764288855787868924621)
                ·
                  refine ⟨11770411608320920450846733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31387764288855787868924621 11770411608320920450846733)
                  ·
                    refine ⟨4413904353120345169067525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11770411608320920450846733 4413904353120345169067525)
                    ·
                      refine ⟨827607066210064719200161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4413904353120345169067525 827607066210064719200161)
                      ·
                        rfl

theorem cell23_1611759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 4].length) (baseStart_1611759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611759 prefixEnd_1611759 := by exact prefixLift 1611759
  have htrace : WordTrace (prefixWord ++ tailWord_1611759) baseStart_1611759 baseEnd_1611759 := by
    simpa [prefixWord, tailWord_1611759, baseEnd_1611759] using wordTrace_append hprefix tailTrace_1611759
  have hstable : (prefixWord ++ tailWord_1611759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611759).length < 2 ^ (prefixWord ++ tailWord_1611759).sum := by decide
  have hdescent : baseEnd_1611759 < baseStart_1611759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611776 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 4, 4, 2]
def baseStart_1611776 : Nat := 118140960795 + 1611776 * 2 ^ 59
def prefixEnd_1611776 : Nat := 4983230072969 + 3 ^ 40 * 1611776 * 2
def baseEnd_1611776 : Nat := 827615795381191152687583

theorem tailTrace_1611776 : CollatzResearch.WordTrace tailWord_1611776 prefixEnd_1611776 827615795381191152687583 := by
  unfold tailWord_1611776
  simp only [CollatzResearch.WordTrace]
  refine ⟨29393150104409148135295591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39190866805878864180394121 29393150104409148135295591)
  ·
    refine ⟨44089725156613722202943387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29393150104409148135295591 44089725156613722202943387)
    ·
      refine ⟨66134587734920583304415081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44089725156613722202943387 66134587734920583304415081)
      ·
        refine ⟨49600940801190437478311311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66134587734920583304415081 49600940801190437478311311)
        ·
          refine ⟨74401411201785656217466967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49600940801190437478311311 74401411201785656217466967)
          ·
            refine ⟨111602116802678484326200451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74401411201785656217466967 111602116802678484326200451)
            ·
              refine ⟨167403175204017726489300677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111602116802678484326200451 167403175204017726489300677)
              ·
                refine ⟨31388095350753323716743877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167403175204017726489300677 31388095350753323716743877)
                ·
                  refine ⟨5885267878266248196889477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31388095350753323716743877 5885267878266248196889477)
                  ·
                    refine ⟨1103487727174921536916777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5885267878266248196889477 1103487727174921536916777)
                    ·
                      refine ⟨827615795381191152687583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1103487727174921536916777 827615795381191152687583)
                      ·
                        rfl

theorem cell23_1611776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 4, 4, 2].length) (baseStart_1611776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611776 prefixEnd_1611776 := by exact prefixLift 1611776
  have htrace : WordTrace (prefixWord ++ tailWord_1611776) baseStart_1611776 baseEnd_1611776 := by
    simpa [prefixWord, tailWord_1611776, baseEnd_1611776] using wordTrace_append hprefix tailTrace_1611776
  have hstable : (prefixWord ++ tailWord_1611776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611776).length < 2 ^ (prefixWord ++ tailWord_1611776).sum := by decide
  have hdescent : baseEnd_1611776 < baseStart_1611776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611830 : List Nat := [5, 1, 2, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_1611830 : Nat := 118140960795 + 1611830 * 2 ^ 59
def prefixEnd_1611830 : Nat := 4983230072969 + 3 ^ 40 * 1611830 * 2
def baseEnd_1611830 : Nat := 827643523336533941412335

theorem tailTrace_1611830 : CollatzResearch.WordTrace tailWord_1611830 prefixEnd_1611830 827643523336533941412335 := by
  unfold tailWord_1611830
  simp only [CollatzResearch.WordTrace]
  refine ⟨3674266859413916468316059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39192179833748442328704629 3674266859413916468316059)
  ·
    refine ⟨5511400289120874702474089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3674266859413916468316059 5511400289120874702474089)
    ·
      refine ⟨4133550216840656026855567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5511400289120874702474089 4133550216840656026855567)
      ·
        refine ⟨6200325325260984040283351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4133550216840656026855567 6200325325260984040283351)
        ·
          refine ⟨9300487987891476060425027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6200325325260984040283351 9300487987891476060425027)
          ·
            refine ⟨13950731981837214090637541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9300487987891476060425027 13950731981837214090637541)
            ·
              refine ⟨2615762246594477641994539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13950731981837214090637541 2615762246594477641994539)
              ·
                refine ⟨3923643369891716462991809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2615762246594477641994539 3923643369891716462991809)
                ·
                  refine ⟨2942732527418787347243857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3923643369891716462991809 2942732527418787347243857)
                  ·
                    refine ⟨2207049395564090510432893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2942732527418787347243857 2207049395564090510432893)
                    ·
                      refine ⟨827643523336533941412335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2207049395564090510432893 827643523336533941412335)
                      ·
                        rfl

theorem cell23_1611830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_1611830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611830 prefixEnd_1611830 := by exact prefixLift 1611830
  have htrace : WordTrace (prefixWord ++ tailWord_1611830) baseStart_1611830 baseEnd_1611830 := by
    simpa [prefixWord, tailWord_1611830, baseEnd_1611830] using wordTrace_append hprefix tailTrace_1611830
  have hstable : (prefixWord ++ tailWord_1611830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611830).length < 2 ^ (prefixWord ++ tailWord_1611830).sum := by decide
  have hdescent : baseEnd_1611830 < baseStart_1611830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611866 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4]
def baseStart_1611866 : Nat := 118140960795 + 1611866 * 2 ^ 59
def prefixEnd_1611866 : Nat := 4983230072969 + 3 ^ 40 * 1611866 * 2
def baseEnd_1611866 : Nat := 827662008640095800562169

theorem tailTrace_1611866 : CollatzResearch.WordTrace tailWord_1611866 prefixEnd_1611866 827662008640095800562169 := by
  unfold tailWord_1611866
  simp only [CollatzResearch.WordTrace]
  refine ⟨14697395694623060410341863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39193055185661494427578301 14697395694623060410341863)
  ·
    refine ⟨22046093541934590615512795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14697395694623060410341863 22046093541934590615512795)
    ·
      refine ⟨33069140312901885923269193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22046093541934590615512795 33069140312901885923269193)
      ·
        refine ⟨24801855234676414442451895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33069140312901885923269193 24801855234676414442451895)
        ·
          refine ⟨37202782852014621663677843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24801855234676414442451895 37202782852014621663677843)
          ·
            refine ⟨55804174278021932495516765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37202782852014621663677843 55804174278021932495516765)
            ·
              refine ⟨20926565354258224685818787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55804174278021932495516765 20926565354258224685818787)
              ·
                refine ⟨31389848031387337028728181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20926565354258224685818787 31389848031387337028728181)
                ·
                  refine ⟨2942798252942562846443267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31389848031387337028728181 2942798252942562846443267)
                  ·
                    refine ⟨4414197379413844269664901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2942798252942562846443267 4414197379413844269664901)
                    ·
                      refine ⟨827662008640095800562169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4414197379413844269664901 827662008640095800562169)
                      ·
                        rfl

theorem cell23_1611866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_1611866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611866 prefixEnd_1611866 := by exact prefixLift 1611866
  have htrace : WordTrace (prefixWord ++ tailWord_1611866) baseStart_1611866 baseEnd_1611866 := by
    simpa [prefixWord, tailWord_1611866, baseEnd_1611866] using wordTrace_append hprefix tailTrace_1611866
  have hstable : (prefixWord ++ tailWord_1611866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611866).length < 2 ^ (prefixWord ++ tailWord_1611866).sum := by decide
  have hdescent : baseEnd_1611866 < baseStart_1611866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611876 : List Nat := [2, 3, 1, 1, 2, 1, 3, 3, 1, 6]
def baseStart_1611876 : Nat := 118140960795 + 1611876 * 2 ^ 59
def prefixEnd_1611876 : Nat := 4983230072969 + 3 ^ 40 * 1611876 * 2
def baseEnd_1611876 : Nat := 275889047815546920479041

theorem tailTrace_1611876 : CollatzResearch.WordTrace tailWord_1611876 prefixEnd_1611876 275889047815546920479041 := by
  unfold tailWord_1611876
  simp only [CollatzResearch.WordTrace]
  refine ⟨29394973754228006674615741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39193298338970675566154321 29394973754228006674615741)
  ·
    refine ⟨11023115157835502502980903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29394973754228006674615741 11023115157835502502980903)
    ·
      refine ⟨16534672736753253754471355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11023115157835502502980903 16534672736753253754471355)
      ·
        refine ⟨24802009105129880631707033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16534672736753253754471355 24802009105129880631707033)
        ·
          refine ⟨18601506828847410473780275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24802009105129880631707033 18601506828847410473780275)
          ·
            refine ⟨27902260243271115710670413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18601506828847410473780275 27902260243271115710670413)
            ·
              refine ⟨10463347591226668391501405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27902260243271115710670413 10463347591226668391501405)
              ·
                refine ⟨3923755346710000646813027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10463347591226668391501405 3923755346710000646813027)
                ·
                  refine ⟨5885633020065000970219541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3923755346710000646813027 5885633020065000970219541)
                  ·
                    refine ⟨275889047815546920479041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5885633020065000970219541 275889047815546920479041)
                    ·
                      rfl

theorem cell23_1611876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_1611876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611876 prefixEnd_1611876 := by exact prefixLift 1611876
  have htrace : WordTrace (prefixWord ++ tailWord_1611876) baseStart_1611876 baseEnd_1611876 := by
    simpa [prefixWord, tailWord_1611876, baseEnd_1611876] using wordTrace_append hprefix tailTrace_1611876
  have hstable : (prefixWord ++ tailWord_1611876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611876).length < 2 ^ (prefixWord ++ tailWord_1611876).sum := by decide
  have hdescent : baseEnd_1611876 < baseStart_1611876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611894 : List Nat := [5, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3]
def baseStart_1611894 : Nat := 118140960795 + 1611894 * 2 ^ 59
def prefixEnd_1611894 : Nat := 4983230072969 + 3 ^ 40 * 1611894 * 2
def baseEnd_1611894 : Nat := 827676386098421691012041

theorem tailTrace_1611894 : CollatzResearch.WordTrace tailWord_1611894 prefixEnd_1611894 827676386098421691012041 := by
  unfold tailWord_1611894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3674412751399425151461671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39193736014927201615591157 3674412751399425151461671)
  ·
    refine ⟨5511619127099137727192507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3674412751399425151461671 5511619127099137727192507)
    ·
      refine ⟨8267428690648706590788761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5511619127099137727192507 8267428690648706590788761)
      ·
        refine ⟨6200571517986529943091571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8267428690648706590788761 6200571517986529943091571)
        ·
          refine ⟨9300857276979794914637357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6200571517986529943091571 9300857276979794914637357)
          ·
            refine ⟨3487821478867423092989009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9300857276979794914637357 3487821478867423092989009)
            ·
              refine ⟨2615866109150567319741757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3487821478867423092989009 2615866109150567319741757)
              ·
                refine ⟨980949790931462744903159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2615866109150567319741757 980949790931462744903159)
                ·
                  refine ⟨1471424686397194117354739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 980949790931462744903159 1471424686397194117354739)
                  ·
                    refine ⟨2207137029595791176032109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1471424686397194117354739 2207137029595791176032109)
                    ·
                      refine ⟨827676386098421691012041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2207137029595791176032109 827676386098421691012041)
                      ·
                        rfl

theorem cell23_1611894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_1611894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611894 prefixEnd_1611894 := by exact prefixLift 1611894
  have htrace : WordTrace (prefixWord ++ tailWord_1611894) baseStart_1611894 baseEnd_1611894 := by
    simpa [prefixWord, tailWord_1611894, baseEnd_1611894] using wordTrace_append hprefix tailTrace_1611894
  have hstable : (prefixWord ++ tailWord_1611894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611894).length < 2 ^ (prefixWord ++ tailWord_1611894).sum := by decide
  have hdescent : baseEnd_1611894 < baseStart_1611894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611900 : List Nat := [2, 2, 2, 1, 1, 4, 4, 1, 1, 1, 4]
def baseStart_1611900 : Nat := 118140960795 + 1611900 * 2 ^ 59
def prefixEnd_1611900 : Nat := 4983230072969 + 3 ^ 40 * 1611900 * 2
def baseEnd_1611900 : Nat := 827679466982348667537013

theorem tailTrace_1611900 : CollatzResearch.WordTrace tailWord_1611900 prefixEnd_1611900 827679466982348667537013 := by
  unfold tailWord_1611900
  simp only [CollatzResearch.WordTrace]
  refine ⟨29395411430184532724052577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39193881906912710298736769 29395411430184532724052577)
  ·
    refine ⟨22046558572638399543039433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29395411430184532724052577 22046558572638399543039433)
    ·
      refine ⟨16534918929478799657279575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22046558572638399543039433 16534918929478799657279575)
      ·
        refine ⟨24802378394218199485919363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16534918929478799657279575 24802378394218199485919363)
        ·
          refine ⟨37203567591327299228879045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24802378394218199485919363 37203567591327299228879045)
          ·
            refine ⟨6975668923373868605414821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37203567591327299228879045 6975668923373868605414821)
            ·
              refine ⟨1307937923132600363515279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6975668923373868605414821 1307937923132600363515279)
              ·
                refine ⟨1961906884698900545272919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1307937923132600363515279 1961906884698900545272919)
                ·
                  refine ⟨2942860327048350817909379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1961906884698900545272919 2942860327048350817909379)
                  ·
                    refine ⟨4414290490572526226864069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2942860327048350817909379 4414290490572526226864069)
                    ·
                      refine ⟨827679466982348667537013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4414290490572526226864069 827679466982348667537013)
                      ·
                        rfl

theorem cell23_1611900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 1, 1, 4].length) (baseStart_1611900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611900 prefixEnd_1611900 := by exact prefixLift 1611900
  have htrace : WordTrace (prefixWord ++ tailWord_1611900) baseStart_1611900 baseEnd_1611900 := by
    simpa [prefixWord, tailWord_1611900, baseEnd_1611900] using wordTrace_append hprefix tailTrace_1611900
  have hstable : (prefixWord ++ tailWord_1611900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611900).length < 2 ^ (prefixWord ++ tailWord_1611900).sum := by decide
  have hdescent : baseEnd_1611900 < baseStart_1611900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611916 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 2, 7, 3]
def baseStart_1611916 : Nat := 118140960795 + 1611916 * 2 ^ 59
def prefixEnd_1611916 : Nat := 4983230072969 + 3 ^ 40 * 1611916 * 2
def baseEnd_1611916 : Nat := 827687682672820604936939

theorem tailTrace_1611916 : CollatzResearch.WordTrace tailWord_1611916 prefixEnd_1611916 827687682672820604936939 := by
  unfold tailWord_1611916
  simp only [CollatzResearch.WordTrace]
  refine ⟨29395703214155550090343801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39194270952207400120458401 29395703214155550090343801)
  ·
    refine ⟨22046777410616662567757851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29395703214155550090343801 22046777410616662567757851)
    ·
      refine ⟨33070166115924993851636777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22046777410616662567757851 33070166115924993851636777)
      ·
        refine ⟨24802624586943745388727583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33070166115924993851636777 24802624586943745388727583)
        ·
          refine ⟨37203936880415618083091375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24802624586943745388727583 37203936880415618083091375)
          ·
            refine ⟨55805905320623427124637063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37203936880415618083091375 55805905320623427124637063)
            ·
              refine ⟨83708857980935140686955595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55805905320623427124637063 83708857980935140686955595)
              ·
                refine ⟨125563286971402711030433393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83708857980935140686955595 125563286971402711030433393)
                ·
                  refine ⟨94172465228552033272825045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125563286971402711030433393 94172465228552033272825045)
                  ·
                    refine ⟨2207167153794188279831837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 94172465228552033272825045 2207167153794188279831837)
                    ·
                      refine ⟨827687682672820604936939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2207167153794188279831837 827687682672820604936939)
                      ·
                        rfl

theorem cell23_1611916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_1611916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611916 prefixEnd_1611916 := by exact prefixLift 1611916
  have htrace : WordTrace (prefixWord ++ tailWord_1611916) baseStart_1611916 baseEnd_1611916 := by
    simpa [prefixWord, tailWord_1611916, baseEnd_1611916] using wordTrace_append hprefix tailTrace_1611916
  have hstable : (prefixWord ++ tailWord_1611916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611916).length < 2 ^ (prefixWord ++ tailWord_1611916).sum := by decide
  have hdescent : baseEnd_1611916 < baseStart_1611916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611927 : List Nat := [1, 1, 3, 3, 4, 1, 3, 1, 2, 4]
def baseStart_1611927 : Nat := 118140960795 + 1611927 * 2 ^ 59
def prefixEnd_1611927 : Nat := 4983230072969 + 3 ^ 40 * 1611927 * 2
def baseEnd_1611927 : Nat := 275897776986673353966463

theorem tailTrace_1611927 : CollatzResearch.WordTrace tailWord_1611927 prefixEnd_1611927 275897776986673353966463 := by
  unfold tailWord_1611927
  simp only [CollatzResearch.WordTrace]
  refine ⟨58791807631271249059338035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39194538420847499372892023 58791807631271249059338035)
  ·
    refine ⟨88187711446906873589007053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58791807631271249059338035 88187711446906873589007053)
    ·
      refine ⟨33070391792590077595877645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88187711446906873589007053 33070391792590077595877645)
      ·
        refine ⟨12401396922221279098454117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33070391792590077595877645 12401396922221279098454117)
        ·
          refine ⟨2325261922916489830960147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12401396922221279098454117 2325261922916489830960147)
          ·
            refine ⟨3487892884374734746440221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2325261922916489830960147 3487892884374734746440221)
            ·
              refine ⟨1307959831640525529915083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3487892884374734746440221 1307959831640525529915083)
              ·
                refine ⟨1961939747460788294872625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1307959831640525529915083 1961939747460788294872625)
                ·
                  refine ⟨1471454810595591221154469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1961939747460788294872625 1471454810595591221154469)
                  ·
                    refine ⟨275897776986673353966463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1471454810595591221154469 275897776986673353966463)
                    ·
                      rfl

theorem cell23_1611927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 2, 4].length) (baseStart_1611927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611927 prefixEnd_1611927 := by exact prefixLift 1611927
  have htrace : WordTrace (prefixWord ++ tailWord_1611927) baseStart_1611927 baseEnd_1611927 := by
    simpa [prefixWord, tailWord_1611927, baseEnd_1611927] using wordTrace_append hprefix tailTrace_1611927
  have hstable : (prefixWord ++ tailWord_1611927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611927).length < 2 ^ (prefixWord ++ tailWord_1611927).sum := by decide
  have hdescent : baseEnd_1611927 < baseStart_1611927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611940 : List Nat := [2, 3, 1, 2, 4, 2, 2, 7]
def baseStart_1611940 : Nat := 118140960795 + 1611940 * 2 ^ 59
def prefixEnd_1611940 : Nat := 4983230072969 + 3 ^ 40 * 1611940 * 2
def baseEnd_1611940 : Nat := 30655555785501055964327

theorem tailTrace_1611940 : CollatzResearch.WordTrace tailWord_1611940 prefixEnd_1611940 30655555785501055964327 := by
  unfold tailWord_1611940
  simp only [CollatzResearch.WordTrace]
  refine ⟨29396140890112076139780637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39194854520149434853040849 29396140890112076139780637)
  ·
    refine ⟨11023552833792028552417739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29396140890112076139780637 11023552833792028552417739)
    ·
      refine ⟨16535329250688042828626609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11023552833792028552417739 16535329250688042828626609)
      ·
        refine ⟨12401496938016032121469957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16535329250688042828626609 12401496938016032121469957)
        ·
          refine ⟨2325280675878006022775617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12401496938016032121469957 2325280675878006022775617)
          ·
            refine ⟨1743960506908504517081713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2325280675878006022775617 1743960506908504517081713)
            ·
              refine ⟨1307970380181378387811285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1743960506908504517081713 1307970380181378387811285)
              ·
                refine ⟨30655555785501055964327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1307970380181378387811285 30655555785501055964327)
                ·
                  rfl

theorem cell23_1611940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 7].length) (baseStart_1611940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611940 prefixEnd_1611940 := by exact prefixLift 1611940
  have htrace : WordTrace (prefixWord ++ tailWord_1611940) baseStart_1611940 baseEnd_1611940 := by
    simpa [prefixWord, tailWord_1611940, baseEnd_1611940] using wordTrace_append hprefix tailTrace_1611940
  have hstable : (prefixWord ++ tailWord_1611940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611940).length < 2 ^ (prefixWord ++ tailWord_1611940).sum := by decide
  have hdescent : baseEnd_1611940 < baseStart_1611940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611960 : List Nat := [2, 1, 2, 1, 2, 1, 3, 5, 1, 3, 2]
def baseStart_1611960 : Nat := 118140960795 + 1611960 * 2 ^ 59
def prefixEnd_1611960 : Nat := 4983230072969 + 3 ^ 40 * 1611960 * 2
def baseEnd_1611960 : Nat := 827710275821618432786737

theorem tailTrace_1611960 : CollatzResearch.WordTrace tailWord_1611960 prefixEnd_1611960 827710275821618432786737 := by
  unfold tailWord_1611960
  simp only [CollatzResearch.WordTrace]
  refine ⟨29396505620075847847644667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39195340826767797130192889 29396505620075847847644667)
  ·
    refine ⟨44094758430113771771467001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29396505620075847847644667 44094758430113771771467001)
    ·
      refine ⟨33071068822585328828600251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44094758430113771771467001 33071068822585328828600251)
      ·
        refine ⟨49606603233877993242900377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33071068822585328828600251 49606603233877993242900377)
        ·
          refine ⟨37204952425408494932175283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49606603233877993242900377 37204952425408494932175283)
          ·
            refine ⟨55807428638112742398262925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37204952425408494932175283 55807428638112742398262925)
            ·
              refine ⟨20927785739292278399348597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55807428638112742398262925 20927785739292278399348597)
              ·
                refine ⟨1961979913058651099938931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20927785739292278399348597 1961979913058651099938931)
                ·
                  refine ⟨2942969869587976649908397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1961979913058651099938931 2942969869587976649908397)
                  ·
                    refine ⟨1103613701095491243715649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2942969869587976649908397 1103613701095491243715649)
                    ·
                      refine ⟨827710275821618432786737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1103613701095491243715649 827710275821618432786737)
                      ·
                        rfl

theorem cell23_1611960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 1, 3, 2].length) (baseStart_1611960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611960 prefixEnd_1611960 := by exact prefixLift 1611960
  have htrace : WordTrace (prefixWord ++ tailWord_1611960) baseStart_1611960 baseEnd_1611960 := by
    simpa [prefixWord, tailWord_1611960, baseEnd_1611960] using wordTrace_append hprefix tailTrace_1611960
  have hstable : (prefixWord ++ tailWord_1611960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611960).length < 2 ^ (prefixWord ++ tailWord_1611960).sum := by decide
  have hdescent : baseEnd_1611960 < baseStart_1611960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1611976 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 3, 3, 5]
def baseStart_1611976 : Nat := 118140960795 + 1611976 * 2 ^ 59
def prefixEnd_1611976 : Nat := 4983230072969 + 3 ^ 40 * 1611976 * 2
def baseEnd_1611976 : Nat := 827718491512090370186663

theorem tailTrace_1611976 : CollatzResearch.WordTrace tailWord_1611976 prefixEnd_1611976 827718491512090370186663 := by
  unfold tailWord_1611976
  simp only [CollatzResearch.WordTrace]
  refine ⟨29396797404046865213935891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39195729872062486951914521 29396797404046865213935891)
  ·
    refine ⟨44095196106070297820903837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29396797404046865213935891 44095196106070297820903837)
    ·
      refine ⟨16535698539776361682838939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44095196106070297820903837 16535698539776361682838939)
      ·
        refine ⟨24803547809664542524258409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16535698539776361682838939 24803547809664542524258409)
        ·
          refine ⟨18602660857248406893193807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24803547809664542524258409 18602660857248406893193807)
          ·
            refine ⟨27903991285872610339790711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18602660857248406893193807 27903991285872610339790711)
            ·
              refine ⟨41855986928808915509686067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27903991285872610339790711 41855986928808915509686067)
              ·
                refine ⟨62783980393213373264529101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41855986928808915509686067 62783980393213373264529101)
                ·
                  refine ⟨23543992647455014974198413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62783980393213373264529101 23543992647455014974198413)
                  ·
                    refine ⟨8828997242795630615324405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23543992647455014974198413 8828997242795630615324405)
                    ·
                      refine ⟨827718491512090370186663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8828997242795630615324405 827718491512090370186663)
                      ·
                        rfl

theorem cell23_1611976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_1611976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1611976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1611976 prefixEnd_1611976 := by exact prefixLift 1611976
  have htrace : WordTrace (prefixWord ++ tailWord_1611976) baseStart_1611976 baseEnd_1611976 := by
    simpa [prefixWord, tailWord_1611976, baseEnd_1611976] using wordTrace_append hprefix tailTrace_1611976
  have hstable : (prefixWord ++ tailWord_1611976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1611976).length < 2 ^ (prefixWord ++ tailWord_1611976).sum := by decide
  have hdescent : baseEnd_1611976 < baseStart_1611976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1611976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612007 : List Nat := [1, 1, 5, 3, 1, 2, 1, 2, 1, 4, 2]
def baseStart_1612007 : Nat := 118140960795 + 1612007 * 2 ^ 59
def prefixEnd_1612007 : Nat := 4983230072969 + 3 ^ 40 * 1612007 * 2
def baseEnd_1612007 : Nat := 827734409412379748899021

theorem tailTrace_1612007 : CollatzResearch.WordTrace tailWord_1612007 prefixEnd_1612007 827734409412379748899021 := by
  unfold tailWord_1612007
  simp only [CollatzResearch.WordTrace]
  refine ⟨58794725470981422722250275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39196483647320948481500183 58794725470981422722250275)
  ·
    refine ⟨88192088206472134083375413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58794725470981422722250275 88192088206472134083375413)
    ·
      refine ⟨8268008269356762570316445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88192088206472134083375413 8268008269356762570316445)
      ·
        refine ⟨3100503101008785963868667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8268008269356762570316445 3100503101008785963868667)
        ·
          refine ⟨4650754651513178945803001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3100503101008785963868667 4650754651513178945803001)
          ·
            refine ⟨3488065988634884209352251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4650754651513178945803001 3488065988634884209352251)
            ·
              refine ⟨5232098982952326314028377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3488065988634884209352251 5232098982952326314028377)
              ·
                refine ⟨3924074237214244735521283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5232098982952326314028377 3924074237214244735521283)
                ·
                  refine ⟨5886111355821367103281925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3924074237214244735521283 5886111355821367103281925)
                  ·
                    refine ⟨1103645879216506331865361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5886111355821367103281925 1103645879216506331865361)
                    ·
                      refine ⟨827734409412379748899021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1103645879216506331865361 827734409412379748899021)
                      ·
                        rfl

theorem cell23_1612007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_1612007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612007 prefixEnd_1612007 := by exact prefixLift 1612007
  have htrace : WordTrace (prefixWord ++ tailWord_1612007) baseStart_1612007 baseEnd_1612007 := by
    simpa [prefixWord, tailWord_1612007, baseEnd_1612007] using wordTrace_append hprefix tailTrace_1612007
  have hstable : (prefixWord ++ tailWord_1612007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612007).length < 2 ^ (prefixWord ++ tailWord_1612007).sum := by decide
  have hdescent : baseEnd_1612007 < baseStart_1612007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612040 : List Nat := [2, 1, 3, 2, 3, 2, 1, 1, 2, 3, 3]
def baseStart_1612040 : Nat := 118140960795 + 1612040 * 2 ^ 59
def prefixEnd_1612040 : Nat := 4983230072969 + 3 ^ 40 * 1612040 * 2
def baseEnd_1612040 : Nat := 827751354273978119786369

theorem tailTrace_1612040 : CollatzResearch.WordTrace tailWord_1612040 prefixEnd_1612040 827751354273978119786369 := by
  unfold tailWord_1612040
  simp only [CollatzResearch.WordTrace]
  refine ⟨29397964539930934679100787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39197286053241246238801049 29397964539930934679100787)
  ·
    refine ⟨44096946809896402018651181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29397964539930934679100787 44096946809896402018651181)
    ·
      refine ⟨16536355053711150756994193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44096946809896402018651181 16536355053711150756994193)
      ·
        refine ⟨12402266290283363067745645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16536355053711150756994193 12402266290283363067745645)
        ·
          refine ⟨4650849858856261150404617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12402266290283363067745645 4650849858856261150404617)
          ·
            refine ⟨3488137394142195862803463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4650849858856261150404617 3488137394142195862803463)
            ·
              refine ⟨5232206091213293794205195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3488137394142195862803463 5232206091213293794205195)
              ·
                refine ⟨7848309136819940691307793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5232206091213293794205195 7848309136819940691307793)
                ·
                  refine ⟨5886231852614955518480845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7848309136819940691307793 5886231852614955518480845)
                  ·
                    refine ⟨2207336944730608319430317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5886231852614955518480845 2207336944730608319430317)
                    ·
                      refine ⟨827751354273978119786369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2207336944730608319430317 827751354273978119786369)
                      ·
                        rfl

theorem cell23_1612040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_1612040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612040 prefixEnd_1612040 := by exact prefixLift 1612040
  have htrace : WordTrace (prefixWord ++ tailWord_1612040) baseStart_1612040 baseEnd_1612040 := by
    simpa [prefixWord, tailWord_1612040, baseEnd_1612040] using wordTrace_append hprefix tailTrace_1612040
  have hstable : (prefixWord ++ tailWord_1612040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612040).length < 2 ^ (prefixWord ++ tailWord_1612040).sum := by decide
  have hdescent : baseEnd_1612040 < baseStart_1612040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612090 : List Nat := [3, 1, 1, 1, 4, 2, 1, 3, 3, 4]
def baseStart_1612090 : Nat := 118140960795 + 1612090 * 2 ^ 59
def prefixEnd_1612090 : Nat := 4983230072969 + 3 ^ 40 * 1612090 * 2
def baseEnd_1612090 : Nat := 275925676102234308053713

theorem tailTrace_1612090 : CollatzResearch.WordTrace tailWord_1612090 prefixEnd_1612090 275925676102234308053713 := by
  unfold tailWord_1612090
  simp only [CollatzResearch.WordTrace]
  refine ⟨14699438182420181974380431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39198501819787151931681149 14699438182420181974380431)
  ·
    refine ⟨22049157273630272961570647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14699438182420181974380431 22049157273630272961570647)
    ·
      refine ⟨33073735910445409442355971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22049157273630272961570647 33073735910445409442355971)
      ·
        refine ⟨49610603865668114163533957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33073735910445409442355971 49610603865668114163533957)
        ·
          refine ⟨9301988224812771405662617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49610603865668114163533957 9301988224812771405662617)
          ·
            refine ⟨6976491168609578554246963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9301988224812771405662617 6976491168609578554246963)
            ·
              refine ⟨10464736752914367831370445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6976491168609578554246963 10464736752914367831370445)
              ·
                refine ⟨3924276282342887936763917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10464736752914367831370445 3924276282342887936763917)
                ·
                  refine ⟨1471603605878582976286469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3924276282342887936763917 1471603605878582976286469)
                  ·
                    refine ⟨275925676102234308053713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1471603605878582976286469 275925676102234308053713)
                    ·
                      rfl

theorem cell23_1612090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 3, 4].length) (baseStart_1612090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612090 prefixEnd_1612090 := by exact prefixLift 1612090
  have htrace : WordTrace (prefixWord ++ tailWord_1612090) baseStart_1612090 baseEnd_1612090 := by
    simpa [prefixWord, tailWord_1612090, baseEnd_1612090] using wordTrace_append hprefix tailTrace_1612090
  have hstable : (prefixWord ++ tailWord_1612090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612090).length < 2 ^ (prefixWord ++ tailWord_1612090).sum := by decide
  have hdescent : baseEnd_1612090 < baseStart_1612090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612153 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 2, 5, 4]
def baseStart_1612153 : Nat := 118140960795 + 1612153 * 2 ^ 59
def prefixEnd_1612153 : Nat := 4983230072969 + 3 ^ 40 * 1612153 * 2
def baseEnd_1612153 : Nat := 827809377587936177673349

theorem tailTrace_1612153 : CollatzResearch.WordTrace tailWord_1612153 prefixEnd_1612153 827809377587936177673349 := by
  unfold tailWord_1612153
  simp only [CollatzResearch.WordTrace]
  refine ⟨58800050528452489657065113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39200033685634993104710075 58800050528452489657065113)
  ·
    refine ⟨44100037896339367242798835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58800050528452489657065113 44100037896339367242798835)
    ·
      refine ⟨66150056844509050864198253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44100037896339367242798835 66150056844509050864198253)
      ·
        refine ⟨24806271316690894074074345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66150056844509050864198253 24806271316690894074074345)
        ·
          refine ⟨18604703487518170555555759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24806271316690894074074345 18604703487518170555555759)
          ·
            refine ⟨27907055231277255833333639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18604703487518170555555759 27907055231277255833333639)
            ·
              refine ⟨41860582846915883750000459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27907055231277255833333639 41860582846915883750000459)
              ·
                refine ⟨62790874270373825625000689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41860582846915883750000459 62790874270373825625000689)
                ·
                  refine ⟨47093155702780369218750517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62790874270373825625000689 47093155702780369218750517)
                  ·
                    refine ⟨4414983347135659614257861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47093155702780369218750517 4414983347135659614257861)
                    ·
                      refine ⟨827809377587936177673349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4414983347135659614257861 827809377587936177673349)
                      ·
                        rfl

theorem cell23_1612153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_1612153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612153 prefixEnd_1612153 := by exact prefixLift 1612153
  have htrace : WordTrace (prefixWord ++ tailWord_1612153) baseStart_1612153 baseEnd_1612153 := by
    simpa [prefixWord, tailWord_1612153, baseEnd_1612153] using wordTrace_append hprefix tailTrace_1612153
  have hstable : (prefixWord ++ tailWord_1612153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612153).length < 2 ^ (prefixWord ++ tailWord_1612153).sum := by decide
  have hdescent : baseEnd_1612153 < baseStart_1612153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612174 : List Nat := [4, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2]
def baseStart_1612174 : Nat := 118140960795 + 1612174 * 2 ^ 59
def prefixEnd_1612174 : Nat := 4983230072969 + 3 ^ 40 * 1612174 * 2
def baseEnd_1612174 : Nat := 827820160681680595510753

theorem tailTrace_1612174 : CollatzResearch.WordTrace tailWord_1612174 prefixEnd_1612174 827820160681680595510753 := by
  unfold tailWord_1612174
  simp only [CollatzResearch.WordTrace]
  refine ⟨7350102057672051280447447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39200544307584273495719717 7350102057672051280447447)
  ·
    refine ⟨11025153086508076920671171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7350102057672051280447447 11025153086508076920671171)
    ·
      refine ⟨16537729629762115381006757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11025153086508076920671171 16537729629762115381006757)
      ·
        refine ⟨3100824305580396633938767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16537729629762115381006757 3100824305580396633938767)
        ·
          refine ⟨4651236458370594950908151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3100824305580396633938767 4651236458370594950908151)
          ·
            refine ⟨6976854687555892426362227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4651236458370594950908151 6976854687555892426362227)
            ·
              refine ⟨10465282031333838639543341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6976854687555892426362227 10465282031333838639543341)
              ·
                refine ⟨3924480761750189489828753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10465282031333838639543341 3924480761750189489828753)
                ·
                  refine ⟨2943360571312642117371565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3924480761750189489828753 2943360571312642117371565)
                  ·
                    refine ⟨1103760214242240794014337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2943360571312642117371565 1103760214242240794014337)
                    ·
                      refine ⟨827820160681680595510753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1103760214242240794014337 827820160681680595510753)
                      ·
                        rfl

theorem cell23_1612174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_1612174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612174 prefixEnd_1612174 := by exact prefixLift 1612174
  have htrace : WordTrace (prefixWord ++ tailWord_1612174) baseStart_1612174 baseEnd_1612174 := by
    simpa [prefixWord, tailWord_1612174, baseEnd_1612174] using wordTrace_append hprefix tailTrace_1612174
  have hstable : (prefixWord ++ tailWord_1612174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612174).length < 2 ^ (prefixWord ++ tailWord_1612174).sum := by decide
  have hdescent : baseEnd_1612174 < baseStart_1612174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612184 : List Nat := [2, 1, 2, 5, 1, 2, 3, 1, 1, 5]
def baseStart_1612184 : Nat := 118140960795 + 1612184 * 2 ^ 59
def prefixEnd_1612184 : Nat := 4983230072969 + 3 ^ 40 * 1612184 * 2
def baseEnd_1612184 : Nat := 275941765162741852128569

theorem tailTrace_1612184 : CollatzResearch.WordTrace tailWord_1612184 prefixEnd_1612184 275941765162741852128569 := by
  unfold tailWord_1612184
  simp only [CollatzResearch.WordTrace]
  refine ⟨29400590595670090975721803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39200787460893454634295737 29400590595670090975721803)
  ·
    refine ⟨44100885893505136463582705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29400590595670090975721803 44100885893505136463582705)
    ·
      refine ⟨33075664420128852347687029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44100885893505136463582705 33075664420128852347687029)
      ·
        refine ⟨3100843539387079907595659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33075664420128852347687029 3100843539387079907595659)
        ·
          refine ⟨4651265309080619861393489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3100843539387079907595659 4651265309080619861393489)
          ·
            refine ⟨3488448981810464896045117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4651265309080619861393489 3488448981810464896045117)
            ·
              refine ⟨1308168368178924336016919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3488448981810464896045117 1308168368178924336016919)
              ·
                refine ⟨1962252552268386504025379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1308168368178924336016919 1962252552268386504025379)
                ·
                  refine ⟨2943378828402579756038069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1962252552268386504025379 2943378828402579756038069)
                  ·
                    refine ⟨275941765162741852128569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2943378828402579756038069 275941765162741852128569)
                    ·
                      rfl

theorem cell23_1612184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 1, 5].length) (baseStart_1612184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612184 prefixEnd_1612184 := by exact prefixLift 1612184
  have htrace : WordTrace (prefixWord ++ tailWord_1612184) baseStart_1612184 baseEnd_1612184 := by
    simpa [prefixWord, tailWord_1612184, baseEnd_1612184] using wordTrace_append hprefix tailTrace_1612184
  have hstable : (prefixWord ++ tailWord_1612184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612184).length < 2 ^ (prefixWord ++ tailWord_1612184).sum := by decide
  have hdescent : baseEnd_1612184 < baseStart_1612184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612197 : List Nat := [1, 3, 1, 2, 1, 1, 6, 2, 2, 4]
def baseStart_1612197 : Nat := 118140960795 + 1612197 * 2 ^ 59
def prefixEnd_1612197 : Nat := 4983230072969 + 3 ^ 40 * 1612197 * 2
def baseEnd_1612197 : Nat := 275943990245578001841049

theorem tailTrace_1612197 : CollatzResearch.WordTrace tailWord_1612197 prefixEnd_1612197 275943990245578001841049 := by
  unfold tailWord_1612197
  simp only [CollatzResearch.WordTrace]
  refine ⟨58801655340293085171666845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39201103560195390114444563 58801655340293085171666845)
  ·
    refine ⟨22050620752609906939375067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58801655340293085171666845 22050620752609906939375067)
    ·
      refine ⟨33075931128914860409062601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22050620752609906939375067 33075931128914860409062601)
      ·
        refine ⟨24806948346686145306796951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33075931128914860409062601 24806948346686145306796951)
        ·
          refine ⟨37210422520029217960195427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24806948346686145306796951 37210422520029217960195427)
          ·
            refine ⟨55815633780043826940293141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37210422520029217960195427 55815633780043826940293141)
            ·
              refine ⟨2616357833439554387826241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55815633780043826940293141 2616357833439554387826241)
              ·
                refine ⟨1962268375079665790869681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2616357833439554387826241 1962268375079665790869681)
                ·
                  refine ⟨1471701281309749343152261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1962268375079665790869681 1471701281309749343152261)
                  ·
                    refine ⟨275943990245578001841049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1471701281309749343152261 275943990245578001841049)
                    ·
                      rfl

theorem cell23_1612197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2, 4].length) (baseStart_1612197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612197 prefixEnd_1612197 := by exact prefixLift 1612197
  have htrace : WordTrace (prefixWord ++ tailWord_1612197) baseStart_1612197 baseEnd_1612197 := by
    simpa [prefixWord, tailWord_1612197, baseEnd_1612197] using wordTrace_append hprefix tailTrace_1612197
  have hstable : (prefixWord ++ tailWord_1612197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612197).length < 2 ^ (prefixWord ++ tailWord_1612197).sum := by decide
  have hdescent : baseEnd_1612197 < baseStart_1612197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612217 : List Nat := [1, 2, 1, 4, 3, 2, 2, 1, 1, 2, 4]
def baseStart_1612217 : Nat := 118140960795 + 1612217 * 2 ^ 59
def prefixEnd_1612217 : Nat := 4983230072969 + 3 ^ 40 * 1612217 * 2
def baseEnd_1612217 : Nat := 827842240349823927273055

theorem tailTrace_1612217 : CollatzResearch.WordTrace tailWord_1612217 prefixEnd_1612217 827842240349823927273055 := by
  unfold tailWord_1612217
  simp only [CollatzResearch.WordTrace]
  refine ⟨58802384800220628587394905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39201589866813752391596603 58802384800220628587394905)
  ·
    refine ⟨44101788600165471440546179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58802384800220628587394905 44101788600165471440546179)
    ·
      refine ⟨66152682900248207160819269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44101788600165471440546179 66152682900248207160819269)
      ·
        refine ⟨12403628043796538842653613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66152682900248207160819269 12403628043796538842653613)
        ·
          refine ⟨4651360516423702065995105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12403628043796538842653613 4651360516423702065995105)
          ·
            refine ⟨3488520387317776549496329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4651360516423702065995105 3488520387317776549496329)
            ·
              refine ⟨2616390290488332412122247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3488520387317776549496329 2616390290488332412122247)
              ·
                refine ⟨3924585435732498618183371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2616390290488332412122247 3924585435732498618183371)
                ·
                  refine ⟨5886878153598747927275057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3924585435732498618183371 5886878153598747927275057)
                  ·
                    refine ⟨4415158615199060945456293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5886878153598747927275057 4415158615199060945456293)
                    ·
                      refine ⟨827842240349823927273055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4415158615199060945456293 827842240349823927273055)
                      ·
                        rfl

theorem cell23_1612217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_1612217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612217 prefixEnd_1612217 := by exact prefixLift 1612217
  have htrace : WordTrace (prefixWord ++ tailWord_1612217) baseStart_1612217 baseEnd_1612217 := by
    simpa [prefixWord, tailWord_1612217, baseEnd_1612217] using wordTrace_append hprefix tailTrace_1612217
  have hstable : (prefixWord ++ tailWord_1612217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612217).length < 2 ^ (prefixWord ++ tailWord_1612217).sum := by decide
  have hdescent : baseEnd_1612217 < baseStart_1612217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612225 : List Nat := [1, 2, 7, 1, 1, 2, 1, 1, 2, 3, 2]
def baseStart_1612225 : Nat := 118140960795 + 1612225 * 2 ^ 59
def prefixEnd_1612225 : Nat := 4983230072969 + 3 ^ 40 * 1612225 * 2
def baseEnd_1612225 : Nat := 827846348195059895973019

theorem tailTrace_1612225 : CollatzResearch.WordTrace tailWord_1612225 prefixEnd_1612225 827846348195059895973019 := by
  unfold tailWord_1612225
  simp only [CollatzResearch.WordTrace]
  refine ⟨58802676584191645953686129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39201784389461097302457419 58802676584191645953686129)
  ·
    refine ⟨44102007438143734465264597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58802676584191645953686129 44102007438143734465264597)
    ·
      refine ⟨1033640799331493776529639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 44102007438143734465264597 1033640799331493776529639)
      ·
        refine ⟨1550461198997240664794459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1033640799331493776529639 1550461198997240664794459)
        ·
          refine ⟨2325691798495860997191689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1550461198997240664794459 2325691798495860997191689)
          ·
            refine ⟨1744268848871895747893767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2325691798495860997191689 1744268848871895747893767)
            ·
              refine ⟨2616403273307843621840651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1744268848871895747893767 2616403273307843621840651)
              ·
                refine ⟨3924604909961765432760977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2616403273307843621840651 3924604909961765432760977)
                ·
                  refine ⟨2943453682471324074570733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3924604909961765432760977 2943453682471324074570733)
                  ·
                    refine ⟨1103795130926746527964025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2943453682471324074570733 1103795130926746527964025)
                    ·
                      refine ⟨827846348195059895973019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1103795130926746527964025 827846348195059895973019)
                      ·
                        rfl

theorem cell23_1612225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_1612225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612225 prefixEnd_1612225 := by exact prefixLift 1612225
  have htrace : WordTrace (prefixWord ++ tailWord_1612225) baseStart_1612225 baseEnd_1612225 := by
    simpa [prefixWord, tailWord_1612225, baseEnd_1612225] using wordTrace_append hprefix tailTrace_1612225
  have hstable : (prefixWord ++ tailWord_1612225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612225).length < 2 ^ (prefixWord ++ tailWord_1612225).sum := by decide
  have hdescent : baseEnd_1612225 < baseStart_1612225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612280 : List Nat := [2, 1, 2, 1, 1, 4, 2, 2, 2, 1, 5]
def baseStart_1612280 : Nat := 118140960795 + 1612280 * 2 ^ 59
def prefixEnd_1612280 : Nat := 4983230072969 + 3 ^ 40 * 1612280 * 2
def baseEnd_1612280 : Nat := 827874589631057180785265

theorem tailTrace_1612280 : CollatzResearch.WordTrace tailWord_1612280 prefixEnd_1612280 827874589631057180785265 := by
  unfold tailWord_1612280
  simp only [CollatzResearch.WordTrace]
  refine ⟨29402341299496195173469147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39203121732661593564625529 29402341299496195173469147)
  ·
    refine ⟨44103511949244292760203721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29402341299496195173469147 44103511949244292760203721)
    ·
      refine ⟨33077633961933219570152791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44103511949244292760203721 33077633961933219570152791)
      ·
        refine ⟨49616450942899829355229187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33077633961933219570152791 49616450942899829355229187)
        ·
          refine ⟨74424676414349744032843781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49616450942899829355229187 74424676414349744032843781)
          ·
            refine ⟨13954626827690577006158209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74424676414349744032843781 13954626827690577006158209)
            ·
              refine ⟨10465970120767932754618657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13954626827690577006158209 10465970120767932754618657)
              ·
                refine ⟨7849477590575949565963993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10465970120767932754618657 7849477590575949565963993)
                ·
                  refine ⟨5887108192931962174472995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7849477590575949565963993 5887108192931962174472995)
                  ·
                    refine ⟨8830662289397943261709493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5887108192931962174472995 8830662289397943261709493)
                    ·
                      refine ⟨827874589631057180785265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8830662289397943261709493 827874589631057180785265)
                      ·
                        rfl

theorem cell23_1612280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_1612280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612280 prefixEnd_1612280 := by exact prefixLift 1612280
  have htrace : WordTrace (prefixWord ++ tailWord_1612280) baseStart_1612280 baseEnd_1612280 := by
    simpa [prefixWord, tailWord_1612280, baseEnd_1612280] using wordTrace_append hprefix tailTrace_1612280
  have hstable : (prefixWord ++ tailWord_1612280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612280).length < 2 ^ (prefixWord ++ tailWord_1612280).sum := by decide
  have hdescent : baseEnd_1612280 < baseStart_1612280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612317 : List Nat := [1, 4, 2, 2, 1, 2, 3, 1, 7]
def baseStart_1612317 : Nat := 118140960795 + 1612317 * 2 ^ 59
def prefixEnd_1612317 : Nat := 4983230072969 + 3 ^ 40 * 1612317 * 2
def baseEnd_1612317 : Nat := 91988176490585948446955

theorem tailTrace_1612317 : CollatzResearch.WordTrace tailWord_1612317 prefixEnd_1612317 91988176490585948446955 := by
  unfold tailWord_1612317
  simp only [CollatzResearch.WordTrace]
  refine ⟨58806032099858345666035205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39204021399905563777356803 58806032099858345666035205)
  ·
    refine ⟨11026131018723439812381601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58806032099858345666035205 11026131018723439812381601)
    ·
      refine ⟨8269598264042579859286201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11026131018723439812381601 8269598264042579859286201)
      ·
        refine ⟨6202198698031934894464651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8269598264042579859286201 6202198698031934894464651)
        ·
          refine ⟨9303298047047902341696977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6202198698031934894464651 9303298047047902341696977)
          ·
            refine ⟨6977473535285926756272733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9303298047047902341696977 6977473535285926756272733)
            ·
              refine ⟨2616552575732222533602275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6977473535285926756272733 2616552575732222533602275)
              ·
                refine ⟨3924828863598333800403413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2616552575732222533602275 3924828863598333800403413)
                ·
                  refine ⟨91988176490585948446955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3924828863598333800403413 91988176490585948446955)
                  ·
                    rfl

theorem cell23_1612317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 7].length) (baseStart_1612317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612317 prefixEnd_1612317 := by exact prefixLift 1612317
  have htrace : WordTrace (prefixWord ++ tailWord_1612317) baseStart_1612317 baseEnd_1612317 := by
    simpa [prefixWord, tailWord_1612317, baseEnd_1612317] using wordTrace_append hprefix tailTrace_1612317
  have hstable : (prefixWord ++ tailWord_1612317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612317).length < 2 ^ (prefixWord ++ tailWord_1612317).sum := by decide
  have hdescent : baseEnd_1612317 < baseStart_1612317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612328 : List Nat := [2, 1, 5, 2, 1, 2, 1, 3, 2, 2, 2]
def baseStart_1612328 : Nat := 118140960795 + 1612328 * 2 ^ 59
def prefixEnd_1612328 : Nat := 4983230072969 + 3 ^ 40 * 1612328 * 2
def baseEnd_1612328 : Nat := 827899236702472992985045

theorem tailTrace_1612328 : CollatzResearch.WordTrace tailWord_1612328 prefixEnd_1612328 827899236702472992985045 := by
  unfold tailWord_1612328
  simp only [CollatzResearch.WordTrace]
  refine ⟨29403216651409247272342819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39204288868545663029790425 29403216651409247272342819)
  ·
    refine ⟨44104824977113870908514229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29403216651409247272342819 44104824977113870908514229)
    ·
      refine ⟨4134827341604425397673209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44104824977113870908514229 4134827341604425397673209)
      ·
        refine ⟨3101120506203319048254907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4134827341604425397673209 3101120506203319048254907)
        ·
          refine ⟨4651680759304978572382361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3101120506203319048254907 4651680759304978572382361)
          ·
            refine ⟨3488760569478733929286771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4651680759304978572382361 3488760569478733929286771)
            ·
              refine ⟨5233140854218100893930157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3488760569478733929286771 5233140854218100893930157)
              ·
                refine ⟨1962427820331787835223809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5233140854218100893930157 1962427820331787835223809)
                ·
                  refine ⟨1471820865248840876417857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1962427820331787835223809 1471820865248840876417857)
                  ·
                    refine ⟨1103865648936630657313393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1471820865248840876417857 1103865648936630657313393)
                    ·
                      refine ⟨827899236702472992985045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1103865648936630657313393 827899236702472992985045)
                      ·
                        rfl

theorem cell23_1612328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_1612328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612328 prefixEnd_1612328 := by exact prefixLift 1612328
  have htrace : WordTrace (prefixWord ++ tailWord_1612328) baseStart_1612328 baseEnd_1612328 := by
    simpa [prefixWord, tailWord_1612328, baseEnd_1612328] using wordTrace_append hprefix tailTrace_1612328
  have hstable : (prefixWord ++ tailWord_1612328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612328).length < 2 ^ (prefixWord ++ tailWord_1612328).sum := by decide
  have hdescent : baseEnd_1612328 < baseStart_1612328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612367 : List Nat := [1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 4]
def baseStart_1612367 : Nat := 118140960795 + 1612367 * 2 ^ 59
def prefixEnd_1612367 : Nat := 4983230072969 + 3 ^ 40 * 1612367 * 2
def baseEnd_1612367 : Nat := 827919262447998340397365

theorem tailTrace_1612367 : CollatzResearch.WordTrace tailWord_1612367 prefixEnd_1612367 827919262447998340397365 := by
  unfold tailWord_1612367
  simp only [CollatzResearch.WordTrace]
  refine ⟨58807855749677204205355355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39205237166451469470236903 58807855749677204205355355)
  ·
    refine ⟨88211783624515806308033033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58807855749677204205355355 88211783624515806308033033)
    ·
      refine ⟨66158837718386854731024775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88211783624515806308033033 66158837718386854731024775)
      ·
        refine ⟨99238256577580282096537163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66158837718386854731024775 99238256577580282096537163)
        ·
          refine ⟨148857384866370423144805745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99238256577580282096537163 148857384866370423144805745)
          ·
            refine ⟨111643038649777817358604309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148857384866370423144805745 111643038649777817358604309)
            ·
              refine ⟨5233267436708335188684577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111643038649777817358604309 5233267436708335188684577)
              ·
                refine ⟨3924950577531251391513433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5233267436708335188684577 3924950577531251391513433)
                ·
                  refine ⟨2943712933148438543635075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3924950577531251391513433 2943712933148438543635075)
                  ·
                    refine ⟨4415569399722657815452613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2943712933148438543635075 4415569399722657815452613)
                    ·
                      refine ⟨827919262447998340397365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4415569399722657815452613 827919262447998340397365)
                      ·
                        rfl

theorem cell23_1612367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 4].length) (baseStart_1612367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612367 prefixEnd_1612367 := by exact prefixLift 1612367
  have htrace : WordTrace (prefixWord ++ tailWord_1612367) baseStart_1612367 baseEnd_1612367 := by
    simpa [prefixWord, tailWord_1612367, baseEnd_1612367] using wordTrace_append hprefix tailTrace_1612367
  have hstable : (prefixWord ++ tailWord_1612367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612367).length < 2 ^ (prefixWord ++ tailWord_1612367).sum := by decide
  have hdescent : baseEnd_1612367 < baseStart_1612367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612387 : List Nat := [1, 1, 1, 5, 1, 2, 2, 2, 1, 4, 3]
def baseStart_1612387 : Nat := 118140960795 + 1612387 * 2 ^ 59
def prefixEnd_1612387 : Nat := 4983230072969 + 3 ^ 40 * 1612387 * 2
def baseEnd_1612387 : Nat := 827929532061088262147273

theorem tailTrace_1612387 : CollatzResearch.WordTrace tailWord_1612387 prefixEnd_1612387 827929532061088262147273 := by
  unfold tailWord_1612387
  simp only [CollatzResearch.WordTrace]
  refine ⟨58808585209604747621083415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39205723473069831747388943 58808585209604747621083415)
  ·
    refine ⟨88212877814407121431625123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58808585209604747621083415 88212877814407121431625123)
    ·
      refine ⟨132319316721610682147437685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88212877814407121431625123 132319316721610682147437685)
      ·
        refine ⟨12404935942651001451322283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132319316721610682147437685 12404935942651001451322283)
        ·
          refine ⟨18607403913976502176983425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12404935942651001451322283 18607403913976502176983425)
          ·
            refine ⟨13955552935482376632737569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18607403913976502176983425 13955552935482376632737569)
            ·
              refine ⟨10466664701611782474553177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13955552935482376632737569 10466664701611782474553177)
              ·
                refine ⟨7849998526208836855914883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10466664701611782474553177 7849998526208836855914883)
                ·
                  refine ⟨11774997789313255283872325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7849998526208836855914883 11774997789313255283872325)
                  ·
                    refine ⟨2207812085496235365726061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11774997789313255283872325 2207812085496235365726061)
                    ·
                      refine ⟨827929532061088262147273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2207812085496235365726061 827929532061088262147273)
                      ·
                        rfl

theorem cell23_1612387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_1612387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612387 prefixEnd_1612387 := by exact prefixLift 1612387
  have htrace : WordTrace (prefixWord ++ tailWord_1612387) baseStart_1612387 baseEnd_1612387 := by
    simpa [prefixWord, tailWord_1612387, baseEnd_1612387] using wordTrace_append hprefix tailTrace_1612387
  have hstable : (prefixWord ++ tailWord_1612387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612387).length < 2 ^ (prefixWord ++ tailWord_1612387).sum := by decide
  have hdescent : baseEnd_1612387 < baseStart_1612387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612394 : List Nat := [3, 1, 3, 2, 1, 1, 3, 2, 3, 4]
def baseStart_1612394 : Nat := 118140960795 + 1612394 * 2 ^ 59
def prefixEnd_1612394 : Nat := 4983230072969 + 3 ^ 40 * 1612394 * 2
def baseEnd_1612394 : Nat := 275977708808556578253247

theorem tailTrace_1612394 : CollatzResearch.WordTrace tailWord_1612394 prefixEnd_1612394 275977708808556578253247 := by
  unfold tailWord_1612394
  simp only [CollatzResearch.WordTrace]
  refine ⟨14702210130144846954147059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39205893680386258544392157 14702210130144846954147059)
  ·
    refine ⟨22053315195217270431220589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14702210130144846954147059 22053315195217270431220589)
    ·
      refine ⟨8269993198206476411707721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22053315195217270431220589 8269993198206476411707721)
      ·
        refine ⟨6202494898654857308780791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8269993198206476411707721 6202494898654857308780791)
        ·
          refine ⟨9303742347982285963171187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6202494898654857308780791 9303742347982285963171187)
          ·
            refine ⟨13955613521973428944756781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9303742347982285963171187 13955613521973428944756781)
            ·
              refine ⟨5233355070740035854283793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13955613521973428944756781 5233355070740035854283793)
              ·
                refine ⟨3925016303055026890712845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5233355070740035854283793 3925016303055026890712845)
                ·
                  refine ⟨1471881113645635084017317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3925016303055026890712845 1471881113645635084017317)
                  ·
                    refine ⟨275977708808556578253247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1471881113645635084017317 275977708808556578253247)
                    ·
                      rfl

theorem cell23_1612394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_1612394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612394 prefixEnd_1612394 := by exact prefixLift 1612394
  have htrace : WordTrace (prefixWord ++ tailWord_1612394) baseStart_1612394 baseEnd_1612394 := by
    simpa [prefixWord, tailWord_1612394, baseEnd_1612394] using wordTrace_append hprefix tailTrace_1612394
  have hstable : (prefixWord ++ tailWord_1612394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612394).length < 2 ^ (prefixWord ++ tailWord_1612394).sum := by decide
  have hdescent : baseEnd_1612394 < baseStart_1612394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612461 : List Nat := [1, 5, 2, 1, 1, 2, 2, 1, 1, 5, 2]
def baseStart_1612461 : Nat := 118140960795 + 1612461 * 2 ^ 59
def prefixEnd_1612461 : Nat := 4983230072969 + 3 ^ 40 * 1612461 * 2
def baseEnd_1612461 : Nat := 827967529629520972621933

theorem tailTrace_1612461 : CollatzResearch.WordTrace tailWord_1612461 prefixEnd_1612461 827967529629520972621933 := by
  unfold tailWord_1612461
  simp only [CollatzResearch.WordTrace]
  refine ⟨58811284211336658259277237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39207522807557772172851491 58811284211336658259277237)
  ·
    refine ⟨5513557894812811711807241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58811284211336658259277237 5513557894812811711807241)
    ·
      refine ⟨4135168421109608783855431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5513557894812811711807241 4135168421109608783855431)
      ·
        refine ⟨6202752631664413175783147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4135168421109608783855431 6202752631664413175783147)
        ·
          refine ⟨9304128947496619763674721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6202752631664413175783147 9304128947496619763674721)
          ·
            refine ⟨6978096710622464822756041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9304128947496619763674721 6978096710622464822756041)
            ·
              refine ⟨5233572532966848617067031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6978096710622464822756041 5233572532966848617067031)
              ·
                refine ⟨7850358799450272925600547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5233572532966848617067031 7850358799450272925600547)
                ·
                  refine ⟨11775538199175409388400821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7850358799450272925600547 11775538199175409388400821)
                  ·
                    refine ⟨1103956706172694630162577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11775538199175409388400821 1103956706172694630162577)
                    ·
                      refine ⟨827967529629520972621933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1103956706172694630162577 827967529629520972621933)
                      ·
                        rfl

theorem cell23_1612461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_1612461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612461 prefixEnd_1612461 := by exact prefixLift 1612461
  have htrace : WordTrace (prefixWord ++ tailWord_1612461) baseStart_1612461 baseEnd_1612461 := by
    simpa [prefixWord, tailWord_1612461, baseEnd_1612461] using wordTrace_append hprefix tailTrace_1612461
  have hstable : (prefixWord ++ tailWord_1612461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612461).length < 2 ^ (prefixWord ++ tailWord_1612461).sum := by decide
  have hdescent : baseEnd_1612461 < baseStart_1612461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612474 : List Nat := [3, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4]
def baseStart_1612474 : Nat := 118140960795 + 1612474 * 2 ^ 59
def prefixEnd_1612474 : Nat := 4983230072969 + 3 ^ 40 * 1612474 * 2
def baseEnd_1612474 : Nat := 827974204878029421759373

theorem tailTrace_1612474 : CollatzResearch.WordTrace tailWord_1612474 prefixEnd_1612474 827974204878029421759373 := by
  unfold tailWord_1612474
  simp only [CollatzResearch.WordTrace]
  refine ⟨14702939590072390369875119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39207838906859707653000317 14702939590072390369875119)
  ·
    refine ⟨22054409385108585554812679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14702939590072390369875119 22054409385108585554812679)
    ·
      refine ⟨33081614077662878332219019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22054409385108585554812679 33081614077662878332219019)
      ·
        refine ⟨49622421116494317498328529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33081614077662878332219019 49622421116494317498328529)
        ·
          refine ⟨37216815837370738123746397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49622421116494317498328529 37216815837370738123746397)
          ·
            refine ⟨13956305939014026796404899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37216815837370738123746397 13956305939014026796404899)
            ·
              refine ⟨20934458908521040194607349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13956305939014026796404899 20934458908521040194607349)
              ·
                refine ⟨1962605522673847518244439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20934458908521040194607349 1962605522673847518244439)
                ·
                  refine ⟨2943908284010771277366659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1962605522673847518244439 2943908284010771277366659)
                  ·
                    refine ⟨4415862426016156916049989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2943908284010771277366659 4415862426016156916049989)
                    ·
                      refine ⟨827974204878029421759373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4415862426016156916049989 827974204878029421759373)
                      ·
                        rfl

theorem cell23_1612474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4].length) (baseStart_1612474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612474 prefixEnd_1612474 := by exact prefixLift 1612474
  have htrace : WordTrace (prefixWord ++ tailWord_1612474) baseStart_1612474 baseEnd_1612474 := by
    simpa [prefixWord, tailWord_1612474, baseEnd_1612474] using wordTrace_append hprefix tailTrace_1612474
  have hstable : (prefixWord ++ tailWord_1612474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612474).length < 2 ^ (prefixWord ++ tailWord_1612474).sum := by decide
  have hdescent : baseEnd_1612474 < baseStart_1612474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612487 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 4]
def baseStart_1612487 : Nat := 118140960795 + 1612487 * 2 ^ 59
def prefixEnd_1612487 : Nat := 4983230072969 + 3 ^ 40 * 1612487 * 2
def baseEnd_1612487 : Nat := 827980880126537870896813

theorem tailTrace_1612487 : CollatzResearch.WordTrace tailWord_1612487 prefixEnd_1612487 827980880126537870896813 := by
  unfold tailWord_1612487
  simp only [CollatzResearch.WordTrace]
  refine ⟨58812232509242464699723715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39208155006161643133149143 58812232509242464699723715)
  ·
    refine ⟨88218348763863697049585573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58812232509242464699723715 88218348763863697049585573)
    ·
      refine ⟨16540940393224443196797295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88218348763863697049585573 16540940393224443196797295)
      ·
        refine ⟨24811410589836664795195943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16540940393224443196797295 24811410589836664795195943)
        ·
          refine ⟨37217115884754997192793915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24811410589836664795195943 37217115884754997192793915)
          ·
            refine ⟨55825673827132495789190873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37217115884754997192793915 55825673827132495789190873)
            ·
              refine ⟨41869255370349371841893155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55825673827132495789190873 41869255370349371841893155)
              ·
                refine ⟨62803883055524057762839733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41869255370349371841893155 62803883055524057762839733)
                ·
                  refine ⟨5887864036455380415266225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62803883055524057762839733 5887864036455380415266225)
                  ·
                    refine ⟨4415898027341535311449669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5887864036455380415266225 4415898027341535311449669)
                    ·
                      refine ⟨827980880126537870896813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4415898027341535311449669 827980880126537870896813)
                      ·
                        rfl

theorem cell23_1612487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_1612487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612487 prefixEnd_1612487 := by exact prefixLift 1612487
  have htrace : WordTrace (prefixWord ++ tailWord_1612487) baseStart_1612487 baseEnd_1612487 := by
    simpa [prefixWord, tailWord_1612487, baseEnd_1612487] using wordTrace_append hprefix tailTrace_1612487
  have hstable : (prefixWord ++ tailWord_1612487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612487).length < 2 ^ (prefixWord ++ tailWord_1612487).sum := by decide
  have hdescent : baseEnd_1612487 < baseStart_1612487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612494 : List Nat := [4, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5]
def baseStart_1612494 : Nat := 118140960795 + 1612494 * 2 ^ 59
def prefixEnd_1612494 : Nat := 4983230072969 + 3 ^ 40 * 1612494 * 2
def baseEnd_1612494 : Nat := 827984474491119343509281

theorem tailTrace_1612494 : CollatzResearch.WordTrace tailWord_1612494 prefixEnd_1612494 827984474491119343509281 := by
  unfold tailWord_1612494
  simp only [CollatzResearch.WordTrace]
  refine ⟨7351560977527138111903567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39208325213478069930152357 7351560977527138111903567)
  ·
    refine ⟨11027341466290707167855351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7351560977527138111903567 11027341466290707167855351)
    ·
      refine ⟨16541012199436060751783027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11027341466290707167855351 16541012199436060751783027)
      ·
        refine ⟨24811518299154091127674541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16541012199436060751783027 24811518299154091127674541)
        ·
          refine ⟨9304319362182784172877953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24811518299154091127674541 9304319362182784172877953)
          ·
            refine ⟨6978239521637088129658465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9304319362182784172877953 6978239521637088129658465)
            ·
              refine ⟨5233679641227816097243849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6978239521637088129658465 5233679641227816097243849)
              ·
                refine ⟨3925259730920862072932887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5233679641227816097243849 3925259730920862072932887)
                ·
                  refine ⟨5887889596381293109399331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3925259730920862072932887 5887889596381293109399331)
                  ·
                    refine ⟨8831834394571939664098997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5887889596381293109399331 8831834394571939664098997)
                    ·
                      refine ⟨827984474491119343509281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8831834394571939664098997 827984474491119343509281)
                      ·
                        rfl

theorem cell23_1612494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_1612494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612494 prefixEnd_1612494 := by exact prefixLift 1612494
  have htrace : WordTrace (prefixWord ++ tailWord_1612494) baseStart_1612494 baseEnd_1612494 := by
    simpa [prefixWord, tailWord_1612494, baseEnd_1612494] using wordTrace_append hprefix tailTrace_1612494
  have hstable : (prefixWord ++ tailWord_1612494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612494).length < 2 ^ (prefixWord ++ tailWord_1612494).sum := by decide
  have hdescent : baseEnd_1612494 < baseStart_1612494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612497 : List Nat := [1, 2, 2, 1, 2, 3, 4, 8]
def baseStart_1612497 : Nat := 118140960795 + 1612497 * 2 ^ 59
def prefixEnd_1612497 : Nat := 4983230072969 + 3 ^ 40 * 1612497 * 2
def baseEnd_1612497 : Nat := 30666148701225290065621

theorem tailTrace_1612497 : CollatzResearch.WordTrace tailWord_1612497 prefixEnd_1612497 30666148701225290065621 := by
  unfold tailWord_1612497
  simp only [CollatzResearch.WordTrace]
  refine ⟨58812597239206236407587745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39208398159470824271725163 58812597239206236407587745)
  ·
    refine ⟨44109447929404677305690809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58812597239206236407587745 44109447929404677305690809)
    ·
      refine ⟨33082085947053507979268107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44109447929404677305690809 33082085947053507979268107)
      ·
        refine ⟨49623128920580261968902161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33082085947053507979268107 49623128920580261968902161)
        ·
          refine ⟨37217346690435196476676621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49623128920580261968902161 37217346690435196476676621)
          ·
            refine ⟨13956505008913198678753733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37217346690435196476676621 13956505008913198678753733)
            ·
              refine ⟨2616844689171224752266325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13956505008913198678753733 2616844689171224752266325)
              ·
                refine ⟨30666148701225290065621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2616844689171224752266325 30666148701225290065621)
                ·
                  rfl

theorem cell23_1612497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 8].length) (baseStart_1612497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612497 prefixEnd_1612497 := by exact prefixLift 1612497
  have htrace : WordTrace (prefixWord ++ tailWord_1612497) baseStart_1612497 baseEnd_1612497 := by
    simpa [prefixWord, tailWord_1612497, baseEnd_1612497] using wordTrace_append hprefix tailTrace_1612497
  have hstable : (prefixWord ++ tailWord_1612497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612497).length < 2 ^ (prefixWord ++ tailWord_1612497).sum := by decide
  have hdescent : baseEnd_1612497 < baseStart_1612497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612508 : List Nat := [2, 2, 5, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_1612508 : Nat := 118140960795 + 1612508 * 2 ^ 59
def prefixEnd_1612508 : Nat := 4983230072969 + 3 ^ 40 * 1612508 * 2
def baseEnd_1612508 : Nat := 827991663220282288734217

theorem tailTrace_1612508 : CollatzResearch.WordTrace tailWord_1612508 prefixEnd_1612508 827991663220282288734217 := by
  unfold tailWord_1612508
  simp only [CollatzResearch.WordTrace]
  refine ⟨29406499221083192643119089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39208665628110923524158785 29406499221083192643119089)
  ·
    refine ⟨22054874415812394482339317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29406499221083192643119089 22054874415812394482339317)
    ·
      refine ⟨2067644476482411982719311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22054874415812394482339317 2067644476482411982719311)
      ·
        refine ⟨3101466714723617974078967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2067644476482411982719311 3101466714723617974078967)
        ·
          refine ⟨4652200072085426961118451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3101466714723617974078967 4652200072085426961118451)
          ·
            refine ⟨6978300108128140441677677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4652200072085426961118451 6978300108128140441677677)
            ·
              refine ⟨2616862540548052665629129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6978300108128140441677677 2616862540548052665629129)
              ·
                refine ⟨1962646905411039499221847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2616862540548052665629129 1962646905411039499221847)
                ·
                  refine ⟨2943970358116559248832771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1962646905411039499221847 2943970358116559248832771)
                  ·
                    refine ⟨4415955537174838873249157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2943970358116559248832771 4415955537174838873249157)
                    ·
                      refine ⟨827991663220282288734217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4415955537174838873249157 827991663220282288734217)
                      ·
                        rfl

theorem cell23_1612508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_1612508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612508 prefixEnd_1612508 := by exact prefixLift 1612508
  have htrace : WordTrace (prefixWord ++ tailWord_1612508) baseStart_1612508 baseEnd_1612508 := by
    simpa [prefixWord, tailWord_1612508, baseEnd_1612508] using wordTrace_append hprefix tailTrace_1612508
  have hstable : (prefixWord ++ tailWord_1612508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612508).length < 2 ^ (prefixWord ++ tailWord_1612508).sum := by decide
  have hdescent : baseEnd_1612508 < baseStart_1612508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612511 : List Nat := [1, 1, 2, 3, 2, 3, 3, 2, 1, 2, 3]
def baseStart_1612511 : Nat := 118140960795 + 1612511 * 2 ^ 59
def prefixEnd_1612511 : Nat := 4983230072969 + 3 ^ 40 * 1612511 * 2
def baseEnd_1612511 : Nat := 827993203662245776996703

theorem tailTrace_1612511 : CollatzResearch.WordTrace tailWord_1612511 prefixEnd_1612511 827993203662245776996703 := by
  unfold tailWord_1612511
  simp only [CollatzResearch.WordTrace]
  refine ⟨58813107861155516798597387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39208738574103677865731591 58813107861155516798597387)
  ·
    refine ⟨88219661791733275197896081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58813107861155516798597387 88219661791733275197896081)
    ·
      refine ⟨66164746343799956398422061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88219661791733275197896081 66164746343799956398422061)
      ·
        refine ⟨24811779878924983649408273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66164746343799956398422061 24811779878924983649408273)
        ·
          refine ⟨18608834909193737737056205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24811779878924983649408273 18608834909193737737056205)
          ·
            refine ⟨6978313090947651651396077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18608834909193737737056205 6978313090947651651396077)
            ·
              refine ⟨2616867409105369369273529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6978313090947651651396077 2616867409105369369273529)
              ·
                refine ⟨1962650556829027026955147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2616867409105369369273529 1962650556829027026955147)
                ·
                  refine ⟨2943975835243540540432721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1962650556829027026955147 2943975835243540540432721)
                  ·
                    refine ⟨2207981876432655405324541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2943975835243540540432721 2207981876432655405324541)
                    ·
                      refine ⟨827993203662245776996703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2207981876432655405324541 827993203662245776996703)
                      ·
                        rfl

theorem cell23_1612511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_1612511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612511 prefixEnd_1612511 := by exact prefixLift 1612511
  have htrace : WordTrace (prefixWord ++ tailWord_1612511) baseStart_1612511 baseEnd_1612511 := by
    simpa [prefixWord, tailWord_1612511, baseEnd_1612511] using wordTrace_append hprefix tailTrace_1612511
  have hstable : (prefixWord ++ tailWord_1612511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612511).length < 2 ^ (prefixWord ++ tailWord_1612511).sum := by decide
  have hdescent : baseEnd_1612511 < baseStart_1612511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612525 : List Nat := [1, 5, 1, 2, 1, 1, 2, 5, 1, 2, 2]
def baseStart_1612525 : Nat := 118140960795 + 1612525 * 2 ^ 59
def prefixEnd_1612525 : Nat := 4983230072969 + 3 ^ 40 * 1612525 * 2
def baseEnd_1612525 : Nat := 828000392391408722221639

theorem tailTrace_1612525 : CollatzResearch.WordTrace tailWord_1612525 prefixEnd_1612525 828000392391408722221639 := by
  unfold tailWord_1612525
  simp only [CollatzResearch.WordTrace]
  refine ⟨58813618483104797189607029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39209078988736531459738019 58813618483104797189607029)
  ·
    refine ⟨5513776732791074736525659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58813618483104797189607029 5513776732791074736525659)
    ·
      refine ⟨8270665099186612104788489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5513776732791074736525659 8270665099186612104788489)
      ·
        refine ⟨6202998824389959078591367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8270665099186612104788489 6202998824389959078591367)
        ·
          refine ⟨9304498236584938617887051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6202998824389959078591367 9304498236584938617887051)
          ·
            refine ⟨13956747354877407926830577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9304498236584938617887051 13956747354877407926830577)
            ·
              refine ⟨10467560516158055945122933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13956747354877407926830577 10467560516158055945122933)
              ·
                refine ⟨981333798389817744855275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10467560516158055945122933 981333798389817744855275)
                ·
                  refine ⟨1472000697584726617282913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 981333798389817744855275 1472000697584726617282913)
                  ·
                    refine ⟨1104000523188544962962185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1472000697584726617282913 1104000523188544962962185)
                    ·
                      refine ⟨828000392391408722221639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1104000523188544962962185 828000392391408722221639)
                      ·
                        rfl

theorem cell23_1612525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_1612525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612525 prefixEnd_1612525 := by exact prefixLift 1612525
  have htrace : WordTrace (prefixWord ++ tailWord_1612525) baseStart_1612525 baseEnd_1612525 := by
    simpa [prefixWord, tailWord_1612525, baseEnd_1612525] using wordTrace_append hprefix tailTrace_1612525
  have hstable : (prefixWord ++ tailWord_1612525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612525).length < 2 ^ (prefixWord ++ tailWord_1612525).sum := by decide
  have hdescent : baseEnd_1612525 < baseStart_1612525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612537 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 2, 2, 5]
def baseStart_1612537 : Nat := 118140960795 + 1612537 * 2 ^ 59
def prefixEnd_1612537 : Nat := 4983230072969 + 3 ^ 40 * 1612537 * 2
def baseEnd_1612537 : Nat := 828006554159262675271583

theorem tailTrace_1612537 : CollatzResearch.WordTrace tailWord_1612537 prefixEnd_1612537 828006554159262675271583 := by
  unfold tailWord_1612537
  simp only [CollatzResearch.WordTrace]
  refine ⟨58814056159061323239043865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39209370772707548826029243 58814056159061323239043865)
  ·
    refine ⟨44110542119295992429282899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58814056159061323239043865 44110542119295992429282899)
    ·
      refine ⟨66165813178943988643924349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44110542119295992429282899 66165813178943988643924349)
      ·
        refine ⟨24812179942103995741471631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66165813178943988643924349 24812179942103995741471631)
        ·
          refine ⟨37218269913155993612207447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24812179942103995741471631 37218269913155993612207447)
          ·
            refine ⟨55827404869733990418311171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37218269913155993612207447 55827404869733990418311171)
            ·
              refine ⟨83741107304600985627466757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55827404869733990418311171 83741107304600985627466757)
              ·
                refine ⟨15701457619612684805150017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83741107304600985627466757 15701457619612684805150017)
                ·
                  refine ⟨11776093214709513603862513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15701457619612684805150017 11776093214709513603862513)
                  ·
                    refine ⟨8832069911032135202896885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11776093214709513603862513 8832069911032135202896885)
                    ·
                      refine ⟨828006554159262675271583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8832069911032135202896885 828006554159262675271583)
                      ·
                        rfl

theorem cell23_1612537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_1612537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612537 prefixEnd_1612537 := by exact prefixLift 1612537
  have htrace : WordTrace (prefixWord ++ tailWord_1612537) baseStart_1612537 baseEnd_1612537 := by
    simpa [prefixWord, tailWord_1612537, baseEnd_1612537] using wordTrace_append hprefix tailTrace_1612537
  have hstable : (prefixWord ++ tailWord_1612537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612537).length < 2 ^ (prefixWord ++ tailWord_1612537).sum := by decide
  have hdescent : baseEnd_1612537 < baseStart_1612537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612542 : List Nat := [4, 2, 2, 1, 2, 2, 1, 4, 1, 2, 2]
def baseStart_1612542 : Nat := 118140960795 + 1612542 * 2 ^ 59
def prefixEnd_1612542 : Nat := 4983230072969 + 3 ^ 40 * 1612542 * 2
def baseEnd_1612542 : Nat := 828009121562535155709061

theorem tailTrace_1612542 : CollatzResearch.WordTrace tailWord_1612542 prefixEnd_1612542 828009121562535155709061 := by
  unfold tailWord_1612542
  simp only [CollatzResearch.WordTrace]
  refine ⟨7351779815505401136621985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39209492349362139395317253 7351779815505401136621985)
  ·
    refine ⟨5513834861629050852466489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7351779815505401136621985 5513834861629050852466489)
    ·
      refine ⟨4135376146221788139349867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5513834861629050852466489 4135376146221788139349867)
      ·
        refine ⟨6203064219332682209024801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4135376146221788139349867 6203064219332682209024801)
        ·
          refine ⟨4652298164499511656768601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6203064219332682209024801 4652298164499511656768601)
          ·
            refine ⟨3489223623374633742576451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4652298164499511656768601 3489223623374633742576451)
            ·
              refine ⟨5233835435061950613864677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489223623374633742576451 5233835435061950613864677)
              ·
                refine ⟨981344144074115740099627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5233835435061950613864677 981344144074115740099627)
                ·
                  refine ⟨1472016216111173610149441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 981344144074115740099627 1472016216111173610149441)
                  ·
                    refine ⟨1104012162083380207612081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1472016216111173610149441 1104012162083380207612081)
                    ·
                      refine ⟨828009121562535155709061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1104012162083380207612081 828009121562535155709061)
                      ·
                        rfl

theorem cell23_1612542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_1612542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612542 prefixEnd_1612542 := by exact prefixLift 1612542
  have htrace : WordTrace (prefixWord ++ tailWord_1612542) baseStart_1612542 baseEnd_1612542 := by
    simpa [prefixWord, tailWord_1612542, baseEnd_1612542] using wordTrace_append hprefix tailTrace_1612542
  have hstable : (prefixWord ++ tailWord_1612542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612542).length < 2 ^ (prefixWord ++ tailWord_1612542).sum := by decide
  have hdescent : baseEnd_1612542 < baseStart_1612542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612581 : List Nat := [1, 3, 1, 2, 3, 1, 1, 4, 1, 4, 2]
def baseStart_1612581 : Nat := 118140960795 + 1612581 * 2 ^ 59
def prefixEnd_1612581 : Nat := 4983230072969 + 3 ^ 40 * 1612581 * 2
def baseEnd_1612581 : Nat := 828029147308060503121381

theorem tailTrace_1612581 : CollatzResearch.WordTrace tailWord_1612581 prefixEnd_1612581 828029147308060503121381 := by
  unfold tailWord_1612581
  simp only [CollatzResearch.WordTrace]
  refine ⟨58815660970901918753645597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39210440647267945835763731 58815660970901918753645597)
  ·
    refine ⟨22055872864088219532617099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58815660970901918753645597 22055872864088219532617099)
    ·
      refine ⟨33083809296132329298925649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22055872864088219532617099 33083809296132329298925649)
      ·
        refine ⟨24812856972099246974194237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33083809296132329298925649 24812856972099246974194237)
        ·
          refine ⟨9304821364537217615322839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24812856972099246974194237 9304821364537217615322839)
          ·
            refine ⟨13957232046805826422984259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9304821364537217615322839 13957232046805826422984259)
            ·
              refine ⟨20935848070208739634476389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13957232046805826422984259 20935848070208739634476389)
              ·
                refine ⟨3925471513164138681464323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20935848070208739634476389 3925471513164138681464323)
                ·
                  refine ⟨5888207269746208022196485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3925471513164138681464323 5888207269746208022196485)
                  ·
                    refine ⟨1104038863077414004161841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5888207269746208022196485 1104038863077414004161841)
                    ·
                      refine ⟨828029147308060503121381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1104038863077414004161841 828029147308060503121381)
                      ·
                        rfl

theorem cell23_1612581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 4, 2].length) (baseStart_1612581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612581 prefixEnd_1612581 := by exact prefixLift 1612581
  have htrace : WordTrace (prefixWord ++ tailWord_1612581) baseStart_1612581 baseEnd_1612581 := by
    simpa [prefixWord, tailWord_1612581, baseEnd_1612581] using wordTrace_append hprefix tailTrace_1612581
  have hstable : (prefixWord ++ tailWord_1612581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612581).length < 2 ^ (prefixWord ++ tailWord_1612581).sum := by decide
  have hdescent : baseEnd_1612581 < baseStart_1612581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612584 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_1612584 : Nat := 118140960795 + 1612584 * 2 ^ 59
def prefixEnd_1612584 : Nat := 4983230072969 + 3 ^ 40 * 1612584 * 2
def baseEnd_1612584 : Nat := 828030687750023991383867

theorem tailTrace_1612584 : CollatzResearch.WordTrace tailWord_1612584 prefixEnd_1612584 828030687750023991383867 := by
  unfold tailWord_1612584
  simp only [CollatzResearch.WordTrace]
  refine ⟨29407885194945525133002403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39210513593260700177336537 29407885194945525133002403)
  ·
    refine ⟨44111827792418287699503605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29407885194945525133002403 44111827792418287699503605)
    ·
      refine ⟨4135483855539214471828463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44111827792418287699503605 4135483855539214471828463)
      ·
        refine ⟨6203225783308821707742695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4135483855539214471828463 6203225783308821707742695)
        ·
          refine ⟨9304838674963232561614043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6203225783308821707742695 9304838674963232561614043)
          ·
            refine ⟨13957258012444848842421065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9304838674963232561614043 13957258012444848842421065)
            ·
              refine ⟨10467943509333636631815799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13957258012444848842421065 10467943509333636631815799)
              ·
                refine ⟨15701915264000454947723699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10467943509333636631815799 15701915264000454947723699)
                ·
                  refine ⟨23552872896000682421585549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15701915264000454947723699 23552872896000682421585549)
                  ·
                    refine ⟨8832327336000255908094581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23552872896000682421585549 8832327336000255908094581)
                    ·
                      refine ⟨828030687750023991383867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8832327336000255908094581 828030687750023991383867)
                      ·
                        rfl

theorem cell23_1612584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_1612584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612584 prefixEnd_1612584 := by exact prefixLift 1612584
  have htrace : WordTrace (prefixWord ++ tailWord_1612584) baseStart_1612584 baseEnd_1612584 := by
    simpa [prefixWord, tailWord_1612584, baseEnd_1612584] using wordTrace_append hprefix tailTrace_1612584
  have hstable : (prefixWord ++ tailWord_1612584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612584).length < 2 ^ (prefixWord ++ tailWord_1612584).sum := by decide
  have hdescent : baseEnd_1612584 < baseStart_1612584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612594 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4]
def baseStart_1612594 : Nat := 118140960795 + 1612594 * 2 ^ 59
def prefixEnd_1612594 : Nat := 4983230072969 + 3 ^ 40 * 1612594 * 2
def baseEnd_1612594 : Nat := 828035822556568952258821

theorem tailTrace_1612594 : CollatzResearch.WordTrace tailWord_1612594 prefixEnd_1612594 828035822556568952258821 := by
  unfold tailWord_1612594
  simp only [CollatzResearch.WordTrace]
  refine ⟨14704033779963705493467209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39210756746569881315912557 14704033779963705493467209)
  ·
    refine ⟨11028025334972779120100407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14704033779963705493467209 11028025334972779120100407)
    ·
      refine ⟨16542038002459168680150611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11028025334972779120100407 16542038002459168680150611)
      ·
        refine ⟨24813057003688753020225917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16542038002459168680150611 24813057003688753020225917)
        ·
          refine ⟨9304896376383282382584719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24813057003688753020225917 9304896376383282382584719)
          ·
            refine ⟨13957344564574923573877079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9304896376383282382584719 13957344564574923573877079)
            ·
              refine ⟨20936016846862385360815619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13957344564574923573877079 20936016846862385360815619)
              ·
                refine ⟨31404025270293578041223429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20936016846862385360815619 31404025270293578041223429)
                ·
                  refine ⟨5888254738180045882729393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31404025270293578041223429 5888254738180045882729393)
                  ·
                    refine ⟨4416191053635034412047045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5888254738180045882729393 4416191053635034412047045)
                    ·
                      refine ⟨828035822556568952258821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4416191053635034412047045 828035822556568952258821)
                      ·
                        rfl

theorem cell23_1612594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_1612594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612594 prefixEnd_1612594 := by exact prefixLift 1612594
  have htrace : WordTrace (prefixWord ++ tailWord_1612594) baseStart_1612594 baseEnd_1612594 := by
    simpa [prefixWord, tailWord_1612594, baseEnd_1612594] using wordTrace_append hprefix tailTrace_1612594
  have hstable : (prefixWord ++ tailWord_1612594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612594).length < 2 ^ (prefixWord ++ tailWord_1612594).sum := by decide
  have hdescent : baseEnd_1612594 < baseStart_1612594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612634 : List Nat := [3, 1, 1, 2, 1, 4, 2, 1, 1, 7]
def baseStart_1612634 : Nat := 118140960795 + 1612634 * 2 ^ 59
def prefixEnd_1612634 : Nat := 4983230072969 + 3 ^ 40 * 1612634 * 2
def baseEnd_1612634 : Nat := 276018787260916265252879

theorem tailTrace_1612634 : CollatzResearch.WordTrace tailWord_1612634 prefixEnd_1612634 276018787260916265252879 := by
  unfold tailWord_1612634
  simp only [CollatzResearch.WordTrace]
  refine ⟨14704398509927477201331239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39211729359806605870216637 14704398509927477201331239)
  ·
    refine ⟨22056597764891215801996859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14704398509927477201331239 22056597764891215801996859)
    ·
      refine ⟨33084896647336823702995289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22056597764891215801996859 33084896647336823702995289)
      ·
        refine ⟨24813672485502617777246467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33084896647336823702995289 24813672485502617777246467)
        ·
          refine ⟨37220508728253926665869701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24813672485502617777246467 37220508728253926665869701)
          ·
            refine ⟨6978845386547611249850569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37220508728253926665869701 6978845386547611249850569)
            ·
              refine ⟨5234134039910708437387927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6978845386547611249850569 5234134039910708437387927)
              ·
                refine ⟨7851201059866062656081891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5234134039910708437387927 7851201059866062656081891)
                ·
                  refine ⟨11776801589799093984122837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7851201059866062656081891 11776801589799093984122837)
                  ·
                    refine ⟨276018787260916265252879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11776801589799093984122837 276018787260916265252879)
                    ·
                      rfl

theorem cell23_1612634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 1, 7].length) (baseStart_1612634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612634 prefixEnd_1612634 := by exact prefixLift 1612634
  have htrace : WordTrace (prefixWord ++ tailWord_1612634) baseStart_1612634 baseEnd_1612634 := by
    simpa [prefixWord, tailWord_1612634, baseEnd_1612634] using wordTrace_append hprefix tailTrace_1612634
  have hstable : (prefixWord ++ tailWord_1612634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612634).length < 2 ^ (prefixWord ++ tailWord_1612634).sum := by decide
  have hdescent : baseEnd_1612634 < baseStart_1612634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612661 : List Nat := [1, 3, 4, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_1612661 : Nat := 118140960795 + 1612661 * 2 ^ 59
def prefixEnd_1612661 : Nat := 4983230072969 + 3 ^ 40 * 1612661 * 2
def baseEnd_1612661 : Nat := 828070225760420190121013

theorem tailTrace_1612661 : CollatzResearch.WordTrace tailWord_1612661 prefixEnd_1612661 828070225760420190121013 := by
  unfold tailWord_1612661
  simp only [CollatzResearch.WordTrace]
  refine ⟨58818578810612092416557837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39212385873741394944371891 58818578810612092416557837)
  ·
    refine ⟨22056967053979534656209189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58818578810612092416557837 22056967053979534656209189)
    ·
      refine ⟨4135681322621162748039223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22056967053979534656209189 4135681322621162748039223)
      ·
        refine ⟨6203521983931744122058835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4135681322621162748039223 6203521983931744122058835)
        ·
          refine ⟨9305282975897616183088253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6203521983931744122058835 9305282975897616183088253)
          ·
            refine ⟨3489481115961606068658095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9305282975897616183088253 3489481115961606068658095)
            ·
              refine ⟨5234221673942409102987143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489481115961606068658095 5234221673942409102987143)
              ·
                refine ⟨7851332510913613654480715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5234221673942409102987143 7851332510913613654480715)
                ·
                  refine ⟨11776998766370420481721073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7851332510913613654480715 11776998766370420481721073)
                  ·
                    refine ⟨8832749074777815361290805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11776998766370420481721073 8832749074777815361290805)
                    ·
                      refine ⟨828070225760420190121013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8832749074777815361290805 828070225760420190121013)
                      ·
                        rfl

theorem cell23_1612661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_1612661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612661 prefixEnd_1612661 := by exact prefixLift 1612661
  have htrace : WordTrace (prefixWord ++ tailWord_1612661) baseStart_1612661 baseEnd_1612661 := by
    simpa [prefixWord, tailWord_1612661, baseEnd_1612661] using wordTrace_append hprefix tailTrace_1612661
  have hstable : (prefixWord ++ tailWord_1612661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612661).length < 2 ^ (prefixWord ++ tailWord_1612661).sum := by decide
  have hdescent : baseEnd_1612661 < baseStart_1612661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612671 : List Nat := [1, 1, 2, 2, 1, 1, 4, 3, 2, 4, 2]
def baseStart_1612671 : Nat := 118140960795 + 1612671 * 2 ^ 59
def prefixEnd_1612671 : Nat := 4983230072969 + 3 ^ 40 * 1612671 * 2
def baseEnd_1612671 : Nat := 828075360566965150995967

theorem tailTrace_1612671 : CollatzResearch.WordTrace tailWord_1612671 prefixEnd_1612671 828075360566965150995967 := by
  unfold tailWord_1612671
  simp only [CollatzResearch.WordTrace]
  refine ⟨58818943540575864124421867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39212629027050576082947911 58818943540575864124421867)
  ·
    refine ⟨88228415310863796186632801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58818943540575864124421867 88228415310863796186632801)
    ·
      refine ⟨66171311483147847139974601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88228415310863796186632801 66171311483147847139974601)
      ·
        refine ⟨49628483612360885354980951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66171311483147847139974601 49628483612360885354980951)
        ·
          refine ⟨74442725418541328032471427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49628483612360885354980951 74442725418541328032471427)
          ·
            refine ⟨111664088127811992048707141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74442725418541328032471427 111664088127811992048707141)
            ·
              refine ⟨20937016523964748509132589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111664088127811992048707141 20937016523964748509132589)
              ·
                refine ⟨7851381196486780690924721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20937016523964748509132589 7851381196486780690924721)
                ·
                  refine ⟨5888535897365085518193541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7851381196486780690924721 5888535897365085518193541)
                  ·
                    refine ⟨1104100480755953534661289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5888535897365085518193541 1104100480755953534661289)
                    ·
                      refine ⟨828075360566965150995967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1104100480755953534661289 828075360566965150995967)
                      ·
                        rfl

theorem cell23_1612671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 4, 2].length) (baseStart_1612671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612671 prefixEnd_1612671 := by exact prefixLift 1612671
  have htrace : WordTrace (prefixWord ++ tailWord_1612671) baseStart_1612671 baseEnd_1612671 := by
    simpa [prefixWord, tailWord_1612671, baseEnd_1612671] using wordTrace_append hprefix tailTrace_1612671
  have hstable : (prefixWord ++ tailWord_1612671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612671).length < 2 ^ (prefixWord ++ tailWord_1612671).sum := by decide
  have hdescent : baseEnd_1612671 < baseStart_1612671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612684 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 2, 4, 4]
def baseStart_1612684 : Nat := 118140960795 + 1612684 * 2 ^ 59
def prefixEnd_1612684 : Nat := 4983230072969 + 3 ^ 40 * 1612684 * 2
def baseEnd_1612684 : Nat := 828082035815473600133407

theorem tailTrace_1612684 : CollatzResearch.WordTrace tailWord_1612684 prefixEnd_1612684 828082035815473600133407 := by
  unfold tailWord_1612684
  simp only [CollatzResearch.WordTrace]
  refine ⟨29409708844764383672322553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39212945126352511563096737 29409708844764383672322553)
  ·
    refine ⟨22057281633573287754241915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29409708844764383672322553 22057281633573287754241915)
    ·
      refine ⟨33085922450359931631362873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22057281633573287754241915 33085922450359931631362873)
      ·
        refine ⟨24814441837769948723522155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33085922450359931631362873 24814441837769948723522155)
        ·
          refine ⟨37221662756654923085283233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24814441837769948723522155 37221662756654923085283233)
          ·
            refine ⟨27916247067491192313962425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37221662756654923085283233 27916247067491192313962425)
            ·
              refine ⟨20937185300618394235471819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27916247067491192313962425 20937185300618394235471819)
              ·
                refine ⟨31405777950927591353207729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20937185300618394235471819 31405777950927591353207729)
                ·
                  refine ⟨23554333463195693514905797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31405777950927591353207729 23554333463195693514905797)
                  ·
                    refine ⟨4416437524349192534044837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23554333463195693514905797 4416437524349192534044837)
                    ·
                      refine ⟨828082035815473600133407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4416437524349192534044837 828082035815473600133407)
                      ·
                        rfl

theorem cell23_1612684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_1612684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612684 prefixEnd_1612684 := by exact prefixLift 1612684
  have htrace : WordTrace (prefixWord ++ tailWord_1612684) baseStart_1612684 baseEnd_1612684 := by
    simpa [prefixWord, tailWord_1612684, baseEnd_1612684] using wordTrace_append hprefix tailTrace_1612684
  have hstable : (prefixWord ++ tailWord_1612684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612684).length < 2 ^ (prefixWord ++ tailWord_1612684).sum := by decide
  have hdescent : baseEnd_1612684 < baseStart_1612684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612748 : List Nat := [2, 2, 1, 4, 1, 1, 3, 1, 1, 5, 2]
def baseStart_1612748 : Nat := 118140960795 + 1612748 * 2 ^ 59
def prefixEnd_1612748 : Nat := 4983230072969 + 3 ^ 40 * 1612748 * 2
def baseEnd_1612748 : Nat := 828114898577361349733113

theorem tailTrace_1612748 : CollatzResearch.WordTrace tailWord_1612748 prefixEnd_1612748 828114898577361349733113 := by
  unfold tailWord_1612748
  simp only [CollatzResearch.WordTrace]
  refine ⟨29410875980648453137487449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39214501307531270849983265 29410875980648453137487449)
  ·
    refine ⟨22058156985486339853115587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29410875980648453137487449 22058156985486339853115587)
    ·
      refine ⟨33087235478229509779673381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22058156985486339853115587 33087235478229509779673381)
      ·
        refine ⟨6203856652168033083688759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33087235478229509779673381 6203856652168033083688759)
        ·
          refine ⟨9305784978252049625533139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6203856652168033083688759 9305784978252049625533139)
          ·
            refine ⟨13958677467378074438299709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9305784978252049625533139 13958677467378074438299709)
            ·
              refine ⟨5234504050266777914362391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13958677467378074438299709 5234504050266777914362391)
              ·
                refine ⟨7851756075400166871543587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5234504050266777914362391 7851756075400166871543587)
                ·
                  refine ⟨11777634113100250307315381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7851756075400166871543587 11777634113100250307315381)
                  ·
                    refine ⟨1104153198103148466310817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11777634113100250307315381 1104153198103148466310817)
                    ·
                      refine ⟨828114898577361349733113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1104153198103148466310817 828114898577361349733113)
                      ·
                        rfl

theorem cell23_1612748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_1612748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612748 prefixEnd_1612748 := by exact prefixLift 1612748
  have htrace : WordTrace (prefixWord ++ tailWord_1612748) baseStart_1612748 baseEnd_1612748 := by
    simpa [prefixWord, tailWord_1612748, baseEnd_1612748] using wordTrace_append hprefix tailTrace_1612748
  have hstable : (prefixWord ++ tailWord_1612748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612748).length < 2 ^ (prefixWord ++ tailWord_1612748).sum := by decide
  have hdescent : baseEnd_1612748 < baseStart_1612748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612784 : List Nat := [2, 1, 1, 1, 3, 2, 1, 12]
def baseStart_1612784 : Nat := 118140960795 + 1612784 * 2 ^ 59
def prefixEnd_1612784 : Nat := 4983230072969 + 3 ^ 40 * 1612784 * 2
def baseEnd_1612784 : Nat := 30671606810404563291961

theorem tailTrace_1612784 : CollatzResearch.WordTrace tailWord_1612784 prefixEnd_1612784 30671606810404563291961 := by
  unfold tailWord_1612784
  simp only [CollatzResearch.WordTrace]
  refine ⟨29411532494583242211642703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39215376659444322948856937 29411532494583242211642703)
  ·
    refine ⟨44117298741874863317464055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29411532494583242211642703 44117298741874863317464055)
    ·
      refine ⟨66175948112812294976196083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44117298741874863317464055 66175948112812294976196083)
      ·
        refine ⟨99263922169218442464294125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66175948112812294976196083 99263922169218442464294125)
        ·
          refine ⟨37223970813456915924110297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99263922169218442464294125 37223970813456915924110297)
          ·
            refine ⟨27917978110092686943082723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37223970813456915924110297 27917978110092686943082723)
            ·
              refine ⟨41876967165139030414624085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27917978110092686943082723 41876967165139030414624085)
              ·
                refine ⟨30671606810404563291961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 41876967165139030414624085 30671606810404563291961)
                ·
                  rfl

theorem cell23_1612784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 12].length) (baseStart_1612784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612784 prefixEnd_1612784 := by exact prefixLift 1612784
  have htrace : WordTrace (prefixWord ++ tailWord_1612784) baseStart_1612784 baseEnd_1612784 := by
    simpa [prefixWord, tailWord_1612784, baseEnd_1612784] using wordTrace_append hprefix tailTrace_1612784
  have hstable : (prefixWord ++ tailWord_1612784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612784).length < 2 ^ (prefixWord ++ tailWord_1612784).sum := by decide
  have hdescent : baseEnd_1612784 < baseStart_1612784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612801 : List Nat := [1, 2, 4, 1, 2, 3, 1, 9]
def baseStart_1612801 : Nat := 118140960795 + 1612801 * 2 ^ 59
def prefixEnd_1612801 : Nat := 4983230072969 + 3 ^ 40 * 1612801 * 2
def baseEnd_1612801 : Nat := 30671930113038875643347

theorem tailTrace_1612801 : CollatzResearch.WordTrace tailWord_1612801 prefixEnd_1612801 30671930113038875643347 := by
  unfold tailWord_1612801
  simp only [CollatzResearch.WordTrace]
  refine ⟨58823685030104896326654257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39215790020069930884436171 58823685030104896326654257)
  ·
    refine ⟨44117763772578672244990693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58823685030104896326654257 44117763772578672244990693)
    ·
      refine ⟨8272080707358501045935755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44117763772578672244990693 8272080707358501045935755)
      ·
        refine ⟨12408121061037751568903633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8272080707358501045935755 12408121061037751568903633)
        ·
          refine ⟨9306090795778313676677725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12408121061037751568903633 9306090795778313676677725)
          ·
            refine ⟨3489784048416867628754147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9306090795778313676677725 3489784048416867628754147)
            ·
              refine ⟨5234676072625301443131221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489784048416867628754147 5234676072625301443131221)
              ·
                refine ⟨30671930113038875643347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5234676072625301443131221 30671930113038875643347)
                ·
                  rfl

theorem cell23_1612801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 9].length) (baseStart_1612801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612801 prefixEnd_1612801 := by exact prefixLift 1612801
  have htrace : WordTrace (prefixWord ++ tailWord_1612801) baseStart_1612801 baseEnd_1612801 := by
    simpa [prefixWord, tailWord_1612801, baseEnd_1612801] using wordTrace_append hprefix tailTrace_1612801
  have hstable : (prefixWord ++ tailWord_1612801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612801).length < 2 ^ (prefixWord ++ tailWord_1612801).sum := by decide
  have hdescent : baseEnd_1612801 < baseStart_1612801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612829 : List Nat := [1, 4, 2, 2, 3, 2, 1, 1, 3, 2, 2]
def baseStart_1612829 : Nat := 118140960795 + 1612829 * 2 ^ 59
def prefixEnd_1612829 : Nat := 4983230072969 + 3 ^ 40 * 1612829 * 2
def baseEnd_1612829 : Nat := 828156490510375532820241

theorem tailTrace_1612829 : CollatzResearch.WordTrace tailWord_1612829 prefixEnd_1612829 828156490510375532820241 := by
  unfold tailWord_1612829
  simp only [CollatzResearch.WordTrace]
  refine ⟨58824706274003457108673541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39216470849335638072449027 58824706274003457108673541)
  ·
    refine ⟨11029632426375648207876289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58824706274003457108673541 11029632426375648207876289)
    ·
      refine ⟨8272224319781736155907217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11029632426375648207876289 8272224319781736155907217)
      ·
        refine ⟨6204168239836302116930413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8272224319781736155907217 6204168239836302116930413)
        ·
          refine ⟨2326563089938613293848905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6204168239836302116930413 2326563089938613293848905)
          ·
            refine ⟨1744922317453959970386679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2326563089938613293848905 1744922317453959970386679)
            ·
              refine ⟨2617383476180939955580019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1744922317453959970386679 2617383476180939955580019)
              ·
                refine ⟨3926075214271409933370029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2617383476180939955580019 3926075214271409933370029)
                ·
                  refine ⟨1472278205351778725013761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3926075214271409933370029 1472278205351778725013761)
                  ·
                    refine ⟨1104208654013834043760321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1472278205351778725013761 1104208654013834043760321)
                    ·
                      refine ⟨828156490510375532820241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1104208654013834043760321 828156490510375532820241)
                      ·
                        rfl

theorem cell23_1612829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_1612829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612829 prefixEnd_1612829 := by exact prefixLift 1612829
  have htrace : WordTrace (prefixWord ++ tailWord_1612829) baseStart_1612829 baseEnd_1612829 := by
    simpa [prefixWord, tailWord_1612829, baseEnd_1612829] using wordTrace_append hprefix tailTrace_1612829
  have hstable : (prefixWord ++ tailWord_1612829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612829).length < 2 ^ (prefixWord ++ tailWord_1612829).sum := by decide
  have hdescent : baseEnd_1612829 < baseStart_1612829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612839 : List Nat := [1, 1, 7, 1, 1, 3, 2, 1, 2, 4]
def baseStart_1612839 : Nat := 118140960795 + 1612839 * 2 ^ 59
def prefixEnd_1612839 : Nat := 4983230072969 + 3 ^ 40 * 1612839 * 2
def baseEnd_1612839 : Nat := 276053875105640164565065

theorem tailTrace_1612839 : CollatzResearch.WordTrace tailWord_1612839 prefixEnd_1612839 276053875105640164565065 := by
  unfold tailWord_1612839
  simp only [CollatzResearch.WordTrace]
  refine ⟨58825071003967228816537571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39216714002644819211025047 58825071003967228816537571)
  ·
    refine ⟨88237606505950843224806357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58825071003967228816537571 88237606505950843224806357)
    ·
      refine ⟨2068068902483222888081399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 88237606505950843224806357 2068068902483222888081399)
      ·
        refine ⟨3102103353724834332122099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2068068902483222888081399 3102103353724834332122099)
        ·
          refine ⟨4653155030587251498183149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3102103353724834332122099 4653155030587251498183149)
          ·
            refine ⟨1744933136470219311818681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4653155030587251498183149 1744933136470219311818681)
            ·
              refine ⟨1308699852352664483864011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1744933136470219311818681 1308699852352664483864011)
              ·
                refine ⟨1963049778528996725796017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1308699852352664483864011 1963049778528996725796017)
                ·
                  refine ⟨1472287333896747544347013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1963049778528996725796017 1472287333896747544347013)
                  ·
                    refine ⟨276053875105640164565065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1472287333896747544347013 276053875105640164565065)
                    ·
                      rfl

theorem cell23_1612839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_1612839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612839 prefixEnd_1612839 := by exact prefixLift 1612839
  have htrace : WordTrace (prefixWord ++ tailWord_1612839) baseStart_1612839 baseEnd_1612839 := by
    simpa [prefixWord, tailWord_1612839, baseEnd_1612839] using wordTrace_append hprefix tailTrace_1612839
  have hstable : (prefixWord ++ tailWord_1612839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612839).length < 2 ^ (prefixWord ++ tailWord_1612839).sum := by decide
  have hdescent : baseEnd_1612839 < baseStart_1612839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612872 : List Nat := [2, 1, 3, 1, 1, 1, 7, 1, 1, 3, 2]
def baseStart_1612872 : Nat := 118140960795 + 1612872 * 2 ^ 59
def prefixEnd_1612872 : Nat := 4983230072969 + 3 ^ 40 * 1612872 * 2
def baseEnd_1612872 : Nat := 828178570178518864582543

theorem tailTrace_1612872 : CollatzResearch.WordTrace tailWord_1612872 prefixEnd_1612872 828178570178518864582543 := by
  unfold tailWord_1612872
  simp only [CollatzResearch.WordTrace]
  refine ⟨29413137306423837726244435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39217516408565116968325913 29413137306423837726244435)
  ·
    refine ⟨44119705959635756589366653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29413137306423837726244435 44119705959635756589366653)
    ·
      refine ⟨16544889734863408721012495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44119705959635756589366653 16544889734863408721012495)
      ·
        refine ⟨24817334602295113081518743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16544889734863408721012495 24817334602295113081518743)
        ·
          refine ⟨37226001903442669622278115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24817334602295113081518743 37226001903442669622278115)
          ·
            refine ⟨55839002855164004433417173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37226001903442669622278115 55839002855164004433417173)
            ·
              refine ⟨1308726629417906353908215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 55839002855164004433417173 1308726629417906353908215)
              ·
                refine ⟨1963089944126859530862323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1308726629417906353908215 1963089944126859530862323)
                ·
                  refine ⟨2944634916190289296293485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1963089944126859530862323 2944634916190289296293485)
                  ·
                    refine ⟨1104238093571358486110057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2944634916190289296293485 1104238093571358486110057)
                    ·
                      refine ⟨828178570178518864582543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1104238093571358486110057 828178570178518864582543)
                      ·
                        rfl

theorem cell23_1612872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 1, 3, 2].length) (baseStart_1612872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612872 prefixEnd_1612872 := by exact prefixLift 1612872
  have htrace : WordTrace (prefixWord ++ tailWord_1612872) baseStart_1612872 baseEnd_1612872 := by
    simpa [prefixWord, tailWord_1612872, baseEnd_1612872] using wordTrace_append hprefix tailTrace_1612872
  have hstable : (prefixWord ++ tailWord_1612872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612872).length < 2 ^ (prefixWord ++ tailWord_1612872).sum := by decide
  have hdescent : baseEnd_1612872 < baseStart_1612872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612925 : List Nat := [1, 4, 1, 1, 3, 1, 4, 3, 5]
def baseStart_1612925 : Nat := 118140960795 + 1612925 * 2 ^ 59
def prefixEnd_1612925 : Nat := 4983230072969 + 3 ^ 40 * 1612925 * 2
def baseEnd_1612925 : Nat := 92022864961467461913311

theorem tailTrace_1612925 : CollatzResearch.WordTrace tailWord_1612925 prefixEnd_1612925 92022864961467461913311 := by
  unfold tailWord_1612925
  simp only [CollatzResearch.WordTrace]
  refine ⟨58828207681655665504168229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39218805121103777002778819 58828207681655665504168229)
  ·
    refine ⟨11030288940310437282031543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58828207681655665504168229 11030288940310437282031543)
    ·
      refine ⟨16545433410465655923047315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11030288940310437282031543 16545433410465655923047315)
      ·
        refine ⟨24818150115698483884570973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16545433410465655923047315 24818150115698483884570973)
        ·
          refine ⟨9306806293386931456714115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24818150115698483884570973 9306806293386931456714115)
          ·
            refine ⟨13960209440080397185071173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9306806293386931456714115 13960209440080397185071173)
            ·
              refine ⟨2617539270015074472200845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13960209440080397185071173 2617539270015074472200845)
              ·
                refine ⟨981577226255652927075317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2617539270015074472200845 981577226255652927075317)
                ·
                  refine ⟨92022864961467461913311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 981577226255652927075317 92022864961467461913311)
                  ·
                    rfl

theorem cell23_1612925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3, 5].length) (baseStart_1612925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612925 prefixEnd_1612925 := by exact prefixLift 1612925
  have htrace : WordTrace (prefixWord ++ tailWord_1612925) baseStart_1612925 baseEnd_1612925 := by
    simpa [prefixWord, tailWord_1612925, baseEnd_1612925] using wordTrace_append hprefix tailTrace_1612925
  have hstable : (prefixWord ++ tailWord_1612925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612925).length < 2 ^ (prefixWord ++ tailWord_1612925).sum := by decide
  have hdescent : baseEnd_1612925 < baseStart_1612925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612936 : List Nat := [2, 1, 3, 4, 2, 2, 1, 2, 2, 2, 2]
def baseStart_1612936 : Nat := 118140960795 + 1612936 * 2 ^ 59
def prefixEnd_1612936 : Nat := 4983230072969 + 3 ^ 40 * 1612936 * 2
def baseEnd_1612936 : Nat := 828211432940406614182249

theorem tailTrace_1612936 : CollatzResearch.WordTrace tailWord_1612936 prefixEnd_1612936 828211432940406614182249 := by
  unfold tailWord_1612936
  simp only [CollatzResearch.WordTrace]
  refine ⟨29414304442307907191409331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39219072589743876255212441 29414304442307907191409331)
  ·
    refine ⟨44121456663461860787113997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29414304442307907191409331 44121456663461860787113997)
    ·
      refine ⟨16545546248798197795167749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44121456663461860787113997 16545546248798197795167749)
      ·
        refine ⟨3102289921649662086593953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16545546248798197795167749 3102289921649662086593953)
        ·
          refine ⟨2326717441237246564945465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3102289921649662086593953 2326717441237246564945465)
          ·
            refine ⟨1745038080927934923709099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2326717441237246564945465 1745038080927934923709099)
            ·
              refine ⟨2617557121391902385563649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1745038080927934923709099 2617557121391902385563649)
              ·
                refine ⟨1963167841043926789172737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2617557121391902385563649 1963167841043926789172737)
                ·
                  refine ⟨1472375880782945091879553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1963167841043926789172737 1472375880782945091879553)
                  ·
                    refine ⟨1104281910587208818909665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1472375880782945091879553 1104281910587208818909665)
                    ·
                      refine ⟨828211432940406614182249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1104281910587208818909665 828211432940406614182249)
                      ·
                        rfl

theorem cell23_1612936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_1612936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612936 prefixEnd_1612936 := by exact prefixLift 1612936
  have htrace : WordTrace (prefixWord ++ tailWord_1612936) baseStart_1612936 baseEnd_1612936 := by
    simpa [prefixWord, tailWord_1612936, baseEnd_1612936] using wordTrace_append hprefix tailTrace_1612936
  have hstable : (prefixWord ++ tailWord_1612936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612936).length < 2 ^ (prefixWord ++ tailWord_1612936).sum := by decide
  have hdescent : baseEnd_1612936 < baseStart_1612936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1612938 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 4, 5]
def baseStart_1612938 : Nat := 118140960795 + 1612938 * 2 ^ 59
def prefixEnd_1612938 : Nat := 4983230072969 + 3 ^ 40 * 1612938 * 2
def baseEnd_1612938 : Nat := 276070819967238535452413

theorem tailTrace_1612938 : CollatzResearch.WordTrace tailWord_1612938 prefixEnd_1612938 276070819967238535452413 := by
  unfold tailWord_1612938
  simp only [CollatzResearch.WordTrace]
  refine ⟨14707170457652142181097867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39219121220405712482927645 14707170457652142181097867)
  ·
    refine ⟨22060755686478213271646801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14707170457652142181097867 22060755686478213271646801)
    ·
      refine ⟨16545566764858659953735101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22060755686478213271646801 16545566764858659953735101)
      ·
        refine ⟨6204587536821997482650663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16545566764858659953735101 6204587536821997482650663)
        ·
          refine ⟨9306881305232996223975995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6204587536821997482650663 9306881305232996223975995)
          ·
            refine ⟨13960321957849494335963993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9306881305232996223975995 13960321957849494335963993)
            ·
              refine ⟨10470241468387120751972995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13960321957849494335963993 10470241468387120751972995)
              ·
                refine ⟨15705362202580681127959493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10470241468387120751972995 15705362202580681127959493)
                ·
                  refine ⟨2944755412983877711492405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15705362202580681127959493 2944755412983877711492405)
                  ·
                    refine ⟨276070819967238535452413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2944755412983877711492405 276070819967238535452413)
                    ·
                      rfl

theorem cell23_1612938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_1612938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1612938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1612938 prefixEnd_1612938 := by exact prefixLift 1612938
  have htrace : WordTrace (prefixWord ++ tailWord_1612938) baseStart_1612938 baseEnd_1612938 := by
    simpa [prefixWord, tailWord_1612938, baseEnd_1612938] using wordTrace_append hprefix tailTrace_1612938
  have hstable : (prefixWord ++ tailWord_1612938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1612938).length < 2 ^ (prefixWord ++ tailWord_1612938).sum := by decide
  have hdescent : baseEnd_1612938 < baseStart_1612938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1612938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613002 : List Nat := [3, 1, 2, 1, 3, 4, 1, 1, 3, 4]
def baseStart_1613002 : Nat := 118140960795 + 1613002 * 2 ^ 59
def prefixEnd_1613002 : Nat := 4983230072969 + 3 ^ 40 * 1613002 * 2
def baseEnd_1613002 : Nat := 276081774221201118652315

theorem tailTrace_1613002 : CollatzResearch.WordTrace tailWord_1613002 prefixEnd_1613002 276081774221201118652315 := by
  unfold tailWord_1613002
  simp only [CollatzResearch.WordTrace]
  refine ⟨14707754025594176913680315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39220677401584471769814173 14707754025594176913680315)
  ·
    refine ⟨22061631038391265370520473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14707754025594176913680315 22061631038391265370520473)
    ·
      refine ⟨16546223278793449027890355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22061631038391265370520473 16546223278793449027890355)
      ·
        refine ⟨24819334918190173541835533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16546223278793449027890355 24819334918190173541835533)
        ·
          refine ⟨9307250594321315078188325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24819334918190173541835533 9307250594321315078188325)
          ·
            refine ⟨1745109486435246577160311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9307250594321315078188325 1745109486435246577160311)
            ·
              refine ⟨2617664229652869865740467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1745109486435246577160311 2617664229652869865740467)
              ·
                refine ⟨3926496344479304798610701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2617664229652869865740467 3926496344479304798610701)
                ·
                  refine ⟨1472436129179739299479013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3926496344479304798610701 1472436129179739299479013)
                  ·
                    refine ⟨276081774221201118652315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1472436129179739299479013 276081774221201118652315)
                    ·
                      rfl

theorem cell23_1613002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_1613002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613002 prefixEnd_1613002 := by exact prefixLift 1613002
  have htrace : WordTrace (prefixWord ++ tailWord_1613002) baseStart_1613002 baseEnd_1613002 := by
    simpa [prefixWord, tailWord_1613002, baseEnd_1613002] using wordTrace_append hprefix tailTrace_1613002
  have hstable : (prefixWord ++ tailWord_1613002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613002).length < 2 ^ (prefixWord ++ tailWord_1613002).sum := by decide
  have hdescent : baseEnd_1613002 < baseStart_1613002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613015 : List Nat := [1, 1, 3, 2, 1, 2, 6, 1, 6]
def baseStart_1613015 : Nat := 118140960795 + 1613015 * 2 ^ 59
def prefixEnd_1613015 : Nat := 4983230072969 + 3 ^ 40 * 1613015 * 2
def baseEnd_1613015 : Nat := 92027999768012422788265

theorem tailTrace_1613015 : CollatzResearch.WordTrace tailWord_1613015 prefixEnd_1613015 92027999768012422788265 := by
  unfold tailWord_1613015
  simp only [CollatzResearch.WordTrace]
  refine ⟨58831490251329610874944499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39220993500886407249962999 58831490251329610874944499)
  ·
    refine ⟨88247235376994416312416749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58831490251329610874944499 88247235376994416312416749)
    ·
      refine ⟨33092713266372906117156281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88247235376994416312416749 33092713266372906117156281)
      ·
        refine ⟨24819534949779679587867211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33092713266372906117156281 24819534949779679587867211)
        ·
          refine ⟨37229302424669519381800817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24819534949779679587867211 37229302424669519381800817)
          ·
            refine ⟨27921976818502139536350613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37229302424669519381800817 27921976818502139536350613)
            ·
              refine ⟨1308842663367287790766435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27921976818502139536350613 1308842663367287790766435)
              ·
                refine ⟨1963263995050931686149653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1308842663367287790766435 1963263995050931686149653)
                ·
                  refine ⟨92027999768012422788265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1963263995050931686149653 92027999768012422788265)
                  ·
                    rfl

theorem cell23_1613015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 6].length) (baseStart_1613015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613015 prefixEnd_1613015 := by exact prefixLift 1613015
  have htrace : WordTrace (prefixWord ++ tailWord_1613015) baseStart_1613015 baseEnd_1613015 := by
    simpa [prefixWord, tailWord_1613015, baseEnd_1613015] using wordTrace_append hprefix tailTrace_1613015
  have hstable : (prefixWord ++ tailWord_1613015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613015).length < 2 ^ (prefixWord ++ tailWord_1613015).sum := by decide
  have hdescent : baseEnd_1613015 < baseStart_1613015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613059 : List Nat := [1, 1, 1, 3, 2, 5, 1, 4, 1, 1, 3]
def baseStart_1613059 : Nat := 118140960795 + 1613059 * 2 ^ 59
def prefixEnd_1613059 : Nat := 4983230072969 + 3 ^ 40 * 1613059 * 2
def baseEnd_1613059 : Nat := 828274591060909632944183

theorem tailTrace_1613059 : CollatzResearch.WordTrace tailWord_1613059 prefixEnd_1613059 828274591060909632944183 := by
  unfold tailWord_1613059
  simp only [CollatzResearch.WordTrace]
  refine ⟨58833095063170206389546231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39222063375446804259697487 58833095063170206389546231)
  ·
    refine ⟨88249642594755309584319347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58833095063170206389546231 88249642594755309584319347)
    ·
      refine ⟨132374463892132964376479021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88249642594755309584319347 132374463892132964376479021)
      ·
        refine ⟨49640423959549861641179633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132374463892132964376479021 49640423959549861641179633)
        ·
          refine ⟨37230317969662396230884725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49640423959549861641179633 37230317969662396230884725)
          ·
            refine ⟨3490342309655849646645443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37230317969662396230884725 3490342309655849646645443)
            ·
              refine ⟨5235513464483774469968165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3490342309655849646645443 5235513464483774469968165)
              ·
                refine ⟨981658774590707713119031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5235513464483774469968165 981658774590707713119031)
                ·
                  refine ⟨1472488161886061569678547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 981658774590707713119031 1472488161886061569678547)
                  ·
                    refine ⟨2208732242829092354517821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1472488161886061569678547 2208732242829092354517821)
                    ·
                      refine ⟨828274591060909632944183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2208732242829092354517821 828274591060909632944183)
                      ·
                        rfl

theorem cell23_1613059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4, 1, 1, 3].length) (baseStart_1613059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613059 prefixEnd_1613059 := by exact prefixLift 1613059
  have htrace : WordTrace (prefixWord ++ tailWord_1613059) baseStart_1613059 baseEnd_1613059 := by
    simpa [prefixWord, tailWord_1613059, baseEnd_1613059] using wordTrace_append hprefix tailTrace_1613059
  have hstable : (prefixWord ++ tailWord_1613059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613059).length < 2 ^ (prefixWord ++ tailWord_1613059).sum := by decide
  have hdescent : baseEnd_1613059 < baseStart_1613059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613086 : List Nat := [4, 3, 2, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_1613086 : Nat := 118140960795 + 1613086 * 2 ^ 59
def prefixEnd_1613086 : Nat := 4983230072969 + 3 ^ 40 * 1613086 * 2
def baseEnd_1613086 : Nat := 828288455038581027306559

theorem tailTrace_1613086 : CollatzResearch.WordTrace tailWord_1613086 prefixEnd_1613086 828288455038581027306559 := by
  unfold tailWord_1613086
  simp only [CollatzResearch.WordTrace]
  refine ⟨7354259979259048750097389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39222719889381593333852741 7354259979259048750097389)
  ·
    refine ⟨2757847492222143281286521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7354259979259048750097389 2757847492222143281286521)
    ·
      refine ⟨2068385619166607460964891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2757847492222143281286521 2068385619166607460964891)
      ·
        refine ⟨3102578428749911191447337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2068385619166607460964891 3102578428749911191447337)
        ·
          refine ⟨2326933821562433393585503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3102578428749911191447337 2326933821562433393585503)
          ·
            refine ⟨3490400732343650090378255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2326933821562433393585503 3490400732343650090378255)
            ·
              refine ⟨5235601098515475135567383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3490400732343650090378255 5235601098515475135567383)
              ·
                refine ⟨7853401647773212703351075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5235601098515475135567383 7853401647773212703351075)
                ·
                  refine ⟨11780102471659819055026613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7853401647773212703351075 11780102471659819055026613)
                  ·
                    refine ⟨1104384606718108036408745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11780102471659819055026613 1104384606718108036408745)
                    ·
                      refine ⟨828288455038581027306559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1104384606718108036408745 828288455038581027306559)
                      ·
                        rfl

theorem cell23_1613086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_1613086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613086 prefixEnd_1613086 := by exact prefixLift 1613086
  have htrace : WordTrace (prefixWord ++ tailWord_1613086) baseStart_1613086 baseEnd_1613086 := by
    simpa [prefixWord, tailWord_1613086, baseEnd_1613086] using wordTrace_append hprefix tailTrace_1613086
  have hstable : (prefixWord ++ tailWord_1613086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613086).length < 2 ^ (prefixWord ++ tailWord_1613086).sum := by decide
  have hdescent : baseEnd_1613086 < baseStart_1613086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613109 : List Nat := [1, 3, 3, 1, 2, 4, 1, 2, 2, 4]
def baseStart_1613109 : Nat := 118140960795 + 1613109 * 2 ^ 59
def prefixEnd_1613109 : Nat := 4983230072969 + 3 ^ 40 * 1613109 * 2
def baseEnd_1613109 : Nat := 276100088364544812439651

theorem tailTrace_1613109 : CollatzResearch.WordTrace tailWord_1613109 prefixEnd_1613109 276100088364544812439651 := by
  unfold tailWord_1613109
  simp only [CollatzResearch.WordTrace]
  refine ⟨58834918712989064928866381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39223279141992709952577587 58834918712989064928866381)
  ·
    refine ⟨22063094517370899348324893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58834918712989064928866381 22063094517370899348324893)
    ·
      refine ⟨8273660444014087255621835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22063094517370899348324893 8273660444014087255621835)
      ·
        refine ⟨12410490666021130883432753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8273660444014087255621835 12410490666021130883432753)
        ·
          refine ⟨9307867999515848162574565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12410490666021130883432753 9307867999515848162574565)
          ·
            refine ⟨1745225249909221530482731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9307867999515848162574565 1745225249909221530482731)
            ·
              refine ⟨2617837874863832295724097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1745225249909221530482731 2617837874863832295724097)
              ·
                refine ⟨1963378406147874221793073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2617837874863832295724097 1963378406147874221793073)
                ·
                  refine ⟨1472533804610905666344805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1963378406147874221793073 1472533804610905666344805)
                  ·
                    refine ⟨276100088364544812439651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1472533804610905666344805 276100088364544812439651)
                    ·
                      rfl

theorem cell23_1613109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_1613109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613109 prefixEnd_1613109 := by exact prefixLift 1613109
  have htrace : WordTrace (prefixWord ++ tailWord_1613109) baseStart_1613109 baseEnd_1613109 := by
    simpa [prefixWord, tailWord_1613109, baseEnd_1613109] using wordTrace_append hprefix tailTrace_1613109
  have hstable : (prefixWord ++ tailWord_1613109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613109).length < 2 ^ (prefixWord ++ tailWord_1613109).sum := by decide
  have hdescent : baseEnd_1613109 < baseStart_1613109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613116 : List Nat := [2, 2, 2, 2, 1, 3, 2, 4, 1, 2, 2]
def baseStart_1613116 : Nat := 118140960795 + 1613116 * 2 ^ 59
def prefixEnd_1613116 : Nat := 4983230072969 + 3 ^ 40 * 1613116 * 2
def baseEnd_1613116 : Nat := 828303859458215909931421

theorem tailTrace_1613116 : CollatzResearch.WordTrace tailWord_1613116 prefixEnd_1613116 828303859458215909931421 := by
  unfold tailWord_1613116
  simp only [CollatzResearch.WordTrace]
  refine ⟨29417587011981852562185601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39223449349309136749580801 29417587011981852562185601)
  ·
    refine ⟨22063190258986389421639201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29417587011981852562185601 22063190258986389421639201)
    ·
      refine ⟨16547392694239792066229401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22063190258986389421639201 16547392694239792066229401)
      ·
        refine ⟨12410544520679844049672051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16547392694239792066229401 12410544520679844049672051)
        ·
          refine ⟨18615816781019766074508077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12410544520679844049672051 18615816781019766074508077)
          ·
            refine ⟨6980931292882412277940529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18615816781019766074508077 6980931292882412277940529)
            ·
              refine ⟨5235698469661809208455397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6980931292882412277940529 5235698469661809208455397)
              ·
                refine ⟨981693463061589226585387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5235698469661809208455397 981693463061589226585387)
                ·
                  refine ⟨1472540194592383839878081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 981693463061589226585387 1472540194592383839878081)
                  ·
                    refine ⟨1104405145944287879908561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1472540194592383839878081 1104405145944287879908561)
                    ·
                      refine ⟨828303859458215909931421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1104405145944287879908561 828303859458215909931421)
                      ·
                        rfl

theorem cell23_1613116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_1613116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613116 prefixEnd_1613116 := by exact prefixLift 1613116
  have htrace : WordTrace (prefixWord ++ tailWord_1613116) baseStart_1613116 baseEnd_1613116 := by
    simpa [prefixWord, tailWord_1613116, baseEnd_1613116] using wordTrace_append hprefix tailTrace_1613116
  have hstable : (prefixWord ++ tailWord_1613116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613116).length < 2 ^ (prefixWord ++ tailWord_1613116).sum := by decide
  have hdescent : baseEnd_1613116 < baseStart_1613116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613132 : List Nat := [2, 2, 1, 3, 2, 2, 3, 1, 1, 3, 3]
def baseStart_1613132 : Nat := 118140960795 + 1613132 * 2 ^ 59
def prefixEnd_1613132 : Nat := 4983230072969 + 3 ^ 40 * 1613132 * 2
def baseEnd_1613132 : Nat := 828312075148687847331347

theorem tailTrace_1613132 : CollatzResearch.WordTrace tailWord_1613132 prefixEnd_1613132 828312075148687847331347 := by
  unfold tailWord_1613132
  simp only [CollatzResearch.WordTrace]
  refine ⟨29417878795952869928476825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39223838394603826571302433 29417878795952869928476825)
  ·
    refine ⟨22063409096964652446357619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29417878795952869928476825 22063409096964652446357619)
    ·
      refine ⟨33095113645446978669536429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22063409096964652446357619 33095113645446978669536429)
      ·
        refine ⟨12410667617042617001076161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33095113645446978669536429 12410667617042617001076161)
        ·
          refine ⟨9308000712781962750807121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12410667617042617001076161 9308000712781962750807121)
          ·
            refine ⟨6981000534586472063105341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9308000712781962750807121 6981000534586472063105341)
            ·
              refine ⟨2617875200469927023664503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6981000534586472063105341 2617875200469927023664503)
              ·
                refine ⟨3926812800704890535496755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2617875200469927023664503 3926812800704890535496755)
                ·
                  refine ⟨5890219201057335803245133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3926812800704890535496755 5890219201057335803245133)
                  ·
                    refine ⟨2208832200396500926216925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5890219201057335803245133 2208832200396500926216925)
                    ·
                      refine ⟨828312075148687847331347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2208832200396500926216925 828312075148687847331347)
                      ·
                        rfl

theorem cell23_1613132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_1613132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613132 prefixEnd_1613132 := by exact prefixLift 1613132
  have htrace : WordTrace (prefixWord ++ tailWord_1613132) baseStart_1613132 baseEnd_1613132 := by
    simpa [prefixWord, tailWord_1613132, baseEnd_1613132] using wordTrace_append hprefix tailTrace_1613132
  have hstable : (prefixWord ++ tailWord_1613132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613132).length < 2 ^ (prefixWord ++ tailWord_1613132).sum := by decide
  have hdescent : baseEnd_1613132 < baseStart_1613132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613175 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 2, 4, 3]
def baseStart_1613175 : Nat := 118140960795 + 1613175 * 2 ^ 59
def prefixEnd_1613175 : Nat := 4983230072969 + 3 ^ 40 * 1613175 * 2
def baseEnd_1613175 : Nat := 828334154816831179093649

theorem tailTrace_1613175 : CollatzResearch.WordTrace tailWord_1613175 prefixEnd_1613175 828334154816831179093649 := by
  unfold tailWord_1613175
  simp only [CollatzResearch.WordTrace]
  refine ⟨58837325930749958200768979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39224883953833305467179319 58837325930749958200768979)
  ·
    refine ⟨88255988896124937301153469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58837325930749958200768979 88255988896124937301153469)
    ·
      refine ⟨33095995836046851487932551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88255988896124937301153469 33095995836046851487932551)
      ·
        refine ⟨49643993754070277231898827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33095995836046851487932551 49643993754070277231898827)
        ·
          refine ⟨74465990631105415847848241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49643993754070277231898827 74465990631105415847848241)
          ·
            refine ⟨55849492973329061885886181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74465990631105415847848241 55849492973329061885886181)
            ·
              refine ⟨10471779932499199103603659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55849492973329061885886181 10471779932499199103603659)
              ·
                refine ⟨15707669898748798655405489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10471779932499199103603659 15707669898748798655405489)
                ·
                  refine ⟨11780752424061598991554117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15707669898748798655405489 11780752424061598991554117)
                  ·
                    refine ⟨2208891079511549810916397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11780752424061598991554117 2208891079511549810916397)
                    ·
                      refine ⟨828334154816831179093649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2208891079511549810916397 828334154816831179093649)
                      ·
                        rfl

theorem cell23_1613175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4, 3].length) (baseStart_1613175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613175 prefixEnd_1613175 := by exact prefixLift 1613175
  have htrace : WordTrace (prefixWord ++ tailWord_1613175) baseStart_1613175 baseEnd_1613175 := by
    simpa [prefixWord, tailWord_1613175, baseEnd_1613175] using wordTrace_append hprefix tailTrace_1613175
  have hstable : (prefixWord ++ tailWord_1613175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613175).length < 2 ^ (prefixWord ++ tailWord_1613175).sum := by decide
  have hdescent : baseEnd_1613175 < baseStart_1613175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613193 : List Nat := [1, 2, 1, 1, 8, 1, 1, 2, 1, 3, 2]
def baseStart_1613193 : Nat := 118140960795 + 1613193 * 2 ^ 59
def prefixEnd_1613193 : Nat := 4983230072969 + 3 ^ 40 * 1613193 * 2
def baseEnd_1613193 : Nat := 828343397468612108668567

theorem tailTrace_1613193 : CollatzResearch.WordTrace tailWord_1613193 prefixEnd_1613193 828343397468612108668567 := by
  unfold tailWord_1613193
  simp only [CollatzResearch.WordTrace]
  refine ⟨58837982444684747274924233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39225321629789831516616155 58837982444684747274924233)
  ·
    refine ⟨44128486833513560456193175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58837982444684747274924233 44128486833513560456193175)
    ·
      refine ⟨66192730250270340684289763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44128486833513560456193175 66192730250270340684289763)
      ·
        refine ⟨99289095375405511026434645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66192730250270340684289763 99289095375405511026434645)
        ·
          refine ⟨1163544086430533332341031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 99289095375405511026434645 1163544086430533332341031)
          ·
            refine ⟨1745316129645799998511547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1163544086430533332341031 1745316129645799998511547)
            ·
              refine ⟨2617974194468699997767321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1745316129645799998511547 2617974194468699997767321)
              ·
                refine ⟨1963480645851524998325491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2617974194468699997767321 1963480645851524998325491)
                ·
                  refine ⟨2945220968777287497488237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1963480645851524998325491 2945220968777287497488237)
                  ·
                    refine ⟨1104457863291482811558089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2945220968777287497488237 1104457863291482811558089)
                    ·
                      refine ⟨828343397468612108668567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1104457863291482811558089 828343397468612108668567)
                      ·
                        rfl

theorem cell23_1613193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 1, 3, 2].length) (baseStart_1613193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613193 prefixEnd_1613193 := by exact prefixLift 1613193
  have htrace : WordTrace (prefixWord ++ tailWord_1613193) baseStart_1613193 baseEnd_1613193 := by
    simpa [prefixWord, tailWord_1613193, baseEnd_1613193] using wordTrace_append hprefix tailTrace_1613193
  have hstable : (prefixWord ++ tailWord_1613193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613193).length < 2 ^ (prefixWord ++ tailWord_1613193).sum := by decide
  have hdescent : baseEnd_1613193 < baseStart_1613193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613305 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 3, 2, 6]
def baseStart_1613305 : Nat := 118140960795 + 1613305 * 2 ^ 59
def prefixEnd_1613305 : Nat := 4983230072969 + 3 ^ 40 * 1613305 * 2
def baseEnd_1613305 : Nat := 828400907301915670468051

theorem tailTrace_1613305 : CollatzResearch.WordTrace tailWord_1613305 prefixEnd_1613305 828400907301915670468051 := by
  unfold tailWord_1613305
  simp only [CollatzResearch.WordTrace]
  refine ⟨58842067420278990403001369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39228044946852660268667579 58842067420278990403001369)
  ·
    refine ⟨44131550565209242802251027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58842067420278990403001369 44131550565209242802251027)
    ·
      refine ⟨66197325847813864203376541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44131550565209242802251027 66197325847813864203376541)
      ·
        refine ⟨24823997192930199076266203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66197325847813864203376541 24823997192930199076266203)
        ·
          refine ⟨37235995789395298614399305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24823997192930199076266203 37235995789395298614399305)
          ·
            refine ⟨27926996842046473960799479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37235995789395298614399305 27926996842046473960799479)
            ·
              refine ⟨41890495263069710941199219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27926996842046473960799479 41890495263069710941199219)
              ·
                refine ⟨62835742894604566411798829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41890495263069710941199219 62835742894604566411798829)
                ·
                  refine ⟨23563403585476712404424561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62835742894604566411798829 23563403585476712404424561)
                  ·
                    refine ⟨17672552689107534303318421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23563403585476712404424561 17672552689107534303318421)
                    ·
                      refine ⟨828400907301915670468051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17672552689107534303318421 828400907301915670468051)
                      ·
                        rfl

theorem cell23_1613305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_1613305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613305 prefixEnd_1613305 := by exact prefixLift 1613305
  have htrace : WordTrace (prefixWord ++ tailWord_1613305) baseStart_1613305 baseEnd_1613305 := by
    simpa [prefixWord, tailWord_1613305, baseEnd_1613305] using wordTrace_append hprefix tailTrace_1613305
  have hstable : (prefixWord ++ tailWord_1613305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613305).length < 2 ^ (prefixWord ++ tailWord_1613305).sum := by decide
  have hdescent : baseEnd_1613305 < baseStart_1613305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613323 : List Nat := [1, 1, 1, 1, 8, 2, 1, 3, 1, 4]
def baseStart_1613323 : Nat := 118140960795 + 1613323 * 2 ^ 59
def prefixEnd_1613323 : Nat := 4983230072969 + 3 ^ 40 * 1613323 * 2
def baseEnd_1613323 : Nat := 276136716651232200014323

theorem tailTrace_1613323 : CollatzResearch.WordTrace tailWord_1613323 prefixEnd_1613323 276136716651232200014323 := by
  unfold tailWord_1613323
  simp only [CollatzResearch.WordTrace]
  refine ⟨58842723934213779477156623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39228482622809186318104415 58842723934213779477156623)
  ·
    refine ⟨88264085901320669215734935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58842723934213779477156623 88264085901320669215734935)
    ·
      refine ⟨132396128851981003823602403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88264085901320669215734935 132396128851981003823602403)
      ·
        refine ⟨198594193277971505735403605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132396128851981003823602403 198594193277971505735403605)
        ·
          refine ⟨2327275702476228582836761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 198594193277971505735403605 2327275702476228582836761)
          ·
            refine ⟨1745456776857171437127571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2327275702476228582836761 1745456776857171437127571)
            ·
              refine ⟨2618185165285757155691357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1745456776857171437127571 2618185165285757155691357)
              ·
                refine ⟨981819436982158933384259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2618185165285757155691357 981819436982158933384259)
                ·
                  refine ⟨1472729155473238400076389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 981819436982158933384259 1472729155473238400076389)
                  ·
                    refine ⟨276136716651232200014323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1472729155473238400076389 276136716651232200014323)
                    ·
                      rfl

theorem cell23_1613323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3, 1, 4].length) (baseStart_1613323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613323 prefixEnd_1613323 := by exact prefixLift 1613323
  have htrace : WordTrace (prefixWord ++ tailWord_1613323) baseStart_1613323 baseEnd_1613323 := by
    simpa [prefixWord, tailWord_1613323, baseEnd_1613323] using wordTrace_append hprefix tailTrace_1613323
  have hstable : (prefixWord ++ tailWord_1613323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613323).length < 2 ^ (prefixWord ++ tailWord_1613323).sum := by decide
  have hdescent : baseEnd_1613323 < baseStart_1613323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613346 : List Nat := [3, 3, 1, 1, 1, 1, 5, 1, 3, 1, 3]
def baseStart_1613346 : Nat := 118140960795 + 1613346 * 2 ^ 59
def prefixEnd_1613346 : Nat := 4983230072969 + 3 ^ 40 * 1613346 * 2
def baseEnd_1613346 : Nat := 828421960008750010055363

theorem tailTrace_1613346 : CollatzResearch.WordTrace tailWord_1613346 prefixEnd_1613346 828421960008750010055363 := by
  unfold tailWord_1613346
  simp only [CollatzResearch.WordTrace]
  refine ⟨14710890703282613601310973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39229041875420302936829261 14710890703282613601310973)
  ·
    refine ⟨5516584013730980100491615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14710890703282613601310973 5516584013730980100491615)
    ·
      refine ⟨8274876020596470150737423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5516584013730980100491615 8274876020596470150737423)
      ·
        refine ⟨12412314030894705226106135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8274876020596470150737423 12412314030894705226106135)
        ·
          refine ⟨18618471046342057839159203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12412314030894705226106135 18618471046342057839159203)
          ·
            refine ⟨27927706569513086758738805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18618471046342057839159203 27927706569513086758738805)
            ·
              refine ⟨2618222490891851883631763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27927706569513086758738805 2618222490891851883631763)
              ·
                refine ⟨3927333736337777825447645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2618222490891851883631763 3927333736337777825447645)
                ·
                  refine ⟨1472750151126666684542867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3927333736337777825447645 1472750151126666684542867)
                  ·
                    refine ⟨2209125226690000026814301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1472750151126666684542867 2209125226690000026814301)
                    ·
                      refine ⟨828421960008750010055363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2209125226690000026814301 828421960008750010055363)
                      ·
                        rfl

theorem cell23_1613346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_1613346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613346 prefixEnd_1613346 := by exact prefixLift 1613346
  have htrace : WordTrace (prefixWord ++ tailWord_1613346) baseStart_1613346 baseEnd_1613346 := by
    simpa [prefixWord, tailWord_1613346, baseEnd_1613346] using wordTrace_append hprefix tailTrace_1613346
  have hstable : (prefixWord ++ tailWord_1613346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613346).length < 2 ^ (prefixWord ++ tailWord_1613346).sum := by decide
  have hdescent : baseEnd_1613346 < baseStart_1613346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613362 : List Nat := [3, 2, 1, 1, 2, 1, 1, 5, 1, 6]
def baseStart_1613362 : Nat := 118140960795 + 1613362 * 2 ^ 59
def prefixEnd_1613362 : Nat := 4983230072969 + 3 ^ 40 * 1613362 * 2
def baseEnd_1613362 : Nat := 276143391899740649151763

theorem tailTrace_1613362 : CollatzResearch.WordTrace tailWord_1613362 prefixEnd_1613362 276143391899740649151763 := by
  unfold tailWord_1613362
  simp only [CollatzResearch.WordTrace]
  refine ⟨14711036595268122284456585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39229430920714992758550893 14711036595268122284456585)
  ·
    refine ⟨11033277446451091713342439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14711036595268122284456585 11033277446451091713342439)
    ·
      refine ⟨16549916169676637570013659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11033277446451091713342439 16549916169676637570013659)
      ·
        refine ⟨24824874254514956355020489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16549916169676637570013659 24824874254514956355020489)
        ·
          refine ⟨18618655690886217266265367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24824874254514956355020489 18618655690886217266265367)
          ·
            refine ⟨27927983536329325899398051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18618655690886217266265367 27927983536329325899398051)
            ·
              refine ⟨41891975304493988849097077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27927983536329325899398051 41891975304493988849097077)
              ·
                refine ⟨3927372684796311454602851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41891975304493988849097077 3927372684796311454602851)
                ·
                  refine ⟨5891059027194467181904277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3927372684796311454602851 5891059027194467181904277)
                  ·
                    refine ⟨276143391899740649151763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5891059027194467181904277 276143391899740649151763)
                    ·
                      rfl

theorem cell23_1613362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_1613362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613362 prefixEnd_1613362 := by exact prefixLift 1613362
  have htrace : WordTrace (prefixWord ++ tailWord_1613362) baseStart_1613362 baseEnd_1613362 := by
    simpa [prefixWord, tailWord_1613362, baseEnd_1613362] using wordTrace_append hprefix tailTrace_1613362
  have hstable : (prefixWord ++ tailWord_1613362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613362).length < 2 ^ (prefixWord ++ tailWord_1613362).sum := by decide
  have hdescent : baseEnd_1613362 < baseStart_1613362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613366 : List Nat := [5, 1, 2, 1, 3, 1, 1, 1, 3, 5]
def baseStart_1613366 : Nat := 118140960795 + 1613366 * 2 ^ 59
def prefixEnd_1613366 : Nat := 4983230072969 + 3 ^ 40 * 1613366 * 2
def baseEnd_1613366 : Nat := 276144076540613310601757

theorem tailTrace_1613366 : CollatzResearch.WordTrace tailWord_1613366 prefixEnd_1613366 276144076540613310601757 := by
  unfold tailWord_1613366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3677768267066124863810747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39229528182038665213981301 3677768267066124863810747)
  ·
    refine ⟨5516652400599187295716121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3677768267066124863810747 5516652400599187295716121)
    ·
      refine ⟨4137489300449390471787091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5516652400599187295716121 4137489300449390471787091)
      ·
        refine ⟨6206233950674085707680637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4137489300449390471787091 6206233950674085707680637)
        ·
          refine ⟨2327337731502782140380239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6206233950674085707680637 2327337731502782140380239)
          ·
            refine ⟨3491006597254173210570359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2327337731502782140380239 3491006597254173210570359)
            ·
              refine ⟨5236509895881259815855539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3491006597254173210570359 5236509895881259815855539)
              ·
                refine ⟨7854764843821889723783309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5236509895881259815855539 7854764843821889723783309)
                ·
                  refine ⟨2945536816433208646418741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7854764843821889723783309 2945536816433208646418741)
                  ·
                    refine ⟨276144076540613310601757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2945536816433208646418741 276144076540613310601757)
                    ·
                      rfl

theorem cell23_1613366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_1613366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613366 prefixEnd_1613366 := by exact prefixLift 1613366
  have htrace : WordTrace (prefixWord ++ tailWord_1613366) baseStart_1613366 baseEnd_1613366 := by
    simpa [prefixWord, tailWord_1613366, baseEnd_1613366] using wordTrace_append hprefix tailTrace_1613366
  have hstable : (prefixWord ++ tailWord_1613366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613366).length < 2 ^ (prefixWord ++ tailWord_1613366).sum := by decide
  have hdescent : baseEnd_1613366 < baseStart_1613366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613369 : List Nat := [1, 2, 1, 5, 1, 3, 1, 1, 3, 1, 4]
def baseStart_1613369 : Nat := 118140960795 + 1613369 * 2 ^ 59
def prefixEnd_1613369 : Nat := 4983230072969 + 3 ^ 40 * 1613369 * 2
def baseEnd_1613369 : Nat := 828433770063803420067757

theorem tailTrace_1613369 : CollatzResearch.WordTrace tailWord_1613369 prefixEnd_1613369 828433770063803420067757 := by
  unfold tailWord_1613369
  simp only [CollatzResearch.WordTrace]
  refine ⟨58844401692047129333331161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39229601128031419555554107 58844401692047129333331161)
  ·
    refine ⟨44133301269035346999998371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58844401692047129333331161 44133301269035346999998371)
    ·
      refine ⟨66199951903553020499997557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44133301269035346999998371 66199951903553020499997557)
      ·
        refine ⟨6206245490958095671874771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66199951903553020499997557 6206245490958095671874771)
        ·
          refine ⟨9309368236437143507812157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6206245490958095671874771 9309368236437143507812157)
          ·
            refine ⟨3491013088663928815429559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9309368236437143507812157 3491013088663928815429559)
            ·
              refine ⟨5236519632995893223144339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3491013088663928815429559 5236519632995893223144339)
              ·
                refine ⟨7854779449493839834716509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5236519632995893223144339 7854779449493839834716509)
                ·
                  refine ⟨2945542293560189938018691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7854779449493839834716509 2945542293560189938018691)
                  ·
                    refine ⟨4418313440340284907028037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2945542293560189938018691 4418313440340284907028037)
                    ·
                      refine ⟨828433770063803420067757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4418313440340284907028037 828433770063803420067757)
                      ·
                        rfl

theorem cell23_1613369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_1613369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613369 prefixEnd_1613369 := by exact prefixLift 1613369
  have htrace : WordTrace (prefixWord ++ tailWord_1613369) baseStart_1613369 baseEnd_1613369 := by
    simpa [prefixWord, tailWord_1613369, baseEnd_1613369] using wordTrace_append hprefix tailTrace_1613369
  have hstable : (prefixWord ++ tailWord_1613369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613369).length < 2 ^ (prefixWord ++ tailWord_1613369).sum := by decide
  have hdescent : baseEnd_1613369 < baseStart_1613369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613373 : List Nat := [1, 4, 1, 3, 3, 1, 2, 1, 2, 3, 2]
def baseStart_1613373 : Nat := 118140960795 + 1613373 * 2 ^ 59
def prefixEnd_1613373 : Nat := 4983230072969 + 3 ^ 40 * 1613373 * 2
def baseEnd_1613373 : Nat := 828435823986421404417739

theorem tailTrace_1613373 : CollatzResearch.WordTrace tailWord_1613373 prefixEnd_1613373 828435823986421404417739 := by
  unfold tailWord_1613373
  simp only [CollatzResearch.WordTrace]
  refine ⟨58844547584032638016476773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39229698389355092010984515 58844547584032638016476773)
  ·
    refine ⟨11033352672006119628089395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58844547584032638016476773 11033352672006119628089395)
    ·
      refine ⟨16550029008009179442134093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11033352672006119628089395 16550029008009179442134093)
      ·
        refine ⟨6206260878003442290800285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16550029008009179442134093 6206260878003442290800285)
        ·
          refine ⟨2327347829251290859050107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6206260878003442290800285 2327347829251290859050107)
          ·
            refine ⟨3491021743876936288575161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2327347829251290859050107 3491021743876936288575161)
            ·
              refine ⟨2618266307907702216431371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3491021743876936288575161 2618266307907702216431371)
              ·
                refine ⟨3927399461861553324647057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2618266307907702216431371 3927399461861553324647057)
                ·
                  refine ⟨2945549596396164993485293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3927399461861553324647057 2945549596396164993485293)
                  ·
                    refine ⟨1104581098648561872556985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2945549596396164993485293 1104581098648561872556985)
                    ·
                      refine ⟨828435823986421404417739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1104581098648561872556985 828435823986421404417739)
                      ·
                        rfl

theorem cell23_1613373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_1613373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613373 prefixEnd_1613373 := by exact prefixLift 1613373
  have htrace : WordTrace (prefixWord ++ tailWord_1613373) baseStart_1613373 baseEnd_1613373 := by
    simpa [prefixWord, tailWord_1613373, baseEnd_1613373] using wordTrace_append hprefix tailTrace_1613373
  have hstable : (prefixWord ++ tailWord_1613373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613373).length < 2 ^ (prefixWord ++ tailWord_1613373).sum := by decide
  have hdescent : baseEnd_1613373 < baseStart_1613373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613386 : List Nat := [3, 1, 2, 1, 1, 3, 5, 1, 1, 1, 4]
def baseStart_1613386 : Nat := 118140960795 + 1613386 * 2 ^ 59
def prefixEnd_1613386 : Nat := 4983230072969 + 3 ^ 40 * 1613386 * 2
def baseEnd_1613386 : Nat := 828442499234929853555179

theorem tailTrace_1613386 : CollatzResearch.WordTrace tailWord_1613386 prefixEnd_1613386 828442499234929853555179 := by
  unfold tailWord_1613386
  simp only [CollatzResearch.WordTrace]
  refine ⟨14711255433246385309175003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39230014488657027491133341 14711255433246385309175003)
  ·
    refine ⟨22066883149869577963762505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14711255433246385309175003 22066883149869577963762505)
    ·
      refine ⟨16550162362402183472821879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22066883149869577963762505 16550162362402183472821879)
      ·
        refine ⟨24825243543603275209232819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16550162362402183472821879 24825243543603275209232819)
        ·
          refine ⟨37237865315404912813849229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24825243543603275209232819 37237865315404912813849229)
          ·
            refine ⟨13964199493276842305193461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37237865315404912813849229 13964199493276842305193461)
            ·
              refine ⟨1309143702494703966111887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13964199493276842305193461 1309143702494703966111887)
              ·
                refine ⟨1963715553742055949167831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1309143702494703966111887 1963715553742055949167831)
                ·
                  refine ⟨2945573330613083923751747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1963715553742055949167831 2945573330613083923751747)
                  ·
                    refine ⟨4418359995919625885627621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2945573330613083923751747 4418359995919625885627621)
                    ·
                      refine ⟨828442499234929853555179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4418359995919625885627621 828442499234929853555179)
                      ·
                        rfl

theorem cell23_1613386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 1, 1, 4].length) (baseStart_1613386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613386 prefixEnd_1613386 := by exact prefixLift 1613386
  have htrace : WordTrace (prefixWord ++ tailWord_1613386) baseStart_1613386 baseEnd_1613386 := by
    simpa [prefixWord, tailWord_1613386, baseEnd_1613386] using wordTrace_append hprefix tailTrace_1613386
  have hstable : (prefixWord ++ tailWord_1613386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613386).length < 2 ^ (prefixWord ++ tailWord_1613386).sum := by decide
  have hdescent : baseEnd_1613386 < baseStart_1613386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613396 : List Nat := [2, 4, 1, 1, 1, 2, 4, 2, 2, 4]
def baseStart_1613396 : Nat := 118140960795 + 1613396 * 2 ^ 59
def prefixEnd_1613396 : Nat := 4983230072969 + 3 ^ 40 * 1613396 * 2
def baseEnd_1613396 : Nat := 276149211347158271476711

theorem tailTrace_1613396 : CollatzResearch.WordTrace tailWord_1613396 prefixEnd_1613396 276149211347158271476711 := by
  unfold tailWord_1613396
  simp only [CollatzResearch.WordTrace]
  refine ⟨29422693231474656472282021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39230257641966208629709361 29422693231474656472282021)
  ·
    refine ⟨5516754980901498088552879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29422693231474656472282021 5516754980901498088552879)
    ·
      refine ⟨8275132471352247132829319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5516754980901498088552879 8275132471352247132829319)
      ·
        refine ⟨12412698707028370699243979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8275132471352247132829319 12412698707028370699243979)
        ·
          refine ⟨18619048060542556048865969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12412698707028370699243979 18619048060542556048865969)
          ·
            refine ⟨13964286045406917036649477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18619048060542556048865969 13964286045406917036649477)
            ·
              refine ⟨2618303633513796944371777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13964286045406917036649477 2618303633513796944371777)
              ·
                refine ⟨1963727725135347708278833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2618303633513796944371777 1963727725135347708278833)
                ·
                  refine ⟨1472795793851510781209125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1963727725135347708278833 1472795793851510781209125)
                  ·
                    refine ⟨276149211347158271476711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1472795793851510781209125 276149211347158271476711)
                    ·
                      rfl

theorem cell23_1613396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_1613396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613396 prefixEnd_1613396 := by exact prefixLift 1613396
  have htrace : WordTrace (prefixWord ++ tailWord_1613396) baseStart_1613396 baseEnd_1613396 := by
    simpa [prefixWord, tailWord_1613396, baseEnd_1613396] using wordTrace_append hprefix tailTrace_1613396
  have hstable : (prefixWord ++ tailWord_1613396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613396).length < 2 ^ (prefixWord ++ tailWord_1613396).sum := by decide
  have hdescent : baseEnd_1613396 < baseStart_1613396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613416 : List Nat := [2, 1, 4, 3, 1, 2, 2, 1, 1, 2, 4]
def baseStart_1613416 : Nat := 118140960795 + 1613416 * 2 ^ 59
def prefixEnd_1613416 : Nat := 4983230072969 + 3 ^ 40 * 1613416 * 2
def baseEnd_1613416 : Nat := 828457903654564736180041

theorem tailTrace_1613416 : CollatzResearch.WordTrace tailWord_1613416 prefixEnd_1613416 828457903654564736180041 := by
  unfold tailWord_1613416
  simp only [CollatzResearch.WordTrace]
  refine ⟨29423057961438428180146051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39230743948584570906861401 29423057961438428180146051)
  ·
    refine ⟨44134586942157642270219077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29423057961438428180146051 44134586942157642270219077)
    ·
      refine ⟨8275235051654557925666077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44134586942157642270219077 8275235051654557925666077)
      ·
        refine ⟨3103213144370459222124779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8275235051654557925666077 3103213144370459222124779)
        ·
          refine ⟨4654819716555688833187169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3103213144370459222124779 4654819716555688833187169)
          ·
            refine ⟨3491114787416766624890377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4654819716555688833187169 3491114787416766624890377)
            ·
              refine ⟨2618336090562574968667783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3491114787416766624890377 2618336090562574968667783)
              ·
                refine ⟨3927504135843862453001675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2618336090562574968667783 3927504135843862453001675)
                ·
                  refine ⟨5891256203765793679502513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3927504135843862453001675 5891256203765793679502513)
                  ·
                    refine ⟨4418442152824345259626885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5891256203765793679502513 4418442152824345259626885)
                    ·
                      refine ⟨828457903654564736180041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4418442152824345259626885 828457903654564736180041)
                      ·
                        rfl

theorem cell23_1613416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_1613416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613416 prefixEnd_1613416 := by exact prefixLift 1613416
  have htrace : WordTrace (prefixWord ++ tailWord_1613416) baseStart_1613416 baseEnd_1613416 := by
    simpa [prefixWord, tailWord_1613416, baseEnd_1613416] using wordTrace_append hprefix tailTrace_1613416
  have hstable : (prefixWord ++ tailWord_1613416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613416).length < 2 ^ (prefixWord ++ tailWord_1613416).sum := by decide
  have hdescent : baseEnd_1613416 < baseStart_1613416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613452 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 4, 6]
def baseStart_1613452 : Nat := 118140960795 + 1613452 * 2 ^ 59
def prefixEnd_1613452 : Nat := 4983230072969 + 3 ^ 40 * 1613452 * 2
def baseEnd_1613452 : Nat := 276158796319375531776625

theorem tailTrace_1613452 : CollatzResearch.WordTrace tailWord_1613452 prefixEnd_1613452 276158796319375531776625 := by
  unfold tailWord_1613452
  simp only [CollatzResearch.WordTrace]
  refine ⟨29423714475373217254301305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39231619300497623005735073 29423714475373217254301305)
  ·
    refine ⟨22067785856529912940725979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29423714475373217254301305 22067785856529912940725979)
    ·
      refine ⟨33101678784794869411088969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22067785856529912940725979 33101678784794869411088969)
      ·
        refine ⟨24826259088596152058316727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33101678784794869411088969 24826259088596152058316727)
        ·
          refine ⟨37239388632894228087475091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24826259088596152058316727 37239388632894228087475091)
          ·
            refine ⟨55859082949341342131212637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37239388632894228087475091 55859082949341342131212637)
            ·
              refine ⟨20947156106003003299204739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55859082949341342131212637 20947156106003003299204739)
              ·
                refine ⟨31420734159004504948807109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20947156106003003299204739 31420734159004504948807109)
                ·
                  refine ⟨5891387654813344677901333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31420734159004504948807109 5891387654813344677901333)
                  ·
                    refine ⟨276158796319375531776625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5891387654813344677901333 276158796319375531776625)
                    ·
                      rfl

theorem cell23_1613452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 4, 6].length) (baseStart_1613452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613452 prefixEnd_1613452 := by exact prefixLift 1613452
  have htrace : WordTrace (prefixWord ++ tailWord_1613452) baseStart_1613452 baseEnd_1613452 := by
    simpa [prefixWord, tailWord_1613452, baseEnd_1613452] using wordTrace_append hprefix tailTrace_1613452
  have hstable : (prefixWord ++ tailWord_1613452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613452).length < 2 ^ (prefixWord ++ tailWord_1613452).sum := by decide
  have hdescent : baseEnd_1613452 < baseStart_1613452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613574 : List Nat := [6, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4]
def baseStart_1613574 : Nat := 118140960795 + 1613574 * 2 ^ 59
def prefixEnd_1613574 : Nat := 4983230072969 + 3 ^ 40 * 1613574 * 2
def baseEnd_1613574 : Nat := 828539033597975118004315

theorem tailTrace_1613574 : CollatzResearch.WordTrace tailWord_1613574 prefixEnd_1613574 828539033597975118004315 := by
  unfold tailWord_1613574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1839121208009514042016993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39234585770869632896362517 1839121208009514042016993)
  ·
    refine ⟨1379340906007135531512745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1839121208009514042016993 1379340906007135531512745)
    ·
      refine ⟨1034505679505351648634559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1379340906007135531512745 1034505679505351648634559)
      ·
        refine ⟨1551758519258027472951839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1034505679505351648634559 1551758519258027472951839)
        ·
          refine ⟨2327637778887041209427759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1551758519258027472951839 2327637778887041209427759)
          ·
            refine ⟨3491456668330561814141639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2327637778887041209427759 3491456668330561814141639)
            ·
              refine ⟨5237185002495842721212459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3491456668330561814141639 5237185002495842721212459)
              ·
                refine ⟨7855777503743764081818689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5237185002495842721212459 7855777503743764081818689)
                ·
                  refine ⟨5891833127807823061364017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7855777503743764081818689 5891833127807823061364017)
                  ·
                    refine ⟨4418874845855867296023013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5891833127807823061364017 4418874845855867296023013)
                    ·
                      refine ⟨828539033597975118004315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4418874845855867296023013 828539033597975118004315)
                      ·
                        rfl

theorem cell23_1613574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_1613574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613574 prefixEnd_1613574 := by exact prefixLift 1613574
  have htrace : WordTrace (prefixWord ++ tailWord_1613574) baseStart_1613574 baseEnd_1613574 := by
    simpa [prefixWord, tailWord_1613574, baseEnd_1613574] using wordTrace_append hprefix tailTrace_1613574
  have hstable : (prefixWord ++ tailWord_1613574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613574).length < 2 ^ (prefixWord ++ tailWord_1613574).sum := by decide
  have hdescent : baseEnd_1613574 < baseStart_1613574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613576 : List Nat := [2, 1, 3, 2, 2, 1, 2, 3, 3, 4]
def baseStart_1613576 : Nat := 118140960795 + 1613576 * 2 ^ 59
def prefixEnd_1613576 : Nat := 4983230072969 + 3 ^ 40 * 1613576 * 2
def baseEnd_1613576 : Nat := 276180020186428036726435

theorem tailTrace_1613576 : CollatzResearch.WordTrace tailWord_1613576 prefixEnd_1613576 276180020186428036726435 := by
  unfold tailWord_1613576
  simp only [CollatzResearch.WordTrace]
  refine ⟨29425975801148601843058291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39234634401531469124077721 29425975801148601843058291)
  ·
    refine ⟨44138963701722902764587437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29425975801148601843058291 44138963701722902764587437)
    ·
      refine ⟨16552111388146088536720289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44138963701722902764587437 16552111388146088536720289)
      ·
        refine ⟨12414083541109566402540217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16552111388146088536720289 12414083541109566402540217)
        ·
          refine ⟨9310562655832174801905163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12414083541109566402540217 9310562655832174801905163)
          ·
            refine ⟨13965843983748262202857745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9310562655832174801905163 13965843983748262202857745)
            ·
              refine ⟨10474382987811196652143309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13965843983748262202857745 10474382987811196652143309)
              ·
                refine ⟨3927893620429198744553741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10474382987811196652143309 3927893620429198744553741)
                ·
                  refine ⟨1472960107660949529207653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3927893620429198744553741 1472960107660949529207653)
                  ·
                    refine ⟨276180020186428036726435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1472960107660949529207653 276180020186428036726435)
                    ·
                      rfl

theorem cell23_1613576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_1613576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613576 prefixEnd_1613576 := by exact prefixLift 1613576
  have htrace : WordTrace (prefixWord ++ tailWord_1613576) baseStart_1613576 baseEnd_1613576 := by
    simpa [prefixWord, tailWord_1613576, baseEnd_1613576] using wordTrace_append hprefix tailTrace_1613576
  have hstable : (prefixWord ++ tailWord_1613576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613576).length < 2 ^ (prefixWord ++ tailWord_1613576).sum := by decide
  have hdescent : baseEnd_1613576 < baseStart_1613576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613653 : List Nat := [1, 3, 2, 2, 2, 3, 2, 2, 1, 5]
def baseStart_1613653 : Nat := 118140960795 + 1613653 * 2 ^ 59
def prefixEnd_1613653 : Nat := 4983230072969 + 3 ^ 40 * 1613653 * 2
def baseEnd_1613653 : Nat := 276193199523226769638817

theorem tailTrace_1613653 : CollatzResearch.WordTrace tailWord_1613653 prefixEnd_1613653 276193199523226769638817 := by
  unfold tailWord_1613653
  simp only [CollatzResearch.WordTrace]
  refine ⟨58854760023018245836669613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39236506682012163891113075 58854760023018245836669613)
  ·
    refine ⟨22070535008631842188751105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58854760023018245836669613 22070535008631842188751105)
    ·
      refine ⟨16552901256473881641563329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22070535008631842188751105 16552901256473881641563329)
      ·
        refine ⟨12414675942355411231172497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16552901256473881641563329 12414675942355411231172497)
        ·
          refine ⟨9311006956766558423379373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12414675942355411231172497 9311006956766558423379373)
          ·
            refine ⟨3491627608787459408767265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9311006956766558423379373 3491627608787459408767265)
            ·
              refine ⟨2618720706590594556575449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3491627608787459408767265 2618720706590594556575449)
              ·
                refine ⟨1964040529942945917431587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2618720706590594556575449 1964040529942945917431587)
                ·
                  refine ⟨2946060794914418876147381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1964040529942945917431587 2946060794914418876147381)
                  ·
                    refine ⟨276193199523226769638817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2946060794914418876147381 276193199523226769638817)
                    ·
                      rfl

theorem cell23_1613653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_1613653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613653 prefixEnd_1613653 := by exact prefixLift 1613653
  have htrace : WordTrace (prefixWord ++ tailWord_1613653) baseStart_1613653 baseEnd_1613653 := by
    simpa [prefixWord, tailWord_1613653, baseEnd_1613653] using wordTrace_append hprefix tailTrace_1613653
  have hstable : (prefixWord ++ tailWord_1613653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613653).length < 2 ^ (prefixWord ++ tailWord_1613653).sum := by decide
  have hdescent : baseEnd_1613653 < baseStart_1613653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613673 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 5, 2, 2]
def baseStart_1613673 : Nat := 118140960795 + 1613673 * 2 ^ 59
def prefixEnd_1613673 : Nat := 4983230072969 + 3 ^ 40 * 1613673 * 2
def baseEnd_1613673 : Nat := 828589868182770230666359

theorem tailTrace_1613673 : CollatzResearch.WordTrace tailWord_1613673 prefixEnd_1613673 828589868182770230666359 := by
  unfold tailWord_1613673
  simp only [CollatzResearch.WordTrace]
  refine ⟨58855489482945789252397673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39236992988630526168265115 58855489482945789252397673)
  ·
    refine ⟨44141617112209341939298255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58855489482945789252397673 44141617112209341939298255)
    ·
      refine ⟨66212425668314012908947383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44141617112209341939298255 66212425668314012908947383)
      ·
        refine ⟨99318638502471019363421075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66212425668314012908947383 99318638502471019363421075)
        ·
          refine ⟨148977957753706529045131613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99318638502471019363421075 148977957753706529045131613)
          ·
            refine ⟨55866734157639948391924355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148977957753706529045131613 55866734157639948391924355)
            ·
              refine ⟨83800101236459922587886533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55866734157639948391924355 83800101236459922587886533)
              ·
                refine ⟨15712518981836235485228725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83800101236459922587886533 15712518981836235485228725)
                ·
                  refine ⟨1473048654547147076740193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15712518981836235485228725 1473048654547147076740193)
                  ·
                    refine ⟨1104786490910360307555145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1473048654547147076740193 1104786490910360307555145)
                    ·
                      refine ⟨828589868182770230666359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1104786490910360307555145 828589868182770230666359)
                      ·
                        rfl

theorem cell23_1613673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5, 2, 2].length) (baseStart_1613673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613673 prefixEnd_1613673 := by exact prefixLift 1613673
  have htrace : WordTrace (prefixWord ++ tailWord_1613673) baseStart_1613673 baseEnd_1613673 := by
    simpa [prefixWord, tailWord_1613673, baseEnd_1613673] using wordTrace_append hprefix tailTrace_1613673
  have hstable : (prefixWord ++ tailWord_1613673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613673).length < 2 ^ (prefixWord ++ tailWord_1613673).sum := by decide
  have hdescent : baseEnd_1613673 < baseStart_1613673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613676 : List Nat := [2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 5]
def baseStart_1613676 : Nat := 118140960795 + 1613676 * 2 ^ 59
def prefixEnd_1613676 : Nat := 4983230072969 + 3 ^ 40 * 1613676 * 2
def baseEnd_1613676 : Nat := 828591408624733718928845

theorem tailTrace_1613676 : CollatzResearch.WordTrace tailWord_1613676 prefixEnd_1613676 828591408624733718928845 := by
  unfold tailWord_1613676
  simp only [CollatzResearch.WordTrace]
  refine ⟨29427799450967460382378441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39237065934623280509837921 29427799450967460382378441)
  ·
    refine ⟨22070849588225595286783831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29427799450967460382378441 22070849588225595286783831)
    ·
      refine ⟨33106274382338392930175747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22070849588225595286783831 33106274382338392930175747)
      ·
        refine ⟨49659411573507589395263621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33106274382338392930175747 49659411573507589395263621)
        ·
          refine ⟨9311139670032673011611929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49659411573507589395263621 9311139670032673011611929)
          ·
            refine ⟨6983354752524504758708947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9311139670032673011611929 6983354752524504758708947)
            ·
              refine ⟨10475032128786757138063421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6983354752524504758708947 10475032128786757138063421)
              ·
                refine ⟨3928137048295033926773783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10475032128786757138063421 3928137048295033926773783)
                ·
                  refine ⟨5892205572442550890160675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3928137048295033926773783 5892205572442550890160675)
                  ·
                    refine ⟨8838308358663826335241013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5892205572442550890160675 8838308358663826335241013)
                    ·
                      refine ⟨828591408624733718928845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8838308358663826335241013 828591408624733718928845)
                      ·
                        rfl

theorem cell23_1613676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_1613676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613676 prefixEnd_1613676 := by exact prefixLift 1613676
  have htrace : WordTrace (prefixWord ++ tailWord_1613676) baseStart_1613676 baseEnd_1613676 := by
    simpa [prefixWord, tailWord_1613676, baseEnd_1613676] using wordTrace_append hprefix tailTrace_1613676
  have hstable : (prefixWord ++ tailWord_1613676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613676).length < 2 ^ (prefixWord ++ tailWord_1613676).sum := by decide
  have hdescent : baseEnd_1613676 < baseStart_1613676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613690 : List Nat := [3, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2]
def baseStart_1613690 : Nat := 118140960795 + 1613690 * 2 ^ 59
def prefixEnd_1613690 : Nat := 4983230072969 + 3 ^ 40 * 1613690 * 2
def baseEnd_1613690 : Nat := 828598597353896664153781

theorem tailTrace_1613690 : CollatzResearch.WordTrace tailWord_1613690 prefixEnd_1613690 828598597353896664153781 := by
  unfold tailWord_1613690
  simp only [CollatzResearch.WordTrace]
  refine ⟨14714027380971050288941631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39237406349256134103844349 14714027380971050288941631)
  ·
    refine ⟨22071041071456575433412447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14714027380971050288941631 22071041071456575433412447)
    ·
      refine ⟨33106561607184863150118671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22071041071456575433412447 33106561607184863150118671)
      ·
        refine ⟨49659842410777294725178007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33106561607184863150118671 49659842410777294725178007)
        ·
          refine ⟨74489763616165942087767011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49659842410777294725178007 74489763616165942087767011)
          ·
            refine ⟨111734645424248913131650517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74489763616165942087767011 111734645424248913131650517)
            ·
              refine ⟨2618780752130833901523059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 111734645424248913131650517 2618780752130833901523059)
              ·
                refine ⟨3928171128196250852284589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2618780752130833901523059 3928171128196250852284589)
                ·
                  refine ⟨1473064173073594069606721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3928171128196250852284589 1473064173073594069606721)
                  ·
                    refine ⟨1104798129805195552205041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1473064173073594069606721 1104798129805195552205041)
                    ·
                      refine ⟨828598597353896664153781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1104798129805195552205041 828598597353896664153781)
                      ·
                        rfl

theorem cell23_1613690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2].length) (baseStart_1613690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613690 prefixEnd_1613690 := by exact prefixLift 1613690
  have htrace : WordTrace (prefixWord ++ tailWord_1613690) baseStart_1613690 baseEnd_1613690 := by
    simpa [prefixWord, tailWord_1613690, baseEnd_1613690] using wordTrace_append hprefix tailTrace_1613690
  have hstable : (prefixWord ++ tailWord_1613690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613690).length < 2 ^ (prefixWord ++ tailWord_1613690).sum := by decide
  have hdescent : baseEnd_1613690 < baseStart_1613690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613700 : List Nat := [2, 3, 2, 1, 1, 1, 6, 1, 2, 4]
def baseStart_1613700 : Nat := 118140960795 + 1613700 * 2 ^ 59
def prefixEnd_1613700 : Nat := 4983230072969 + 3 ^ 40 * 1613700 * 2
def baseEnd_1613700 : Nat := 276201244053480541676245

theorem tailTrace_1613700 : CollatzResearch.WordTrace tailWord_1613700 prefixEnd_1613700 276201244053480541676245 := by
  unfold tailWord_1613700
  simp only [CollatzResearch.WordTrace]
  refine ⟨29428237126923986431815277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39237649502565315242420369 29428237126923986431815277)
  ·
    refine ⟨11035588922596494911930729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29428237126923986431815277 11035588922596494911930729)
    ·
      refine ⟨8276691691947371183948047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11035588922596494911930729 8276691691947371183948047)
      ·
        refine ⟨12415037537921056775922071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8276691691947371183948047 12415037537921056775922071)
        ·
          refine ⟨18622556306881585163883107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12415037537921056775922071 18622556306881585163883107)
          ·
            refine ⟨27933834460322377745824661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18622556306881585163883107 27933834460322377745824661)
            ·
              refine ⟨1309398490327611456835531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27933834460322377745824661 1309398490327611456835531)
              ·
                refine ⟨1964097735491417185253297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1309398490327611456835531 1964097735491417185253297)
                ·
                  refine ⟨1473073301618562888939973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1964097735491417185253297 1473073301618562888939973)
                  ·
                    refine ⟨276201244053480541676245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1473073301618562888939973 276201244053480541676245)
                    ·
                      rfl

theorem cell23_1613700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_1613700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613700 prefixEnd_1613700 := by exact prefixLift 1613700
  have htrace : WordTrace (prefixWord ++ tailWord_1613700) baseStart_1613700 baseEnd_1613700 := by
    simpa [prefixWord, tailWord_1613700, baseEnd_1613700] using wordTrace_append hprefix tailTrace_1613700
  have hstable : (prefixWord ++ tailWord_1613700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613700).length < 2 ^ (prefixWord ++ tailWord_1613700).sum := by decide
  have hdescent : baseEnd_1613700 < baseStart_1613700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613720 : List Nat := [2, 1, 2, 6, 1, 1, 1, 2, 1, 2, 4]
def baseStart_1613720 : Nat := 118140960795 + 1613720 * 2 ^ 59
def prefixEnd_1613720 : Nat := 4983230072969 + 3 ^ 40 * 1613720 * 2
def baseEnd_1613720 : Nat := 828614001773531546778643

theorem tailTrace_1613720 : CollatzResearch.WordTrace tailWord_1613720 prefixEnd_1613720 828614001773531546778643 := by
  unfold tailWord_1613720
  simp only [CollatzResearch.WordTrace]
  refine ⟨29428601856887758139679307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39238135809183677519572409 29428601856887758139679307)
  ·
    refine ⟨44142902785331637209518961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29428601856887758139679307 44142902785331637209518961)
    ·
      refine ⟨33107177088998727907139221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44142902785331637209518961 33107177088998727907139221)
      ·
        refine ⟨1551898926046815370647151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33107177088998727907139221 1551898926046815370647151)
        ·
          refine ⟨2327848389070223055970727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1551898926046815370647151 2327848389070223055970727)
          ·
            refine ⟨3491772583605334583956091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2327848389070223055970727 3491772583605334583956091)
            ·
              refine ⟨5237658875408001875934137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3491772583605334583956091 5237658875408001875934137)
              ·
                refine ⟨3928244156556001406950603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5237658875408001875934137 3928244156556001406950603)
                ·
                  refine ⟨5892366234834002110425905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3928244156556001406950603 5892366234834002110425905)
                  ·
                    refine ⟨4419274676125501582819429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5892366234834002110425905 4419274676125501582819429)
                    ·
                      refine ⟨828614001773531546778643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4419274676125501582819429 828614001773531546778643)
                      ·
                        rfl

theorem cell23_1613720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_1613720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613720 prefixEnd_1613720 := by exact prefixLift 1613720
  have htrace : WordTrace (prefixWord ++ tailWord_1613720) baseStart_1613720 baseEnd_1613720 := by
    simpa [prefixWord, tailWord_1613720, baseEnd_1613720] using wordTrace_append hprefix tailTrace_1613720
  have hstable : (prefixWord ++ tailWord_1613720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613720).length < 2 ^ (prefixWord ++ tailWord_1613720).sum := by decide
  have hdescent : baseEnd_1613720 < baseStart_1613720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613727 : List Nat := [1, 1, 2, 5, 3, 1, 3, 1, 1, 2, 3]
def baseStart_1613727 : Nat := 118140960795 + 1613727 * 2 ^ 59
def prefixEnd_1613727 : Nat := 4983230072969 + 3 ^ 40 * 1613727 * 2
def baseEnd_1613727 : Nat := 828617596138113019391111

theorem tailTrace_1613727 : CollatzResearch.WordTrace tailWord_1613727 prefixEnd_1613727 828617596138113019391111 := by
  unfold tailWord_1613727
  simp only [CollatzResearch.WordTrace]
  refine ⟨58857459024750156474863435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39238306016500104316575623 58857459024750156474863435)
  ·
    refine ⟨88286188537125234712295153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58857459024750156474863435 88286188537125234712295153)
    ·
      refine ⟨66214641402843926034221365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88286188537125234712295153 66214641402843926034221365)
      ·
        refine ⟨6207622631516618065708253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66214641402843926034221365 6207622631516618065708253)
        ·
          refine ⟨2327858486818731774640595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6207622631516618065708253 2327858486818731774640595)
          ·
            refine ⟨3491787730228097661960893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2327858486818731774640595 3491787730228097661960893)
            ·
              refine ⟨1309420398835536623235335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3491787730228097661960893 1309420398835536623235335)
              ·
                refine ⟨1964130598253304934853003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1309420398835536623235335 1964130598253304934853003)
                ·
                  refine ⟨2946195897379957402279505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1964130598253304934853003 2946195897379957402279505)
                  ·
                    refine ⟨2209646923034968051709629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2946195897379957402279505 2209646923034968051709629)
                    ·
                      refine ⟨828617596138113019391111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2209646923034968051709629 828617596138113019391111)
                      ·
                        rfl

theorem cell23_1613727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_1613727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613727 prefixEnd_1613727 := by exact prefixLift 1613727
  have htrace : WordTrace (prefixWord ++ tailWord_1613727) baseStart_1613727 baseEnd_1613727 := by
    simpa [prefixWord, tailWord_1613727, baseEnd_1613727] using wordTrace_append hprefix tailTrace_1613727
  have hstable : (prefixWord ++ tailWord_1613727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613727).length < 2 ^ (prefixWord ++ tailWord_1613727).sum := by decide
  have hdescent : baseEnd_1613727 < baseStart_1613727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613780 : List Nat := [2, 4, 1, 2, 1, 1, 1, 4, 1, 4, 2]
def baseStart_1613780 : Nat := 118140960795 + 1613780 * 2 ^ 59
def prefixEnd_1613780 : Nat := 4983230072969 + 3 ^ 40 * 1613780 * 2
def baseEnd_1613780 : Nat := 828644810612801312028367

theorem tailTrace_1613780 : CollatzResearch.WordTrace tailWord_1613780 prefixEnd_1613780 828644810612801312028367 := by
  unfold tailWord_1613780
  simp only [CollatzResearch.WordTrace]
  refine ⟨29429696046779073263271397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39239594729038764351028529 29429696046779073263271397)
  ·
    refine ⟨5518068008771076236863387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29429696046779073263271397 5518068008771076236863387)
    ·
      refine ⟨8277102013156614355295081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5518068008771076236863387 8277102013156614355295081)
      ·
        refine ⟨6207826509867460766471311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8277102013156614355295081 6207826509867460766471311)
        ·
          refine ⟨9311739764801191149706967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6207826509867460766471311 9311739764801191149706967)
          ·
            refine ⟨13967609647201786724560451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9311739764801191149706967 13967609647201786724560451)
            ·
              refine ⟨20951414470802680086840677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13967609647201786724560451 20951414470802680086840677)
              ·
                refine ⟨3928390213275502516282627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20951414470802680086840677 3928390213275502516282627)
                ·
                  refine ⟨5892585319913253774423941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3928390213275502516282627 5892585319913253774423941)
                  ·
                    refine ⟨1104859747483735082704489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5892585319913253774423941 1104859747483735082704489)
                    ·
                      refine ⟨828644810612801312028367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1104859747483735082704489 828644810612801312028367)
                      ·
                        rfl

theorem cell23_1613780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_1613780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613780 prefixEnd_1613780 := by exact prefixLift 1613780
  have htrace : WordTrace (prefixWord ++ tailWord_1613780) baseStart_1613780 baseEnd_1613780 := by
    simpa [prefixWord, tailWord_1613780, baseEnd_1613780] using wordTrace_append hprefix tailTrace_1613780
  have hstable : (prefixWord ++ tailWord_1613780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613780).length < 2 ^ (prefixWord ++ tailWord_1613780).sum := by decide
  have hdescent : baseEnd_1613780 < baseStart_1613780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613814 : List Nat := [5, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2]
def baseStart_1613814 : Nat := 118140960795 + 1613814 * 2 ^ 59
def prefixEnd_1613814 : Nat := 4983230072969 + 3 ^ 40 * 1613814 * 2
def baseEnd_1613814 : Nat := 828662268955054179003211

theorem tailTrace_1613814 : CollatzResearch.WordTrace tailWord_1613814 prefixEnd_1613814 828662268955054179003211 := by
  unfold tailWord_1613814
  simp only [CollatzResearch.WordTrace]
  refine ⟨3678789510964685645830031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39240421450289980222186997 3678789510964685645830031)
  ·
    refine ⟨5518184266447028468745047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3678789510964685645830031 5518184266447028468745047)
    ·
      refine ⟨8277276399670542703117571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5518184266447028468745047 8277276399670542703117571)
      ·
        refine ⟨12415914599505814054676357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8277276399670542703117571 12415914599505814054676357)
        ·
          refine ⟨2327983987407340135251817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12415914599505814054676357 2327983987407340135251817)
          ·
            refine ⟨1745987990555505101438863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2327983987407340135251817 1745987990555505101438863)
            ·
              refine ⟨2618981985833257652158295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1745987990555505101438863 2618981985833257652158295)
              ·
                refine ⟨3928472978749886478237443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2618981985833257652158295 3928472978749886478237443)
                ·
                  refine ⟨5892709468124829717356165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3928472978749886478237443 5892709468124829717356165)
                  ·
                    refine ⟨1104883025273405572004281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5892709468124829717356165 1104883025273405572004281)
                    ·
                      refine ⟨828662268955054179003211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1104883025273405572004281 828662268955054179003211)
                      ·
                        rfl

theorem cell23_1613814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_1613814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613814 prefixEnd_1613814 := by exact prefixLift 1613814
  have htrace : WordTrace (prefixWord ++ tailWord_1613814) baseStart_1613814 baseEnd_1613814 := by
    simpa [prefixWord, tailWord_1613814, baseEnd_1613814] using wordTrace_append hprefix tailTrace_1613814
  have hstable : (prefixWord ++ tailWord_1613814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613814).length < 2 ^ (prefixWord ++ tailWord_1613814).sum := by decide
  have hdescent : baseEnd_1613814 < baseStart_1613814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613816 : List Nat := [2, 1, 2, 1, 1, 3, 3, 2, 1, 7]
def baseStart_1613816 : Nat := 118140960795 + 1613816 * 2 ^ 59
def prefixEnd_1613816 : Nat := 4983230072969 + 3 ^ 40 * 1613816 * 2
def baseEnd_1613816 : Nat := 276221098638787723726067

theorem tailTrace_1613816 : CollatzResearch.WordTrace tailWord_1613816 prefixEnd_1613816 276221098638787723726067 := by
  unfold tailWord_1613816
  simp only [CollatzResearch.WordTrace]
  refine ⟨29430352560713862337426651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39240470080951816449902201 29430352560713862337426651)
  ·
    refine ⟨44145528841070793506139977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29430352560713862337426651 44145528841070793506139977)
    ·
      refine ⟨33109146630803095129604983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44145528841070793506139977 33109146630803095129604983)
      ·
        refine ⟨49663719946204642694407475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33109146630803095129604983 49663719946204642694407475)
        ·
          refine ⟨74495579919306964041611213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49663719946204642694407475 74495579919306964041611213)
          ·
            refine ⟨27935842469740111515604205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74495579919306964041611213 27935842469740111515604205)
            ·
              refine ⟨10475940926152541818351577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27935842469740111515604205 10475940926152541818351577)
              ·
                refine ⟨7856955694614406363763683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10475940926152541818351577 7856955694614406363763683)
                ·
                  refine ⟨11785433541921609545645525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7856955694614406363763683 11785433541921609545645525)
                  ·
                    refine ⟨276221098638787723726067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11785433541921609545645525 276221098638787723726067)
                    ·
                      rfl

theorem cell23_1613816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 1, 7].length) (baseStart_1613816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613816 prefixEnd_1613816 := by exact prefixLift 1613816
  have htrace : WordTrace (prefixWord ++ tailWord_1613816) baseStart_1613816 baseEnd_1613816 := by
    simpa [prefixWord, tailWord_1613816, baseEnd_1613816] using wordTrace_append hprefix tailTrace_1613816
  have hstable : (prefixWord ++ tailWord_1613816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613816).length < 2 ^ (prefixWord ++ tailWord_1613816).sum := by decide
  have hdescent : baseEnd_1613816 < baseStart_1613816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613823 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 2, 5, 2]
def baseStart_1613823 : Nat := 118140960795 + 1613823 * 2 ^ 59
def prefixEnd_1613823 : Nat := 4983230072969 + 3 ^ 40 * 1613823 * 2
def baseEnd_1613823 : Nat := 828666890280944643790669

theorem tailTrace_1613823 : CollatzResearch.WordTrace tailWord_1613823 prefixEnd_1613823 828666890280944643790669 := by
  unfold tailWord_1613823
  simp only [CollatzResearch.WordTrace]
  refine ⟨58860960432402364870358123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39240640288268243246905415 58860960432402364870358123)
  ·
    refine ⟨88291440648603547305537185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58860960432402364870358123 88291440648603547305537185)
    ·
      refine ⟨66218580486452660479152889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88291440648603547305537185 66218580486452660479152889)
      ·
        refine ⟨49663935364839495359364667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66218580486452660479152889 49663935364839495359364667)
        ·
          refine ⟨74495903047259243039047001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49663935364839495359364667 74495903047259243039047001)
          ·
            refine ⟨55871927285444432279285251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74495903047259243039047001 55871927285444432279285251)
            ·
              refine ⟨83807890928166648418927877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55871927285444432279285251 83807890928166648418927877)
              ·
                refine ⟨15713979549031246578548977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83807890928166648418927877 15713979549031246578548977)
                ·
                  refine ⟨11785484661773434933911733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15713979549031246578548977 11785484661773434933911733)
                  ·
                    refine ⟨1104889187041259525054225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11785484661773434933911733 1104889187041259525054225)
                    ·
                      refine ⟨828666890280944643790669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1104889187041259525054225 828666890280944643790669)
                      ·
                        rfl

theorem cell23_1613823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 5, 2].length) (baseStart_1613823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613823 prefixEnd_1613823 := by exact prefixLift 1613823
  have htrace : WordTrace (prefixWord ++ tailWord_1613823) baseStart_1613823 baseEnd_1613823 := by
    simpa [prefixWord, tailWord_1613823, baseEnd_1613823] using wordTrace_append hprefix tailTrace_1613823
  have hstable : (prefixWord ++ tailWord_1613823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613823).length < 2 ^ (prefixWord ++ tailWord_1613823).sum := by decide
  have hdescent : baseEnd_1613823 < baseStart_1613823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613860 : List Nat := [2, 3, 1, 4, 2, 1, 1, 1, 1, 2, 5]
def baseStart_1613860 : Nat := 118140960795 + 1613860 * 2 ^ 59
def prefixEnd_1613860 : Nat := 4983230072969 + 3 ^ 40 * 1613860 * 2
def baseEnd_1613860 : Nat := 828685889065160999027999

theorem tailTrace_1613860 : CollatzResearch.WordTrace tailWord_1613860 prefixEnd_1613860 828685889065160999027999 := by
  unfold tailWord_1613860
  simp only [CollatzResearch.WordTrace]
  refine ⟨29431154966634160094727517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39241539955512213459636689 29431154966634160094727517)
  ·
    refine ⟨11036683112487810035522819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29431154966634160094727517 11036683112487810035522819)
    ·
      refine ⟨16555024668731715053284229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11036683112487810035522819 16555024668731715053284229)
      ·
        refine ⟨3104067125387196572490793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16555024668731715053284229 3104067125387196572490793)
        ·
          refine ⟨2328050344040397429368095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3104067125387196572490793 2328050344040397429368095)
          ·
            refine ⟨3492075516060596144052143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2328050344040397429368095 3492075516060596144052143)
            ·
              refine ⟨5238113274090894216078215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3492075516060596144052143 5238113274090894216078215)
              ·
                refine ⟨7857169911136341324117323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5238113274090894216078215 7857169911136341324117323)
                ·
                  refine ⟨11785754866704511986175985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7857169911136341324117323 11785754866704511986175985)
                  ·
                    refine ⟨8839316150028383989631989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11785754866704511986175985 8839316150028383989631989)
                    ·
                      refine ⟨828685889065160999027999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8839316150028383989631989 828685889065160999027999)
                      ·
                        rfl

theorem cell23_1613860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_1613860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613860 prefixEnd_1613860 := by exact prefixLift 1613860
  have htrace : WordTrace (prefixWord ++ tailWord_1613860) baseStart_1613860 baseEnd_1613860 := by
    simpa [prefixWord, tailWord_1613860, baseEnd_1613860] using wordTrace_append hprefix tailTrace_1613860
  have hstable : (prefixWord ++ tailWord_1613860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613860).length < 2 ^ (prefixWord ++ tailWord_1613860).sum := by decide
  have hdescent : baseEnd_1613860 < baseStart_1613860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613923 : List Nat := [1, 1, 1, 5, 1, 1, 3, 2, 3, 5]
def baseStart_1613923 : Nat := 118140960795 + 1613923 * 2 ^ 59
def prefixEnd_1613923 : Nat := 4983230072969 + 3 ^ 40 * 1613923 * 2
def baseEnd_1613923 : Nat := 276239412782131417513403

theorem tailTrace_1613923 : CollatzResearch.WordTrace tailWord_1613923 prefixEnd_1613923 276239412782131417513403 := by
  unfold tailWord_1613923
  simp only [CollatzResearch.WordTrace]
  refine ⟨58864607732040081948998423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39243071821360054632665615 58864607732040081948998423)
  ·
    refine ⟨88296911598060122923497635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58864607732040081948998423 88296911598060122923497635)
    ·
      refine ⟨132445367397090184385246453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88296911598060122923497635 132445367397090184385246453)
      ·
        refine ⟨12416753193477204786116855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132445367397090184385246453 12416753193477204786116855)
        ·
          refine ⟨18625129790215807179175283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12416753193477204786116855 18625129790215807179175283)
          ·
            refine ⟨27937694685323710768762925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18625129790215807179175283 27937694685323710768762925)
            ·
              refine ⟨10476635506996391538286097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27937694685323710768762925 10476635506996391538286097)
              ·
                refine ⟨7857476630247293653714573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10476635506996391538286097 7857476630247293653714573)
                ·
                  refine ⟨2946553736342735120142965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7857476630247293653714573 2946553736342735120142965)
                  ·
                    refine ⟨276239412782131417513403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2946553736342735120142965 276239412782131417513403)
                    ·
                      rfl

theorem cell23_1613923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 5].length) (baseStart_1613923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613923 prefixEnd_1613923 := by exact prefixLift 1613923
  have htrace : WordTrace (prefixWord ++ tailWord_1613923) baseStart_1613923 baseEnd_1613923 := by
    simpa [prefixWord, tailWord_1613923, baseEnd_1613923] using wordTrace_append hprefix tailTrace_1613923
  have hstable : (prefixWord ++ tailWord_1613923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613923).length < 2 ^ (prefixWord ++ tailWord_1613923).sum := by decide
  have hdescent : baseEnd_1613923 < baseStart_1613923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613933 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_1613933 : Nat := 118140960795 + 1613933 * 2 ^ 59
def prefixEnd_1613933 : Nat := 4983230072969 + 3 ^ 40 * 1613933 * 2
def baseEnd_1613933 : Nat := 828723373152939213415163

theorem tailTrace_1613933 : CollatzResearch.WordTrace tailWord_1613933 prefixEnd_1613933 828723373152939213415163 := by
  unfold tailWord_1613933
  simp only [CollatzResearch.WordTrace]
  refine ⟨58864972462003853656862453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39243314974669235771241635 58864972462003853656862453)
  ·
    refine ⟨5518591168312861280330855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58864972462003853656862453 5518591168312861280330855)
    ·
      refine ⟨8277886752469291920496283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5518591168312861280330855 8277886752469291920496283)
      ·
        refine ⟨12416830128703937880744425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8277886752469291920496283 12416830128703937880744425)
        ·
          refine ⟨9312622596527953410558319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12416830128703937880744425 9312622596527953410558319)
          ·
            refine ⟨13968933894791930115837479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9312622596527953410558319 13968933894791930115837479)
            ·
              refine ⟨20953400842187895173756219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13968933894791930115837479 20953400842187895173756219)
              ·
                refine ⟨31430101263281842760634329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20953400842187895173756219 31430101263281842760634329)
                ·
                  refine ⟨23572575947461382070475747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31430101263281842760634329 23572575947461382070475747)
                  ·
                    refine ⟨35358863921192073105713621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23572575947461382070475747 35358863921192073105713621)
                    ·
                      refine ⟨828723373152939213415163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 35358863921192073105713621 828723373152939213415163)
                      ·
                        rfl

theorem cell23_1613933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_1613933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613933 prefixEnd_1613933 := by exact prefixLift 1613933
  have htrace : WordTrace (prefixWord ++ tailWord_1613933) baseStart_1613933 baseEnd_1613933 := by
    simpa [prefixWord, tailWord_1613933, baseEnd_1613933] using wordTrace_append hprefix tailTrace_1613933
  have hstable : (prefixWord ++ tailWord_1613933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613933).length < 2 ^ (prefixWord ++ tailWord_1613933).sum := by decide
  have hdescent : baseEnd_1613933 < baseStart_1613933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613957 : List Nat := [1, 3, 1, 1, 5, 1, 4, 1, 1, 5]
def baseStart_1613957 : Nat := 118140960795 + 1613957 * 2 ^ 59
def prefixEnd_1613957 : Nat := 4983230072969 + 3 ^ 40 * 1613957 * 2
def baseEnd_1613957 : Nat := 276245232229549039838351

theorem tailTrace_1613957 : CollatzResearch.WordTrace tailWord_1613957 prefixEnd_1613957 276245232229549039838351 := by
  unfold tailWord_1613957
  simp only [CollatzResearch.WordTrace]
  refine ⟨58865847813916905755736125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39243898542611270503824083 58865847813916905755736125)
  ·
    refine ⟨22074692930218839658401047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58865847813916905755736125 22074692930218839658401047)
    ·
      refine ⟨33112039395328259487601571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22074692930218839658401047 33112039395328259487601571)
      ·
        refine ⟨49668059092992389231402357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33112039395328259487601571 49668059092992389231402357)
        ·
          refine ⟨4656380539968036490443971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49668059092992389231402357 4656380539968036490443971)
          ·
            refine ⟨6984570809952054735665957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4656380539968036490443971 6984570809952054735665957)
            ·
              refine ⟨1309607026866010262937367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6984570809952054735665957 1309607026866010262937367)
              ·
                refine ⟨1964410540299015394406051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1309607026866010262937367 1964410540299015394406051)
                ·
                  refine ⟨2946615810448523091609077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1964410540299015394406051 2946615810448523091609077)
                  ·
                    refine ⟨276245232229549039838351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2946615810448523091609077 276245232229549039838351)
                    ·
                      rfl

theorem cell23_1613957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 1, 5].length) (baseStart_1613957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613957 prefixEnd_1613957 := by exact prefixLift 1613957
  have htrace : WordTrace (prefixWord ++ tailWord_1613957) baseStart_1613957 baseEnd_1613957 := by
    simpa [prefixWord, tailWord_1613957, baseEnd_1613957] using wordTrace_append hprefix tailTrace_1613957
  have hstable : (prefixWord ++ tailWord_1613957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613957).length < 2 ^ (prefixWord ++ tailWord_1613957).sum := by decide
  have hdescent : baseEnd_1613957 < baseStart_1613957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613973 : List Nat := [1, 3, 2, 1, 1, 1, 4, 2, 1, 1, 6]
def baseStart_1613973 : Nat := 118140960795 + 1613973 * 2 ^ 59
def prefixEnd_1613973 : Nat := 4983230072969 + 3 ^ 40 * 1613973 * 2
def baseEnd_1613973 : Nat := 828743912379119056914979

theorem tailTrace_1613973 : CollatzResearch.WordTrace tailWord_1613973 prefixEnd_1613973 828743912379119056914979 := by
  unfold tailWord_1613973
  simp only [CollatzResearch.WordTrace]
  refine ⟨58866431381858940488318573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39244287587905960325545715 58866431381858940488318573)
  ·
    refine ⟨22074911768197102683119465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58866431381858940488318573 22074911768197102683119465)
    ·
      refine ⟨16556183826147827012339599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22074911768197102683119465 16556183826147827012339599)
      ·
        refine ⟨24834275739221740518509399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16556183826147827012339599 24834275739221740518509399)
        ·
          refine ⟨37251413608832610777764099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24834275739221740518509399 37251413608832610777764099)
          ·
            refine ⟨55877120413248916166646149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37251413608832610777764099 55877120413248916166646149)
            ·
              refine ⟨10476960077484171781246153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55877120413248916166646149 10476960077484171781246153)
              ·
                refine ⟨7857720058113128835934615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10476960077484171781246153 7857720058113128835934615)
                ·
                  refine ⟨11786580087169693253901923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7857720058113128835934615 11786580087169693253901923)
                  ·
                    refine ⟨17679870130754539880852885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11786580087169693253901923 17679870130754539880852885)
                    ·
                      refine ⟨828743912379119056914979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17679870130754539880852885 828743912379119056914979)
                      ·
                        rfl

theorem cell23_1613973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_1613973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613973 prefixEnd_1613973 := by exact prefixLift 1613973
  have htrace : WordTrace (prefixWord ++ tailWord_1613973) baseStart_1613973 baseEnd_1613973 := by
    simpa [prefixWord, tailWord_1613973, baseEnd_1613973] using wordTrace_append hprefix tailTrace_1613973
  have hstable : (prefixWord ++ tailWord_1613973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613973).length < 2 ^ (prefixWord ++ tailWord_1613973).sum := by decide
  have hdescent : baseEnd_1613973 < baseStart_1613973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1613980 : List Nat := [2, 2, 3, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_1613980 : Nat := 118140960795 + 1613980 * 2 ^ 59
def prefixEnd_1613980 : Nat := 4983230072969 + 3 ^ 40 * 1613980 * 2
def baseEnd_1613980 : Nat := 828747506743700529527447

theorem tailTrace_1613980 : CollatzResearch.WordTrace tailWord_1613980 prefixEnd_1613980 828747506743700529527447 := by
  unfold tailWord_1613980
  simp only [CollatzResearch.WordTrace]
  refine ⟨29433343346416790341911697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39244457795222387122548929 29433343346416790341911697)
  ·
    refine ⟨22075007509812592756433773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29433343346416790341911697 22075007509812592756433773)
    ·
      refine ⟨8278127816179722283662665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22075007509812592756433773 8278127816179722283662665)
      ·
        refine ⟨6208595862134791712746999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8278127816179722283662665 6208595862134791712746999)
        ·
          refine ⟨9312893793202187569120499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6208595862134791712746999 9312893793202187569120499)
          ·
            refine ⟨13969340689803281353680749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9312893793202187569120499 13969340689803281353680749)
            ·
              refine ⟨5238502758676230507630281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13969340689803281353680749 5238502758676230507630281)
              ·
                refine ⟨3928877069007172880722711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5238502758676230507630281 3928877069007172880722711)
                ·
                  refine ⟨5893315603510759321084067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3928877069007172880722711 5893315603510759321084067)
                  ·
                    refine ⟨8839973405266138981626101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5893315603510759321084067 8839973405266138981626101)
                    ·
                      refine ⟨828747506743700529527447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8839973405266138981626101 828747506743700529527447)
                      ·
                        rfl

theorem cell23_1613980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_1613980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1613980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1613980 prefixEnd_1613980 := by exact prefixLift 1613980
  have htrace : WordTrace (prefixWord ++ tailWord_1613980) baseStart_1613980 baseEnd_1613980 := by
    simpa [prefixWord, tailWord_1613980, baseEnd_1613980] using wordTrace_append hprefix tailTrace_1613980
  have hstable : (prefixWord ++ tailWord_1613980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1613980).length < 2 ^ (prefixWord ++ tailWord_1613980).sum := by decide
  have hdescent : baseEnd_1613980 < baseStart_1613980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1613980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614005 : List Nat := [1, 3, 3, 4, 2, 1, 1, 3, 1, 1, 3]
def baseStart_1614005 : Nat := 118140960795 + 1614005 * 2 ^ 59
def prefixEnd_1614005 : Nat := 4983230072969 + 3 ^ 40 * 1614005 * 2
def baseEnd_1614005 : Nat := 828760343760062931714833

theorem tailTrace_1614005 : CollatzResearch.WordTrace tailWord_1614005 prefixEnd_1614005 828760343760062931714833 := by
  unfold tailWord_1614005
  simp only [CollatzResearch.WordTrace]
  refine ⟨58867598517743009953483469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39245065678495339968988979 58867598517743009953483469)
  ·
    refine ⟨22075349444153628732556301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58867598517743009953483469 22075349444153628732556301)
    ·
      refine ⟨8278256041557610774708613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22075349444153628732556301 8278256041557610774708613)
      ·
        refine ⟨1552173007792052020257865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8278256041557610774708613 1552173007792052020257865)
        ·
          refine ⟨1164129755844039015193399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1552173007792052020257865 1164129755844039015193399)
          ·
            refine ⟨1746194633766058522790099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1164129755844039015193399 1746194633766058522790099)
            ·
              refine ⟨2619291950649087784185149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1746194633766058522790099 2619291950649087784185149)
              ·
                refine ⟨982234481493407919069431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2619291950649087784185149 982234481493407919069431)
                ·
                  refine ⟨1473351722240111878604147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 982234481493407919069431 1473351722240111878604147)
                  ·
                    refine ⟨2210027583360167817906221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1473351722240111878604147 2210027583360167817906221)
                    ·
                      refine ⟨828760343760062931714833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2210027583360167817906221 828760343760062931714833)
                      ·
                        rfl

theorem cell23_1614005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_1614005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614005 prefixEnd_1614005 := by exact prefixLift 1614005
  have htrace : WordTrace (prefixWord ++ tailWord_1614005) baseStart_1614005 baseEnd_1614005 := by
    simpa [prefixWord, tailWord_1614005, baseEnd_1614005] using wordTrace_append hprefix tailTrace_1614005
  have hstable : (prefixWord ++ tailWord_1614005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614005).length < 2 ^ (prefixWord ++ tailWord_1614005).sum := by decide
  have hdescent : baseEnd_1614005 < baseStart_1614005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614010 : List Nat := [3, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3]
def baseStart_1614010 : Nat := 118140960795 + 1614010 * 2 ^ 59
def prefixEnd_1614010 : Nat := 4983230072969 + 3 ^ 40 * 1614010 * 2
def baseEnd_1614010 : Nat := 828762911163335412152309

theorem tailTrace_1614010 : CollatzResearch.WordTrace tailWord_1614010 prefixEnd_1614010 828762911163335412152309 := by
  unfold tailWord_1614010
  simp only [CollatzResearch.WordTrace]
  refine ⟨14716945220681223951853871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39245187255149930538276989 14716945220681223951853871)
  ·
    refine ⟨22075417831021835927780807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14716945220681223951853871 22075417831021835927780807)
    ·
      refine ⟨33113126746532753891671211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22075417831021835927780807 33113126746532753891671211)
      ·
        refine ⟨49669690119799130837506817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33113126746532753891671211 49669690119799130837506817)
        ·
          refine ⟨37252267589849348128130113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49669690119799130837506817 37252267589849348128130113)
          ·
            refine ⟨27939200692387011096097585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37252267589849348128130113 27939200692387011096097585)
            ·
              refine ⟨20954400519290258322073189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27939200692387011096097585 20954400519290258322073189)
              ·
                refine ⟨3928950097366923435388723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20954400519290258322073189 3928950097366923435388723)
                ·
                  refine ⟨5893425146050385153083085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3928950097366923435388723 5893425146050385153083085)
                  ·
                    refine ⟨2210034429768894432406157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5893425146050385153083085 2210034429768894432406157)
                    ·
                      refine ⟨828762911163335412152309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2210034429768894432406157 828762911163335412152309)
                      ·
                        rfl

theorem cell23_1614010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3].length) (baseStart_1614010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614010 prefixEnd_1614010 := by exact prefixLift 1614010
  have htrace : WordTrace (prefixWord ++ tailWord_1614010) baseStart_1614010 baseEnd_1614010 := by
    simpa [prefixWord, tailWord_1614010, baseEnd_1614010] using wordTrace_append hprefix tailTrace_1614010
  have hstable : (prefixWord ++ tailWord_1614010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614010).length < 2 ^ (prefixWord ++ tailWord_1614010).sum := by decide
  have hdescent : baseEnd_1614010 < baseStart_1614010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614013 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 1, 9]
def baseStart_1614013 : Nat := 118140960795 + 1614013 * 2 ^ 59
def prefixEnd_1614013 : Nat := 4983230072969 + 3 ^ 40 * 1614013 * 2
def baseEnd_1614013 : Nat := 276254817201766300138265

theorem tailTrace_1614013 : CollatzResearch.WordTrace tailWord_1614013 prefixEnd_1614013 276254817201766300138265 := by
  unfold tailWord_1614013
  simp only [CollatzResearch.WordTrace]
  refine ⟨58867890301714027319774693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39245260201142684879849795 58867890301714027319774693)
  ·
    refine ⟨11037729431571380122457755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58867890301714027319774693 11037729431571380122457755)
    ·
      refine ⟨16556594147357070183686633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11037729431571380122457755 16556594147357070183686633)
      ·
        refine ⟨12417445610517802637764975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16556594147357070183686633 12417445610517802637764975)
        ·
          refine ⟨18626168415776703956647463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12417445610517802637764975 18626168415776703956647463)
          ·
            refine ⟨27939252623665055934971195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18626168415776703956647463 27939252623665055934971195)
            ·
              refine ⟨41908878935497583902456793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27939252623665055934971195 41908878935497583902456793)
              ·
                refine ⟨31431659201623187926842595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41908878935497583902456793 31431659201623187926842595)
                ·
                  refine ⟨47147488802434781890263893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31431659201623187926842595 47147488802434781890263893)
                  ·
                    refine ⟨276254817201766300138265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 47147488802434781890263893 276254817201766300138265)
                    ·
                      rfl

theorem cell23_1614013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_1614013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614013 prefixEnd_1614013 := by exact prefixLift 1614013
  have htrace : WordTrace (prefixWord ++ tailWord_1614013) baseStart_1614013 baseEnd_1614013 := by
    simpa [prefixWord, tailWord_1614013, baseEnd_1614013] using wordTrace_append hprefix tailTrace_1614013
  have hstable : (prefixWord ++ tailWord_1614013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614013).length < 2 ^ (prefixWord ++ tailWord_1614013).sum := by decide
  have hdescent : baseEnd_1614013 < baseStart_1614013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614017 : List Nat := [1, 2, 6, 1, 2, 2, 9]
def baseStart_1614017 : Nat := 118140960795 + 1614017 * 2 ^ 59
def prefixEnd_1614017 : Nat := 4983230072969 + 3 ^ 40 * 1614017 * 2
def baseEnd_1614017 : Nat := 10231685253431072651417

theorem tailTrace_1614017 : CollatzResearch.WordTrace tailWord_1614017 prefixEnd_1614017 10231685253431072651417 := by
  unfold tailWord_1614017
  simp only [CollatzResearch.WordTrace]
  refine ⟨58868036193699536002920305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39245357462466357335280203 58868036193699536002920305)
  ·
    refine ⟨44151027145274652002190229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58868036193699536002920305 44151027145274652002190229)
    ·
      refine ⟨2069579397434749312602667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 44151027145274652002190229 2069579397434749312602667)
      ·
        refine ⟨3104369096152123968904001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2069579397434749312602667 3104369096152123968904001)
        ·
          refine ⟨2328276822114092976678001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3104369096152123968904001 2328276822114092976678001)
          ·
            refine ⟨1746207616585569732508501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2328276822114092976678001 1746207616585569732508501)
            ·
              refine ⟨10231685253431072651417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1746207616585569732508501 10231685253431072651417)
              ·
                rfl

theorem cell23_1614017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 9].length) (baseStart_1614017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614017 prefixEnd_1614017 := by exact prefixLift 1614017
  have htrace : WordTrace (prefixWord ++ tailWord_1614017) baseStart_1614017 baseEnd_1614017 := by
    simpa [prefixWord, tailWord_1614017, baseEnd_1614017] using wordTrace_append hprefix tailTrace_1614017
  have hstable : (prefixWord ++ tailWord_1614017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614017).length < 2 ^ (prefixWord ++ tailWord_1614017).sum := by decide
  have hdescent : baseEnd_1614017 < baseStart_1614017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614027 : List Nat := [1, 1, 1, 1, 3, 2, 4, 4, 2, 1, 3]
def baseStart_1614027 : Nat := 118140960795 + 1614027 * 2 ^ 59
def prefixEnd_1614027 : Nat := 4983230072969 + 3 ^ 40 * 1614027 * 2
def baseEnd_1614027 : Nat := 828771640334461845639731

theorem tailTrace_1614027 : CollatzResearch.WordTrace tailWord_1614027 prefixEnd_1614027 828771640334461845639731 := by
  unfold tailWord_1614027
  simp only [CollatzResearch.WordTrace]
  refine ⟨58868400923663307710784335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39245600615775538473856223 58868400923663307710784335)
  ·
    refine ⟨88302601385494961566176503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58868400923663307710784335 88302601385494961566176503)
    ·
      refine ⟨132453902078242442349264755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88302601385494961566176503 132453902078242442349264755)
      ·
        refine ⟨198680853117363663523897133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132453902078242442349264755 198680853117363663523897133)
        ·
          refine ⟨74505319919011373821461425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198680853117363663523897133 74505319919011373821461425)
          ·
            refine ⟨55878989939258530366096069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74505319919011373821461425 55878989939258530366096069)
            ·
              refine ⟨10477310613610974443643013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55878989939258530366096069 10477310613610974443643013)
              ·
                refine ⟨1964495740052057708183065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10477310613610974443643013 1964495740052057708183065)
                ·
                  refine ⟨1473371805039043281137299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1964495740052057708183065 1473371805039043281137299)
                  ·
                    refine ⟨2210057707558564921705949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1473371805039043281137299 2210057707558564921705949)
                    ·
                      refine ⟨828771640334461845639731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2210057707558564921705949 828771640334461845639731)
                      ·
                        rfl

theorem cell23_1614027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2, 1, 3].length) (baseStart_1614027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614027 prefixEnd_1614027 := by exact prefixLift 1614027
  have htrace : WordTrace (prefixWord ++ tailWord_1614027) baseStart_1614027 baseEnd_1614027 := by
    simpa [prefixWord, tailWord_1614027, baseEnd_1614027] using wordTrace_append hprefix tailTrace_1614027
  have hstable : (prefixWord ++ tailWord_1614027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614027).length < 2 ^ (prefixWord ++ tailWord_1614027).sum := by decide
  have hdescent : baseEnd_1614027 < baseStart_1614027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614028 : List Nat := [2, 2, 1, 6, 1, 2, 1, 1, 3, 2, 2]
def baseStart_1614028 : Nat := 118140960795 + 1614028 * 2 ^ 59
def prefixEnd_1614028 : Nat := 4983230072969 + 3 ^ 40 * 1614028 * 2
def baseEnd_1614028 : Nat := 828772153815116341727227

theorem tailTrace_1614028 : CollatzResearch.WordTrace tailWord_1614028 prefixEnd_1614028 828772153815116341727227 := by
  unfold tailWord_1614028
  simp only [CollatzResearch.WordTrace]
  refine ⟨29434218698329842440785369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39245624931106456587713825 29434218698329842440785369)
  ·
    refine ⟨22075664023747381830589027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29434218698329842440785369 22075664023747381830589027)
    ·
      refine ⟨33113496035621072745883541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22075664023747381830589027 33113496035621072745883541)
      ·
        refine ⟨1552195126669737784963291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33113496035621072745883541 1552195126669737784963291)
        ·
          refine ⟨2328292690004606677444937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1552195126669737784963291 2328292690004606677444937)
          ·
            refine ⟨1746219517503455008083703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2328292690004606677444937 1746219517503455008083703)
            ·
              refine ⟨2619329276255182512125555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1746219517503455008083703 2619329276255182512125555)
              ·
                refine ⟨3928993914382773768188333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2619329276255182512125555 3928993914382773768188333)
                ·
                  refine ⟨1473372717893540163070625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3928993914382773768188333 1473372717893540163070625)
                  ·
                    refine ⟨1105029538420155122302969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1473372717893540163070625 1105029538420155122302969)
                    ·
                      refine ⟨828772153815116341727227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1105029538420155122302969 828772153815116341727227)
                      ·
                        rfl

theorem cell23_1614028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_1614028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614028 prefixEnd_1614028 := by exact prefixLift 1614028
  have htrace : WordTrace (prefixWord ++ tailWord_1614028) baseStart_1614028 baseEnd_1614028 := by
    simpa [prefixWord, tailWord_1614028, baseEnd_1614028] using wordTrace_append hprefix tailTrace_1614028
  have hstable : (prefixWord ++ tailWord_1614028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614028).length < 2 ^ (prefixWord ++ tailWord_1614028).sum := by decide
  have hdescent : baseEnd_1614028 < baseStart_1614028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614038 : List Nat := [5, 2, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_1614038 : Nat := 118140960795 + 1614038 * 2 ^ 59
def prefixEnd_1614038 : Nat := 4983230072969 + 3 ^ 40 * 1614038 * 2
def baseEnd_1614038 : Nat := 276259096207220434200727

theorem tailTrace_1614038 : CollatzResearch.WordTrace tailWord_1614038 prefixEnd_1614038 276259096207220434200727 := by
  unfold tailWord_1614038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3679300132913966036839673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39245868084415637726289845 3679300132913966036839673)
  ·
    refine ⟨2759475099685474527629755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3679300132913966036839673 2759475099685474527629755)
    ·
      refine ⟨4139212649528211791444633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2759475099685474527629755 4139212649528211791444633)
      ·
        refine ⟨3104409487146158843583475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4139212649528211791444633 3104409487146158843583475)
        ·
          refine ⟨4656614230719238265375213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3104409487146158843583475 4656614230719238265375213)
          ·
            refine ⟨1746230336519714349515705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4656614230719238265375213 1746230336519714349515705)
            ·
              refine ⟨1309672752389785762136779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1746230336519714349515705 1309672752389785762136779)
              ·
                refine ⟨1964509128584678643205169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1309672752389785762136779 1964509128584678643205169)
                ·
                  refine ⟨1473381846438508982403877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1964509128584678643205169 1473381846438508982403877)
                  ·
                    refine ⟨276259096207220434200727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1473381846438508982403877 276259096207220434200727)
                    ·
                      rfl

theorem cell23_1614038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_1614038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614038 prefixEnd_1614038 := by exact prefixLift 1614038
  have htrace : WordTrace (prefixWord ++ tailWord_1614038) baseStart_1614038 baseEnd_1614038 := by
    simpa [prefixWord, tailWord_1614038, baseEnd_1614038] using wordTrace_append hprefix tailTrace_1614038
  have hstable : (prefixWord ++ tailWord_1614038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614038).length < 2 ^ (prefixWord ++ tailWord_1614038).sum := by decide
  have hdescent : baseEnd_1614038 < baseStart_1614038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614067 : List Nat := [1, 1, 1, 2, 2, 4, 3, 2, 1, 4, 2]
def baseStart_1614067 : Nat := 118140960795 + 1614067 * 2 ^ 59
def prefixEnd_1614067 : Nat := 4983230072969 + 3 ^ 40 * 1614067 * 2
def baseEnd_1614067 : Nat := 828792179560641689139547

theorem tailTrace_1614067 : CollatzResearch.WordTrace tailWord_1614067 prefixEnd_1614067 828792179560641689139547 := by
  unfold tailWord_1614067
  simp only [CollatzResearch.WordTrace]
  refine ⟨58869859843518394542240455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39246573229012263028160303 58869859843518394542240455)
  ·
    refine ⟨88304789765277591813360683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58869859843518394542240455 88304789765277591813360683)
    ·
      refine ⟨132457184647916387720041025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88304789765277591813360683 132457184647916387720041025)
      ·
        refine ⟨99342888485937290790030769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132457184647916387720041025 99342888485937290790030769)
        ·
          refine ⟨74507166364452968092523077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99342888485937290790030769 74507166364452968092523077)
          ·
            refine ⟨13970093693334931517348077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74507166364452968092523077 13970093693334931517348077)
            ·
              refine ⟨5238785135000599319005529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13970093693334931517348077 5238785135000599319005529)
              ·
                refine ⟨3929088851250449489254147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5238785135000599319005529 3929088851250449489254147)
                ·
                  refine ⟨5893633276875674233881221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3929088851250449489254147 5893633276875674233881221)
                  ·
                    refine ⟨1105056239414188918852729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5893633276875674233881221 1105056239414188918852729)
                    ·
                      refine ⟨828792179560641689139547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1105056239414188918852729 828792179560641689139547)
                      ·
                        rfl

theorem cell23_1614067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 4, 2].length) (baseStart_1614067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614067 prefixEnd_1614067 := by exact prefixLift 1614067
  have htrace : WordTrace (prefixWord ++ tailWord_1614067) baseStart_1614067 baseEnd_1614067 := by
    simpa [prefixWord, tailWord_1614067, baseEnd_1614067] using wordTrace_append hprefix tailTrace_1614067
  have hstable : (prefixWord ++ tailWord_1614067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614067).length < 2 ^ (prefixWord ++ tailWord_1614067).sum := by decide
  have hdescent : baseEnd_1614067 < baseStart_1614067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614073 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 11]
def baseStart_1614073 : Nat := 118140960795 + 1614073 * 2 ^ 59
def prefixEnd_1614073 : Nat := 4983230072969 + 3 ^ 40 * 1614073 * 2
def baseEnd_1614073 : Nat := 92088362271618740629391

theorem tailTrace_1614073 : CollatzResearch.WordTrace tailWord_1614073 prefixEnd_1614073 92088362271618740629391 := by
  unfold tailWord_1614073
  simp only [CollatzResearch.WordTrace]
  refine ⟨58870078681496657566958873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39246719120997771711305915 58870078681496657566958873)
  ·
    refine ⟨44152559011122493175219155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58870078681496657566958873 44152559011122493175219155)
    ·
      refine ⟨66228838516683739762828733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44152559011122493175219155 66228838516683739762828733)
      ·
        refine ⟨24835814443756402411060775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66228838516683739762828733 24835814443756402411060775)
        ·
          refine ⟨37253721665634603616591163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24835814443756402411060775 37253721665634603616591163)
          ·
            refine ⟨55880582498451905424886745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37253721665634603616591163 55880582498451905424886745)
            ·
              refine ⟨41910436873838929068665059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55880582498451905424886745 41910436873838929068665059)
              ·
                refine ⟨62865655310758393602997589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41910436873838929068665059 62865655310758393602997589)
                ·
                  refine ⟨92088362271618740629391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 62865655310758393602997589 92088362271618740629391)
                  ·
                    rfl

theorem cell23_1614073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 11].length) (baseStart_1614073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614073 prefixEnd_1614073 := by exact prefixLift 1614073
  have htrace : WordTrace (prefixWord ++ tailWord_1614073) baseStart_1614073 baseEnd_1614073 := by
    simpa [prefixWord, tailWord_1614073, baseEnd_1614073] using wordTrace_append hprefix tailTrace_1614073
  have hstable : (prefixWord ++ tailWord_1614073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614073).length < 2 ^ (prefixWord ++ tailWord_1614073).sum := by decide
  have hdescent : baseEnd_1614073 < baseStart_1614073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614167 : List Nat := [1, 1, 3, 2, 3, 1, 1, 4, 3, 4]
def baseStart_1614167 : Nat := 118140960795 + 1614167 * 2 ^ 59
def prefixEnd_1614167 : Nat := 4983230072969 + 3 ^ 40 * 1614167 * 2
def baseEnd_1614167 : Nat := 276281175875363765963029

theorem tailTrace_1614167 : CollatzResearch.WordTrace tailWord_1614167 prefixEnd_1614167 276281175875363765963029 := by
  unfold tailWord_1614167
  simp only [CollatzResearch.WordTrace]
  refine ⟨58873507143156111620880755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39249004762104074413920503 58873507143156111620880755)
  ·
    refine ⟨88310260714734167431321133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58873507143156111620880755 88310260714734167431321133)
    ·
      refine ⟨33116347768025312786745425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88310260714734167431321133 33116347768025312786745425)
      ·
        refine ⟨24837260826018984590059069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33116347768025312786745425 24837260826018984590059069)
        ·
          refine ⟨9313972809757119221272151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24837260826018984590059069 9313972809757119221272151)
          ·
            refine ⟨13970959214635678831908227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9313972809757119221272151 13970959214635678831908227)
            ·
              refine ⟨20956438821953518247862341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13970959214635678831908227 20956438821953518247862341)
              ·
                refine ⟨3929332279116284671474189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20956438821953518247862341 3929332279116284671474189)
                ·
                  refine ⟨1473499604668606751802821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3929332279116284671474189 1473499604668606751802821)
                  ·
                    refine ⟨276281175875363765963029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1473499604668606751802821 276281175875363765963029)
                    ·
                      rfl

theorem cell23_1614167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 3, 4].length) (baseStart_1614167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614167 prefixEnd_1614167 := by exact prefixLift 1614167
  have htrace : WordTrace (prefixWord ++ tailWord_1614167) baseStart_1614167 baseEnd_1614167 := by
    simpa [prefixWord, tailWord_1614167, baseEnd_1614167] using wordTrace_append hprefix tailTrace_1614167
  have hstable : (prefixWord ++ tailWord_1614167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614167).length < 2 ^ (prefixWord ++ tailWord_1614167).sum := by decide
  have hdescent : baseEnd_1614167 < baseStart_1614167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614170 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4]
def baseStart_1614170 : Nat := 118140960795 + 1614170 * 2 ^ 59
def prefixEnd_1614170 : Nat := 4983230072969 + 3 ^ 40 * 1614170 * 2
def baseEnd_1614170 : Nat := 828845068068054786151573

theorem tailTrace_1614170 : CollatzResearch.WordTrace tailWord_1614170 prefixEnd_1614170 828845068068054786151573 := by
  unfold tailWord_1614170
  simp only [CollatzResearch.WordTrace]
  refine ⟨14718404140536310783309991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39249077708096828755493309 14718404140536310783309991)
  ·
    refine ⟨22077606210804466174964987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14718404140536310783309991 22077606210804466174964987)
    ·
      refine ⟨33116409316206699262447481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22077606210804466174964987 33116409316206699262447481)
      ·
        refine ⟨24837306987155024446835611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33116409316206699262447481 24837306987155024446835611)
        ·
          refine ⟨37255960480732536670253417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24837306987155024446835611 37255960480732536670253417)
          ·
            refine ⟨27941970360549402502690063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37255960480732536670253417 27941970360549402502690063)
            ·
              refine ⟨41912955540824103754035095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27941970360549402502690063 41912955540824103754035095)
              ·
                refine ⟨62869433311236155631052643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41912955540824103754035095 62869433311236155631052643)
                ·
                  refine ⟨94304149966854233446578965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62869433311236155631052643 94304149966854233446578965)
                  ·
                    refine ⟨4420507029696292192808389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94304149966854233446578965 4420507029696292192808389)
                    ·
                      refine ⟨828845068068054786151573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4420507029696292192808389 828845068068054786151573)
                      ·
                        rfl

theorem cell23_1614170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_1614170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614170 prefixEnd_1614170 := by exact prefixLift 1614170
  have htrace : WordTrace (prefixWord ++ tailWord_1614170) baseStart_1614170 baseEnd_1614170 := by
    simpa [prefixWord, tailWord_1614170, baseEnd_1614170] using wordTrace_append hprefix tailTrace_1614170
  have hstable : (prefixWord ++ tailWord_1614170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614170).length < 2 ^ (prefixWord ++ tailWord_1614170).sum := by decide
  have hdescent : baseEnd_1614170 < baseStart_1614170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614180 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 10]
def baseStart_1614180 : Nat := 118140960795 + 1614180 * 2 ^ 59
def prefixEnd_1614180 : Nat := 4983230072969 + 3 ^ 40 * 1614180 * 2
def baseEnd_1614180 : Nat := 92094466986066638558503

theorem tailTrace_1614180 : CollatzResearch.WordTrace tailWord_1614180 prefixEnd_1614180 92094466986066638558503 := by
  unfold tailWord_1614180
  simp only [CollatzResearch.WordTrace]
  refine ⟨29436990646054507420551997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39249320861406009894069329 29436990646054507420551997)
  ·
    refine ⟨11038871492270440282706999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29436990646054507420551997 11038871492270440282706999)
    ·
      refine ⟨16558307238405660424060499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11038871492270440282706999 16558307238405660424060499)
      ·
        refine ⟨24837460857608490636090749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16558307238405660424060499 24837460857608490636090749)
        ·
          refine ⟨9314047821603183988534031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24837460857608490636090749 9314047821603183988534031)
          ·
            refine ⟨13971071732404775982801047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9314047821603183988534031 13971071732404775982801047)
            ·
              refine ⟨20956607598607163974201571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13971071732404775982801047 20956607598607163974201571)
              ·
                refine ⟨31434911397910745961302357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20956607598607163974201571 31434911397910745961302357)
                ·
                  refine ⟨92094466986066638558503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 31434911397910745961302357 92094466986066638558503)
                  ·
                    rfl

theorem cell23_1614180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_1614180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614180 prefixEnd_1614180 := by exact prefixLift 1614180
  have htrace : WordTrace (prefixWord ++ tailWord_1614180) baseStart_1614180 baseEnd_1614180 := by
    simpa [prefixWord, tailWord_1614180, baseEnd_1614180] using wordTrace_append hprefix tailTrace_1614180
  have hstable : (prefixWord ++ tailWord_1614180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614180).length < 2 ^ (prefixWord ++ tailWord_1614180).sum := by decide
  have hdescent : baseEnd_1614180 < baseStart_1614180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614194 : List Nat := [3, 2, 1, 2, 1, 4, 1, 2, 2, 2, 3]
def baseStart_1614194 : Nat := 118140960795 + 1614194 * 2 ^ 59
def prefixEnd_1614194 : Nat := 4983230072969 + 3 ^ 40 * 1614194 * 2
def baseEnd_1614194 : Nat := 828857391603762692251463

theorem tailTrace_1614194 : CollatzResearch.WordTrace tailWord_1614194 prefixEnd_1614194 828857391603762692251463 := by
  unfold tailWord_1614194
  simp only [CollatzResearch.WordTrace]
  refine ⟨14718622978514573808028409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39249661276038863488075757 14718622978514573808028409)
  ·
    refine ⟨11038967233885930356021307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14718622978514573808028409 11038967233885930356021307)
    ·
      refine ⟨16558450850828895534031961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11038967233885930356021307 16558450850828895534031961)
      ·
        refine ⟨12418838138121671650523971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16558450850828895534031961 12418838138121671650523971)
        ·
          refine ⟨18628257207182507475785957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12418838138121671650523971 18628257207182507475785957)
          ·
            refine ⟨3492798226346720151709867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18628257207182507475785957 3492798226346720151709867)
            ·
              refine ⟨5239197339520080227564801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3492798226346720151709867 5239197339520080227564801)
              ·
                refine ⟨3929398004640060170673601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5239197339520080227564801 3929398004640060170673601)
                ·
                  refine ⟨2947048503480045128005201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3929398004640060170673601 2947048503480045128005201)
                  ·
                    refine ⟨2210286377610033846003901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2947048503480045128005201 2210286377610033846003901)
                    ·
                      refine ⟨828857391603762692251463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2210286377610033846003901 828857391603762692251463)
                      ·
                        rfl

theorem cell23_1614194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_1614194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614194 prefixEnd_1614194 := by exact prefixLift 1614194
  have htrace : WordTrace (prefixWord ++ tailWord_1614194) baseStart_1614194 baseEnd_1614194 := by
    simpa [prefixWord, tailWord_1614194, baseEnd_1614194] using wordTrace_append hprefix tailTrace_1614194
  have hstable : (prefixWord ++ tailWord_1614194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614194).length < 2 ^ (prefixWord ++ tailWord_1614194).sum := by decide
  have hdescent : baseEnd_1614194 < baseStart_1614194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614197 : List Nat := [1, 3, 4, 1, 2, 1, 2, 1, 8]
def baseStart_1614197 : Nat := 118140960795 + 1614197 * 2 ^ 59
def prefixEnd_1614197 : Nat := 4983230072969 + 3 ^ 40 * 1614197 * 2
def baseEnd_1614197 : Nat := 92095436893969575612661

theorem tailTrace_1614197 : CollatzResearch.WordTrace tailWord_1614197 prefixEnd_1614197 92095436893969575612661 := by
  unfold tailWord_1614197
  simp only [CollatzResearch.WordTrace]
  refine ⟨58874601333047426744472845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39249734222031617829648563 58874601333047426744472845)
  ·
    refine ⟨22077975499892785029177317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58874601333047426744472845 22077975499892785029177317)
    ·
      refine ⟨4139620406229897192970747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22077975499892785029177317 4139620406229897192970747)
      ·
        refine ⟨6209430609344845789456121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4139620406229897192970747 6209430609344845789456121)
        ·
          refine ⟨4657072957008634342092091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6209430609344845789456121 4657072957008634342092091)
          ·
            refine ⟨6985609435512951513138137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4657072957008634342092091 6985609435512951513138137)
            ·
              refine ⟨5239207076634713634853603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6985609435512951513138137 5239207076634713634853603)
              ·
                refine ⟨7858810614952070452280405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5239207076634713634853603 7858810614952070452280405)
                ·
                  refine ⟨92095436893969575612661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7858810614952070452280405 92095436893969575612661)
                  ·
                    rfl

theorem cell23_1614197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 8].length) (baseStart_1614197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614197 prefixEnd_1614197 := by exact prefixLift 1614197
  have htrace : WordTrace (prefixWord ++ tailWord_1614197) baseStart_1614197 baseEnd_1614197 := by
    simpa [prefixWord, tailWord_1614197, baseEnd_1614197] using wordTrace_append hprefix tailTrace_1614197
  have hstable : (prefixWord ++ tailWord_1614197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614197).length < 2 ^ (prefixWord ++ tailWord_1614197).sum := by decide
  have hdescent : baseEnd_1614197 < baseStart_1614197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614301 : List Nat := [1, 4, 3, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_1614301 : Nat := 118140960795 + 1614301 * 2 ^ 59
def prefixEnd_1614301 : Nat := 4983230072969 + 3 ^ 40 * 1614301 * 2
def baseEnd_1614301 : Nat := 828912334033793773613471

theorem tailTrace_1614301 : CollatzResearch.WordTrace tailWord_1614301 prefixEnd_1614301 828912334033793773613471 := by
  unfold tailWord_1614301
  simp only [CollatzResearch.WordTrace]
  refine ⟨58878394524670652506258757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39252263016447101670839171 58878394524670652506258757)
  ·
    refine ⟨11039698973375747344923517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58878394524670652506258757 11039698973375747344923517)
    ·
      refine ⟨4139887115015905254346319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11039698973375747344923517 4139887115015905254346319)
      ·
        refine ⟨6209830672523857881519479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4139887115015905254346319 6209830672523857881519479)
        ·
          refine ⟨9314746008785786822279219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6209830672523857881519479 9314746008785786822279219)
          ·
            refine ⟨13972119013178680233418829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9314746008785786822279219 13972119013178680233418829)
            ·
              refine ⟨5239544629942005087532061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13972119013178680233418829 5239544629942005087532061)
              ·
                refine ⟨1964829236228251907824523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5239544629942005087532061 1964829236228251907824523)
                ·
                  refine ⟨2947243854342377861736785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1964829236228251907824523 2947243854342377861736785)
                  ·
                    refine ⟨2210432890756783396302589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2947243854342377861736785 2210432890756783396302589)
                    ·
                      refine ⟨828912334033793773613471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2210432890756783396302589 828912334033793773613471)
                      ·
                        rfl

theorem cell23_1614301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_1614301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614301 prefixEnd_1614301 := by exact prefixLift 1614301
  have htrace : WordTrace (prefixWord ++ tailWord_1614301) baseStart_1614301 baseEnd_1614301 := by
    simpa [prefixWord, tailWord_1614301, baseEnd_1614301] using wordTrace_append hprefix tailTrace_1614301
  have hstable : (prefixWord ++ tailWord_1614301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614301).length < 2 ^ (prefixWord ++ tailWord_1614301).sum := by decide
  have hdescent : baseEnd_1614301 < baseStart_1614301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614325 : List Nat := [1, 3, 5, 1, 2, 1, 3, 1, 2, 4]
def baseStart_1614325 : Nat := 118140960795 + 1614325 * 2 ^ 59
def prefixEnd_1614325 : Nat := 4983230072969 + 3 ^ 40 * 1614325 * 2
def baseEnd_1614325 : Nat := 276308219189833893237787

theorem tailTrace_1614325 : CollatzResearch.WordTrace tailWord_1614325 prefixEnd_1614325 276308219189833893237787 := by
  unfold tailWord_1614325
  simp only [CollatzResearch.WordTrace]
  refine ⟨58879269876583704605132429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39252846584389136403421619 58879269876583704605132429)
  ·
    refine ⟨22079726203718889226924661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58879269876583704605132429 22079726203718889226924661)
    ·
      refine ⟨2069974331598645865024187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22079726203718889226924661 2069974331598645865024187)
      ·
        refine ⟨3104961497397968797536281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2069974331598645865024187 3104961497397968797536281)
        ·
          refine ⟨2328721123048476598152211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3104961497397968797536281 2328721123048476598152211)
          ·
            refine ⟨3493081684572714897228317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2328721123048476598152211 3493081684572714897228317)
            ·
              refine ⟨1309905631714768086460619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3493081684572714897228317 1309905631714768086460619)
              ·
                refine ⟨1964858447572152129690929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1309905631714768086460619 1964858447572152129690929)
                ·
                  refine ⟨1473643835679114097268197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1964858447572152129690929 1473643835679114097268197)
                  ·
                    refine ⟨276308219189833893237787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1473643835679114097268197 276308219189833893237787)
                    ·
                      rfl

theorem cell23_1614325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_1614325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614325 prefixEnd_1614325 := by exact prefixLift 1614325
  have htrace : WordTrace (prefixWord ++ tailWord_1614325) baseStart_1614325 baseEnd_1614325 := by
    simpa [prefixWord, tailWord_1614325, baseEnd_1614325] using wordTrace_append hprefix tailTrace_1614325
  have hstable : (prefixWord ++ tailWord_1614325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614325).length < 2 ^ (prefixWord ++ tailWord_1614325).sum := by decide
  have hdescent : baseEnd_1614325 < baseStart_1614325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614338 : List Nat := [3, 4, 1, 2, 2, 2, 2, 7]
def baseStart_1614338 : Nat := 118140960795 + 1614338 * 2 ^ 59
def prefixEnd_1614338 : Nat := 4983230072969 + 3 ^ 40 * 1614338 * 2
def baseEnd_1614338 : Nat := 30701160474741115883363

theorem tailTrace_1614338 : CollatzResearch.WordTrace tailWord_1614338 prefixEnd_1614338 30701160474741115883363 := by
  unfold tailWord_1614338
  simp only [CollatzResearch.WordTrace]
  refine ⟨14719936006384151956338917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39253162683691071883570445 14719936006384151956338917)
  ·
    refine ⟨2759988001197028491813547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14719936006384151956338917 2759988001197028491813547)
    ·
      refine ⟨4139982001795542737720321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2759988001197028491813547 4139982001795542737720321)
      ·
        refine ⟨3104986501346657053290241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4139982001795542737720321 3104986501346657053290241)
        ·
          refine ⟨2328739876009992789967681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3104986501346657053290241 2328739876009992789967681)
          ·
            refine ⟨1746554907007494592475761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2328739876009992789967681 1746554907007494592475761)
            ·
              refine ⟨1309916180255620944356821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1746554907007494592475761 1309916180255620944356821)
              ·
                refine ⟨30701160474741115883363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1309916180255620944356821 30701160474741115883363)
                ·
                  rfl

theorem cell23_1614338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 7].length) (baseStart_1614338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614338 prefixEnd_1614338 := by exact prefixLift 1614338
  have htrace : WordTrace (prefixWord ++ tailWord_1614338) baseStart_1614338 baseEnd_1614338 := by
    simpa [prefixWord, tailWord_1614338, baseEnd_1614338] using wordTrace_append hprefix tailTrace_1614338
  have hstable : (prefixWord ++ tailWord_1614338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614338).length < 2 ^ (prefixWord ++ tailWord_1614338).sum := by decide
  have hdescent : baseEnd_1614338 < baseStart_1614338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614341 : List Nat := [1, 3, 1, 1, 2, 2, 3, 4, 1, 3, 2]
def baseStart_1614341 : Nat := 118140960795 + 1614341 * 2 ^ 59
def prefixEnd_1614341 : Nat := 4983230072969 + 3 ^ 40 * 1614341 * 2
def baseEnd_1614341 : Nat := 828932873259973617113287

theorem tailTrace_1614341 : CollatzResearch.WordTrace tailWord_1614341 prefixEnd_1614341 828932873259973617113287 := by
  unfold tailWord_1614341
  simp only [CollatzResearch.WordTrace]
  refine ⟨58879853444525739337714877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39253235629683826225143251 58879853444525739337714877)
  ·
    refine ⟨22079945041697152251643079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58879853444525739337714877 22079945041697152251643079)
    ·
      refine ⟨33119917562545728377464619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22079945041697152251643079 33119917562545728377464619)
      ·
        refine ⟨49679876343818592566196929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33119917562545728377464619 49679876343818592566196929)
        ·
          refine ⟨37259907257863944424647697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49679876343818592566196929 37259907257863944424647697)
          ·
            refine ⟨27944930443397958318485773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37259907257863944424647697 27944930443397958318485773)
            ·
              refine ⟨10479348916274234369432165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27944930443397958318485773 10479348916274234369432165)
              ·
                refine ⟨1964877921801418944268531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10479348916274234369432165 1964877921801418944268531)
                ·
                  refine ⟨2947316882702128416402797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1964877921801418944268531 2947316882702128416402797)
                  ·
                    refine ⟨1105243831013298156151049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2947316882702128416402797 1105243831013298156151049)
                    ·
                      refine ⟨828932873259973617113287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1105243831013298156151049 828932873259973617113287)
                      ·
                        rfl

theorem cell23_1614341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 3, 2].length) (baseStart_1614341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614341 prefixEnd_1614341 := by exact prefixLift 1614341
  have htrace : WordTrace (prefixWord ++ tailWord_1614341) baseStart_1614341 baseEnd_1614341 := by
    simpa [prefixWord, tailWord_1614341, baseEnd_1614341] using wordTrace_append hprefix tailTrace_1614341
  have hstable : (prefixWord ++ tailWord_1614341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614341).length < 2 ^ (prefixWord ++ tailWord_1614341).sum := by decide
  have hdescent : baseEnd_1614341 < baseStart_1614341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614349 : List Nat := [1, 7, 1, 1, 1, 1, 3, 3, 1, 2, 2]
def baseStart_1614349 : Nat := 118140960795 + 1614349 * 2 ^ 59
def prefixEnd_1614349 : Nat := 4983230072969 + 3 ^ 40 * 1614349 * 2
def baseEnd_1614349 : Nat := 828936981105209585813251

theorem tailTrace_1614349 : CollatzResearch.WordTrace tailWord_1614349 prefixEnd_1614349 828936981105209585813251 := by
  unfold tailWord_1614349
  simp only [CollatzResearch.WordTrace]
  refine ⟨58880145228496756704006101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39253430152331171136004067 58880145228496756704006101)
  ·
    refine ⟨1380003403792892735250143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 58880145228496756704006101 1380003403792892735250143)
    ·
      refine ⟨2070005105689339102875215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1380003403792892735250143 2070005105689339102875215)
      ·
        refine ⟨3105007658534008654312823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2070005105689339102875215 3105007658534008654312823)
        ·
          refine ⟨4657511487801012981469235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3105007658534008654312823 4657511487801012981469235)
          ·
            refine ⟨6986267231701519472203853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4657511487801012981469235 6986267231701519472203853)
            ·
              refine ⟨2619850211888069802076445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6986267231701519472203853 2619850211888069802076445)
              ·
                refine ⟨982443829458026175778667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2619850211888069802076445 982443829458026175778667)
                ·
                  refine ⟨1473665744187039263668001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 982443829458026175778667 1473665744187039263668001)
                  ·
                    refine ⟨1105249308140279447751001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1473665744187039263668001 1105249308140279447751001)
                    ·
                      refine ⟨828936981105209585813251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1105249308140279447751001 828936981105209585813251)
                      ·
                        rfl

theorem cell23_1614349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_1614349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614349 prefixEnd_1614349 := by exact prefixLift 1614349
  have htrace : WordTrace (prefixWord ++ tailWord_1614349) baseStart_1614349 baseEnd_1614349 := by
    simpa [prefixWord, tailWord_1614349, baseEnd_1614349] using wordTrace_append hprefix tailTrace_1614349
  have hstable : (prefixWord ++ tailWord_1614349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614349).length < 2 ^ (prefixWord ++ tailWord_1614349).sum := by decide
  have hdescent : baseEnd_1614349 < baseStart_1614349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614382 : List Nat := [4, 1, 3, 1, 3, 2, 2, 1, 2, 1, 3]
def baseStart_1614382 : Nat := 118140960795 + 1614382 * 2 ^ 59
def prefixEnd_1614382 : Nat := 4983230072969 + 3 ^ 40 * 1614382 * 2
def baseEnd_1614382 : Nat := 828953925966807956700599

theorem tailTrace_1614382 : CollatzResearch.WordTrace tailWord_1614382 prefixEnd_1614382 828953925966807956700599 := by
  unfold tailWord_1614382
  simp only [CollatzResearch.WordTrace]
  refine ⟨7360168604672150417494675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39254232558251468893304933 7360168604672150417494675)
  ·
    refine ⟨11040252907008225626242013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7360168604672150417494675 11040252907008225626242013)
    ·
      refine ⟨4140094840128084609840755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11040252907008225626242013 4140094840128084609840755)
      ·
        refine ⟨6210142260192126914761133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4140094840128084609840755 6210142260192126914761133)
        ·
          refine ⟨2328803347572047593035425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6210142260192126914761133 2328803347572047593035425)
          ·
            refine ⟨1746602510679035694776569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2328803347572047593035425 1746602510679035694776569)
            ·
              refine ⟨1309951883009276771082427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1746602510679035694776569 1309951883009276771082427)
              ·
                refine ⟨1964927824513915156623641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1309951883009276771082427 1964927824513915156623641)
                ·
                  refine ⟨1473695868385436367467731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1964927824513915156623641 1473695868385436367467731)
                  ·
                    refine ⟨2210543802578154551201597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1473695868385436367467731 2210543802578154551201597)
                    ·
                      refine ⟨828953925966807956700599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2210543802578154551201597 828953925966807956700599)
                      ·
                        rfl

theorem cell23_1614382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_1614382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614382 prefixEnd_1614382 := by exact prefixLift 1614382
  have htrace : WordTrace (prefixWord ++ tailWord_1614382) baseStart_1614382 baseEnd_1614382 := by
    simpa [prefixWord, tailWord_1614382, baseEnd_1614382] using wordTrace_append hprefix tailTrace_1614382
  have hstable : (prefixWord ++ tailWord_1614382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614382).length < 2 ^ (prefixWord ++ tailWord_1614382).sum := by decide
  have hdescent : baseEnd_1614382 < baseStart_1614382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614424 : List Nat := [2, 1, 2, 2, 1, 2, 4, 2, 2, 5]
def baseStart_1614424 : Nat := 118140960795 + 1614424 * 2 ^ 59
def prefixEnd_1614424 : Nat := 4983230072969 + 3 ^ 40 * 1614424 * 2
def baseEnd_1614424 : Nat := 276325164051432264125135

theorem tailTrace_1614424 : CollatzResearch.WordTrace tailWord_1614424 prefixEnd_1614424 276325164051432264125135 := by
  unfold tailWord_1614424
  simp only [CollatzResearch.WordTrace]
  refine ⟨29441440351612522256493163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39255253802150029675324217 29441440351612522256493163)
  ·
    refine ⟨44162160527418783384739745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29441440351612522256493163 44162160527418783384739745)
    ·
      refine ⟨33121620395564087538554809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44162160527418783384739745 33121620395564087538554809)
      ·
        refine ⟨24841215296673065653916107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33121620395564087538554809 24841215296673065653916107)
        ·
          refine ⟨37261822945009598480874161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24841215296673065653916107 37261822945009598480874161)
          ·
            refine ⟨27946367208757198860655621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37261822945009598480874161 27946367208757198860655621)
            ·
              refine ⟨5239943851641974786372929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27946367208757198860655621 5239943851641974786372929)
              ·
                refine ⟨3929957888731481089779697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5239943851641974786372929 3929957888731481089779697)
                ·
                  refine ⟨2947468416548610817334773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3929957888731481089779697 2947468416548610817334773)
                  ·
                    refine ⟨276325164051432264125135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2947468416548610817334773 276325164051432264125135)
                    ·
                      rfl

theorem cell23_1614424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 2, 5].length) (baseStart_1614424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614424 prefixEnd_1614424 := by exact prefixLift 1614424
  have htrace : WordTrace (prefixWord ++ tailWord_1614424) baseStart_1614424 baseEnd_1614424 := by
    simpa [prefixWord, tailWord_1614424, baseEnd_1614424] using wordTrace_append hprefix tailTrace_1614424
  have hstable : (prefixWord ++ tailWord_1614424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614424).length < 2 ^ (prefixWord ++ tailWord_1614424).sum := by decide
  have hdescent : baseEnd_1614424 < baseStart_1614424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614428 : List Nat := [2, 2, 4, 1, 3, 1, 1, 4, 5]
def baseStart_1614428 : Nat := 118140960795 + 1614428 * 2 ^ 59
def prefixEnd_1614428 : Nat := 4983230072969 + 3 ^ 40 * 1614428 * 2
def baseEnd_1614428 : Nat := 92108616230768308525043

theorem tailTrace_1614428 : CollatzResearch.WordTrace tailWord_1614428 prefixEnd_1614428 92108616230768308525043 := by
  unfold tailWord_1614428
  simp only [CollatzResearch.WordTrace]
  refine ⟨29441513297605276598065969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39255351063473702130754625 29441513297605276598065969)
  ·
    refine ⟨22081134973203957448549477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29441513297605276598065969 22081134973203957448549477)
    ·
      refine ⟨4140212807475742021603027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22081134973203957448549477 4140212807475742021603027)
      ·
        refine ⟨6210319211213613032404541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4140212807475742021603027 6210319211213613032404541)
        ·
          refine ⟨2328869704205104887151703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6210319211213613032404541 2328869704205104887151703)
          ·
            refine ⟨3493304556307657330727555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2328869704205104887151703 3493304556307657330727555)
            ·
              refine ⟨5239956834461485996091333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3493304556307657330727555 5239956834461485996091333)
              ·
                refine ⟨982491906461528624267125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5239956834461485996091333 982491906461528624267125)
                ·
                  refine ⟨92108616230768308525043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 982491906461528624267125 92108616230768308525043)
                  ·
                    rfl

theorem cell23_1614428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4, 5].length) (baseStart_1614428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614428 prefixEnd_1614428 := by exact prefixLift 1614428
  have htrace : WordTrace (prefixWord ++ tailWord_1614428) baseStart_1614428 baseEnd_1614428 := by
    simpa [prefixWord, tailWord_1614428, baseEnd_1614428] using wordTrace_append hprefix tailTrace_1614428
  have hstable : (prefixWord ++ tailWord_1614428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614428).length < 2 ^ (prefixWord ++ tailWord_1614428).sum := by decide
  have hdescent : baseEnd_1614428 < baseStart_1614428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614444 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 4]
def baseStart_1614444 : Nat := 118140960795 + 1614444 * 2 ^ 59
def prefixEnd_1614444 : Nat := 4983230072969 + 3 ^ 40 * 1614444 * 2
def baseEnd_1614444 : Nat := 828985761767386714125313

theorem tailTrace_1614444 : CollatzResearch.WordTrace tailWord_1614444 prefixEnd_1614444 828985761767386714125313 := by
  unfold tailWord_1614444
  simp only [CollatzResearch.WordTrace]
  refine ⟨29441805081576293964357193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39255740108768391952476257 29441805081576293964357193)
  ·
    refine ⟨22081353811182220473267895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29441805081576293964357193 22081353811182220473267895)
    ·
      refine ⟨33122030716773330709901843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22081353811182220473267895 33122030716773330709901843)
      ·
        refine ⟨49683046075159996064852765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33122030716773330709901843 49683046075159996064852765)
        ·
          refine ⟨18631142278184998524319787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49683046075159996064852765 18631142278184998524319787)
          ·
            refine ⟨27946713417277497786479681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18631142278184998524319787 27946713417277497786479681)
            ·
              refine ⟨20960035062958123339859761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27946713417277497786479681 20960035062958123339859761)
              ·
                refine ⟨15720026297218592504894821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20960035062958123339859761 15720026297218592504894821)
                ·
                  refine ⟨2947504930728486094667779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15720026297218592504894821 2947504930728486094667779)
                  ·
                    refine ⟨4421257396092729142001669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2947504930728486094667779 4421257396092729142001669)
                    ·
                      refine ⟨828985761767386714125313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4421257396092729142001669 828985761767386714125313)
                      ·
                        rfl

theorem cell23_1614444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_1614444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614444 prefixEnd_1614444 := by exact prefixLift 1614444
  have htrace : WordTrace (prefixWord ++ tailWord_1614444) baseStart_1614444 baseEnd_1614444 := by
    simpa [prefixWord, tailWord_1614444, baseEnd_1614444] using wordTrace_append hprefix tailTrace_1614444
  have hstable : (prefixWord ++ tailWord_1614444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614444).length < 2 ^ (prefixWord ++ tailWord_1614444).sum := by decide
  have hdescent : baseEnd_1614444 < baseStart_1614444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614461 : List Nat := [1, 4, 1, 1, 5, 1, 1, 1, 1, 3, 4]
def baseStart_1614461 : Nat := 118140960795 + 1614461 * 2 ^ 59
def prefixEnd_1614461 : Nat := 4983230072969 + 3 ^ 40 * 1614461 * 2
def baseEnd_1614461 : Nat := 828994490938513147612735

theorem tailTrace_1614461 : CollatzResearch.WordTrace tailWord_1614461 prefixEnd_1614461 828994490938513147612735 := by
  unfold tailWord_1614461
  simp only [CollatzResearch.WordTrace]
  refine ⟨58884230204090999832083237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39256153469393999888055491 58884230204090999832083237)
  ·
    refine ⟨11040793163267062468515607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58884230204090999832083237 11040793163267062468515607)
    ·
      refine ⟨16561189744900593702773411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11040793163267062468515607 16561189744900593702773411)
      ·
        refine ⟨24841784617350890554160117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16561189744900593702773411 24841784617350890554160117)
        ·
          refine ⟨2328917307876645989452511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24841784617350890554160117 2328917307876645989452511)
          ·
            refine ⟨3493375961814968984178767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2328917307876645989452511 3493375961814968984178767)
            ·
              refine ⟨5240063942722453476268151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3493375961814968984178767 5240063942722453476268151)
              ·
                refine ⟨7860095914083680214402227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5240063942722453476268151 7860095914083680214402227)
                ·
                  refine ⟨11790143871125520321603341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7860095914083680214402227 11790143871125520321603341)
                  ·
                    refine ⟨4421303951672070120601253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11790143871125520321603341 4421303951672070120601253)
                    ·
                      refine ⟨828994490938513147612735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4421303951672070120601253 828994490938513147612735)
                      ·
                        rfl

theorem cell23_1614461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_1614461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614461 prefixEnd_1614461 := by exact prefixLift 1614461
  have htrace : WordTrace (prefixWord ++ tailWord_1614461) baseStart_1614461 baseEnd_1614461 := by
    simpa [prefixWord, tailWord_1614461, baseEnd_1614461] using wordTrace_append hprefix tailTrace_1614461
  have hstable : (prefixWord ++ tailWord_1614461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614461).length < 2 ^ (prefixWord ++ tailWord_1614461).sum := by decide
  have hdescent : baseEnd_1614461 < baseStart_1614461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614488 : List Nat := [2, 1, 2, 4, 1, 1, 1, 6, 1, 4]
def baseStart_1614488 : Nat := 118140960795 + 1614488 * 2 ^ 59
def prefixEnd_1614488 : Nat := 4983230072969 + 3 ^ 40 * 1614488 * 2
def baseEnd_1614488 : Nat := 276336118305394847325037

theorem tailTrace_1614488 : CollatzResearch.WordTrace tailWord_1614488 prefixEnd_1614488 276336118305394847325037 := by
  unfold tailWord_1614488
  simp only [CollatzResearch.WordTrace]
  refine ⟨29442607487496591721658059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39256809983328788962210745 29442607487496591721658059)
  ·
    refine ⟨44163911231244887582487089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29442607487496591721658059 44163911231244887582487089)
    ·
      refine ⟨33122933423433665686865317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44163911231244887582487089 33122933423433665686865317)
      ·
        refine ⟨6210550016893812316287247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33122933423433665686865317 6210550016893812316287247)
        ·
          refine ⟨9315825025340718474430871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6210550016893812316287247 9315825025340718474430871)
          ·
            refine ⟨13973737538011077711646307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9315825025340718474430871 13973737538011077711646307)
            ·
              refine ⟨20960606307016616567469461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13973737538011077711646307 20960606307016616567469461)
              ·
                refine ⟨982528420641403901600131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20960606307016616567469461 982528420641403901600131)
                ·
                  refine ⟨1473792630962105852400197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 982528420641403901600131 1473792630962105852400197)
                  ·
                    refine ⟨276336118305394847325037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1473792630962105852400197 276336118305394847325037)
                    ·
                      rfl

theorem cell23_1614488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6, 1, 4].length) (baseStart_1614488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614488 prefixEnd_1614488 := by exact prefixLift 1614488
  have htrace : WordTrace (prefixWord ++ tailWord_1614488) baseStart_1614488 baseEnd_1614488 := by
    simpa [prefixWord, tailWord_1614488, baseEnd_1614488] using wordTrace_append hprefix tailTrace_1614488
  have hstable : (prefixWord ++ tailWord_1614488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614488).length < 2 ^ (prefixWord ++ tailWord_1614488).sum := by decide
  have hdescent : baseEnd_1614488 < baseStart_1614488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614538 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 4, 3, 2]
def baseStart_1614538 : Nat := 118140960795 + 1614538 * 2 ^ 59
def prefixEnd_1614538 : Nat := 4983230072969 + 3 ^ 40 * 1614538 * 2
def baseEnd_1614538 : Nat := 829034028948909346349881

theorem tailTrace_1614538 : CollatzResearch.WordTrace tailWord_1614538 prefixEnd_1614538 829034028948909346349881 := by
  unfold tailWord_1614538
  simp only [CollatzResearch.WordTrace]
  refine ⟨14721759656203010495659067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39258025749874694655090845 14721759656203010495659067)
  ·
    refine ⟨22082639484304515743488601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14721759656203010495659067 22082639484304515743488601)
    ·
      refine ⟨16561979613228386807616451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22082639484304515743488601 16561979613228386807616451)
      ·
        refine ⟨24842969419842580211424677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16561979613228386807616451 24842969419842580211424677)
        ·
          refine ⟨4658056766220483789642127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24842969419842580211424677 4658056766220483789642127)
          ·
            refine ⟨6987085149330725684463191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4658056766220483789642127 6987085149330725684463191)
            ·
              refine ⟨10480627723996088526694787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6987085149330725684463191 10480627723996088526694787)
              ·
                refine ⟨15720941585994132790042181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10480627723996088526694787 15720941585994132790042181)
                ·
                  refine ⟨2947676547373899898132909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15720941585994132790042181 2947676547373899898132909)
                  ·
                    refine ⟨1105378705265212461799841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2947676547373899898132909 1105378705265212461799841)
                    ·
                      refine ⟨829034028948909346349881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1105378705265212461799841 829034028948909346349881)
                      ·
                        rfl

theorem cell23_1614538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 4, 3, 2].length) (baseStart_1614538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614538 prefixEnd_1614538 := by exact prefixLift 1614538
  have htrace : WordTrace (prefixWord ++ tailWord_1614538) baseStart_1614538 baseEnd_1614538 := by
    simpa [prefixWord, tailWord_1614538, baseEnd_1614538] using wordTrace_append hprefix tailTrace_1614538
  have hstable : (prefixWord ++ tailWord_1614538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614538).length < 2 ^ (prefixWord ++ tailWord_1614538).sum := by decide
  have hdescent : baseEnd_1614538 < baseStart_1614538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614568 : List Nat := [2, 1, 4, 1, 4, 1, 1, 1, 3, 1, 4]
def baseStart_1614568 : Nat := 118140960795 + 1614568 * 2 ^ 59
def prefixEnd_1614568 : Nat := 4983230072969 + 3 ^ 40 * 1614568 * 2
def baseEnd_1614568 : Nat := 829049433368544228974743

theorem tailTrace_1614568 : CollatzResearch.WordTrace tailWord_1614568 prefixEnd_1614568 829049433368544228974743 := by
  unfold tailWord_1614568
  simp only [CollatzResearch.WordTrace]
  refine ⟨29444066407351678553114179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39258755209802238070818905 29444066407351678553114179)
  ·
    refine ⟨44166099611027517829671269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29444066407351678553114179 44166099611027517829671269)
    ·
      refine ⟨8281143677067659593063363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44166099611027517829671269 8281143677067659593063363)
      ·
        refine ⟨12421715515601489389595045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8281143677067659593063363 12421715515601489389595045)
        ·
          refine ⟨2329071659175279260549071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12421715515601489389595045 2329071659175279260549071)
          ·
            refine ⟨3493607488762918890823607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2329071659175279260549071 3493607488762918890823607)
            ·
              refine ⟨5240411233144378336235411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3493607488762918890823607 5240411233144378336235411)
              ·
                refine ⟨7860616849716567504353117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5240411233144378336235411 7860616849716567504353117)
                ·
                  refine ⟨2947731318643712814132419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7860616849716567504353117 2947731318643712814132419)
                  ·
                    refine ⟨4421596977965569221198629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2947731318643712814132419 4421596977965569221198629)
                    ·
                      refine ⟨829049433368544228974743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4421596977965569221198629 829049433368544228974743)
                      ·
                        rfl

theorem cell23_1614568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_1614568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614568 prefixEnd_1614568 := by exact prefixLift 1614568
  have htrace : WordTrace (prefixWord ++ tailWord_1614568) baseStart_1614568 baseEnd_1614568 := by
    simpa [prefixWord, tailWord_1614568, baseEnd_1614568] using wordTrace_append hprefix tailTrace_1614568
  have hstable : (prefixWord ++ tailWord_1614568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614568).length < 2 ^ (prefixWord ++ tailWord_1614568).sum := by decide
  have hdescent : baseEnd_1614568 < baseStart_1614568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614588 : List Nat := [2, 2, 2, 1, 3, 4, 1, 1, 1, 1, 5]
def baseStart_1614588 : Nat := 118140960795 + 1614588 * 2 ^ 59
def prefixEnd_1614588 : Nat := 4983230072969 + 3 ^ 40 * 1614588 * 2
def baseEnd_1614588 : Nat := 829059702981634150724651

theorem tailTrace_1614588 : CollatzResearch.WordTrace tailWord_1614588 prefixEnd_1614588 829059702981634150724651 := by
  unfold tailWord_1614588
  simp only [CollatzResearch.WordTrace]
  refine ⟨29444431137315450260978209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39259241516420600347970945 29444431137315450260978209)
  ·
    refine ⟨22083323352986587695733657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29444431137315450260978209 22083323352986587695733657)
    ·
      refine ⟨16562492514739940771800243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22083323352986587695733657 16562492514739940771800243)
      ·
        refine ⟨24843738772109911157700365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16562492514739940771800243 24843738772109911157700365)
        ·
          refine ⟨9316402039541216684137637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24843738772109911157700365 9316402039541216684137637)
          ·
            refine ⟨1746825382413978128275807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9316402039541216684137637 1746825382413978128275807)
            ·
              refine ⟨2620238073620967192413711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1746825382413978128275807 2620238073620967192413711)
              ·
                refine ⟨3930357110431450788620567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2620238073620967192413711 3930357110431450788620567)
                ·
                  refine ⟨5895535665647176182930851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3930357110431450788620567 5895535665647176182930851)
                  ·
                    refine ⟨8843303498470764274396277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5895535665647176182930851 8843303498470764274396277)
                    ·
                      refine ⟨829059702981634150724651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8843303498470764274396277 829059702981634150724651)
                      ·
                        rfl

theorem cell23_1614588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_1614588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614588 prefixEnd_1614588 := by exact prefixLift 1614588
  have htrace : WordTrace (prefixWord ++ tailWord_1614588) baseStart_1614588 baseEnd_1614588 := by
    simpa [prefixWord, tailWord_1614588, baseEnd_1614588] using wordTrace_append hprefix tailTrace_1614588
  have hstable : (prefixWord ++ tailWord_1614588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614588).length < 2 ^ (prefixWord ++ tailWord_1614588).sum := by decide
  have hdescent : baseEnd_1614588 < baseStart_1614588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614602 : List Nat := [3, 1, 2, 2, 1, 2, 3, 4, 1, 2, 2]
def baseStart_1614602 : Nat := 118140960795 + 1614602 * 2 ^ 59
def prefixEnd_1614602 : Nat := 4983230072969 + 3 ^ 40 * 1614602 * 2
def baseEnd_1614602 : Nat := 829066891710797095949587

theorem tailTrace_1614602 : CollatzResearch.WordTrace tailWord_1614602 prefixEnd_1614602 829066891710797095949587 := by
  unfold tailWord_1614602
  simp only [CollatzResearch.WordTrace]
  refine ⟨14722343224145045228241515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39259581931053453941977373 14722343224145045228241515)
  ·
    refine ⟨22083514836217567842362273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14722343224145045228241515 22083514836217567842362273)
    ·
      refine ⟨16562636127163175881771705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22083514836217567842362273 16562636127163175881771705)
      ·
        refine ⟨12421977095372381911328779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16562636127163175881771705 12421977095372381911328779)
        ·
          refine ⟨18632965643058572866993169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12421977095372381911328779 18632965643058572866993169)
          ·
            refine ⟨13974724232293929650244877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18632965643058572866993169 13974724232293929650244877)
            ·
              refine ⟨5240521587110223618841829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13974724232293929650244877 5240521587110223618841829)
              ·
                refine ⟨982597797583166928532843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5240521587110223618841829 982597797583166928532843)
                ·
                  refine ⟨1473896696374750392799265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 982597797583166928532843 1473896696374750392799265)
                  ·
                    refine ⟨1105422522281062794599449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1473896696374750392799265 1105422522281062794599449)
                    ·
                      refine ⟨829066891710797095949587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1105422522281062794599449 829066891710797095949587)
                      ·
                        rfl

theorem cell23_1614602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_1614602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614602 prefixEnd_1614602 := by exact prefixLift 1614602
  have htrace : WordTrace (prefixWord ++ tailWord_1614602) baseStart_1614602 baseEnd_1614602 := by
    simpa [prefixWord, tailWord_1614602, baseEnd_1614602] using wordTrace_append hprefix tailTrace_1614602
  have hstable : (prefixWord ++ tailWord_1614602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614602).length < 2 ^ (prefixWord ++ tailWord_1614602).sum := by decide
  have hdescent : baseEnd_1614602 < baseStart_1614602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614618 : List Nat := [3, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3]
def baseStart_1614618 : Nat := 118140960795 + 1614618 * 2 ^ 59
def prefixEnd_1614618 : Nat := 4983230072969 + 3 ^ 40 * 1614618 * 2
def baseEnd_1614618 : Nat := 829075107401269033349513

theorem tailTrace_1614618 : CollatzResearch.WordTrace tailWord_1614618 prefixEnd_1614618 829075107401269033349513 := by
  unfold tailWord_1614618
  simp only [CollatzResearch.WordTrace]
  refine ⟨14722489116130553911387127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39259970976348143763699005 14722489116130553911387127)
  ·
    refine ⟨22083733674195830867080691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14722489116130553911387127 22083733674195830867080691)
    ·
      refine ⟨33125600511293746300621037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22083733674195830867080691 33125600511293746300621037)
      ·
        refine ⟨12422100191735154862732889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33125600511293746300621037 12422100191735154862732889)
        ·
          refine ⟨9316575143801366147049667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12422100191735154862732889 9316575143801366147049667)
          ·
            refine ⟨13974862715702049220574501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9316575143801366147049667 13974862715702049220574501)
            ·
              refine ⟨2620286759194134228857719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13974862715702049220574501 2620286759194134228857719)
              ·
                refine ⟨3930430138791201343286579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2620286759194134228857719 3930430138791201343286579)
                ·
                  refine ⟨5895645208186802014929869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3930430138791201343286579 5895645208186802014929869)
                  ·
                    refine ⟨2210866953070050755598701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5895645208186802014929869 2210866953070050755598701)
                    ·
                      refine ⟨829075107401269033349513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2210866953070050755598701 829075107401269033349513)
                      ·
                        rfl

theorem cell23_1614618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_1614618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614618 prefixEnd_1614618 := by exact prefixLift 1614618
  have htrace : WordTrace (prefixWord ++ tailWord_1614618) baseStart_1614618 baseEnd_1614618 := by
    simpa [prefixWord, tailWord_1614618, baseEnd_1614618] using wordTrace_append hprefix tailTrace_1614618
  have hstable : (prefixWord ++ tailWord_1614618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614618).length < 2 ^ (prefixWord ++ tailWord_1614618).sum := by decide
  have hdescent : baseEnd_1614618 < baseStart_1614618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614661 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 2, 4, 3]
def baseStart_1614661 : Nat := 118140960795 + 1614661 * 2 ^ 59
def prefixEnd_1614661 : Nat := 4983230072969 + 3 ^ 40 * 1614661 * 2
def baseEnd_1614661 : Nat := 829097187069412365111815

theorem tailTrace_1614661 : CollatzResearch.WordTrace tailWord_1614661 prefixEnd_1614661 829097187069412365111815 := by
  unfold tailWord_1614661
  simp only [CollatzResearch.WordTrace]
  refine ⟨58891524803366433989363837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39261016535577622659575891 58891524803366433989363837)
  ·
    refine ⟨22084321801262412746011439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58891524803366433989363837 22084321801262412746011439)
    ·
      refine ⟨33126482701893619119017159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22084321801262412746011439 33126482701893619119017159)
      ·
        refine ⟨49689724052840428678525739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33126482701893619119017159 49689724052840428678525739)
        ·
          refine ⟨74534586079260643017788609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49689724052840428678525739 74534586079260643017788609)
          ·
            refine ⟨55900939559445482263341457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74534586079260643017788609 55900939559445482263341457)
            ·
              refine ⟨41925704669584111697506093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55900939559445482263341457 41925704669584111697506093)
              ·
                refine ⟨15722139251094041886564785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41925704669584111697506093 15722139251094041886564785)
                ·
                  refine ⟨11791604438320531414923589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15722139251094041886564785 11791604438320531414923589)
                  ·
                    refine ⟨2210925832185099640298173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11791604438320531414923589 2210925832185099640298173)
                    ·
                      refine ⟨829097187069412365111815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2210925832185099640298173 829097187069412365111815)
                      ·
                        rfl

theorem cell23_1614661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 4, 3].length) (baseStart_1614661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614661 prefixEnd_1614661 := by exact prefixLift 1614661
  have htrace : WordTrace (prefixWord ++ tailWord_1614661) baseStart_1614661 baseEnd_1614661 := by
    simpa [prefixWord, tailWord_1614661, baseEnd_1614661] using wordTrace_append hprefix tailTrace_1614661
  have hstable : (prefixWord ++ tailWord_1614661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614661).length < 2 ^ (prefixWord ++ tailWord_1614661).sum := by decide
  have hdescent : baseEnd_1614661 < baseStart_1614661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614669 : List Nat := [1, 6, 1, 2, 3, 1, 1, 1, 1, 3, 3]
def baseStart_1614669 : Nat := 118140960795 + 1614669 * 2 ^ 59
def prefixEnd_1614669 : Nat := 4983230072969 + 3 ^ 40 * 1614669 * 2
def baseEnd_1614669 : Nat := 829101294914648333811779

theorem tailTrace_1614669 : CollatzResearch.WordTrace tailWord_1614669 prefixEnd_1614669 829101294914648333811779 := by
  unfold tailWord_1614669
  simp only [CollatzResearch.WordTrace]
  refine ⟨58891816587337451355655061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39261211058224967570436707 58891816587337451355655061)
  ·
    refine ⟨2760553902531443032296331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58891816587337451355655061 2760553902531443032296331)
    ·
      refine ⟨4140830853797164548444497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2760553902531443032296331 4140830853797164548444497)
      ·
        refine ⟨3105623140347873411333373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4140830853797164548444497 3105623140347873411333373)
        ·
          refine ⟨1164608677630452529250015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3105623140347873411333373 1164608677630452529250015)
          ·
            refine ⟨1746913016445678793875023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1164608677630452529250015 1746913016445678793875023)
            ·
              refine ⟨2620369524668518190812535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1746913016445678793875023 2620369524668518190812535)
              ·
                refine ⟨3930554287002777286218803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2620369524668518190812535 3930554287002777286218803)
                ·
                  refine ⟨5895831430504165929328205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3930554287002777286218803 5895831430504165929328205)
                  ·
                    refine ⟨2210936786439062223498077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5895831430504165929328205 2210936786439062223498077)
                    ·
                      refine ⟨829101294914648333811779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2210936786439062223498077 829101294914648333811779)
                      ·
                        rfl

theorem cell23_1614669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_1614669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614669 prefixEnd_1614669 := by exact prefixLift 1614669
  have htrace : WordTrace (prefixWord ++ tailWord_1614669) baseStart_1614669 baseEnd_1614669 := by
    simpa [prefixWord, tailWord_1614669, baseEnd_1614669] using wordTrace_append hprefix tailTrace_1614669
  have hstable : (prefixWord ++ tailWord_1614669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614669).length < 2 ^ (prefixWord ++ tailWord_1614669).sum := by decide
  have hdescent : baseEnd_1614669 < baseStart_1614669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614675 : List Nat := [1, 1, 1, 2, 1, 1, 3, 7, 2, 2, 2]
def baseStart_1614675 : Nat := 118140960795 + 1614675 * 2 ^ 59
def prefixEnd_1614675 : Nat := 4983230072969 + 3 ^ 40 * 1614675 * 2
def baseEnd_1614675 : Nat := 829104375798575310336751

theorem tailTrace_1614675 : CollatzResearch.WordTrace tailWord_1614675 prefixEnd_1614675 829104375798575310336751 := by
  unfold tailWord_1614675
  simp only [CollatzResearch.WordTrace]
  refine ⟨58892035425315714380373479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39261356950210476253582319 58892035425315714380373479)
  ·
    refine ⟨88338053137973571570560219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58892035425315714380373479 88338053137973571570560219)
    ·
      refine ⟨132507079706960357355840329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88338053137973571570560219 132507079706960357355840329)
      ·
        refine ⟨99380309780220268016880247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132507079706960357355840329 99380309780220268016880247)
        ·
          refine ⟨149070464670330402025320371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99380309780220268016880247 149070464670330402025320371)
          ·
            refine ⟨223605697005495603037980557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149070464670330402025320371 223605697005495603037980557)
            ·
              refine ⟨83852136377060851139242709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223605697005495603037980557 83852136377060851139242709)
              ·
                refine ⟨1965284446337363698576001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 83852136377060851139242709 1965284446337363698576001)
                ·
                  refine ⟨1473963334753022773932001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1965284446337363698576001 1473963334753022773932001)
                  ·
                    refine ⟨1105472501064767080449001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1473963334753022773932001 1105472501064767080449001)
                    ·
                      refine ⟨829104375798575310336751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1105472501064767080449001 829104375798575310336751)
                      ·
                        rfl

theorem cell23_1614675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2, 2, 2].length) (baseStart_1614675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614675 prefixEnd_1614675 := by exact prefixLift 1614675
  have htrace : WordTrace (prefixWord ++ tailWord_1614675) baseStart_1614675 baseEnd_1614675 := by
    simpa [prefixWord, tailWord_1614675, baseEnd_1614675] using wordTrace_append hprefix tailTrace_1614675
  have hstable : (prefixWord ++ tailWord_1614675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614675).length < 2 ^ (prefixWord ++ tailWord_1614675).sum := by decide
  have hdescent : baseEnd_1614675 < baseStart_1614675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614681 : List Nat := [1, 2, 1, 2, 2, 4, 2, 2, 7]
def baseStart_1614681 : Nat := 118140960795 + 1614681 * 2 ^ 59
def prefixEnd_1614681 : Nat := 4983230072969 + 3 ^ 40 * 1614681 * 2
def baseEnd_1614681 : Nat := 92123050742500254095747

theorem tailTrace_1614681 : CollatzResearch.WordTrace tailWord_1614681 prefixEnd_1614681 92123050742500254095747 := by
  unfold tailWord_1614681
  simp only [CollatzResearch.WordTrace]
  refine ⟨58892254263293977405091897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39261502842195984936727931 58892254263293977405091897)
  ·
    refine ⟨44169190697470483053818923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58892254263293977405091897 44169190697470483053818923)
    ·
      refine ⟨66253786046205724580728385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44169190697470483053818923 66253786046205724580728385)
      ·
        refine ⟨49690339534654293435546289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66253786046205724580728385 49690339534654293435546289)
        ·
          refine ⟨37267754650990720076659717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49690339534654293435546289 37267754650990720076659717)
          ·
            refine ⟨6987703997060760014373697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37267754650990720076659717 6987703997060760014373697)
            ·
              refine ⟨5240777997795570010780273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6987703997060760014373697 5240777997795570010780273)
              ·
                refine ⟨3930583498346677508085205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5240777997795570010780273 3930583498346677508085205)
                ·
                  refine ⟨92123050742500254095747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3930583498346677508085205 92123050742500254095747)
                  ·
                    rfl

theorem cell23_1614681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 7].length) (baseStart_1614681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614681 prefixEnd_1614681 := by exact prefixLift 1614681
  have htrace : WordTrace (prefixWord ++ tailWord_1614681) baseStart_1614681 baseEnd_1614681 := by
    simpa [prefixWord, tailWord_1614681, baseEnd_1614681] using wordTrace_append hprefix tailTrace_1614681
  have hstable : (prefixWord ++ tailWord_1614681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614681).length < 2 ^ (prefixWord ++ tailWord_1614681).sum := by decide
  have hdescent : baseEnd_1614681 < baseStart_1614681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614731 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 4]
def baseStart_1614731 : Nat := 118140960795 + 1614731 * 2 ^ 59
def prefixEnd_1614731 : Nat := 4983230072969 + 3 ^ 40 * 1614731 * 2
def baseEnd_1614731 : Nat := 829133130715227091236493

theorem tailTrace_1614731 : CollatzResearch.WordTrace tailWord_1614731 prefixEnd_1614731 829133130715227091236493 := by
  unfold tailWord_1614731
  simp only [CollatzResearch.WordTrace]
  refine ⟨58894077913112835944412047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39262718608741890629608031 58894077913112835944412047)
  ·
    refine ⟨88341116869669253916618071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58894077913112835944412047 88341116869669253916618071)
    ·
      refine ⟨132511675304503880874927107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88341116869669253916618071 132511675304503880874927107)
      ·
        refine ⟨198767512956755821312390661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132511675304503880874927107 198767512956755821312390661)
        ·
          refine ⟨37268908679391716496073249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198767512956755821312390661 37268908679391716496073249)
          ·
            refine ⟨27951681509543787372054937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37268908679391716496073249 27951681509543787372054937)
            ·
              refine ⟨20963761132157840529041203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27951681509543787372054937 20963761132157840529041203)
              ·
                refine ⟨31445641698236760793561805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20963761132157840529041203 31445641698236760793561805)
                ·
                  refine ⟨11792115636838785297585677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31445641698236760793561805 11792115636838785297585677)
                  ·
                    refine ⟨4422043363814544486594629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11792115636838785297585677 4422043363814544486594629)
                    ·
                      refine ⟨829133130715227091236493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4422043363814544486594629 829133130715227091236493)
                      ·
                        rfl

theorem cell23_1614731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 4].length) (baseStart_1614731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614731 prefixEnd_1614731 := by exact prefixLift 1614731
  have htrace : WordTrace (prefixWord ++ tailWord_1614731) baseStart_1614731 baseEnd_1614731 := by
    simpa [prefixWord, tailWord_1614731, baseEnd_1614731] using wordTrace_append hprefix tailTrace_1614731
  have hstable : (prefixWord ++ tailWord_1614731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614731).length < 2 ^ (prefixWord ++ tailWord_1614731).sum := by decide
  have hdescent : baseEnd_1614731 < baseStart_1614731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614761 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 2, 1, 6]
def baseStart_1614761 : Nat := 118140960795 + 1614761 * 2 ^ 59
def prefixEnd_1614761 : Nat := 4983230072969 + 3 ^ 40 * 1614761 * 2
def baseEnd_1614761 : Nat := 829148535134861973861355

theorem tailTrace_1614761 : CollatzResearch.WordTrace tailWord_1614761 prefixEnd_1614761 829148535134861973861355 := by
  unfold tailWord_1614761
  simp only [CollatzResearch.WordTrace]
  refine ⟨58895172103004151068004137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39263448068669434045336091 58895172103004151068004137)
  ·
    refine ⟨44171379077253113301003103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58895172103004151068004137 44171379077253113301003103)
    ·
      refine ⟨66257068615879669951504655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44171379077253113301003103 66257068615879669951504655)
      ·
        refine ⟨99385602923819504927256983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66257068615879669951504655 99385602923819504927256983)
        ·
          refine ⟨149078404385729257390885475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99385602923819504927256983 149078404385729257390885475)
          ·
            refine ⟨223617606578593886086328213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149078404385729257390885475 223617606578593886086328213)
            ·
              refine ⟨10482075308371588410296635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 223617606578593886086328213 10482075308371588410296635)
              ·
                refine ⟨15723112962557382615444953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10482075308371588410296635 15723112962557382615444953)
                ·
                  refine ⟨11792334721918036961583715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15723112962557382615444953 11792334721918036961583715)
                  ·
                    refine ⟨17688502082877055442375573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11792334721918036961583715 17688502082877055442375573)
                    ·
                      refine ⟨829148535134861973861355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17688502082877055442375573 829148535134861973861355)
                      ·
                        rfl

theorem cell23_1614761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 1, 6].length) (baseStart_1614761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614761 prefixEnd_1614761 := by exact prefixLift 1614761
  have htrace : WordTrace (prefixWord ++ tailWord_1614761) baseStart_1614761 baseEnd_1614761 := by
    simpa [prefixWord, tailWord_1614761, baseEnd_1614761] using wordTrace_append hprefix tailTrace_1614761
  have hstable : (prefixWord ++ tailWord_1614761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614761).length < 2 ^ (prefixWord ++ tailWord_1614761).sum := by decide
  have hdescent : baseEnd_1614761 < baseStart_1614761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614802 : List Nat := [3, 2, 2, 3, 1, 1, 3, 1, 2, 2, 3]
def baseStart_1614802 : Nat := 118140960795 + 1614802 * 2 ^ 59
def prefixEnd_1614802 : Nat := 4983230072969 + 3 ^ 40 * 1614802 * 2
def baseEnd_1614802 : Nat := 829169587841696313448667

theorem tailTrace_1614802 : CollatzResearch.WordTrace tailWord_1614802 prefixEnd_1614802 829169587841696313448667 := by
  unfold tailWord_1614802
  simp only [CollatzResearch.WordTrace]
  refine ⟨14724166873963903767561665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39264444997237076713497773 14724166873963903767561665)
  ·
    refine ⟨11043125155472927825671249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14724166873963903767561665 11043125155472927825671249)
    ·
      refine ⟨8282343866604695869253437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11043125155472927825671249 8282343866604695869253437)
      ·
        refine ⟨3105878949976760950970039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8282343866604695869253437 3105878949976760950970039)
        ·
          refine ⟨4658818424965141426455059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3105878949976760950970039 4658818424965141426455059)
          ·
            refine ⟨6988227637447712139682589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4658818424965141426455059 6988227637447712139682589)
            ·
              refine ⟨2620585364042892052380971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6988227637447712139682589 2620585364042892052380971)
              ·
                refine ⟨3930878046064338078571457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2620585364042892052380971 3930878046064338078571457)
                ·
                  refine ⟨2948158534548253558928593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3930878046064338078571457 2948158534548253558928593)
                  ·
                    refine ⟨2211118900911190169196445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2948158534548253558928593 2211118900911190169196445)
                    ·
                      refine ⟨829169587841696313448667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2211118900911190169196445 829169587841696313448667)
                      ·
                        rfl

theorem cell23_1614802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_1614802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614802 prefixEnd_1614802 := by exact prefixLift 1614802
  have htrace : WordTrace (prefixWord ++ tailWord_1614802) baseStart_1614802 baseEnd_1614802 := by
    simpa [prefixWord, tailWord_1614802, baseEnd_1614802] using wordTrace_append hprefix tailTrace_1614802
  have hstable : (prefixWord ++ tailWord_1614802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614802).length < 2 ^ (prefixWord ++ tailWord_1614802).sum := by decide
  have hdescent : baseEnd_1614802 < baseStart_1614802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614855 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 2, 6, 2]
def baseStart_1614855 : Nat := 118140960795 + 1614855 * 2 ^ 59
def prefixEnd_1614855 : Nat := 4983230072969 + 3 ^ 40 * 1614855 * 2
def baseEnd_1614855 : Nat := 829196802316384606085923

theorem tailTrace_1614855 : CollatzResearch.WordTrace tailWord_1614855 prefixEnd_1614855 829196802316384606085923 := by
  unfold tailWord_1614855
  simp only [CollatzResearch.WordTrace]
  refine ⟨58898600564663605121926019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39265733709775736747950679 58898600564663605121926019)
  ·
    refine ⟨88347900846995407682889029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58898600564663605121926019 88347900846995407682889029)
    ·
      refine ⟨16565231408811638940541693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88347900846995407682889029 16565231408811638940541693)
      ·
        refine ⟨6211961778304364602703135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16565231408811638940541693 6211961778304364602703135)
        ·
          refine ⟨9317942667456546904054703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6211961778304364602703135 9317942667456546904054703)
          ·
            refine ⟨13976914001184820356082055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9317942667456546904054703 13976914001184820356082055)
            ·
              refine ⟨20965371001777230534123083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13976914001184820356082055 20965371001777230534123083)
              ·
                refine ⟨31448056502665845801184625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20965371001777230534123083 31448056502665845801184625)
                ·
                  refine ⟨23586042376999384350888469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31448056502665845801184625 23586042376999384350888469)
                  ·
                    refine ⟨1105595736421846141447897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23586042376999384350888469 1105595736421846141447897)
                    ·
                      refine ⟨829196802316384606085923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1105595736421846141447897 829196802316384606085923)
                      ·
                        rfl

theorem cell23_1614855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_1614855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614855 prefixEnd_1614855 := by exact prefixLift 1614855
  have htrace : WordTrace (prefixWord ++ tailWord_1614855) baseStart_1614855 baseEnd_1614855 := by
    simpa [prefixWord, tailWord_1614855, baseEnd_1614855] using wordTrace_append hprefix tailTrace_1614855
  have hstable : (prefixWord ++ tailWord_1614855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614855).length < 2 ^ (prefixWord ++ tailWord_1614855).sum := by decide
  have hdescent : baseEnd_1614855 < baseStart_1614855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614898 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6]
def baseStart_1614898 : Nat := 118140960795 + 1614898 * 2 ^ 59
def prefixEnd_1614898 : Nat := 4983230072969 + 3 ^ 40 * 1614898 * 2
def baseEnd_1614898 : Nat := 829218881984527937848225

theorem tailTrace_1614898 : CollatzResearch.WordTrace tailWord_1614898 prefixEnd_1614898 829218881984527937848225 := by
  unfold tailWord_1614898
  simp only [CollatzResearch.WordTrace]
  refine ⟨14725042225876955866435337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39266779269005215643827565 14725042225876955866435337)
  ·
    refine ⟨11043781669407716899826503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14725042225876955866435337 11043781669407716899826503)
    ·
      refine ⟨16565672504111575349739755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11043781669407716899826503 16565672504111575349739755)
      ·
        refine ⟨24848508756167363024609633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16565672504111575349739755 24848508756167363024609633)
        ·
          refine ⟨18636381567125522268457225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24848508756167363024609633 18636381567125522268457225)
          ·
            refine ⟨13977286175344141701342919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18636381567125522268457225 13977286175344141701342919)
            ·
              refine ⟨20965929263016212552014379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13977286175344141701342919 20965929263016212552014379)
              ·
                refine ⟨31448893894524318828021569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20965929263016212552014379 31448893894524318828021569)
                ·
                  refine ⟨23586670420893239121016177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31448893894524318828021569 23586670420893239121016177)
                  ·
                    refine ⟨17690002815669929340762133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23586670420893239121016177 17690002815669929340762133)
                    ·
                      refine ⟨829218881984527937848225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17690002815669929340762133 829218881984527937848225)
                      ·
                        rfl

theorem cell23_1614898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_1614898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614898 prefixEnd_1614898 := by exact prefixLift 1614898
  have htrace : WordTrace (prefixWord ++ tailWord_1614898) baseStart_1614898 baseEnd_1614898 := by
    simpa [prefixWord, tailWord_1614898, baseEnd_1614898] using wordTrace_append hprefix tailTrace_1614898
  have hstable : (prefixWord ++ tailWord_1614898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614898).length < 2 ^ (prefixWord ++ tailWord_1614898).sum := by decide
  have hdescent : baseEnd_1614898 < baseStart_1614898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614909 : List Nat := [1, 4, 1, 3, 1, 4, 1, 2, 1, 2, 3]
def baseStart_1614909 : Nat := 118140960795 + 1614909 * 2 ^ 59
def prefixEnd_1614909 : Nat := 4983230072969 + 3 ^ 40 * 1614909 * 2
def baseEnd_1614909 : Nat := 829224530271727394810675

theorem tailTrace_1614909 : CollatzResearch.WordTrace tailWord_1614909 prefixEnd_1614909 829224530271727394810675 := by
  unfold tailWord_1614909
  simp only [CollatzResearch.WordTrace]
  refine ⟨58900570106467972344391781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39267046737645314896261187 58900570106467972344391781)
  ·
    refine ⟨11043856894962744814573459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58900570106467972344391781 11043856894962744814573459)
    ·
      refine ⟨16565785342444117221860189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11043856894962744814573459 16565785342444117221860189)
      ·
        refine ⟨6212169503416543958197571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16565785342444117221860189 6212169503416543958197571)
        ·
          refine ⟨9318254255124815937296357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6212169503416543958197571 9318254255124815937296357)
          ·
            refine ⟨1747172672835902988243067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9318254255124815937296357 1747172672835902988243067)
            ·
              refine ⟨2620759009253854482364601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1747172672835902988243067 2620759009253854482364601)
              ·
                refine ⟨1965569256940390861773451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2620759009253854482364601 1965569256940390861773451)
                ·
                  refine ⟨2948353885410586292660177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1965569256940390861773451 2948353885410586292660177)
                  ·
                    refine ⟨2211265414057939719495133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2948353885410586292660177 2211265414057939719495133)
                    ·
                      refine ⟨829224530271727394810675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2211265414057939719495133 829224530271727394810675)
                      ·
                        rfl

theorem cell23_1614909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_1614909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614909 prefixEnd_1614909 := by exact prefixLift 1614909
  have htrace : WordTrace (prefixWord ++ tailWord_1614909) baseStart_1614909 baseEnd_1614909 := by
    simpa [prefixWord, tailWord_1614909, baseEnd_1614909] using wordTrace_append hprefix tailTrace_1614909
  have hstable : (prefixWord ++ tailWord_1614909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614909).length < 2 ^ (prefixWord ++ tailWord_1614909).sum := by decide
  have hdescent : baseEnd_1614909 < baseStart_1614909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614928 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 4]
def baseStart_1614928 : Nat := 118140960795 + 1614928 * 2 ^ 59
def prefixEnd_1614928 : Nat := 4983230072969 + 3 ^ 40 * 1614928 * 2
def baseEnd_1614928 : Nat := 829234286404162820473087

theorem tailTrace_1614928 : CollatzResearch.WordTrace tailWord_1614928 prefixEnd_1614928 829234286404162820473087 := by
  unfold tailWord_1614928
  simp only [CollatzResearch.WordTrace]
  refine ⟨29450631546699569294666719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39267508728932759059555625 29450631546699569294666719)
  ·
    refine ⟨44175947320049353942000079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29450631546699569294666719 44175947320049353942000079)
    ·
      refine ⟨66263920980074030913000119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44175947320049353942000079 66263920980074030913000119)
      ·
        refine ⟨99395881470111046369500179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66263920980074030913000119 99395881470111046369500179)
        ·
          refine ⟨149093822205166569554250269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99395881470111046369500179 149093822205166569554250269)
          ·
            refine ⟨55910183326937463582843851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149093822205166569554250269 55910183326937463582843851)
            ·
              refine ⟨83865274990406195374265777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55910183326937463582843851 83865274990406195374265777)
              ·
                refine ⟨62898956242804646530699333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83865274990406195374265777 62898956242804646530699333)
                ·
                  refine ⟨11793554295525871224506125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62898956242804646530699333 11793554295525871224506125)
                  ·
                    refine ⟨4422582860822201709189797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11793554295525871224506125 4422582860822201709189797)
                    ·
                      refine ⟨829234286404162820473087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4422582860822201709189797 829234286404162820473087)
                      ·
                        rfl

theorem cell23_1614928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 4].length) (baseStart_1614928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614928 prefixEnd_1614928 := by exact prefixLift 1614928
  have htrace : WordTrace (prefixWord ++ tailWord_1614928) baseStart_1614928 baseEnd_1614928 := by
    simpa [prefixWord, tailWord_1614928, baseEnd_1614928] using wordTrace_append hprefix tailTrace_1614928
  have hstable : (prefixWord ++ tailWord_1614928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614928).length < 2 ^ (prefixWord ++ tailWord_1614928).sum := by decide
  have hdescent : baseEnd_1614928 < baseStart_1614928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614968 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 9]
def baseStart_1614968 : Nat := 118140960795 + 1614968 * 2 ^ 59
def prefixEnd_1614968 : Nat := 4983230072969 + 3 ^ 40 * 1614968 * 2
def baseEnd_1614968 : Nat := 92139425070038073774767

theorem tailTrace_1614968 : CollatzResearch.WordTrace tailWord_1614968 prefixEnd_1614968 92139425070038073774767 := by
  unfold tailWord_1614968
  simp only [CollatzResearch.WordTrace]
  refine ⟨29451361006627112710394779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39268481342169483613859705 29451361006627112710394779)
  ·
    refine ⟨44177041509940669065592169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29451361006627112710394779 44177041509940669065592169)
    ·
      refine ⟨33132781132455501799194127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44177041509940669065592169 33132781132455501799194127)
      ·
        refine ⟨49699171698683252698791191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33132781132455501799194127 49699171698683252698791191)
        ·
          refine ⟨74548757548024879048186787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49699171698683252698791191 74548757548024879048186787)
          ·
            refine ⟨111823136322037318572280181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74548757548024879048186787 111823136322037318572280181)
            ·
              refine ⟨10483419030190998616151267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111823136322037318572280181 10483419030190998616151267)
              ·
                refine ⟨15725128545286497924226901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10483419030190998616151267 15725128545286497924226901)
                ·
                  refine ⟨92139425070038073774767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15725128545286497924226901 92139425070038073774767)
                  ·
                    rfl

theorem cell23_1614968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 9].length) (baseStart_1614968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614968 prefixEnd_1614968 := by exact prefixLift 1614968
  have htrace : WordTrace (prefixWord ++ tailWord_1614968) baseStart_1614968 baseEnd_1614968 := by
    simpa [prefixWord, tailWord_1614968, baseEnd_1614968] using wordTrace_append hprefix tailTrace_1614968
  have hstable : (prefixWord ++ tailWord_1614968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614968).length < 2 ^ (prefixWord ++ tailWord_1614968).sum := by decide
  have hdescent : baseEnd_1614968 < baseStart_1614968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1614995 : List Nat := [1, 1, 1, 2, 1, 2, 5, 2, 2, 3, 3]
def baseStart_1614995 : Nat := 118140960795 + 1614995 * 2 ^ 59
def prefixEnd_1614995 : Nat := 4983230072969 + 3 ^ 40 * 1614995 * 2
def baseEnd_1614995 : Nat := 829268689608014058335279

theorem tailTrace_1614995 : CollatzResearch.WordTrace tailWord_1614995 prefixEnd_1614995 829268689608014058335279 := by
  unfold tailWord_1614995
  simp only [CollatzResearch.WordTrace]
  refine ⟨58903706784156409032022439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39269137856104272688014959 58903706784156409032022439)
  ·
    refine ⟨88355560176234613548033659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58903706784156409032022439 88355560176234613548033659)
    ·
      refine ⟨132533340264351920322050489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88355560176234613548033659 132533340264351920322050489)
      ·
        refine ⟨99400005198263940241537867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132533340264351920322050489 99400005198263940241537867)
        ·
          refine ⟨149100007797395910362306801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99400005198263940241537867 149100007797395910362306801)
          ·
            refine ⟨111825005848046932771730101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149100007797395910362306801 111825005848046932771730101)
            ·
              refine ⟨10483594298254399947349697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111825005848046932771730101 10483594298254399947349697)
              ·
                refine ⟨7862695723690799960512273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10483594298254399947349697 7862695723690799960512273)
                ·
                  refine ⟨5897021792768099970384205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7862695723690799960512273 5897021792768099970384205)
                  ·
                    refine ⟨2211383172288037488894077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5897021792768099970384205 2211383172288037488894077)
                    ·
                      refine ⟨829268689608014058335279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2211383172288037488894077 829268689608014058335279)
                      ·
                        rfl

theorem cell23_1614995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3, 3].length) (baseStart_1614995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1614995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1614995 prefixEnd_1614995 := by exact prefixLift 1614995
  have htrace : WordTrace (prefixWord ++ tailWord_1614995) baseStart_1614995 baseEnd_1614995 := by
    simpa [prefixWord, tailWord_1614995, baseEnd_1614995] using wordTrace_append hprefix tailTrace_1614995
  have hstable : (prefixWord ++ tailWord_1614995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1614995).length < 2 ^ (prefixWord ++ tailWord_1614995).sum := by decide
  have hdescent : baseEnd_1614995 < baseStart_1614995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1614995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615002 : List Nat := [3, 1, 1, 5, 1, 2, 2, 1, 7]
def baseStart_1615002 : Nat := 118140960795 + 1615002 * 2 ^ 59
def prefixEnd_1615002 : Nat := 4983230072969 + 3 ^ 40 * 1615002 * 2
def baseEnd_1615002 : Nat := 92141364885843947883083

theorem tailTrace_1615002 : CollatzResearch.WordTrace tailWord_1615002 prefixEnd_1615002 92141364885843947883083 := by
  unfold tailWord_1615002
  simp only [CollatzResearch.WordTrace]
  refine ⟨14725990523782762306881815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39269308063420699485018173 14725990523782762306881815)
  ·
    refine ⟨22088985785674143460322723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14725990523782762306881815 22088985785674143460322723)
    ·
      refine ⟨33133478678511215190484085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22088985785674143460322723 33133478678511215190484085)
      ·
        refine ⟨3106263626110426424107883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33133478678511215190484085 3106263626110426424107883)
        ·
          refine ⟨4659395439165639636161825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3106263626110426424107883 4659395439165639636161825)
          ·
            refine ⟨3494546579374229727121369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4659395439165639636161825 3494546579374229727121369)
            ·
              refine ⟨2620909934530672295341027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3494546579374229727121369 2620909934530672295341027)
              ·
                refine ⟨3931364901796008443011541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2620909934530672295341027 3931364901796008443011541)
                ·
                  refine ⟨92141364885843947883083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3931364901796008443011541 92141364885843947883083)
                  ·
                    rfl

theorem cell23_1615002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 7].length) (baseStart_1615002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615002 prefixEnd_1615002 := by exact prefixLift 1615002
  have htrace : WordTrace (prefixWord ++ tailWord_1615002) baseStart_1615002 baseEnd_1615002 := by
    simpa [prefixWord, tailWord_1615002, baseEnd_1615002] using wordTrace_append hprefix tailTrace_1615002
  have hstable : (prefixWord ++ tailWord_1615002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615002).length < 2 ^ (prefixWord ++ tailWord_1615002).sum := by decide
  have hdescent : baseEnd_1615002 < baseStart_1615002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615012 : List Nat := [2, 3, 1, 2, 3, 1, 2, 1, 2, 3, 3]
def baseStart_1615012 : Nat := 118140960795 + 1615012 * 2 ^ 59
def prefixEnd_1615012 : Nat := 4983230072969 + 3 ^ 40 * 1615012 * 2
def baseEnd_1615012 : Nat := 829277418779140491822701

theorem tailTrace_1615012 : CollatzResearch.WordTrace tailWord_1615012 prefixEnd_1615012 829277418779140491822701 := by
  unfold tailWord_1615012
  simp only [CollatzResearch.WordTrace]
  refine ⟨29452163412547410467695645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39269551216729880623594193 29452163412547410467695645)
  ·
    refine ⟨11044561279705278925385867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29452163412547410467695645 11044561279705278925385867)
    ·
      refine ⟨16566841919557918388078801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11044561279705278925385867 16566841919557918388078801)
      ·
        refine ⟨12425131439668438791059101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16566841919557918388078801 12425131439668438791059101)
        ·
          refine ⟨4659424289875664546647163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12425131439668438791059101 4659424289875664546647163)
          ·
            refine ⟨6989136434813496819970745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4659424289875664546647163 6989136434813496819970745)
            ·
              refine ⟨5241852326110122614978059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6989136434813496819970745 5241852326110122614978059)
              ·
                refine ⟨7862778489165183922467089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5241852326110122614978059 7862778489165183922467089)
                ·
                  refine ⟨5897083866873887941850317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7862778489165183922467089 5897083866873887941850317)
                  ·
                    refine ⟨2211406450077707978193869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5897083866873887941850317 2211406450077707978193869)
                    ·
                      refine ⟨829277418779140491822701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2211406450077707978193869 829277418779140491822701)
                      ·
                        rfl

theorem cell23_1615012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_1615012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615012 prefixEnd_1615012 := by exact prefixLift 1615012
  have htrace : WordTrace (prefixWord ++ tailWord_1615012) baseStart_1615012 baseEnd_1615012 := by
    simpa [prefixWord, tailWord_1615012, baseEnd_1615012] using wordTrace_append hprefix tailTrace_1615012
  have hstable : (prefixWord ++ tailWord_1615012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615012).length < 2 ^ (prefixWord ++ tailWord_1615012).sum := by decide
  have hdescent : baseEnd_1615012 < baseStart_1615012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615053 : List Nat := [1, 6, 2, 2, 2, 1, 1, 1, 7]
def baseStart_1615053 : Nat := 118140960795 + 1615053 * 2 ^ 59
def prefixEnd_1615053 : Nat := 4983230072969 + 3 ^ 40 * 1615053 * 2
def baseEnd_1615053 : Nat := 92144274609552759045557

theorem tailTrace_1615053 : CollatzResearch.WordTrace tailWord_1615053 prefixEnd_1615053 92144274609552759045557 := by
  unfold tailWord_1615053
  simp only [CollatzResearch.WordTrace]
  refine ⟨58905822217946284937633813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39270548145297523291755875 58905822217946284937633813)
  ·
    refine ⟨2761210416466232106451585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58905822217946284937633813 2761210416466232106451585)
    ·
      refine ⟨2070907812349674079838689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2761210416466232106451585 2070907812349674079838689)
      ·
        refine ⟨1553180859262255559879017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2070907812349674079838689 1553180859262255559879017)
        ·
          refine ⟨1164885644446691669909263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1553180859262255559879017 1164885644446691669909263)
          ·
            refine ⟨1747328466670037504863895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1164885644446691669909263 1747328466670037504863895)
            ·
              refine ⟨2620992700005056257295843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1747328466670037504863895 2620992700005056257295843)
              ·
                refine ⟨3931489050007584385943765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2620992700005056257295843 3931489050007584385943765)
                ·
                  refine ⟨92144274609552759045557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3931489050007584385943765 92144274609552759045557)
                  ·
                    rfl

theorem cell23_1615053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_1615053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615053 prefixEnd_1615053 := by exact prefixLift 1615053
  have htrace : WordTrace (prefixWord ++ tailWord_1615053) baseStart_1615053 baseEnd_1615053 := by
    simpa [prefixWord, tailWord_1615053, baseEnd_1615053] using wordTrace_append hprefix tailTrace_1615053
  have hstable : (prefixWord ++ tailWord_1615053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615053).length < 2 ^ (prefixWord ++ tailWord_1615053).sum := by decide
  have hdescent : baseEnd_1615053 < baseStart_1615053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615055 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 3, 4, 3]
def baseStart_1615055 : Nat := 118140960795 + 1615055 * 2 ^ 59
def prefixEnd_1615055 : Nat := 4983230072969 + 3 ^ 40 * 1615055 * 2
def baseEnd_1615055 : Nat := 829299498447283823585003

theorem tailTrace_1615055 : CollatzResearch.WordTrace tailWord_1615055 prefixEnd_1615055 829299498447283823585003 := by
  unfold tailWord_1615055
  simp only [CollatzResearch.WordTrace]
  refine ⟨58905895163939039279206619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39270596775959359519471079 58905895163939039279206619)
  ·
    refine ⟨88358842745908558918809929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58905895163939039279206619 88358842745908558918809929)
    ·
      refine ⟨66269132059431419189107447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88358842745908558918809929 66269132059431419189107447)
      ·
        refine ⟨99403698089147128783661171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66269132059431419189107447 99403698089147128783661171)
        ·
          refine ⟨149105547133720693175491757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99403698089147128783661171 149105547133720693175491757)
          ·
            refine ⟨55914580175145259940809409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149105547133720693175491757 55914580175145259940809409)
            ·
              refine ⟨41935935131358944955607057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55914580175145259940809409 41935935131358944955607057)
              ·
                refine ⟨31451951348519208716705293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41935935131358944955607057 31451951348519208716705293)
                ·
                  refine ⟨11794481755694703268764485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31451951348519208716705293 11794481755694703268764485)
                  ·
                    refine ⟨2211465329192756862893341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11794481755694703268764485 2211465329192756862893341)
                    ·
                      refine ⟨829299498447283823585003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2211465329192756862893341 829299498447283823585003)
                      ·
                        rfl

theorem cell23_1615055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 4, 3].length) (baseStart_1615055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615055 prefixEnd_1615055 := by exact prefixLift 1615055
  have htrace : WordTrace (prefixWord ++ tailWord_1615055) baseStart_1615055 baseEnd_1615055 := by
    simpa [prefixWord, tailWord_1615055, baseEnd_1615055] using wordTrace_append hprefix tailTrace_1615055
  have hstable : (prefixWord ++ tailWord_1615055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615055).length < 2 ^ (prefixWord ++ tailWord_1615055).sum := by decide
  have hdescent : baseEnd_1615055 < baseStart_1615055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615136 : List Nat := [2, 1, 1, 5, 3, 1, 1, 2, 3, 1, 3]
def baseStart_1615136 : Nat := 118140960795 + 1615136 * 2 ^ 59
def prefixEnd_1615136 : Nat := 4983230072969 + 3 ^ 40 * 1615136 * 2
def baseEnd_1615136 : Nat := 829341090380298006672131

theorem tailTrace_1615136 : CollatzResearch.WordTrace tailWord_1615136 prefixEnd_1615136 829341090380298006672131 := by
  unfold tailWord_1615136
  simp only [CollatzResearch.WordTrace]
  refine ⟨29454424738322795056452631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39272566317763726741936841 29454424738322795056452631)
  ·
    refine ⟨44181637107484192584678947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29454424738322795056452631 44181637107484192584678947)
    ·
      refine ⟨66272455661226288877018421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44181637107484192584678947 66272455661226288877018421)
      ·
        refine ⟨6213042718239964582220477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66272455661226288877018421 6213042718239964582220477)
        ·
          refine ⟨2329891019339986718332679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6213042718239964582220477 2329891019339986718332679)
          ·
            refine ⟨3494836529009980077499019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2329891019339986718332679 3494836529009980077499019)
            ·
              refine ⟨5242254793514970116248529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3494836529009980077499019 5242254793514970116248529)
              ·
                refine ⟨3931691095136227587186397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5242254793514970116248529 3931691095136227587186397)
                ·
                  refine ⟨1474384160676085345194899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3931691095136227587186397 1474384160676085345194899)
                  ·
                    refine ⟨2211576241014128017792349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1474384160676085345194899 2211576241014128017792349)
                    ·
                      refine ⟨829341090380298006672131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2211576241014128017792349 829341090380298006672131)
                      ·
                        rfl

theorem cell23_1615136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_1615136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615136 prefixEnd_1615136 := by exact prefixLift 1615136
  have htrace : WordTrace (prefixWord ++ tailWord_1615136) baseStart_1615136 baseEnd_1615136 := by
    simpa [prefixWord, tailWord_1615136, baseEnd_1615136] using wordTrace_append hprefix tailTrace_1615136
  have hstable : (prefixWord ++ tailWord_1615136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615136).length < 2 ^ (prefixWord ++ tailWord_1615136).sum := by decide
  have hdescent : baseEnd_1615136 < baseStart_1615136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615146 : List Nat := [3, 1, 4, 2, 1, 2, 1, 1, 1, 5, 2]
def baseStart_1615146 : Nat := 118140960795 + 1615146 * 2 ^ 59
def prefixEnd_1615146 : Nat := 4983230072969 + 3 ^ 40 * 1615146 * 2
def baseEnd_1615146 : Nat := 829346225186842967547085

theorem tailTrace_1615146 : CollatzResearch.WordTrace tailWord_1615146 prefixEnd_1615146 829346225186842967547085 := by
  unfold tailWord_1615146
  simp only [CollatzResearch.WordTrace]
  refine ⟨14727303551652340455192323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39272809471072907880512861 14727303551652340455192323)
  ·
    refine ⟨22090955327478510682788485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14727303551652340455192323 22090955327478510682788485)
    ·
      refine ⟨4142054123902220753022841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22090955327478510682788485 4142054123902220753022841)
      ·
        refine ⟨3106540592926665564767131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4142054123902220753022841 3106540592926665564767131)
        ·
          refine ⟨4659810889389998347150697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3106540592926665564767131 4659810889389998347150697)
          ·
            refine ⟨3494858167042498760363023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4659810889389998347150697 3494858167042498760363023)
            ·
              refine ⟨5242287250563748140544535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3494858167042498760363023 5242287250563748140544535)
              ·
                refine ⟨7863430875845622210816803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5242287250563748140544535 7863430875845622210816803)
                ·
                  refine ⟨11795146313768433316225205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7863430875845622210816803 11795146313768433316225205)
                  ·
                    refine ⟨1105794966915790623396113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11795146313768433316225205 1105794966915790623396113)
                    ·
                      refine ⟨829346225186842967547085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1105794966915790623396113 829346225186842967547085)
                      ·
                        rfl

theorem cell23_1615146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_1615146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615146 prefixEnd_1615146 := by exact prefixLift 1615146
  have htrace : WordTrace (prefixWord ++ tailWord_1615146) baseStart_1615146 baseEnd_1615146 := by
    simpa [prefixWord, tailWord_1615146, baseEnd_1615146] using wordTrace_append hprefix tailTrace_1615146
  have hstable : (prefixWord ++ tailWord_1615146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615146).length < 2 ^ (prefixWord ++ tailWord_1615146).sum := by decide
  have hdescent : baseEnd_1615146 < baseStart_1615146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615152 : List Nat := [2, 1, 1, 1, 2, 2, 4, 2, 4, 4]
def baseStart_1615152 : Nat := 118140960795 + 1615152 * 2 ^ 59
def prefixEnd_1615152 : Nat := 4983230072969 + 3 ^ 40 * 1615152 * 2
def baseEnd_1615152 : Nat := 276449768690256648024019

theorem tailTrace_1615152 : CollatzResearch.WordTrace tailWord_1615152 prefixEnd_1615152 276449768690256648024019 := by
  unfold tailWord_1615152
  simp only [CollatzResearch.WordTrace]
  refine ⟨29454716522293812422743855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39272955363058416563658473 29454716522293812422743855)
  ·
    refine ⟨44182074783440718634115783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29454716522293812422743855 44182074783440718634115783)
    ·
      refine ⟨66273112175161077951173675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44182074783440718634115783 66273112175161077951173675)
      ·
        refine ⟨99409668262741616926760513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66273112175161077951173675 99409668262741616926760513)
        ·
          refine ⟨74557251197056212695070385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99409668262741616926760513 74557251197056212695070385)
          ·
            refine ⟨55917938397792159521302789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74557251197056212695070385 55917938397792159521302789)
            ·
              refine ⟨10484613449586029910244273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55917938397792159521302789 10484613449586029910244273)
              ·
                refine ⟨7863460087189522432683205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10484613449586029910244273 7863460087189522432683205)
                ·
                  refine ⟨1474398766348035456128101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7863460087189522432683205 1474398766348035456128101)
                  ·
                    refine ⟨276449768690256648024019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1474398766348035456128101 276449768690256648024019)
                    ·
                      rfl

theorem cell23_1615152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 4, 4].length) (baseStart_1615152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615152 prefixEnd_1615152 := by exact prefixLift 1615152
  have htrace : WordTrace (prefixWord ++ tailWord_1615152) baseStart_1615152 baseEnd_1615152 := by
    simpa [prefixWord, tailWord_1615152, baseEnd_1615152] using wordTrace_append hprefix tailTrace_1615152
  have hstable : (prefixWord ++ tailWord_1615152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615152).length < 2 ^ (prefixWord ++ tailWord_1615152).sum := by decide
  have hdescent : baseEnd_1615152 < baseStart_1615152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615153 : List Nat := [1, 2, 2, 3, 3, 2, 2, 3, 1, 1, 3]
def baseStart_1615153 : Nat := 118140960795 + 1615153 * 2 ^ 59
def prefixEnd_1615153 : Nat := 4983230072969 + 3 ^ 40 * 1615153 * 2
def baseEnd_1615153 : Nat := 829349819551424440159553

theorem tailTrace_1615153 : CollatzResearch.WordTrace tailWord_1615153 prefixEnd_1615153 829349819551424440159553 := by
  unfold tailWord_1615153
  simp only [CollatzResearch.WordTrace]
  refine ⟨58909469517584002016274113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39272979678389334677516075 58909469517584002016274113)
  ·
    refine ⟨44182102138188001512205585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58909469517584002016274113 44182102138188001512205585)
    ·
      refine ⟨33136576603641001134154189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44182102138188001512205585 33136576603641001134154189)
      ·
        refine ⟨12426216226365375425307821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33136576603641001134154189 12426216226365375425307821)
        ·
          refine ⟨4659831084887015784490433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12426216226365375425307821 4659831084887015784490433)
          ·
            refine ⟨3494873313665261838367825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4659831084887015784490433 3494873313665261838367825)
            ·
              refine ⟨2621154985248946378775869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3494873313665261838367825 2621154985248946378775869)
              ·
                refine ⟨982933119468354892040951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2621154985248946378775869 982933119468354892040951)
                ·
                  refine ⟨1474399679202532338061427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 982933119468354892040951 1474399679202532338061427)
                  ·
                    refine ⟨2211599518803798507092141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1474399679202532338061427 2211599518803798507092141)
                    ·
                      refine ⟨829349819551424440159553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2211599518803798507092141 829349819551424440159553)
                      ·
                        rfl

theorem cell23_1615153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_1615153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615153 prefixEnd_1615153 := by exact prefixLift 1615153
  have htrace : WordTrace (prefixWord ++ tailWord_1615153) baseStart_1615153 baseEnd_1615153 := by
    simpa [prefixWord, tailWord_1615153, baseEnd_1615153] using wordTrace_append hprefix tailTrace_1615153
  have hstable : (prefixWord ++ tailWord_1615153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615153).length < 2 ^ (prefixWord ++ tailWord_1615153).sum := by decide
  have hdescent : baseEnd_1615153 < baseStart_1615153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615162 : List Nat := [3, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5]
def baseStart_1615162 : Nat := 118140960795 + 1615162 * 2 ^ 59
def prefixEnd_1615162 : Nat := 4983230072969 + 3 ^ 40 * 1615162 * 2
def baseEnd_1615162 : Nat := 829354440877314904947011

theorem tailTrace_1615162 : CollatzResearch.WordTrace tailWord_1615162 prefixEnd_1615162 829354440877314904947011 := by
  unfold tailWord_1615162
  simp only [CollatzResearch.WordTrace]
  refine ⟨14727449443637849138337935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39273198516367597702234493 14727449443637849138337935)
  ·
    refine ⟨22091174165456773707506903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14727449443637849138337935 22091174165456773707506903)
    ·
      refine ⟨33136761248185160561260355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22091174165456773707506903 33136761248185160561260355)
      ·
        refine ⟨49705141872277740841890533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33136761248185160561260355 49705141872277740841890533)
        ·
          refine ⟨9319714101052076407854475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49705141872277740841890533 9319714101052076407854475)
          ·
            refine ⟨13979571151578114611781713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9319714101052076407854475 13979571151578114611781713)
            ·
              refine ⟨10484678363683585958836285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13979571151578114611781713 10484678363683585958836285)
              ·
                refine ⟨3931754386381344734563607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10484678363683585958836285 3931754386381344734563607)
                ·
                  refine ⟨5897631579572017101845411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3931754386381344734563607 5897631579572017101845411)
                  ·
                    refine ⟨8846447369358025652768117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5897631579572017101845411 8846447369358025652768117)
                    ·
                      refine ⟨829354440877314904947011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8846447369358025652768117 829354440877314904947011)
                      ·
                        rfl

theorem cell23_1615162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_1615162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615162 prefixEnd_1615162 := by exact prefixLift 1615162
  have htrace : WordTrace (prefixWord ++ tailWord_1615162) baseStart_1615162 baseEnd_1615162 := by
    simpa [prefixWord, tailWord_1615162, baseEnd_1615162] using wordTrace_append hprefix tailTrace_1615162
  have hstable : (prefixWord ++ tailWord_1615162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615162).length < 2 ^ (prefixWord ++ tailWord_1615162).sum := by decide
  have hdescent : baseEnd_1615162 < baseStart_1615162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615189 : List Nat := [1, 3, 2, 2, 3, 1, 3, 1, 1, 2, 4]
def baseStart_1615189 : Nat := 118140960795 + 1615189 * 2 ^ 59
def prefixEnd_1615189 : Nat := 4983230072969 + 3 ^ 40 * 1615189 * 2
def baseEnd_1615189 : Nat := 829368304854986299309387

theorem tailTrace_1615189 : CollatzResearch.WordTrace tailWord_1615189 prefixEnd_1615189 829368304854986299309387 := by
  unfold tailWord_1615189
  simp only [CollatzResearch.WordTrace]
  refine ⟨58910782545453580164584621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39273855030302386776389747 58910782545453580164584621)
  ·
    refine ⟨22091543454545092561719233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58910782545453580164584621 22091543454545092561719233)
    ·
      refine ⟨16568657590908819421289425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22091543454545092561719233 16568657590908819421289425)
      ·
        refine ⟨12426493193181614565967069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16568657590908819421289425 12426493193181614565967069)
        ·
          refine ⟨4659934947443105462237651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12426493193181614565967069 4659934947443105462237651)
          ·
            refine ⟨6989902421164658193356477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4659934947443105462237651 6989902421164658193356477)
            ·
              refine ⟨2621213407936746822508679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6989902421164658193356477 2621213407936746822508679)
              ·
                refine ⟨3931820111905120233763019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2621213407936746822508679 3931820111905120233763019)
                ·
                  refine ⟨5897730167857680350644529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3931820111905120233763019 5897730167857680350644529)
                  ·
                    refine ⟨4423297625893260262983397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5897730167857680350644529 4423297625893260262983397)
                    ·
                      refine ⟨829368304854986299309387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4423297625893260262983397 829368304854986299309387)
                      ·
                        rfl

theorem cell23_1615189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_1615189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615189 prefixEnd_1615189 := by exact prefixLift 1615189
  have htrace : WordTrace (prefixWord ++ tailWord_1615189) baseStart_1615189 baseEnd_1615189 := by
    simpa [prefixWord, tailWord_1615189, baseEnd_1615189] using wordTrace_append hprefix tailTrace_1615189
  have hstable : (prefixWord ++ tailWord_1615189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615189).length < 2 ^ (prefixWord ++ tailWord_1615189).sum := by decide
  have hdescent : baseEnd_1615189 < baseStart_1615189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615266 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 3, 4, 2]
def baseStart_1615266 : Nat := 118140960795 + 1615266 * 2 ^ 59
def prefixEnd_1615266 : Nat := 4983230072969 + 3 ^ 40 * 1615266 * 2
def baseEnd_1615266 : Nat := 829407842865382498046533

theorem tailTrace_1615266 : CollatzResearch.WordTrace tailWord_1615266 prefixEnd_1615266 829407842865382498046533 := by
  unfold tailWord_1615266
  simp only [CollatzResearch.WordTrace]
  refine ⟨14728397741543655578784413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39275727310783081543425101 14728397741543655578784413)
  ·
    refine ⟨5523149153078870842044155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14728397741543655578784413 5523149153078870842044155)
    ·
      refine ⟨8284723729618306263066233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5523149153078870842044155 8284723729618306263066233)
      ·
        refine ⟨6213542797213729697299675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8284723729618306263066233 6213542797213729697299675)
        ·
          refine ⟨9320314195820594545949513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6213542797213729697299675 9320314195820594545949513)
          ·
            refine ⟨6990235646865445909462135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9320314195820594545949513 6990235646865445909462135)
            ·
              refine ⟨10485353470298168864193203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6990235646865445909462135 10485353470298168864193203)
              ·
                refine ⟨15728030205447253296289805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10485353470298168864193203 15728030205447253296289805)
                ·
                  refine ⟨5898011327042719986108677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15728030205447253296289805 5898011327042719986108677)
                  ·
                    refine ⟨1105877123820509997395377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5898011327042719986108677 1105877123820509997395377)
                    ·
                      refine ⟨829407842865382498046533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1105877123820509997395377 829407842865382498046533)
                      ·
                        rfl

theorem cell23_1615266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_1615266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1615266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1615266 prefixEnd_1615266 := by exact prefixLift 1615266
  have htrace : WordTrace (prefixWord ++ tailWord_1615266) baseStart_1615266 baseEnd_1615266 := by
    simpa [prefixWord, tailWord_1615266, baseEnd_1615266] using wordTrace_append hprefix tailTrace_1615266
  have hstable : (prefixWord ++ tailWord_1615266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615266).length < 2 ^ (prefixWord ++ tailWord_1615266).sum := by decide
  have hdescent : baseEnd_1615266 < baseStart_1615266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
