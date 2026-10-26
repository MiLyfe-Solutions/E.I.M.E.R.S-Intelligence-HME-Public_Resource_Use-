import V185TrunkScan23Chunk1000

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5927685 : List Nat := [1, 3, 1, 1, 2, 1, 1, 6, 3, 2, 2]
def baseStart_5927685 : Nat := 118140960795 + 5927685 * 2 ^ 59
def prefixEnd_5927685 : Nat := 4983230072969 + 3 ^ 40 * 5927685 * 2
def baseEnd_5927685 : Nat := 3043751573446745638876579

theorem tailTrace_5927685 : CollatzResearch.WordTrace tailWord_5927685 prefixEnd_5927685 3043751573446745638876579 := by
  unfold tailWord_5927685
  simp only [CollatzResearch.WordTrace]
  refine ⟨216200433530017087844376509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144133622353344725229584339 216200433530017087844376509)
  ·
    refine ⟨81075162573756407941641191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216200433530017087844376509 81075162573756407941641191)
    ·
      refine ⟨121612743860634611912461787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81075162573756407941641191 121612743860634611912461787)
      ·
        refine ⟨182419115790951917868692681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121612743860634611912461787 182419115790951917868692681)
        ·
          refine ⟨136814336843213938401519511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182419115790951917868692681 136814336843213938401519511)
          ·
            refine ⟨205221505264820907602279267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136814336843213938401519511 205221505264820907602279267)
            ·
              refine ⟨307832257897231361403418901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205221505264820907602279267 307832257897231361403418901)
              ·
                refine ⟨14429637088932720065785261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 307832257897231361403418901 14429637088932720065785261)
                ·
                  refine ⟨5411113908349770024669473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14429637088932720065785261 5411113908349770024669473)
                  ·
                    refine ⟨4058335431262327518502105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5411113908349770024669473 4058335431262327518502105)
                    ·
                      refine ⟨3043751573446745638876579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4058335431262327518502105 3043751573446745638876579)
                      ·
                        rfl

theorem cell23_5927685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 3, 2, 2].length) (baseStart_5927685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927685 prefixEnd_5927685 := by exact prefixLift 5927685
  have htrace : WordTrace (prefixWord ++ tailWord_5927685) baseStart_5927685 baseEnd_5927685 := by
    simpa [prefixWord, tailWord_5927685, baseEnd_5927685] using wordTrace_append hprefix tailTrace_5927685
  have hstable : (prefixWord ++ tailWord_5927685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927685).length < 2 ^ (prefixWord ++ tailWord_5927685).sum := by decide
  have hdescent : baseEnd_5927685 < baseStart_5927685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927732 : List Nat := [2, 5, 1, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_5927732 : Nat := 118140960795 + 5927732 * 2 ^ 59
def prefixEnd_5927732 : Nat := 4983230072969 + 3 ^ 40 * 5927732 * 2
def baseEnd_5927732 : Nat := 3043775707037506954988863

theorem tailTrace_5927732 : CollatzResearch.WordTrace tailWord_5927732 prefixEnd_5927732 3043775707037506954988863 := by
  unfold tailWord_5927732
  simp only [CollatzResearch.WordTrace]
  refine ⟨108101073880423407435668725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144134765173897876580891633 108101073880423407435668725)
  ·
    refine ⟨10134475676289694447093943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108101073880423407435668725 10134475676289694447093943)
    ·
      refine ⟨15201713514434541670640915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10134475676289694447093943 15201713514434541670640915)
      ·
        refine ⟨22802570271651812505961373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15201713514434541670640915 22802570271651812505961373)
        ·
          refine ⟨8550963851869429689735515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22802570271651812505961373 8550963851869429689735515)
          ·
            refine ⟨12826445777804144534603273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8550963851869429689735515 12826445777804144534603273)
            ·
              refine ⟨9619834333353108400952455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12826445777804144534603273 9619834333353108400952455)
              ·
                refine ⟨14429751500029662601428683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9619834333353108400952455 14429751500029662601428683)
                ·
                  refine ⟨21644627250044493902143025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14429751500029662601428683 21644627250044493902143025)
                  ·
                    refine ⟨16233470437533370426607269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21644627250044493902143025 16233470437533370426607269)
                    ·
                      refine ⟨3043775707037506954988863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16233470437533370426607269 3043775707037506954988863)
                      ·
                        rfl

theorem cell23_5927732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_5927732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927732 prefixEnd_5927732 := by exact prefixLift 5927732
  have htrace : WordTrace (prefixWord ++ tailWord_5927732) baseStart_5927732 baseEnd_5927732 := by
    simpa [prefixWord, tailWord_5927732, baseEnd_5927732] using wordTrace_append hprefix tailTrace_5927732
  have hstable : (prefixWord ++ tailWord_5927732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927732).length < 2 ^ (prefixWord ++ tailWord_5927732).sum := by decide
  have hdescent : baseEnd_5927732 < baseStart_5927732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927735 : List Nat := [1, 1, 3, 1, 2, 1, 3, 5, 2, 1, 3]
def baseStart_5927735 : Nat := 118140960795 + 5927735 * 2 ^ 59
def prefixEnd_5927735 : Nat := 4983230072969 + 3 ^ 40 * 5927735 * 2
def baseEnd_5927735 : Nat := 3043777247479470443251349

theorem tailTrace_5927735 : CollatzResearch.WordTrace tailWord_5927735 prefixEnd_5927735 3043777247479470443251349 := by
  unfold tailWord_5927735
  simp only [CollatzResearch.WordTrace]
  refine ⟨216202257179835946383696659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144134838119890630922464439 216202257179835946383696659)
  ·
    refine ⟨324303385769753919575544989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216202257179835946383696659 324303385769753919575544989)
    ·
      refine ⟨121613769663657719840829371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324303385769753919575544989 121613769663657719840829371)
      ·
        refine ⟨182420654495486579761244057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121613769663657719840829371 182420654495486579761244057)
        ·
          refine ⟨136815490871614934820933043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182420654495486579761244057 136815490871614934820933043)
          ·
            refine ⟨205223236307422402231399565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136815490871614934820933043 205223236307422402231399565)
            ·
              refine ⟨76958713615283400836774837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 205223236307422402231399565 76958713615283400836774837)
              ·
                refine ⟨7214879401432818828447641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76958713615283400836774837 7214879401432818828447641)
                ·
                  refine ⟨5411159551074614121335731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7214879401432818828447641 5411159551074614121335731)
                  ·
                    refine ⟨8116739326611921182003597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5411159551074614121335731 8116739326611921182003597)
                    ·
                      refine ⟨3043777247479470443251349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8116739326611921182003597 3043777247479470443251349)
                      ·
                        rfl

theorem cell23_5927735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2, 1, 3].length) (baseStart_5927735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927735 prefixEnd_5927735 := by exact prefixLift 5927735
  have htrace : WordTrace (prefixWord ++ tailWord_5927735) baseStart_5927735 baseEnd_5927735 := by
    simpa [prefixWord, tailWord_5927735, baseEnd_5927735] using wordTrace_append hprefix tailTrace_5927735
  have hstable : (prefixWord ++ tailWord_5927735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927735).length < 2 ^ (prefixWord ++ tailWord_5927735).sum := by decide
  have hdescent : baseEnd_5927735 < baseStart_5927735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927751 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 3, 8]
def baseStart_5927751 : Nat := 118140960795 + 5927751 * 2 ^ 59
def prefixEnd_5927751 : Nat := 4983230072969 + 3 ^ 40 * 5927751 * 2
def baseEnd_5927751 : Nat := 1014595154389980793550425

theorem tailTrace_5927751 : CollatzResearch.WordTrace tailWord_5927751 prefixEnd_5927751 1014595154389980793550425 := by
  unfold tailWord_5927751
  simp only [CollatzResearch.WordTrace]
  refine ⟨216202840747777981116279107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144135227165185320744186071 216202840747777981116279107)
  ·
    refine ⟨324304261121666971674418661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216202840747777981116279107 324304261121666971674418661)
    ·
      refine ⟨60807048960312557188953499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 324304261121666971674418661 60807048960312557188953499)
      ·
        refine ⟨91210573440468835783430249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60807048960312557188953499 91210573440468835783430249)
        ·
          refine ⟨68407930080351626837572687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91210573440468835783430249 68407930080351626837572687)
          ·
            refine ⟨102611895120527440256359031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68407930080351626837572687 102611895120527440256359031)
            ·
              refine ⟨153917842680791160384538547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102611895120527440256359031 153917842680791160384538547)
              ·
                refine ⟨230876764021186740576807821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153917842680791160384538547 230876764021186740576807821)
                ·
                  refine ⟨86578786507945027716302933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 230876764021186740576807821 86578786507945027716302933)
                  ·
                    refine ⟨1014595154389980793550425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86578786507945027716302933 1014595154389980793550425)
                    ·
                      rfl

theorem cell23_5927751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_5927751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927751 prefixEnd_5927751 := by exact prefixLift 5927751
  have htrace : WordTrace (prefixWord ++ tailWord_5927751) baseStart_5927751 baseEnd_5927751 := by
    simpa [prefixWord, tailWord_5927751, baseEnd_5927751] using wordTrace_append hprefix tailTrace_5927751
  have hstable : (prefixWord ++ tailWord_5927751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927751).length < 2 ^ (prefixWord ++ tailWord_5927751).sum := by decide
  have hdescent : baseEnd_5927751 < baseStart_5927751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927762 : List Nat := [3, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2]
def baseStart_5927762 : Nat := 118140960795 + 5927762 * 2 ^ 59
def prefixEnd_5927762 : Nat := 4983230072969 + 3 ^ 40 * 5927762 * 2
def baseEnd_5927762 : Nat := 3043791111457141837613725

theorem tailTrace_5927762 : CollatzResearch.WordTrace tailWord_5927762 prefixEnd_5927762 3043791111457141837613725 := by
  unfold tailWord_5927762
  simp only [CollatzResearch.WordTrace]
  refine ⟨54050810487684532498732385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144135494633825419996619693 54050810487684532498732385)
  ·
    refine ⟨40538107865763399374049289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54050810487684532498732385 40538107865763399374049289)
    ·
      refine ⟨30403580899322549530536967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40538107865763399374049289 30403580899322549530536967)
      ·
        refine ⟨45605371348983824295805451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30403580899322549530536967 45605371348983824295805451)
        ·
          refine ⟨68408057023475736443708177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45605371348983824295805451 68408057023475736443708177)
          ·
            refine ⟨51306042767606802332781133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68408057023475736443708177 51306042767606802332781133)
            ·
              refine ⟨19239766037852550874792925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51306042767606802332781133 19239766037852550874792925)
              ·
                refine ⟨7214912264194706578047347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19239766037852550874792925 7214912264194706578047347)
                ·
                  refine ⟨10822368396292059867071021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7214912264194706578047347 10822368396292059867071021)
                  ·
                    refine ⟨4058388148609522450151633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10822368396292059867071021 4058388148609522450151633)
                    ·
                      refine ⟨3043791111457141837613725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4058388148609522450151633 3043791111457141837613725)
                      ·
                        rfl

theorem cell23_5927762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_5927762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927762 prefixEnd_5927762 := by exact prefixLift 5927762
  have htrace : WordTrace (prefixWord ++ tailWord_5927762) baseStart_5927762 baseEnd_5927762 := by
    simpa [prefixWord, tailWord_5927762, baseEnd_5927762] using wordTrace_append hprefix tailTrace_5927762
  have hstable : (prefixWord ++ tailWord_5927762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927762).length < 2 ^ (prefixWord ++ tailWord_5927762).sum := by decide
  have hdescent : baseEnd_5927762 < baseStart_5927762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927788 : List Nat := [2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 4]
def baseStart_5927788 : Nat := 118140960795 + 5927788 * 2 ^ 59
def prefixEnd_5927788 : Nat := 4983230072969 + 3 ^ 40 * 5927788 * 2
def baseEnd_5927788 : Nat := 3043804461954158735888605

theorem tailTrace_5927788 : CollatzResearch.WordTrace tailWord_5927788 prefixEnd_5927788 3043804461954158735888605 := by
  unfold tailWord_5927788
  simp only [CollatzResearch.WordTrace]
  refine ⟨108102095124321968217688009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144136126832429290956917345 108102095124321968217688009)
  ·
    refine ⟨81076571343241476163266007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108102095124321968217688009 81076571343241476163266007)
    ·
      refine ⟨121614857014862214244899011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81076571343241476163266007 121614857014862214244899011)
      ·
        refine ⟨182422285522293321367348517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121614857014862214244899011 182422285522293321367348517)
        ·
          refine ⟨34204178535429997756377847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182422285522293321367348517 34204178535429997756377847)
          ·
            refine ⟨51306267803144996634566771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34204178535429997756377847 51306267803144996634566771)
            ·
              refine ⟨76959401704717494951850157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51306267803144996634566771 76959401704717494951850157)
              ·
                refine ⟨28859775639269060606943809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76959401704717494951850157 28859775639269060606943809)
                ·
                  refine ⟨21644831729451795455207857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28859775639269060606943809 21644831729451795455207857)
                  ·
                    refine ⟨16233623797088846591405893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21644831729451795455207857 16233623797088846591405893)
                    ·
                      refine ⟨3043804461954158735888605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16233623797088846591405893 3043804461954158735888605)
                      ·
                        rfl

theorem cell23_5927788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_5927788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927788 prefixEnd_5927788 := by exact prefixLift 5927788
  have htrace : WordTrace (prefixWord ++ tailWord_5927788) baseStart_5927788 baseEnd_5927788 := by
    simpa [prefixWord, tailWord_5927788, baseEnd_5927788] using wordTrace_append hprefix tailTrace_5927788
  have hstable : (prefixWord ++ tailWord_5927788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927788).length < 2 ^ (prefixWord ++ tailWord_5927788).sum := by decide
  have hdescent : baseEnd_5927788 < baseStart_5927788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927791 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 9]
def baseStart_5927791 : Nat := 118140960795 + 5927791 * 2 ^ 59
def prefixEnd_5927791 : Nat := 4983230072969 + 3 ^ 40 * 5927791 * 2
def baseEnd_5927791 : Nat := 3043806002396122224151091

theorem tailTrace_5927791 : CollatzResearch.WordTrace tailWord_5927791 prefixEnd_5927791 3043806002396122224151091 := by
  unfold tailWord_5927791
  simp only [CollatzResearch.WordTrace]
  refine ⟨216204299667633067947735227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144136199778422045298490151 216204299667633067947735227)
  ·
    refine ⟨324306449501449601921602841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216204299667633067947735227 324306449501449601921602841)
    ·
      refine ⟨243229837126087201441202131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324306449501449601921602841 243229837126087201441202131)
      ·
        refine ⟨364844755689130802161803197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243229837126087201441202131 364844755689130802161803197)
        ·
          refine ⟨136816783383424050810676199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 364844755689130802161803197 136816783383424050810676199)
          ·
            refine ⟨205225175075136076216014299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136816783383424050810676199 205225175075136076216014299)
            ·
              refine ⟨307837762612704114324021449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205225175075136076216014299 307837762612704114324021449)
              ·
                refine ⟨230878321959528085743016087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 307837762612704114324021449 230878321959528085743016087)
                ·
                  refine ⟨346317482939292128614524131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 230878321959528085743016087 346317482939292128614524131)
                  ·
                    refine ⟨519476224408938192921786197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 346317482939292128614524131 519476224408938192921786197)
                    ·
                      refine ⟨3043806002396122224151091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 519476224408938192921786197 3043806002396122224151091)
                      ·
                        rfl

theorem cell23_5927791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_5927791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927791 prefixEnd_5927791 := by exact prefixLift 5927791
  have htrace : WordTrace (prefixWord ++ tailWord_5927791) baseStart_5927791 baseEnd_5927791 := by
    simpa [prefixWord, tailWord_5927791, baseEnd_5927791] using wordTrace_append hprefix tailTrace_5927791
  have hstable : (prefixWord ++ tailWord_5927791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927791).length < 2 ^ (prefixWord ++ tailWord_5927791).sum := by decide
  have hdescent : baseEnd_5927791 < baseStart_5927791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927792 : List Nat := [2, 1, 1, 1, 4, 1, 2, 5, 2, 2, 2]
def baseStart_5927792 : Nat := 118140960795 + 5927792 * 2 ^ 59
def prefixEnd_5927792 : Nat := 4983230072969 + 3 ^ 40 * 5927792 * 2
def baseEnd_5927792 : Nat := 3043806515876776720238587

theorem tailTrace_5927792 : CollatzResearch.WordTrace tailWord_5927792 prefixEnd_5927792 3043806515876776720238587 := by
  unfold tailWord_5927792
  simp only [CollatzResearch.WordTrace]
  refine ⟨108102168070314722559260815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144136224093752963412347753 108102168070314722559260815)
  ·
    refine ⟨162153252105472083838891223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108102168070314722559260815 162153252105472083838891223)
    ·
      refine ⟨243229878158208125758336835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162153252105472083838891223 243229878158208125758336835)
      ·
        refine ⟨364844817237312188637505253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243229878158208125758336835 364844817237312188637505253)
        ·
          refine ⟨68408403231996035369532235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 364844817237312188637505253 68408403231996035369532235)
          ·
            refine ⟨102612604847994053054298353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68408403231996035369532235 102612604847994053054298353)
            ·
              refine ⟨76959453635995539790723765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102612604847994053054298353 76959453635995539790723765)
              ·
                refine ⟨7214948778374581855380353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76959453635995539790723765 7214948778374581855380353)
                ·
                  refine ⟨5411211583780936391535265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7214948778374581855380353 5411211583780936391535265)
                  ·
                    refine ⟨4058408687835702293651449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5411211583780936391535265 4058408687835702293651449)
                    ·
                      refine ⟨3043806515876776720238587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4058408687835702293651449 3043806515876776720238587)
                      ·
                        rfl

theorem cell23_5927792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 2, 2, 2].length) (baseStart_5927792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927792 prefixEnd_5927792 := by exact prefixLift 5927792
  have htrace : WordTrace (prefixWord ++ tailWord_5927792) baseStart_5927792 baseEnd_5927792 := by
    simpa [prefixWord, tailWord_5927792, baseEnd_5927792] using wordTrace_append hprefix tailTrace_5927792
  have hstable : (prefixWord ++ tailWord_5927792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927792).length < 2 ^ (prefixWord ++ tailWord_5927792).sum := by decide
  have hdescent : baseEnd_5927792 < baseStart_5927792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927808 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 3]
def baseStart_5927808 : Nat := 118140960795 + 5927808 * 2 ^ 59
def prefixEnd_5927808 : Nat := 4983230072969 + 3 ^ 40 * 5927808 * 2
def baseEnd_5927808 : Nat := 3043814731567248657638513

theorem tailTrace_5927808 : CollatzResearch.WordTrace tailWord_5927808 prefixEnd_5927808 3043814731567248657638513 := by
  unfold tailWord_5927808
  simp only [CollatzResearch.WordTrace]
  refine ⟨108102459854285739925552039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144136613139047653234069385 108102459854285739925552039)
  ·
    refine ⟨162153689781428609888328059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108102459854285739925552039 162153689781428609888328059)
    ·
      refine ⟨243230534672142914832492089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162153689781428609888328059 243230534672142914832492089)
      ·
        refine ⟨182422901004107186124369067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243230534672142914832492089 182422901004107186124369067)
        ·
          refine ⟨273634351506160779186553601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182422901004107186124369067 273634351506160779186553601)
          ·
            refine ⟨205225763629620584389915201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273634351506160779186553601 205225763629620584389915201)
            ·
              refine ⟨153919322722215438292436401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205225763629620584389915201 153919322722215438292436401)
              ·
                refine ⟨115439492041661578719327301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153919322722215438292436401 115439492041661578719327301)
                ·
                  refine ⟨21644904757811546009873869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115439492041661578719327301 21644904757811546009873869)
                  ·
                    refine ⟨8116839284179329753702701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21644904757811546009873869 8116839284179329753702701)
                    ·
                      refine ⟨3043814731567248657638513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8116839284179329753702701 3043814731567248657638513)
                      ·
                        rfl

theorem cell23_5927808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 3].length) (baseStart_5927808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927808 prefixEnd_5927808 := by exact prefixLift 5927808
  have htrace : WordTrace (prefixWord ++ tailWord_5927808) baseStart_5927808 baseEnd_5927808 := by
    simpa [prefixWord, tailWord_5927808, baseEnd_5927808] using wordTrace_append hprefix tailTrace_5927808
  have hstable : (prefixWord ++ tailWord_5927808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927808).length < 2 ^ (prefixWord ++ tailWord_5927808).sum := by decide
  have hdescent : baseEnd_5927808 < baseStart_5927808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927865 : List Nat := [1, 2, 1, 4, 2, 2, 1, 3, 2, 1, 4]
def baseStart_5927865 : Nat := 118140960795 + 5927865 * 2 ^ 59
def prefixEnd_5927865 : Nat := 4983230072969 + 3 ^ 40 * 5927865 * 2
def baseEnd_5927865 : Nat := 3043843999964554934625751

theorem tailTrace_5927865 : CollatzResearch.WordTrace tailWord_5927865 prefixEnd_5927865 3043843999964554934625751 := by
  unfold tailWord_5927865
  simp only [CollatzResearch.WordTrace]
  refine ⟨216206998669364978585929049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144137999112909985723952699 216206998669364978585929049)
  ·
    refine ⟨162155249002023733939446787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216206998669364978585929049 162155249002023733939446787)
    ·
      refine ⟨243232873503035600909170181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162155249002023733939446787 243232873503035600909170181)
      ·
        refine ⟨45606163781819175170469409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 243232873503035600909170181 45606163781819175170469409)
        ·
          refine ⟨34204622836364381377852057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45606163781819175170469409 34204622836364381377852057)
          ·
            refine ⟨25653467127273286033389043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34204622836364381377852057 25653467127273286033389043)
            ·
              refine ⟨38480200690909929050083565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25653467127273286033389043 38480200690909929050083565)
              ·
                refine ⟨14430075259091223393781337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38480200690909929050083565 14430075259091223393781337)
                ·
                  refine ⟨10822556444318417545336003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14430075259091223393781337 10822556444318417545336003)
                  ·
                    refine ⟨16233834666477626318004005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10822556444318417545336003 16233834666477626318004005)
                    ·
                      refine ⟨3043843999964554934625751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16233834666477626318004005 3043843999964554934625751)
                      ·
                        rfl

theorem cell23_5927865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_5927865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927865 prefixEnd_5927865 := by exact prefixLift 5927865
  have htrace : WordTrace (prefixWord ++ tailWord_5927865) baseStart_5927865 baseEnd_5927865 := by
    simpa [prefixWord, tailWord_5927865, baseEnd_5927865] using wordTrace_append hprefix tailTrace_5927865
  have hstable : (prefixWord ++ tailWord_5927865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927865).length < 2 ^ (prefixWord ++ tailWord_5927865).sum := by decide
  have hdescent : baseEnd_5927865 < baseStart_5927865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927908 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 3, 2, 6]
def baseStart_5927908 : Nat := 118140960795 + 5927908 * 2 ^ 59
def prefixEnd_5927908 : Nat := 4983230072969 + 3 ^ 40 * 5927908 * 2
def baseEnd_5927908 : Nat := 3043866079632698266388053

theorem tailTrace_5927908 : CollatzResearch.WordTrace tailWord_5927908 prefixEnd_5927908 3043866079632698266388053 := by
  unfold tailWord_5927908
  simp only [CollatzResearch.WordTrace]
  refine ⟨108104283504104598464872189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144139044672139464619829585 108104283504104598464872189)
  ·
    refine ⟨40539106314039224424327071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108104283504104598464872189 40539106314039224424327071)
    ·
      refine ⟨60808659471058836636490607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40539106314039224424327071 60808659471058836636490607)
      ·
        refine ⟨91212989206588254954735911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60808659471058836636490607 91212989206588254954735911)
        ·
          refine ⟨136819483809882382432103867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91212989206588254954735911 136819483809882382432103867)
          ·
            refine ⟨205229225714823573648155801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136819483809882382432103867 205229225714823573648155801)
            ·
              refine ⟨153921919286117680236116851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205229225714823573648155801 153921919286117680236116851)
              ·
                refine ⟨230882878929176520354175277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153921919286117680236116851 230882878929176520354175277)
                ·
                  refine ⟨86581079598441195132815729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 230882878929176520354175277 86581079598441195132815729)
                  ·
                    refine ⟨64935809698830896349611797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86581079598441195132815729 64935809698830896349611797)
                    ·
                      refine ⟨3043866079632698266388053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64935809698830896349611797 3043866079632698266388053)
                      ·
                        rfl

theorem cell23_5927908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_5927908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927908 prefixEnd_5927908 := by exact prefixLift 5927908
  have htrace : WordTrace (prefixWord ++ tailWord_5927908) baseStart_5927908 baseEnd_5927908 := by
    simpa [prefixWord, tailWord_5927908, baseEnd_5927908] using wordTrace_append hprefix tailTrace_5927908
  have hstable : (prefixWord ++ tailWord_5927908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927908).length < 2 ^ (prefixWord ++ tailWord_5927908).sum := by decide
  have hdescent : baseEnd_5927908 < baseStart_5927908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927909 : List Nat := [1, 3, 1, 6, 1, 1, 1, 2, 3, 4]
def baseStart_5927909 : Nat := 118140960795 + 5927909 * 2 ^ 59
def prefixEnd_5927909 : Nat := 4983230072969 + 3 ^ 40 * 5927909 * 2
def baseEnd_5927909 : Nat := 1014622197704450920825183

theorem tailTrace_5927909 : CollatzResearch.WordTrace tailWord_5927909 prefixEnd_5927909 1014622197704450920825183 := by
  unfold tailWord_5927909
  simp only [CollatzResearch.WordTrace]
  refine ⟨216208603481205574100530781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144139068987470382733687187 216208603481205574100530781)
  ·
    refine ⟨81078226305452090287699043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216208603481205574100530781 81078226305452090287699043)
    ·
      refine ⟨121617339458178135431548565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81078226305452090287699043 121617339458178135431548565)
      ·
        refine ⟨5700812787102100098353839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 121617339458178135431548565 5700812787102100098353839)
        ·
          refine ⟨8551219180653150147530759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5700812787102100098353839 8551219180653150147530759)
          ·
            refine ⟨12826828770979725221296139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8551219180653150147530759 12826828770979725221296139)
            ·
              refine ⟨19240243156469587831944209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12826828770979725221296139 19240243156469587831944209)
              ·
                refine ⟨14430182367352190873958157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19240243156469587831944209 14430182367352190873958157)
                ·
                  refine ⟨5411318387757071577734309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14430182367352190873958157 5411318387757071577734309)
                  ·
                    refine ⟨1014622197704450920825183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5411318387757071577734309 1014622197704450920825183)
                    ·
                      rfl

theorem cell23_5927909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 3, 4].length) (baseStart_5927909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927909 prefixEnd_5927909 := by exact prefixLift 5927909
  have htrace : WordTrace (prefixWord ++ tailWord_5927909) baseStart_5927909 baseEnd_5927909 := by
    simpa [prefixWord, tailWord_5927909, baseEnd_5927909] using wordTrace_append hprefix tailTrace_5927909
  have hstable : (prefixWord ++ tailWord_5927909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927909).length < 2 ^ (prefixWord ++ tailWord_5927909).sum := by decide
  have hdescent : baseEnd_5927909 < baseStart_5927909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927926 : List Nat := [5, 1, 1, 1, 3, 2, 2, 3, 1, 4]
def baseStart_5927926 : Nat := 118140960795 + 5927926 * 2 ^ 59
def prefixEnd_5927926 : Nat := 4983230072969 + 3 ^ 40 * 5927926 * 2
def baseEnd_5927926 : Nat := 1014625107428159731987657

theorem tailTrace_5927926 : CollatzResearch.WordTrace tailWord_5927926 prefixEnd_5927926 1014625107428159731987657 := by
  unfold tailWord_5927926
  simp only [CollatzResearch.WordTrace]
  refine ⟨13513076470133999125243727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144139482348095990669266421 13513076470133999125243727)
  ·
    refine ⟨20269614705200998687865591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13513076470133999125243727 20269614705200998687865591)
    ·
      refine ⟨30404422057801498031798387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20269614705200998687865591 30404422057801498031798387)
      ·
        refine ⟨45606633086702247047697581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30404422057801498031798387 45606633086702247047697581)
        ·
          refine ⟨17102487407513342642886593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45606633086702247047697581 17102487407513342642886593)
          ·
            refine ⟨12826865555635006982164945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17102487407513342642886593 12826865555635006982164945)
            ·
              refine ⟨9620149166726255236623709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12826865555635006982164945 9620149166726255236623709)
              ·
                refine ⟨3607555937522345713733891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9620149166726255236623709 3607555937522345713733891)
                ·
                  refine ⟨5411333906283518570600837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3607555937522345713733891 5411333906283518570600837)
                  ·
                    refine ⟨1014625107428159731987657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5411333906283518570600837 1014625107428159731987657)
                    ·
                      rfl

theorem cell23_5927926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_5927926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927926 prefixEnd_5927926 := by exact prefixLift 5927926
  have htrace : WordTrace (prefixWord ++ tailWord_5927926) baseStart_5927926 baseEnd_5927926 := by
    simpa [prefixWord, tailWord_5927926, baseEnd_5927926] using wordTrace_append hprefix tailTrace_5927926
  have hstable : (prefixWord ++ tailWord_5927926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927926).length < 2 ^ (prefixWord ++ tailWord_5927926).sum := by decide
  have hdescent : baseEnd_5927926 < baseStart_5927926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927928 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 2, 4, 5]
def baseStart_5927928 : Nat := 118140960795 + 5927928 * 2 ^ 59
def prefixEnd_5927928 : Nat := 4983230072969 + 3 ^ 40 * 5927928 * 2
def baseEnd_5927928 : Nat := 3043876349245788188137961

theorem tailTrace_5927928 : CollatzResearch.WordTrace tailWord_5927928 prefixEnd_5927928 3043876349245788188137961 := by
  unfold tailWord_5927928
  simp only [CollatzResearch.WordTrace]
  refine ⟨108104648234068370172736219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144139530978757826896981625 108104648234068370172736219)
  ·
    refine ⟨162156972351102555259104329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108104648234068370172736219 162156972351102555259104329)
    ·
      refine ⟨121617729263326916444328247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162156972351102555259104329 121617729263326916444328247)
      ·
        refine ⟨182426593894990374666492371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121617729263326916444328247 182426593894990374666492371)
        ·
          refine ⟨273639890842485561999738557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182426593894990374666492371 273639890842485561999738557)
          ·
            refine ⟨102614959065932085749901959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273639890842485561999738557 102614959065932085749901959)
            ·
              refine ⟨153922438598898128624852939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102614959065932085749901959 153922438598898128624852939)
              ·
                refine ⟨230883657898347192937279409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153922438598898128624852939 230883657898347192937279409)
                ·
                  refine ⟨173162743423760394702959557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230883657898347192937279409 173162743423760394702959557)
                  ·
                    refine ⟨32468014391955074006804917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 173162743423760394702959557 32468014391955074006804917)
                    ·
                      refine ⟨3043876349245788188137961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32468014391955074006804917 3043876349245788188137961)
                      ·
                        rfl

theorem cell23_5927928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_5927928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927928 prefixEnd_5927928 := by exact prefixLift 5927928
  have htrace : WordTrace (prefixWord ++ tailWord_5927928) baseStart_5927928 baseEnd_5927928 := by
    simpa [prefixWord, tailWord_5927928, baseEnd_5927928] using wordTrace_append hprefix tailTrace_5927928
  have hstable : (prefixWord ++ tailWord_5927928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927928).length < 2 ^ (prefixWord ++ tailWord_5927928).sum := by decide
  have hdescent : baseEnd_5927928 < baseStart_5927928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927982 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 6, 4]
def baseStart_5927982 : Nat := 118140960795 + 5927982 * 2 ^ 59
def prefixEnd_5927982 : Nat := 4983230072969 + 3 ^ 40 * 5927982 * 2
def baseEnd_5927982 : Nat := 1014634692400376992287571

theorem tailTrace_5927982 : CollatzResearch.WordTrace tailWord_5927982 prefixEnd_5927982 1014634692400376992287571 := by
  unfold tailWord_5927982
  simp only [CollatzResearch.WordTrace]
  refine ⟨27026408251242638445992275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144140844006627405045292133 27026408251242638445992275)
  ·
    refine ⟨40539612376863957668988413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27026408251242638445992275 40539612376863957668988413)
    ·
      refine ⟨15202354641323984125870655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40539612376863957668988413 15202354641323984125870655)
      ·
        refine ⟨22803531961985976188805983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15202354641323984125870655 22803531961985976188805983)
        ·
          refine ⟨34205297942978964283208975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22803531961985976188805983 34205297942978964283208975)
          ·
            refine ⟨51307946914468446424813463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34205297942978964283208975 51307946914468446424813463)
            ·
              refine ⟨76961920371702669637220195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51307946914468446424813463 76961920371702669637220195)
              ·
                refine ⟨115442880557554004455830293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76961920371702669637220195 115442880557554004455830293)
                ·
                  refine ⟨5411385026135343958867045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 115442880557554004455830293 5411385026135343958867045)
                  ·
                    refine ⟨1014634692400376992287571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5411385026135343958867045 1014634692400376992287571)
                    ·
                      rfl

theorem cell23_5927982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_5927982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927982 prefixEnd_5927982 := by exact prefixLift 5927982
  have htrace : WordTrace (prefixWord ++ tailWord_5927982) baseStart_5927982 baseEnd_5927982 := by
    simpa [prefixWord, tailWord_5927982, baseEnd_5927982] using wordTrace_append hprefix tailTrace_5927982
  have hstable : (prefixWord ++ tailWord_5927982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927982).length < 2 ^ (prefixWord ++ tailWord_5927982).sum := by decide
  have hdescent : baseEnd_5927982 < baseStart_5927982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927985 : List Nat := [1, 2, 2, 3, 1, 2, 2, 1, 3, 2, 4]
def baseStart_5927985 : Nat := 118140960795 + 5927985 * 2 ^ 59
def prefixEnd_5927985 : Nat := 4983230072969 + 3 ^ 40 * 5927985 * 2
def baseEnd_5927985 : Nat := 3043905617643094465125199

theorem tailTrace_5927985 : CollatzResearch.WordTrace tailWord_5927985 prefixEnd_5927985 3043905617643094465125199 := by
  unfold tailWord_5927985
  simp only [CollatzResearch.WordTrace]
  refine ⟨216211375428930239080297409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144140916952620159386864939 216211375428930239080297409)
  ·
    refine ⟨162158531571697679310223057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216211375428930239080297409 162158531571697679310223057)
    ·
      refine ⟨121618898678773259482667293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162158531571697679310223057 121618898678773259482667293)
      ·
        refine ⟨45607087004539972306000235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121618898678773259482667293 45607087004539972306000235)
        ·
          refine ⟨68410630506809958459000353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45607087004539972306000235 68410630506809958459000353)
          ·
            refine ⟨51307972880107468844250265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68410630506809958459000353 51307972880107468844250265)
            ·
              refine ⟨38480979660080601633187699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51307972880107468844250265 38480979660080601633187699)
              ·
                refine ⟨57721469490120902449781549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38480979660080601633187699 57721469490120902449781549)
                ·
                  refine ⟨21645551058795338418668081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57721469490120902449781549 21645551058795338418668081)
                  ·
                    refine ⟨16234163294096503814001061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21645551058795338418668081 16234163294096503814001061)
                    ·
                      refine ⟨3043905617643094465125199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16234163294096503814001061 3043905617643094465125199)
                      ·
                        rfl

theorem cell23_5927985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_5927985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927985 prefixEnd_5927985 := by exact prefixLift 5927985
  have htrace : WordTrace (prefixWord ++ tailWord_5927985) baseStart_5927985 baseEnd_5927985 := by
    simpa [prefixWord, tailWord_5927985, baseEnd_5927985] using wordTrace_append hprefix tailTrace_5927985
  have hstable : (prefixWord ++ tailWord_5927985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927985).length < 2 ^ (prefixWord ++ tailWord_5927985).sum := by decide
  have hdescent : baseEnd_5927985 < baseStart_5927985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5927992 : List Nat := [2, 1, 2, 1, 5, 2, 2, 1, 1, 1, 5]
def baseStart_5927992 : Nat := 118140960795 + 5927992 * 2 ^ 59
def prefixEnd_5927992 : Nat := 4983230072969 + 3 ^ 40 * 5927992 * 2
def baseEnd_5927992 : Nat := 3043909212007675937737667

theorem tailTrace_5927992 : CollatzResearch.WordTrace tailWord_5927992 prefixEnd_5927992 3043909212007675937737667 := by
  unfold tailWord_5927992
  simp only [CollatzResearch.WordTrace]
  refine ⟨108105815369952439637901115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144141087159936586183868153 108105815369952439637901115)
  ·
    refine ⟨162158723054928659456851673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108105815369952439637901115 162158723054928659456851673)
    ·
      refine ⟨121619042291196494592638755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162158723054928659456851673 121619042291196494592638755)
      ·
        refine ⟨182428563436794741888958133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121619042291196494592638755 182428563436794741888958133)
        ·
          refine ⟨17102677822199507052089825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 182428563436794741888958133 17102677822199507052089825)
          ·
            refine ⟨12827008366649630289067369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17102677822199507052089825 12827008366649630289067369)
            ·
              refine ⟨9620256274987222716800527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12827008366649630289067369 9620256274987222716800527)
              ·
                refine ⟨14430384412480834075200791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9620256274987222716800527 14430384412480834075200791)
                ·
                  refine ⟨21645576618721251112801187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14430384412480834075200791 21645576618721251112801187)
                  ·
                    refine ⟨32468364928081876669201781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21645576618721251112801187 32468364928081876669201781)
                    ·
                      refine ⟨3043909212007675937737667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32468364928081876669201781 3043909212007675937737667)
                      ·
                        rfl

theorem cell23_5927992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 1, 1, 5].length) (baseStart_5927992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5927992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5927992 prefixEnd_5927992 := by exact prefixLift 5927992
  have htrace : WordTrace (prefixWord ++ tailWord_5927992) baseStart_5927992 baseEnd_5927992 := by
    simpa [prefixWord, tailWord_5927992, baseEnd_5927992] using wordTrace_append hprefix tailTrace_5927992
  have hstable : (prefixWord ++ tailWord_5927992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5927992).length < 2 ^ (prefixWord ++ tailWord_5927992).sum := by decide
  have hdescent : baseEnd_5927992 < baseStart_5927992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5927992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928055 : List Nat := [1, 1, 3, 1, 1, 4, 2, 2, 2, 6]
def baseStart_5928055 : Nat := 118140960795 + 5928055 * 2 ^ 59
def prefixEnd_5928055 : Nat := 4983230072969 + 3 ^ 40 * 5928055 * 2
def baseEnd_5928055 : Nat := 1014647187096303063749959

theorem tailTrace_5928055 : CollatzResearch.WordTrace tailWord_5928055 prefixEnd_5928055 1014647187096303063749959 := by
  unfold tailWord_5928055
  simp only [CollatzResearch.WordTrace]
  refine ⟨216213928538676641035345619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144142619025784427356897079 216213928538676641035345619)
  ·
    refine ⟨324320892808014961553018429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216213928538676641035345619 324320892808014961553018429)
    ·
      refine ⟨121620334803005610582381911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324320892808014961553018429 121620334803005610582381911)
      ·
        refine ⟨182430502204508415873572867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121620334803005610582381911 182430502204508415873572867)
        ·
          refine ⟨273645753306762623810359301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182430502204508415873572867 273645753306762623810359301)
          ·
            refine ⟨51308578745017991964442369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 273645753306762623810359301 51308578745017991964442369)
            ·
              refine ⟨38481434058763493973331777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51308578745017991964442369 38481434058763493973331777)
              ·
                refine ⟨28861075544072620479998833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38481434058763493973331777 28861075544072620479998833)
                ·
                  refine ⟨21645806658054465359999125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28861075544072620479998833 21645806658054465359999125)
                  ·
                    refine ⟨1014647187096303063749959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21645806658054465359999125 1014647187096303063749959)
                    ·
                      rfl

theorem cell23_5928055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 6].length) (baseStart_5928055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928055 prefixEnd_5928055 := by exact prefixLift 5928055
  have htrace : WordTrace (prefixWord ++ tailWord_5928055) baseStart_5928055 baseEnd_5928055 := by
    simpa [prefixWord, tailWord_5928055, baseEnd_5928055] using wordTrace_append hprefix tailTrace_5928055
  have hstable : (prefixWord ++ tailWord_5928055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928055).length < 2 ^ (prefixWord ++ tailWord_5928055).sum := by decide
  have hdescent : baseEnd_5928055 < baseStart_5928055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928057 : List Nat := [1, 2, 1, 3, 6, 1, 2, 2, 1, 2, 2]
def baseStart_5928057 : Nat := 118140960795 + 5928057 * 2 ^ 59
def prefixEnd_5928057 : Nat := 4983230072969 + 3 ^ 40 * 5928057 * 2
def baseEnd_5928057 : Nat := 3043942588250218183424869

theorem tailTrace_5928057 : CollatzResearch.WordTrace tailWord_5928057 prefixEnd_5928057 3043942588250218183424869 := by
  unfold tailWord_5928057
  simp only [CollatzResearch.WordTrace]
  refine ⟨216214001484669395376918425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144142667656446263584612283 216214001484669395376918425)
  ·
    refine ⟨162160501113502046532688819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216214001484669395376918425 162160501113502046532688819)
    ·
      refine ⟨243240751670253069799033229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162160501113502046532688819 243240751670253069799033229)
      ·
        refine ⟨91215281876344901174637461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243240751670253069799033229 91215281876344901174637461)
        ·
          refine ⟨4275716337953667242561131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 91215281876344901174637461 4275716337953667242561131)
          ·
            refine ⟨6413574506930500863841697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4275716337953667242561131 6413574506930500863841697)
            ·
              refine ⟨4810180880197875647881273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6413574506930500863841697 4810180880197875647881273)
              ·
                refine ⟨3607635660148406735910955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4810180880197875647881273 3607635660148406735910955)
                ·
                  refine ⟨5411453490222610103866433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3607635660148406735910955 5411453490222610103866433)
                  ·
                    refine ⟨4058590117666957577899825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5411453490222610103866433 4058590117666957577899825)
                    ·
                      refine ⟨3043942588250218183424869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4058590117666957577899825 3043942588250218183424869)
                      ·
                        rfl

theorem cell23_5928057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2, 1, 2, 2].length) (baseStart_5928057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928057 prefixEnd_5928057 := by exact prefixLift 5928057
  have htrace : WordTrace (prefixWord ++ tailWord_5928057) baseStart_5928057 baseEnd_5928057 := by
    simpa [prefixWord, tailWord_5928057, baseEnd_5928057] using wordTrace_append hprefix tailTrace_5928057
  have hstable : (prefixWord ++ tailWord_5928057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928057).length < 2 ^ (prefixWord ++ tailWord_5928057).sum := by decide
  have hdescent : baseEnd_5928057 < baseStart_5928057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928113 : List Nat := [1, 2, 2, 5, 1, 1, 3, 2, 2, 2, 2]
def baseStart_5928113 : Nat := 118140960795 + 5928113 * 2 ^ 59
def prefixEnd_5928113 : Nat := 4983230072969 + 3 ^ 40 * 5928113 * 2
def baseEnd_5928113 : Nat := 3043971343166869964324611

theorem tailTrace_5928113 : CollatzResearch.WordTrace tailWord_5928113 prefixEnd_5928113 3043971343166869964324611 := by
  unfold tailWord_5928113
  simp only [CollatzResearch.WordTrace]
  refine ⟨216216043972466516940956993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144144029314977677960637995 216216043972466516940956993)
  ·
    refine ⟨162162032979349887705717745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216216043972466516940956993 162162032979349887705717745)
    ·
      refine ⟨121621524734512415779288309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162162032979349887705717745 121621524734512415779288309)
      ·
        refine ⟨11402017943860538979308279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121621524734512415779288309 11402017943860538979308279)
        ·
          refine ⟨17103026915790808468962419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11402017943860538979308279 17103026915790808468962419)
          ·
            refine ⟨25654540373686212703443629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17103026915790808468962419 25654540373686212703443629)
            ·
              refine ⟨9620452640132329763791361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25654540373686212703443629 9620452640132329763791361)
              ·
                refine ⟨7215339480099247322843521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9620452640132329763791361 7215339480099247322843521)
                ·
                  refine ⟨5411504610074435492132641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7215339480099247322843521 5411504610074435492132641)
                  ·
                    refine ⟨4058628457555826619099481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5411504610074435492132641 4058628457555826619099481)
                    ·
                      refine ⟨3043971343166869964324611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4058628457555826619099481 3043971343166869964324611)
                      ·
                        rfl

theorem cell23_5928113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_5928113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928113 prefixEnd_5928113 := by exact prefixLift 5928113
  have htrace : WordTrace (prefixWord ++ tailWord_5928113) baseStart_5928113 baseEnd_5928113 := by
    simpa [prefixWord, tailWord_5928113, baseEnd_5928113] using wordTrace_append hprefix tailTrace_5928113
  have hstable : (prefixWord ++ tailWord_5928113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928113).length < 2 ^ (prefixWord ++ tailWord_5928113).sum := by decide
  have hdescent : baseEnd_5928113 < baseStart_5928113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928145 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 1, 10]
def baseStart_5928145 : Nat := 118140960795 + 5928145 * 2 ^ 59
def prefixEnd_5928145 : Nat := 4983230072969 + 3 ^ 40 * 5928145 * 2
def baseEnd_5928145 : Nat := 1014662591515937946374821

theorem tailTrace_5928145 : CollatzResearch.WordTrace tailWord_5928145 prefixEnd_5928145 1014662591515937946374821 := by
  unfold tailWord_5928145
  simp only [CollatzResearch.WordTrace]
  refine ⟨216217211108350586406121889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144144807405567057604081259 216217211108350586406121889)
  ·
    refine ⟨162162908331262939804591417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216217211108350586406121889 162162908331262939804591417)
    ·
      refine ⟨121622181248447204853443563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162162908331262939804591417 121622181248447204853443563)
      ·
        refine ⟨182433271872670807280165345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121622181248447204853443563 182433271872670807280165345)
        ·
          refine ⟨136824953904503105460124009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182433271872670807280165345 136824953904503105460124009)
          ·
            refine ⟨102618715428377329095093007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136824953904503105460124009 102618715428377329095093007)
            ·
              refine ⟨153928073142565993642639511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102618715428377329095093007 153928073142565993642639511)
              ·
                refine ⟨230892109713848990463959267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153928073142565993642639511 230892109713848990463959267)
                ·
                  refine ⟨346338164570773485695938901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 230892109713848990463959267 346338164570773485695938901)
                  ·
                    refine ⟨1014662591515937946374821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 346338164570773485695938901 1014662591515937946374821)
                    ·
                      rfl

theorem cell23_5928145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_5928145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928145 prefixEnd_5928145 := by exact prefixLift 5928145
  have htrace : WordTrace (prefixWord ++ tailWord_5928145) baseStart_5928145 baseEnd_5928145 := by
    simpa [prefixWord, tailWord_5928145, baseEnd_5928145] using wordTrace_append hprefix tailTrace_5928145
  have hstable : (prefixWord ++ tailWord_5928145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928145).length < 2 ^ (prefixWord ++ tailWord_5928145).sum := by decide
  have hdescent : baseEnd_5928145 < baseStart_5928145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928179 : List Nat := [1, 1, 1, 2, 2, 5, 3, 1, 3, 4]
def baseStart_5928179 : Nat := 118140960795 + 5928179 * 2 ^ 59
def prefixEnd_5928179 : Nat := 4983230072969 + 3 ^ 40 * 5928179 * 2
def baseEnd_5928179 : Nat := 1014668410963355568699769

theorem tailTrace_5928179 : CollatzResearch.WordTrace tailWord_5928179 prefixEnd_5928179 1014668410963355568699769 := by
  unfold tailWord_5928179
  simp only [CollatzResearch.WordTrace]
  refine ⟨216218451190227410212859591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144145634126818273475239727 216218451190227410212859591)
  ·
    refine ⟨324327676785341115319289387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216218451190227410212859591 324327676785341115319289387)
    ·
      refine ⟨486491515178011672978934081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324327676785341115319289387 486491515178011672978934081)
      ·
        refine ⟨364868636383508754734200561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 486491515178011672978934081 364868636383508754734200561)
        ·
          refine ⟨273651477287631566050650421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364868636383508754734200561 273651477287631566050650421)
          ·
            refine ⟨25654825995715459317248477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 273651477287631566050650421 25654825995715459317248477)
            ·
              refine ⟨9620559748393297243968179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25654825995715459317248477 9620559748393297243968179)
              ·
                refine ⟨14430839622589945865952269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9620559748393297243968179 14430839622589945865952269)
                ·
                  refine ⟨5411564858471229699732101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14430839622589945865952269 5411564858471229699732101)
                  ·
                    refine ⟨1014668410963355568699769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5411564858471229699732101 1014668410963355568699769)
                    ·
                      rfl

theorem cell23_5928179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3, 4].length) (baseStart_5928179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928179 prefixEnd_5928179 := by exact prefixLift 5928179
  have htrace : WordTrace (prefixWord ++ tailWord_5928179) baseStart_5928179 baseEnd_5928179 := by
    simpa [prefixWord, tailWord_5928179, baseEnd_5928179] using wordTrace_append hprefix tailTrace_5928179
  have hstable : (prefixWord ++ tailWord_5928179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928179).length < 2 ^ (prefixWord ++ tailWord_5928179).sum := by decide
  have hdescent : baseEnd_5928179 < baseStart_5928179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928206 : List Nat := [4, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3]
def baseStart_5928206 : Nat := 118140960795 + 5928206 * 2 ^ 59
def prefixEnd_5928206 : Nat := 4983230072969 + 3 ^ 40 * 5928206 * 2
def baseEnd_5928206 : Nat := 3044019096867738100461683

theorem tailTrace_5928206 : CollatzResearch.WordTrace tailWord_5928206 prefixEnd_5928206 3044019096867738100461683 := by
  unfold tailWord_5928206
  simp only [CollatzResearch.WordTrace]
  refine ⟨27027429495141199228011559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144146290640753062549394981 27027429495141199228011559)
  ·
    refine ⟨40541144242711798842017339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27027429495141199228011559 40541144242711798842017339)
    ·
      refine ⟨60811716364067698263026009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40541144242711798842017339 60811716364067698263026009)
      ·
        refine ⟨45608787273050773697269507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60811716364067698263026009 45608787273050773697269507)
        ·
          refine ⟨68413180909576160545904261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45608787273050773697269507 68413180909576160545904261)
          ·
            refine ⟨12827471420545530102357049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68413180909576160545904261 12827471420545530102357049)
            ·
              refine ⟨9620603565409147576767787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12827471420545530102357049 9620603565409147576767787)
              ·
                refine ⟨14430905348113721365151681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9620603565409147576767787 14430905348113721365151681)
                ·
                  refine ⟨10823179011085291023863761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14430905348113721365151681 10823179011085291023863761)
                  ·
                    refine ⟨8117384258313968267897821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10823179011085291023863761 8117384258313968267897821)
                    ·
                      refine ⟨3044019096867738100461683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8117384258313968267897821 3044019096867738100461683)
                      ·
                        rfl

theorem cell23_5928206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_5928206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928206 prefixEnd_5928206 := by exact prefixLift 5928206
  have htrace : WordTrace (prefixWord ++ tailWord_5928206) baseStart_5928206 baseEnd_5928206 := by
    simpa [prefixWord, tailWord_5928206, baseEnd_5928206] using wordTrace_append hprefix tailTrace_5928206
  have hstable : (prefixWord ++ tailWord_5928206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928206).length < 2 ^ (prefixWord ++ tailWord_5928206).sum := by decide
  have hdescent : baseEnd_5928206 < baseStart_5928206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928226 : List Nat := [3, 3, 1, 1, 4, 1, 2, 2, 6]
def baseStart_5928226 : Nat := 118140960795 + 5928226 * 2 ^ 59
def prefixEnd_5928226 : Nat := 4983230072969 + 3 ^ 40 * 5928226 * 2
def baseEnd_5928226 : Nat := 338225485164536446912399

theorem tailTrace_5928226 : CollatzResearch.WordTrace tailWord_5928226 prefixEnd_5928226 338225485164536446912399 := by
  unfold tailWord_5928226
  simp only [CollatzResearch.WordTrace]
  refine ⟨54055041355264284309955133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144146776947371424826547021 54055041355264284309955133)
  ·
    refine ⟨20270640508224106616233175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54055041355264284309955133 20270640508224106616233175)
    ·
      refine ⟨30405960762336159924349763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20270640508224106616233175 30405960762336159924349763)
      ·
        refine ⟨45608941143504239886524645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30405960762336159924349763 45608941143504239886524645)
        ·
          refine ⟨8551676464407044978723371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45608941143504239886524645 8551676464407044978723371)
          ·
            refine ⟨12827514696610567468085057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8551676464407044978723371 12827514696610567468085057)
            ·
              refine ⟨9620636022457925601063793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12827514696610567468085057 9620636022457925601063793)
              ·
                refine ⟨7215477016843444200797845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9620636022457925601063793 7215477016843444200797845)
                ·
                  refine ⟨338225485164536446912399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7215477016843444200797845 338225485164536446912399)
                  ·
                    rfl

theorem cell23_5928226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_5928226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928226 prefixEnd_5928226 := by exact prefixLift 5928226
  have htrace : WordTrace (prefixWord ++ tailWord_5928226) baseStart_5928226 baseEnd_5928226 := by
    simpa [prefixWord, tailWord_5928226, baseEnd_5928226] using wordTrace_append hprefix tailTrace_5928226
  have hstable : (prefixWord ++ tailWord_5928226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928226).length < 2 ^ (prefixWord ++ tailWord_5928226).sum := by decide
  have hdescent : baseEnd_5928226 < baseStart_5928226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928259 : List Nat := [1, 1, 1, 3, 1, 3, 1, 6, 1, 1, 4]
def baseStart_5928259 : Nat := 118140960795 + 5928259 * 2 ^ 59
def prefixEnd_5928259 : Nat := 4983230072969 + 3 ^ 40 * 5928259 * 2
def baseEnd_5928259 : Nat := 3044046311342426393098939

theorem tailTrace_5928259 : CollatzResearch.WordTrace tailWord_5928259 prefixEnd_5928259 3044046311342426393098939 := by
  unfold tailWord_5928259
  simp only [CollatzResearch.WordTrace]
  refine ⟨216221369029937583875771831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144147579353291722583847887 216221369029937583875771831)
  ·
    refine ⟨324332053544906375813657747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216221369029937583875771831 324332053544906375813657747)
    ·
      refine ⟨486498080317359563720486621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324332053544906375813657747 486498080317359563720486621)
      ·
        refine ⟨182436780119009836395182483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 486498080317359563720486621 182436780119009836395182483)
        ·
          refine ⟨273655170178514754592773725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182436780119009836395182483 273655170178514754592773725)
          ·
            refine ⟨102620688816943032972290147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273655170178514754592773725 102620688816943032972290147)
            ·
              refine ⟨153931033225414549458435221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102620688816943032972290147 153931033225414549458435221)
              ·
                refine ⟨7215517182441307005864151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 153931033225414549458435221 7215517182441307005864151)
                ·
                  refine ⟨10823275773661960508796227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7215517182441307005864151 10823275773661960508796227)
                  ·
                    refine ⟨16234913660492940763194341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10823275773661960508796227 16234913660492940763194341)
                    ·
                      refine ⟨3044046311342426393098939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16234913660492940763194341 3044046311342426393098939)
                      ·
                        rfl

theorem cell23_5928259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 1, 4].length) (baseStart_5928259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928259 prefixEnd_5928259 := by exact prefixLift 5928259
  have htrace : WordTrace (prefixWord ++ tailWord_5928259) baseStart_5928259 baseEnd_5928259 := by
    simpa [prefixWord, tailWord_5928259, baseEnd_5928259] using wordTrace_append hprefix tailTrace_5928259
  have hstable : (prefixWord ++ tailWord_5928259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928259).length < 2 ^ (prefixWord ++ tailWord_5928259).sum := by decide
  have hdescent : baseEnd_5928259 < baseStart_5928259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928263 : List Nat := [1, 1, 4, 1, 2, 5, 1, 1, 2, 3, 2]
def baseStart_5928263 : Nat := 118140960795 + 5928263 * 2 ^ 59
def prefixEnd_5928263 : Nat := 4983230072969 + 3 ^ 40 * 5928263 * 2
def baseEnd_5928263 : Nat := 3044048365265044377448921

theorem tailTrace_5928263 : CollatzResearch.WordTrace tailWord_5928263 prefixEnd_5928263 3044048365265044377448921 := by
  unfold tailWord_5928263
  simp only [CollatzResearch.WordTrace]
  refine ⟨216221514921923092558917443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144147676614615395039278295 216221514921923092558917443)
  ·
    refine ⟨324332272382884638838376165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216221514921923092558917443 324332272382884638838376165)
    ·
      refine ⟨60812301071790869782195531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 324332272382884638838376165 60812301071790869782195531)
      ·
        refine ⟨91218451607686304673293297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60812301071790869782195531 91218451607686304673293297)
        ·
          refine ⟨68413838705764728504969973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91218451607686304673293297 68413838705764728504969973)
          ·
            refine ⟨6413797378665443297340935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68413838705764728504969973 6413797378665443297340935)
            ·
              refine ⟨9620696067998164946011403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6413797378665443297340935 9620696067998164946011403)
              ·
                refine ⟨14431044101997247419017105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9620696067998164946011403 14431044101997247419017105)
                ·
                  refine ⟨10823283076497935564262829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14431044101997247419017105 10823283076497935564262829)
                  ·
                    refine ⟨4058731153686725836598561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10823283076497935564262829 4058731153686725836598561)
                    ·
                      refine ⟨3044048365265044377448921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4058731153686725836598561 3044048365265044377448921)
                      ·
                        rfl

theorem cell23_5928263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 2, 3, 2].length) (baseStart_5928263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928263 prefixEnd_5928263 := by exact prefixLift 5928263
  have htrace : WordTrace (prefixWord ++ tailWord_5928263) baseStart_5928263 baseEnd_5928263 := by
    simpa [prefixWord, tailWord_5928263, baseEnd_5928263] using wordTrace_append hprefix tailTrace_5928263
  have hstable : (prefixWord ++ tailWord_5928263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928263).length < 2 ^ (prefixWord ++ tailWord_5928263).sum := by decide
  have hdescent : baseEnd_5928263 < baseStart_5928263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928276 : List Nat := [2, 4, 1, 1, 2, 1, 3, 3, 1, 1, 4]
def baseStart_5928276 : Nat := 118140960795 + 5928276 * 2 ^ 59
def prefixEnd_5928276 : Nat := 4983230072969 + 3 ^ 40 * 5928276 * 2
def baseEnd_5928276 : Nat := 3044055040513552826586361

theorem tailTrace_5928276 : CollatzResearch.WordTrace tailWord_5928276 prefixEnd_5928276 3044055040513552826586361 := by
  unfold tailWord_5928276
  simp only [CollatzResearch.WordTrace]
  refine ⟨108110994535437997889570341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144147992713917330519427121 108110994535437997889570341)
  ·
    refine ⟨20270811475394624604294439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108110994535437997889570341 20270811475394624604294439)
    ·
      refine ⟨30406217213091936906441659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20270811475394624604294439 30406217213091936906441659)
      ·
        refine ⟨45609325819637905359662489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30406217213091936906441659 45609325819637905359662489)
        ·
          refine ⟨34206994364728429019746867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45609325819637905359662489 34206994364728429019746867)
          ·
            refine ⟨51310491547092643529620301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34206994364728429019746867 51310491547092643529620301)
            ·
              refine ⟨19241434330159741323607613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51310491547092643529620301 19241434330159741323607613)
              ·
                refine ⟨7215537873809902996352855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19241434330159741323607613 7215537873809902996352855)
                ·
                  refine ⟨10823306810714854494529283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7215537873809902996352855 10823306810714854494529283)
                  ·
                    refine ⟨16234960216072281741793925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10823306810714854494529283 16234960216072281741793925)
                    ·
                      refine ⟨3044055040513552826586361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16234960216072281741793925 3044055040513552826586361)
                      ·
                        rfl

theorem cell23_5928276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_5928276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928276 prefixEnd_5928276 := by exact prefixLift 5928276
  have htrace : WordTrace (prefixWord ++ tailWord_5928276) baseStart_5928276 baseEnd_5928276 := by
    simpa [prefixWord, tailWord_5928276, baseEnd_5928276] using wordTrace_append hprefix tailTrace_5928276
  have hstable : (prefixWord ++ tailWord_5928276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928276).length < 2 ^ (prefixWord ++ tailWord_5928276).sum := by decide
  have hdescent : baseEnd_5928276 < baseStart_5928276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928293 : List Nat := [1, 3, 1, 3, 1, 2, 4, 1, 3, 2, 2]
def baseStart_5928293 : Nat := 118140960795 + 5928293 * 2 ^ 59
def prefixEnd_5928293 : Nat := 4983230072969 + 3 ^ 40 * 5928293 * 2
def baseEnd_5928293 : Nat := 3044063769684679260073783

theorem tailTrace_5928293 : CollatzResearch.WordTrace tailWord_5928293 prefixEnd_5928293 3044063769684679260073783 := by
  unfold tailWord_5928293
  simp only [CollatzResearch.WordTrace]
  refine ⟨216222609111814407682509533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144148406074542938455006355 216222609111814407682509533)
  ·
    refine ⟨81083478416930402880941075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216222609111814407682509533 81083478416930402880941075)
    ·
      refine ⟨121625217625395604321411613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81083478416930402880941075 121625217625395604321411613)
      ·
        refine ⟨45609456609523351620529355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121625217625395604321411613 45609456609523351620529355)
        ·
          refine ⟨68414184914285027430794033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45609456609523351620529355 68414184914285027430794033)
          ·
            refine ⟨51310638685713770573095525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68414184914285027430794033 51310638685713770573095525)
            ·
              refine ⟨9620744753571331982455411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51310638685713770573095525 9620744753571331982455411)
              ·
                refine ⟨14431117130356997973683117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9620744753571331982455411 14431117130356997973683117)
                ·
                  refine ⟨5411668923883874240131169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14431117130356997973683117 5411668923883874240131169)
                  ·
                    refine ⟨4058751692912905680098377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5411668923883874240131169 4058751692912905680098377)
                    ·
                      refine ⟨3044063769684679260073783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4058751692912905680098377 3044063769684679260073783)
                      ·
                        rfl

theorem cell23_5928293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_5928293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928293 prefixEnd_5928293 := by exact prefixLift 5928293
  have htrace : WordTrace (prefixWord ++ tailWord_5928293) baseStart_5928293 baseEnd_5928293 := by
    simpa [prefixWord, tailWord_5928293, baseEnd_5928293] using wordTrace_append hprefix tailTrace_5928293
  have hstable : (prefixWord ++ tailWord_5928293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928293).length < 2 ^ (prefixWord ++ tailWord_5928293).sum := by decide
  have hdescent : baseEnd_5928293 < baseStart_5928293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928296 : List Nat := [2, 1, 4, 2, 3, 1, 1, 2, 1, 1, 5]
def baseStart_5928296 : Nat := 118140960795 + 5928296 * 2 ^ 59
def prefixEnd_5928296 : Nat := 4983230072969 + 3 ^ 40 * 5928296 * 2
def baseEnd_5928296 : Nat := 3044065310126642748336269

theorem tailTrace_5928296 : CollatzResearch.WordTrace tailWord_5928296 prefixEnd_5928296 3044065310126642748336269 := by
  unfold tailWord_5928296
  simp only [CollatzResearch.WordTrace]
  refine ⟨108111359265401769597434371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144148479020535692796579161 108111359265401769597434371)
  ·
    refine ⟨162167038898102654396151557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108111359265401769597434371 162167038898102654396151557)
    ·
      refine ⟨30406319793394247699278417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162167038898102654396151557 30406319793394247699278417)
      ·
        refine ⟨22804739845045685774458813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30406319793394247699278417 22804739845045685774458813)
        ·
          refine ⟨8551777441892132165422055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22804739845045685774458813 8551777441892132165422055)
          ·
            refine ⟨12827666162838198248133083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8551777441892132165422055 12827666162838198248133083)
            ·
              refine ⟨19241499244257297372199625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12827666162838198248133083 19241499244257297372199625)
              ·
                refine ⟨14431124433192973029149719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19241499244257297372199625 14431124433192973029149719)
                ·
                  refine ⟨21646686649789459543724579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14431124433192973029149719 21646686649789459543724579)
                  ·
                    refine ⟨32470029974684189315586869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21646686649789459543724579 32470029974684189315586869)
                    ·
                      refine ⟨3044065310126642748336269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32470029974684189315586869 3044065310126642748336269)
                      ·
                        rfl

theorem cell23_5928296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_5928296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928296 prefixEnd_5928296 := by exact prefixLift 5928296
  have htrace : WordTrace (prefixWord ++ tailWord_5928296) baseStart_5928296 baseEnd_5928296 := by
    simpa [prefixWord, tailWord_5928296, baseEnd_5928296] using wordTrace_append hprefix tailTrace_5928296
  have hstable : (prefixWord ++ tailWord_5928296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928296).length < 2 ^ (prefixWord ++ tailWord_5928296).sum := by decide
  have hdescent : baseEnd_5928296 < baseStart_5928296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928327 : List Nat := [1, 1, 4, 2, 2, 4, 1, 3, 1, 2, 2]
def baseStart_5928327 : Nat := 118140960795 + 5928327 * 2 ^ 59
def prefixEnd_5928327 : Nat := 4983230072969 + 3 ^ 40 * 5928327 * 2
def baseEnd_5928327 : Nat := 3044081228026932127048627

theorem tailTrace_5928327 : CollatzResearch.WordTrace tailWord_5928327 prefixEnd_5928327 3044081228026932127048627 := by
  unfold tailWord_5928327
  simp only [CollatzResearch.WordTrace]
  refine ⟨216223849193691231489247235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144149232795794154326164823 216223849193691231489247235)
  ·
    refine ⟨324335773790536847233870853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216223849193691231489247235 324335773790536847233870853)
    ·
      refine ⟨60812957585725658856350785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 324335773790536847233870853 60812957585725658856350785)
      ·
        refine ⟨45609718189294244142263089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60812957585725658856350785 45609718189294244142263089)
        ·
          refine ⟨34207288641970683106697317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45609718189294244142263089 34207288641970683106697317)
          ·
            refine ⟨6413866620369503082505747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34207288641970683106697317 6413866620369503082505747)
            ·
              refine ⟨9620799930554254623758621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6413866620369503082505747 9620799930554254623758621)
              ·
                refine ⟨3607799973957845483909483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9620799930554254623758621 3607799973957845483909483)
                ·
                  refine ⟨5411699960936768225864225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3607799973957845483909483 5411699960936768225864225)
                  ·
                    refine ⟨4058774970702576169398169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5411699960936768225864225 4058774970702576169398169)
                    ·
                      refine ⟨3044081228026932127048627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4058774970702576169398169 3044081228026932127048627)
                      ·
                        rfl

theorem cell23_5928327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_5928327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928327 prefixEnd_5928327 := by exact prefixLift 5928327
  have htrace : WordTrace (prefixWord ++ tailWord_5928327) baseStart_5928327 baseEnd_5928327 := by
    simpa [prefixWord, tailWord_5928327, baseEnd_5928327] using wordTrace_append hprefix tailTrace_5928327
  have hstable : (prefixWord ++ tailWord_5928327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928327).length < 2 ^ (prefixWord ++ tailWord_5928327).sum := by decide
  have hdescent : baseEnd_5928327 < baseStart_5928327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928344 : List Nat := [2, 1, 2, 5, 2, 1, 3, 2, 1, 2, 2]
def baseStart_5928344 : Nat := 118140960795 + 5928344 * 2 ^ 59
def prefixEnd_5928344 : Nat := 4983230072969 + 3 ^ 40 * 5928344 * 2
def baseEnd_5928344 : Nat := 3044089957198058560536049

theorem tailTrace_5928344 : CollatzResearch.WordTrace tailWord_5928344 prefixEnd_5928344 3044089957198058560536049 := by
  unfold tailWord_5928344
  simp only [CollatzResearch.WordTrace]
  refine ⟨108112234617314821696308043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144149646156419762261744057 108112234617314821696308043)
  ·
    refine ⟨162168351925972232544462065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108112234617314821696308043 162168351925972232544462065)
    ·
      refine ⟨121626263944479174408346549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162168351925972232544462065 121626263944479174408346549)
      ·
        refine ⟨11402462244794922600782489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121626263944479174408346549 11402462244794922600782489)
        ·
          refine ⟨8551846683596191950586867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11402462244794922600782489 8551846683596191950586867)
          ·
            refine ⟨12827770025394287925880301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8551846683596191950586867 12827770025394287925880301)
            ·
              refine ⟨4810413759522857972205113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12827770025394287925880301 4810413759522857972205113)
              ·
                refine ⟨3607810319642143479153835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4810413759522857972205113 3607810319642143479153835)
                ·
                  refine ⟨5411715479463215218730753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3607810319642143479153835 5411715479463215218730753)
                  ·
                    refine ⟨4058786609597411414048065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5411715479463215218730753 4058786609597411414048065)
                    ·
                      refine ⟨3044089957198058560536049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4058786609597411414048065 3044089957198058560536049)
                      ·
                        rfl

theorem cell23_5928344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_5928344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928344 prefixEnd_5928344 := by exact prefixLift 5928344
  have htrace : WordTrace (prefixWord ++ tailWord_5928344) baseStart_5928344 baseEnd_5928344 := by
    simpa [prefixWord, tailWord_5928344, baseEnd_5928344] using wordTrace_append hprefix tailTrace_5928344
  have hstable : (prefixWord ++ tailWord_5928344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928344).length < 2 ^ (prefixWord ++ tailWord_5928344).sum := by decide
  have hdescent : baseEnd_5928344 < baseStart_5928344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928359 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 1, 8]
def baseStart_5928359 : Nat := 118140960795 + 5928359 * 2 ^ 59
def prefixEnd_5928359 : Nat := 4983230072969 + 3 ^ 40 * 5928359 * 2
def baseEnd_5928359 : Nat := 1014699219802625333949493

theorem tailTrace_5928359 : CollatzResearch.WordTrace tailWord_5928359 prefixEnd_5928359 1014699219802625333949493 := by
  unfold tailWord_5928359
  simp only [CollatzResearch.WordTrace]
  refine ⟨216225016329575300954412131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144150010886383533969608087 216225016329575300954412131)
  ·
    refine ⟨324337524494362951431618197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216225016329575300954412131 324337524494362951431618197)
    ·
      refine ⟨15203321460673263348357103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 324337524494362951431618197 15203321460673263348357103)
      ·
        refine ⟨22804982191009895022535655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15203321460673263348357103 22804982191009895022535655)
        ·
          refine ⟨34207473286514842533803483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22804982191009895022535655 34207473286514842533803483)
          ·
            refine ⟨51311209929772263800705225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34207473286514842533803483 51311209929772263800705225)
            ·
              refine ⟨38483407447329197850528919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51311209929772263800705225 38483407447329197850528919)
              ·
                refine ⟨57725111170993796775793379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38483407447329197850528919 57725111170993796775793379)
                ·
                  refine ⟨86587666756490695163690069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57725111170993796775793379 86587666756490695163690069)
                  ·
                    refine ⟨1014699219802625333949493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86587666756490695163690069 1014699219802625333949493)
                    ·
                      rfl

theorem cell23_5928359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_5928359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928359 prefixEnd_5928359 := by exact prefixLift 5928359
  have htrace : WordTrace (prefixWord ++ tailWord_5928359) baseStart_5928359 baseEnd_5928359 := by
    simpa [prefixWord, tailWord_5928359, baseEnd_5928359] using wordTrace_append hprefix tailTrace_5928359
  have hstable : (prefixWord ++ tailWord_5928359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928359).length < 2 ^ (prefixWord ++ tailWord_5928359).sum := by decide
  have hdescent : baseEnd_5928359 < baseStart_5928359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928369 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 4, 1, 5]
def baseStart_5928369 : Nat := 118140960795 + 5928369 * 2 ^ 59
def prefixEnd_5928369 : Nat := 4983230072969 + 3 ^ 40 * 5928369 * 2
def baseEnd_5928369 : Nat := 3044102794214420962723433

theorem tailTrace_5928369 : CollatzResearch.WordTrace tailWord_5928369 prefixEnd_5928369 3044102794214420962723433 := by
  unfold tailWord_5928369
  simp only [CollatzResearch.WordTrace]
  refine ⟨216225381059539072662276161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144150254039692715108184107 216225381059539072662276161)
  ·
    refine ⟨162169035794654304496707121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216225381059539072662276161 162169035794654304496707121)
    ·
      refine ⟨121626776845990728372530341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162169035794654304496707121 121626776845990728372530341)
      ·
        refine ⟨22805020658623261569849439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121626776845990728372530341 22805020658623261569849439)
        ·
          refine ⟨34207530987934892354774159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22805020658623261569849439 34207530987934892354774159)
          ·
            refine ⟨51311296481902338532161239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34207530987934892354774159 51311296481902338532161239)
            ·
              refine ⟨76966944722853507798241859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51311296481902338532161239 76966944722853507798241859)
              ·
                refine ⟨115450417084280261697362789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76966944722853507798241859 115450417084280261697362789)
                ·
                  refine ⟨21646953203302549068255523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115450417084280261697362789 21646953203302549068255523)
                  ·
                    refine ⟨32470429804953823602383285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21646953203302549068255523 32470429804953823602383285)
                    ·
                      refine ⟨3044102794214420962723433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32470429804953823602383285 3044102794214420962723433)
                      ·
                        rfl

theorem cell23_5928369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_5928369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928369 prefixEnd_5928369 := by exact prefixLift 5928369
  have htrace : WordTrace (prefixWord ++ tailWord_5928369) baseStart_5928369 baseEnd_5928369 := by
    simpa [prefixWord, tailWord_5928369, baseEnd_5928369] using wordTrace_append hprefix tailTrace_5928369
  have hstable : (prefixWord ++ tailWord_5928369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928369).length < 2 ^ (prefixWord ++ tailWord_5928369).sum := by decide
  have hdescent : baseEnd_5928369 < baseStart_5928369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928456 : List Nat := [2, 1, 3, 2, 1, 1, 2, 4, 2, 1, 4]
def baseStart_5928456 : Nat := 118140960795 + 5928456 * 2 ^ 59
def prefixEnd_5928456 : Nat := 4983230072969 + 3 ^ 40 * 5928456 * 2
def baseEnd_5928456 : Nat := 3044147467031362122335533

theorem tailTrace_5928456 : CollatzResearch.WordTrace tailWord_5928456 prefixEnd_5928456 3044147467031362122335533 := by
  unfold tailWord_5928456
  simp only [CollatzResearch.WordTrace]
  refine ⟨108114277105111943260346611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144152369473482591013795481 108114277105111943260346611)
  ·
    refine ⟨162171415657667914890519917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108114277105111943260346611 162171415657667914890519917)
    ·
      refine ⟨60814280871625468083944969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162171415657667914890519917 60814280871625468083944969)
      ·
        refine ⟨45610710653719101062958727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60814280871625468083944969 45610710653719101062958727)
        ·
          refine ⟨68416065980578651594438091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45610710653719101062958727 68416065980578651594438091)
          ·
            refine ⟨102624098970867977391657137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68416065980578651594438091 102624098970867977391657137)
            ·
              refine ⟨76968074228150983043742853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102624098970867977391657137 76968074228150983043742853)
              ·
                refine ⟨14431513917778309320701785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76968074228150983043742853 14431513917778309320701785)
                ·
                  refine ⟨10823635438333731990526339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14431513917778309320701785 10823635438333731990526339)
                  ·
                    refine ⟨16235453157500597985789509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10823635438333731990526339 16235453157500597985789509)
                    ·
                      refine ⟨3044147467031362122335533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16235453157500597985789509 3044147467031362122335533)
                      ·
                        rfl

theorem cell23_5928456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_5928456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928456 prefixEnd_5928456 := by exact prefixLift 5928456
  have htrace : WordTrace (prefixWord ++ tailWord_5928456) baseStart_5928456 baseEnd_5928456 := by
    simpa [prefixWord, tailWord_5928456, baseEnd_5928456] using wordTrace_append hprefix tailTrace_5928456
  have hstable : (prefixWord ++ tailWord_5928456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928456).length < 2 ^ (prefixWord ++ tailWord_5928456).sum := by decide
  have hdescent : baseEnd_5928456 < baseStart_5928456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928476 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 3, 4, 3]
def baseStart_5928476 : Nat := 118140960795 + 5928476 * 2 ^ 59
def prefixEnd_5928476 : Nat := 4983230072969 + 3 ^ 40 * 5928476 * 2
def baseEnd_5928476 : Nat := 3044157736644452044085441

theorem tailTrace_5928476 : CollatzResearch.WordTrace tailWord_5928476 prefixEnd_5928476 3044157736644452044085441 := by
  unfold tailWord_5928476
  simp only [CollatzResearch.WordTrace]
  refine ⟨108114641835075714968210641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144152855780100953290947521 108114641835075714968210641)
  ·
    refine ⟨81085981376306786226157981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108114641835075714968210641 81085981376306786226157981)
    ·
      refine ⟨30407243016115044834809243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81085981376306786226157981 30407243016115044834809243)
      ·
        refine ⟨45610864524172567252213865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30407243016115044834809243 45610864524172567252213865)
        ·
          refine ⟨34208148393129425439160399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45610864524172567252213865 34208148393129425439160399)
          ·
            refine ⟨51312222589694138158740599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34208148393129425439160399 51312222589694138158740599)
            ·
              refine ⟨76968333884541207238110899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51312222589694138158740599 76968333884541207238110899)
              ·
                refine ⟨115452500826811810857166349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76968333884541207238110899 115452500826811810857166349)
                ·
                  refine ⟨43294687810054429071437381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115452500826811810857166349 43294687810054429071437381)
                  ·
                    refine ⟨8117753964385205450894509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43294687810054429071437381 8117753964385205450894509)
                    ·
                      refine ⟨3044157736644452044085441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8117753964385205450894509 3044157736644452044085441)
                      ·
                        rfl

theorem cell23_5928476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_5928476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928476 prefixEnd_5928476 := by exact prefixLift 5928476
  have htrace : WordTrace (prefixWord ++ tailWord_5928476) baseStart_5928476 baseEnd_5928476 := by
    simpa [prefixWord, tailWord_5928476, baseEnd_5928476] using wordTrace_append hprefix tailTrace_5928476
  have hstable : (prefixWord ++ tailWord_5928476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928476).length < 2 ^ (prefixWord ++ tailWord_5928476).sum := by decide
  have hdescent : baseEnd_5928476 < baseStart_5928476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928526 : List Nat := [4, 1, 1, 1, 1, 2, 1, 4, 3, 5]
def baseStart_5928526 : Nat := 118140960795 + 5928526 * 2 ^ 59
def prefixEnd_5928526 : Nat := 4983230072969 + 3 ^ 40 * 5928526 * 2
def baseEnd_5928526 : Nat := 1014727803559058949486737

theorem tailTrace_5928526 : CollatzResearch.WordTrace tailWord_5928526 prefixEnd_5928526 1014727803559058949486737 := by
  unfold tailWord_5928526
  simp only [CollatzResearch.WordTrace]
  refine ⟨27028888414996286059467679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144154071546646858983827621 27028888414996286059467679)
  ·
    refine ⟨40543332622494429089201519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27028888414996286059467679 40543332622494429089201519)
    ·
      refine ⟨60814998933741643633802279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40543332622494429089201519 60814998933741643633802279)
      ·
        refine ⟨91222498400612465450703419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60814998933741643633802279 91222498400612465450703419)
        ·
          refine ⟨136833747600918698176055129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91222498400612465450703419 136833747600918698176055129)
          ·
            refine ⟨102625310700689023632041347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136833747600918698176055129 102625310700689023632041347)
            ·
              refine ⟨153937966051033535448062021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102625310700689023632041347 153937966051033535448062021)
              ·
                refine ⟨28863368634568787896511629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 153937966051033535448062021 28863368634568787896511629)
                ·
                  refine ⟨10823763237963295461191861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28863368634568787896511629 10823763237963295461191861)
                  ·
                    refine ⟨1014727803559058949486737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10823763237963295461191861 1014727803559058949486737)
                    ·
                      rfl

theorem cell23_5928526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_5928526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928526 prefixEnd_5928526 := by exact prefixLift 5928526
  have htrace : WordTrace (prefixWord ++ tailWord_5928526) baseStart_5928526 baseEnd_5928526 := by
    simpa [prefixWord, tailWord_5928526, baseEnd_5928526] using wordTrace_append hprefix tailTrace_5928526
  have hstable : (prefixWord ++ tailWord_5928526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928526).length < 2 ^ (prefixWord ++ tailWord_5928526).sum := by decide
  have hdescent : baseEnd_5928526 < baseStart_5928526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928530 : List Nat := [3, 2, 2, 1, 2, 4, 2, 1, 6]
def baseStart_5928530 : Nat := 118140960795 + 5928530 * 2 ^ 59
def prefixEnd_5928530 : Nat := 4983230072969 + 3 ^ 40 * 5928530 * 2
def baseEnd_5928530 : Nat := 338242829399977203645577

theorem tailTrace_5928530 : CollatzResearch.WordTrace tailWord_5928530 prefixEnd_5928530 338242829399977203645577 := by
  unfold tailWord_5928530
  simp only [CollatzResearch.WordTrace]
  refine ⟨54057813302988949289721761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144154168807970531439258029 54057813302988949289721761)
  ·
    refine ⟨40543359977241711967291321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54057813302988949289721761 40543359977241711967291321)
    ·
      refine ⟨30407519982931283975468491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40543359977241711967291321 30407519982931283975468491)
      ·
        refine ⟨45611279974396925963202737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30407519982931283975468491 45611279974396925963202737)
        ·
          refine ⟨34208459980797694472402053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45611279974396925963202737 34208459980797694472402053)
          ·
            refine ⟨6414086246399567713575385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34208459980797694472402053 6414086246399567713575385)
            ·
              refine ⟨4810564684799675785181539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6414086246399567713575385 4810564684799675785181539)
              ·
                refine ⟨7215847027199513677772309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4810564684799675785181539 7215847027199513677772309)
                ·
                  refine ⟨338242829399977203645577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7215847027199513677772309 338242829399977203645577)
                  ·
                    rfl

theorem cell23_5928530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 6].length) (baseStart_5928530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928530 prefixEnd_5928530 := by exact prefixLift 5928530
  have htrace : WordTrace (prefixWord ++ tailWord_5928530) baseStart_5928530 baseEnd_5928530 := by
    simpa [prefixWord, tailWord_5928530, baseEnd_5928530] using wordTrace_append hprefix tailTrace_5928530
  have hstable : (prefixWord ++ tailWord_5928530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928530).length < 2 ^ (prefixWord ++ tailWord_5928530).sum := by decide
  have hdescent : baseEnd_5928530 < baseStart_5928530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928533 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 6, 3, 2]
def baseStart_5928533 : Nat := 118140960795 + 5928533 * 2 ^ 59
def prefixEnd_5928533 : Nat := 4983230072969 + 3 ^ 40 * 5928533 * 2
def baseEnd_5928533 : Nat := 3044187005041758321072679

theorem tailTrace_5928533 : CollatzResearch.WordTrace tailWord_5928533 prefixEnd_5928533 3044187005041758321072679 := by
  unfold tailWord_5928533
  simp only [CollatzResearch.WordTrace]
  refine ⟨216231362630944928671246253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144154241753963285780830835 216231362630944928671246253)
  ·
    refine ⟨81086760986604348251717345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216231362630944928671246253 81086760986604348251717345)
    ·
      refine ⟨60815070739953261188788009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81086760986604348251717345 60815070739953261188788009)
      ·
        refine ⟨45611303054964945891591007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60815070739953261188788009 45611303054964945891591007)
        ·
          refine ⟨68416954582447418837386511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45611303054964945891591007 68416954582447418837386511)
          ·
            refine ⟨102625431873671128256079767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68416954582447418837386511 102625431873671128256079767)
            ·
              refine ⟨153938147810506692384119651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102625431873671128256079767 153938147810506692384119651)
              ·
                refine ⟨230907221715760038576179477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153938147810506692384119651 230907221715760038576179477)
                ·
                  refine ⟨10823776017926251808258413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 230907221715760038576179477 10823776017926251808258413)
                  ·
                    refine ⟨4058916006722344428096905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10823776017926251808258413 4058916006722344428096905)
                    ·
                      refine ⟨3044187005041758321072679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4058916006722344428096905 3044187005041758321072679)
                      ·
                        rfl

theorem cell23_5928533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_5928533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928533 prefixEnd_5928533 := by exact prefixLift 5928533
  have htrace : WordTrace (prefixWord ++ tailWord_5928533) baseStart_5928533 baseEnd_5928533 := by
    simpa [prefixWord, tailWord_5928533, baseEnd_5928533] using wordTrace_append hprefix tailTrace_5928533
  have hstable : (prefixWord ++ tailWord_5928533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928533).length < 2 ^ (prefixWord ++ tailWord_5928533).sum := by decide
  have hdescent : baseEnd_5928533 < baseStart_5928533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928560 : List Nat := [2, 1, 1, 1, 6, 2, 3, 1, 1, 5]
def baseStart_5928560 : Nat := 118140960795 + 5928560 * 2 ^ 59
def prefixEnd_5928560 : Nat := 4983230072969 + 3 ^ 40 * 5928560 * 2
def baseEnd_5928560 : Nat := 1014733623006476571811685

theorem tailTrace_5928560 : CollatzResearch.WordTrace tailWord_5928560 prefixEnd_5928560 1014733623006476571811685 := by
  unfold tailWord_5928560
  simp only [CollatzResearch.WordTrace]
  refine ⟨108116173700923556141239567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144154898267898074854986089 108116173700923556141239567)
  ·
    refine ⟨162174260551385334211859351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108116173700923556141239567 162174260551385334211859351)
    ·
      refine ⟨243261390827078001317789027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162174260551385334211859351 243261390827078001317789027)
      ·
        refine ⟨364892086240617001976683541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243261390827078001317789027 364892086240617001976683541)
        ·
          refine ⟨17104316542528921967657041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 364892086240617001976683541 17104316542528921967657041)
          ·
            refine ⟨12828237406896691475742781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17104316542528921967657041 12828237406896691475742781)
            ·
              refine ⟨4810589027586259303403543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12828237406896691475742781 4810589027586259303403543)
              ·
                refine ⟨7215883541379388955105315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4810589027586259303403543 7215883541379388955105315)
                ·
                  refine ⟨10823825312069083432657973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7215883541379388955105315 10823825312069083432657973)
                  ·
                    refine ⟨1014733623006476571811685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10823825312069083432657973 1014733623006476571811685)
                    ·
                      rfl

theorem cell23_5928560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 1, 5].length) (baseStart_5928560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928560 prefixEnd_5928560 := by exact prefixLift 5928560
  have htrace : WordTrace (prefixWord ++ tailWord_5928560) baseStart_5928560 baseEnd_5928560 := by
    simpa [prefixWord, tailWord_5928560, baseEnd_5928560] using wordTrace_append hprefix tailTrace_5928560
  have hstable : (prefixWord ++ tailWord_5928560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928560).length < 2 ^ (prefixWord ++ tailWord_5928560).sum := by decide
  have hdescent : baseEnd_5928560 < baseStart_5928560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928576 : List Nat := [2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 4]
def baseStart_5928576 : Nat := 118140960795 + 5928576 * 2 ^ 59
def prefixEnd_5928576 : Nat := 4983230072969 + 3 ^ 40 * 5928576 * 2
def baseEnd_5928576 : Nat := 3044209084709901652834981

theorem tailTrace_5928576 : CollatzResearch.WordTrace tailWord_5928576 prefixEnd_5928576 3044209084709901652834981 := by
  unfold tailWord_5928576
  simp only [CollatzResearch.WordTrace]
  refine ⟨108116465484894573507530791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144155287313192764676707721 108116465484894573507530791)
  ·
    refine ⟨162174698227341860261296187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108116465484894573507530791 162174698227341860261296187)
    ·
      refine ⟨243262047341012790391944281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162174698227341860261296187 243262047341012790391944281)
      ·
        refine ⟨182446535505759592793958211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243262047341012790391944281 182446535505759592793958211)
        ·
          refine ⟨273669803258639389190937317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182446535505759592793958211 273669803258639389190937317)
          ·
            refine ⟨51313088110994885473300747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 273669803258639389190937317 51313088110994885473300747)
            ·
              refine ⟨76969632166492328209951121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51313088110994885473300747 76969632166492328209951121)
              ·
                refine ⟨57727224124869246157463341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76969632166492328209951121 57727224124869246157463341)
                ·
                  refine ⟨21647709046825967309048753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57727224124869246157463341 21647709046825967309048753)
                  ·
                    refine ⟨16235781785119475481786565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21647709046825967309048753 16235781785119475481786565)
                    ·
                      refine ⟨3044209084709901652834981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16235781785119475481786565 3044209084709901652834981)
                      ·
                        rfl

theorem cell23_5928576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_5928576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928576 prefixEnd_5928576 := by exact prefixLift 5928576
  have htrace : WordTrace (prefixWord ++ tailWord_5928576) baseStart_5928576 baseEnd_5928576 := by
    simpa [prefixWord, tailWord_5928576, baseEnd_5928576] using wordTrace_append hprefix tailTrace_5928576
  have hstable : (prefixWord ++ tailWord_5928576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928576).length < 2 ^ (prefixWord ++ tailWord_5928576).sum := by decide
  have hdescent : baseEnd_5928576 < baseStart_5928576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928583 : List Nat := [1, 1, 4, 2, 1, 3, 1, 2, 3, 2, 3]
def baseStart_5928583 : Nat := 118140960795 + 5928583 * 2 ^ 59
def prefixEnd_5928583 : Nat := 4983230072969 + 3 ^ 40 * 5928583 * 2
def baseEnd_5928583 : Nat := 3044212679074483125447449

theorem tailTrace_5928583 : CollatzResearch.WordTrace tailWord_5928583 prefixEnd_5928583 3044212679074483125447449 := by
  unfold tailWord_5928583
  simp only [CollatzResearch.WordTrace]
  refine ⟨216233186280763787210566403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144155457520509191473710935 216233186280763787210566403)
  ·
    refine ⟨324349779421145680815849605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216233186280763787210566403 324349779421145680815849605)
    ·
      refine ⟨60815583641464815152971801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 324349779421145680815849605 60815583641464815152971801)
      ·
        refine ⟨45611687731098611364728851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60815583641464815152971801 45611687731098611364728851)
        ·
          refine ⟨68417531596647917047093277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45611687731098611364728851 68417531596647917047093277)
          ·
            refine ⟨25656574348742968892659979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68417531596647917047093277 25656574348742968892659979)
            ·
              refine ⟨38484861523114453338989969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25656574348742968892659979 38484861523114453338989969)
              ·
                refine ⟨28863646142335840004242477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38484861523114453338989969 28863646142335840004242477)
                ·
                  refine ⟨10823867303375940001590929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28863646142335840004242477 10823867303375940001590929)
                  ·
                    refine ⟨8117900477531955001193197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10823867303375940001590929 8117900477531955001193197)
                    ·
                      refine ⟨3044212679074483125447449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8117900477531955001193197 3044212679074483125447449)
                      ·
                        rfl

theorem cell23_5928583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_5928583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928583 prefixEnd_5928583 := by exact prefixLift 5928583
  have htrace : WordTrace (prefixWord ++ tailWord_5928583) baseStart_5928583 baseEnd_5928583 := by
    simpa [prefixWord, tailWord_5928583, baseEnd_5928583] using wordTrace_append hprefix tailTrace_5928583
  have hstable : (prefixWord ++ tailWord_5928583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928583).length < 2 ^ (prefixWord ++ tailWord_5928583).sum := by decide
  have hdescent : baseEnd_5928583 < baseStart_5928583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928590 : List Nat := [4, 1, 1, 3, 1, 2, 2, 3, 2, 4]
def baseStart_5928590 : Nat := 118140960795 + 5928590 * 2 ^ 59
def prefixEnd_5928590 : Nat := 4983230072969 + 3 ^ 40 * 5928590 * 2
def baseEnd_5928590 : Nat := 1014738757813021532686639

theorem tailTrace_5928590 : CollatzResearch.WordTrace tailWord_5928590 prefixEnd_5928590 1014738757813021532686639 := by
  unfold tailWord_5928590
  simp only [CollatzResearch.WordTrace]
  refine ⟨27029180198967303425758903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144155627727825618270714149 27029180198967303425758903)
  ·
    refine ⟨40543770298450955138638355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27029180198967303425758903 40543770298450955138638355)
    ·
      refine ⟨60815655447676432707957533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40543770298450955138638355 60815655447676432707957533)
      ·
        refine ⟨22805870792878662265484075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60815655447676432707957533 22805870792878662265484075)
        ·
          refine ⟨34208806189317993398226113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22805870792878662265484075 34208806189317993398226113)
          ·
            refine ⟨25656604641988495048669585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34208806189317993398226113 25656604641988495048669585)
            ·
              refine ⟨19242453481491371286502189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25656604641988495048669585 19242453481491371286502189)
              ·
                refine ⟨7215920055559264232438321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19242453481491371286502189 7215920055559264232438321)
                ·
                  refine ⟨5411940041669448174328741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7215920055559264232438321 5411940041669448174328741)
                  ·
                    refine ⟨1014738757813021532686639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5411940041669448174328741 1014738757813021532686639)
                    ·
                      rfl

theorem cell23_5928590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_5928590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928590 prefixEnd_5928590 := by exact prefixLift 5928590
  have htrace : WordTrace (prefixWord ++ tailWord_5928590) baseStart_5928590 baseEnd_5928590 := by
    simpa [prefixWord, tailWord_5928590, baseEnd_5928590] using wordTrace_append hprefix tailTrace_5928590
  have hstable : (prefixWord ++ tailWord_5928590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928590).length < 2 ^ (prefixWord ++ tailWord_5928590).sum := by decide
  have hdescent : baseEnd_5928590 < baseStart_5928590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928613 : List Nat := [1, 3, 1, 2, 1, 2, 4, 2, 1, 3, 3]
def baseStart_5928613 : Nat := 118140960795 + 5928613 * 2 ^ 59
def prefixEnd_5928613 : Nat := 4983230072969 + 3 ^ 40 * 5928613 * 2
def baseEnd_5928613 : Nat := 3044228083494118008072311

theorem tailTrace_5928613 : CollatzResearch.WordTrace tailWord_5928613 prefixEnd_5928613 3044228083494118008072311 := by
  unfold tailWord_5928613
  simp only [CollatzResearch.WordTrace]
  refine ⟨216234280470655102334158493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144156186980436734889438995 216234280470655102334158493)
  ·
    refine ⟨81087855176495663375309435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216234280470655102334158493 81087855176495663375309435)
    ·
      refine ⟨121631782764743495062964153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81087855176495663375309435 121631782764743495062964153)
      ·
        refine ⟨91223837073557621297223115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121631782764743495062964153 91223837073557621297223115)
        ·
          refine ⟨136835755610336431945834673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91223837073557621297223115 136835755610336431945834673)
          ·
            refine ⟨102626816707752323959376005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136835755610336431945834673 102626816707752323959376005)
            ·
              refine ⟨19242528132703560742383001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102626816707752323959376005 19242528132703560742383001)
              ·
                refine ⟨14431896099527670556787251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19242528132703560742383001 14431896099527670556787251)
                ·
                  refine ⟨21647844149291505835180877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14431896099527670556787251 21647844149291505835180877)
                  ·
                    refine ⟨8117941555984314688192829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21647844149291505835180877 8117941555984314688192829)
                    ·
                      refine ⟨3044228083494118008072311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8117941555984314688192829 3044228083494118008072311)
                      ·
                        rfl

theorem cell23_5928613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_5928613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928613 prefixEnd_5928613 := by exact prefixLift 5928613
  have htrace : WordTrace (prefixWord ++ tailWord_5928613) baseStart_5928613 baseEnd_5928613 := by
    simpa [prefixWord, tailWord_5928613, baseEnd_5928613] using wordTrace_append hprefix tailTrace_5928613
  have hstable : (prefixWord ++ tailWord_5928613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928613).length < 2 ^ (prefixWord ++ tailWord_5928613).sum := by decide
  have hdescent : baseEnd_5928613 < baseStart_5928613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928647 : List Nat := [1, 1, 4, 1, 1, 1, 7, 1, 2, 1, 3]
def baseStart_5928647 : Nat := 118140960795 + 5928647 * 2 ^ 59
def prefixEnd_5928647 : Nat := 4983230072969 + 3 ^ 40 * 5928647 * 2
def baseEnd_5928647 : Nat := 3044245541836370875047155

theorem tailTrace_5928647 : CollatzResearch.WordTrace tailWord_5928647 prefixEnd_5928647 3044245541836370875047155 := by
  unfold tailWord_5928647
  simp only [CollatzResearch.WordTrace]
  refine ⟨216235520552531926140896195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144157013701687950760597463 216235520552531926140896195)
  ·
    refine ⟨324353280828797889211344293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216235520552531926140896195 324353280828797889211344293)
    ·
      refine ⟨60816240155399604227127055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 324353280828797889211344293 60816240155399604227127055)
      ·
        refine ⟨91224360233099406340690583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60816240155399604227127055 91224360233099406340690583)
        ·
          refine ⟨136836540349649109511035875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91224360233099406340690583 136836540349649109511035875)
          ·
            refine ⟨205254810524473664266553813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136836540349649109511035875 205254810524473664266553813)
            ·
              refine ⟨4810659621667351506247355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 205254810524473664266553813 4810659621667351506247355)
              ·
                refine ⟨7215989432501027259371033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4810659621667351506247355 7215989432501027259371033)
                ·
                  refine ⟨5411992074375770444528275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7215989432501027259371033 5411992074375770444528275)
                  ·
                    refine ⟨8117988111563655666792413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5411992074375770444528275 8117988111563655666792413)
                    ·
                      refine ⟨3044245541836370875047155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8117988111563655666792413 3044245541836370875047155)
                      ·
                        rfl

theorem cell23_5928647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 2, 1, 3].length) (baseStart_5928647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928647 prefixEnd_5928647 := by exact prefixLift 5928647
  have htrace : WordTrace (prefixWord ++ tailWord_5928647) baseStart_5928647 baseEnd_5928647 := by
    simpa [prefixWord, tailWord_5928647, baseEnd_5928647] using wordTrace_append hprefix tailTrace_5928647
  have hstable : (prefixWord ++ tailWord_5928647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928647).length < 2 ^ (prefixWord ++ tailWord_5928647).sum := by decide
  have hdescent : baseEnd_5928647 < baseStart_5928647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928657 : List Nat := [1, 2, 2, 1, 2, 5, 2, 2, 1, 3, 2]
def baseStart_5928657 : Nat := 118140960795 + 5928657 * 2 ^ 59
def prefixEnd_5928657 : Nat := 4983230072969 + 3 ^ 40 * 5928657 * 2
def baseEnd_5928657 : Nat := 3044250676642915835922109

theorem tailTrace_5928657 : CollatzResearch.WordTrace tailWord_5928657 prefixEnd_5928657 3044250676642915835922109 := by
  unfold tailWord_5928657
  simp only [CollatzResearch.WordTrace]
  refine ⟨216235885282495697848760225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144157256854997131899173483 216235885282495697848760225)
  ·
    refine ⟨162176913961871773386570169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216235885282495697848760225 162176913961871773386570169)
    ·
      refine ⟨121632685471403830039927627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162176913961871773386570169 121632685471403830039927627)
      ·
        refine ⟨182449028207105745059891441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121632685471403830039927627 182449028207105745059891441)
        ·
          refine ⟨136836771155329308794918581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182449028207105745059891441 136836771155329308794918581)
          ·
            refine ⟨12828447295812122699523617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136836771155329308794918581 12828447295812122699523617)
            ·
              refine ⟨9621335471859092024642713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12828447295812122699523617 9621335471859092024642713)
              ·
                refine ⟨7216001603894319018482035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9621335471859092024642713 7216001603894319018482035)
                ·
                  refine ⟨10824002405841478527723053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7216001603894319018482035 10824002405841478527723053)
                  ·
                    refine ⟨4059000902190554447896145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10824002405841478527723053 4059000902190554447896145)
                    ·
                      refine ⟨3044250676642915835922109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4059000902190554447896145 3044250676642915835922109)
                      ·
                        rfl

theorem cell23_5928657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 1, 3, 2].length) (baseStart_5928657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928657 prefixEnd_5928657 := by exact prefixLift 5928657
  have htrace : WordTrace (prefixWord ++ tailWord_5928657) baseStart_5928657 baseEnd_5928657 := by
    simpa [prefixWord, tailWord_5928657, baseEnd_5928657] using wordTrace_append hprefix tailTrace_5928657
  have hstable : (prefixWord ++ tailWord_5928657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928657).length < 2 ^ (prefixWord ++ tailWord_5928657).sum := by decide
  have hdescent : baseEnd_5928657 < baseStart_5928657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928687 : List Nat := [1, 1, 2, 1, 5, 1, 2, 4, 2, 2, 2]
def baseStart_5928687 : Nat := 118140960795 + 5928687 * 2 ^ 59
def prefixEnd_5928687 : Nat := 4983230072969 + 3 ^ 40 * 5928687 * 2
def baseEnd_5928687 : Nat := 3044266081062550718546971

theorem tailTrace_5928687 : CollatzResearch.WordTrace tailWord_5928687 prefixEnd_5928687 3044266081062550718546971 := by
  unfold tailWord_5928687
  simp only [CollatzResearch.WordTrace]
  refine ⟨216236979472387012972352315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144157986314924675314901543 216236979472387012972352315)
  ·
    refine ⟨324355469208580519458528473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216236979472387012972352315 324355469208580519458528473)
    ·
      refine ⟨243266601906435389593896355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324355469208580519458528473 243266601906435389593896355)
      ·
        refine ⟨364899902859653084390844533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243266601906435389593896355 364899902859653084390844533)
        ·
          refine ⟨34209365893092476661641675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 364899902859653084390844533 34209365893092476661641675)
          ·
            refine ⟨51314048839638714992462513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34209365893092476661641675 51314048839638714992462513)
            ·
              refine ⟨38485536629729036244346885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51314048839638714992462513 38485536629729036244346885)
              ·
                refine ⟨7216038118074194295815041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38485536629729036244346885 7216038118074194295815041)
                ·
                  refine ⟨5412028588555645721861281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7216038118074194295815041 5412028588555645721861281)
                  ·
                    refine ⟨4059021441416734291395961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5412028588555645721861281 4059021441416734291395961)
                    ·
                      refine ⟨3044266081062550718546971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4059021441416734291395961 3044266081062550718546971)
                      ·
                        rfl

theorem cell23_5928687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 2, 2, 2].length) (baseStart_5928687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928687 prefixEnd_5928687 := by exact prefixLift 5928687
  have htrace : WordTrace (prefixWord ++ tailWord_5928687) baseStart_5928687 baseEnd_5928687 := by
    simpa [prefixWord, tailWord_5928687, baseEnd_5928687] using wordTrace_append hprefix tailTrace_5928687
  have hstable : (prefixWord ++ tailWord_5928687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928687).length < 2 ^ (prefixWord ++ tailWord_5928687).sum := by decide
  have hdescent : baseEnd_5928687 < baseStart_5928687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928696 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 2, 1, 8]
def baseStart_5928696 : Nat := 118140960795 + 5928696 * 2 ^ 59
def prefixEnd_5928696 : Nat := 4983230072969 + 3 ^ 40 * 5928696 * 2
def baseEnd_5928696 : Nat := 3044270702388441183334429

theorem tailTrace_5928696 : CollatzResearch.WordTrace tailWord_5928696 prefixEnd_5928696 3044270702388441183334429 := by
  unfold tailWord_5928696
  simp only [CollatzResearch.WordTrace]
  refine ⟨108118653864677203754714971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144158205152902938339619961 108118653864677203754714971)
  ·
    refine ⟨162177980797015805632072457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108118653864677203754714971 162177980797015805632072457)
    ·
      refine ⟨121633485597761854224054343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162177980797015805632072457 121633485597761854224054343)
      ·
        refine ⟨182450228396642781336081515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121633485597761854224054343 182450228396642781336081515)
        ·
          refine ⟨273675342594964172004122273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182450228396642781336081515 273675342594964172004122273)
          ·
            refine ⟨205256506946223129003091705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273675342594964172004122273 205256506946223129003091705)
            ·
              refine ⟨153942380209667346752318779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205256506946223129003091705 153942380209667346752318779)
              ·
                refine ⟨230913570314501020128478169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153942380209667346752318779 230913570314501020128478169)
                ·
                  refine ⟨173185177735875765096358627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230913570314501020128478169 173185177735875765096358627)
                  ·
                    refine ⟨259777766603813647644537941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 173185177735875765096358627 259777766603813647644537941)
                    ·
                      refine ⟨3044270702388441183334429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 259777766603813647644537941 3044270702388441183334429)
                      ·
                        rfl

theorem cell23_5928696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_5928696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928696 prefixEnd_5928696 := by exact prefixLift 5928696
  have htrace : WordTrace (prefixWord ++ tailWord_5928696) baseStart_5928696 baseEnd_5928696 := by
    simpa [prefixWord, tailWord_5928696, baseEnd_5928696] using wordTrace_append hprefix tailTrace_5928696
  have hstable : (prefixWord ++ tailWord_5928696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928696).length < 2 ^ (prefixWord ++ tailWord_5928696).sum := by decide
  have hdescent : baseEnd_5928696 < baseStart_5928696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928703 : List Nat := [1, 1, 2, 2, 1, 3, 2, 3, 2, 3, 3]
def baseStart_5928703 : Nat := 118140960795 + 5928703 * 2 ^ 59
def prefixEnd_5928703 : Nat := 4983230072969 + 3 ^ 40 * 5928703 * 2
def baseEnd_5928703 : Nat := 3044274296753022655946897

theorem tailTrace_5928703 : CollatzResearch.WordTrace tailWord_5928703 prefixEnd_5928703 3044274296753022655946897 := by
  unfold tailWord_5928703
  simp only [CollatzResearch.WordTrace]
  refine ⟨216237563040329047704934763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144158375360219365136623175 216237563040329047704934763)
  ·
    refine ⟨324356344560493571557402145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216237563040329047704934763 324356344560493571557402145)
    ·
      refine ⟨243267258420370178668051609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324356344560493571557402145 243267258420370178668051609)
      ·
        refine ⟨182450443815277634001038707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243267258420370178668051609 182450443815277634001038707)
        ·
          refine ⟨273675665722916451001558061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182450443815277634001038707 273675665722916451001558061)
          ·
            refine ⟨102628374646093669125584273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273675665722916451001558061 102628374646093669125584273)
            ·
              refine ⟨76971280984570251844188205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102628374646093669125584273 76971280984570251844188205)
              ·
                refine ⟨28864230369213844441570577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76971280984570251844188205 28864230369213844441570577)
                ·
                  refine ⟨21648172776910383331177933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28864230369213844441570577 21648172776910383331177933)
                  ·
                    refine ⟨8118064791341393749191725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21648172776910383331177933 8118064791341393749191725)
                    ·
                      refine ⟨3044274296753022655946897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8118064791341393749191725 3044274296753022655946897)
                      ·
                        rfl

theorem cell23_5928703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 3, 3].length) (baseStart_5928703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928703 prefixEnd_5928703 := by exact prefixLift 5928703
  have htrace : WordTrace (prefixWord ++ tailWord_5928703) baseStart_5928703 baseEnd_5928703 := by
    simpa [prefixWord, tailWord_5928703, baseEnd_5928703] using wordTrace_append hprefix tailTrace_5928703
  have hstable : (prefixWord ++ tailWord_5928703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928703).length < 2 ^ (prefixWord ++ tailWord_5928703).sum := by decide
  have hdescent : baseEnd_5928703 < baseStart_5928703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928740 : List Nat := [2, 3, 1, 3, 2, 1, 2, 2, 2, 5]
def baseStart_5928740 : Nat := 118140960795 + 5928740 * 2 ^ 59
def prefixEnd_5928740 : Nat := 4983230072969 + 3 ^ 40 * 5928740 * 2
def baseEnd_5928740 : Nat := 1014764431845746337061409

theorem tailTrace_5928740 : CollatzResearch.WordTrace tailWord_5928740 prefixEnd_5928740 1014764431845746337061409 := by
  unfold tailWord_5928740
  simp only [CollatzResearch.WordTrace]
  refine ⟨108119456270597501512015837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144159275027463335349354449 108119456270597501512015837)
  ·
    refine ⟨40544796101474063067005939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108119456270597501512015837 40544796101474063067005939)
    ·
      refine ⟨60817194152211094600508909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40544796101474063067005939 60817194152211094600508909)
      ·
        refine ⟨22806447807079160475190841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60817194152211094600508909 22806447807079160475190841)
        ·
          refine ⟨17104835855309370356393131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22806447807079160475190841 17104835855309370356393131)
          ·
            refine ⟨25657253782964055534589697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17104835855309370356393131 25657253782964055534589697)
            ·
              refine ⟨19242940337223041650942273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25657253782964055534589697 19242940337223041650942273)
              ·
                refine ⟨14432205252917281238206705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19242940337223041650942273 14432205252917281238206705)
                ·
                  refine ⟨10824153939687960928655029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14432205252917281238206705 10824153939687960928655029)
                  ·
                    refine ⟨1014764431845746337061409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10824153939687960928655029 1014764431845746337061409)
                    ·
                      rfl

theorem cell23_5928740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_5928740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928740 prefixEnd_5928740 := by exact prefixLift 5928740
  have htrace : WordTrace (prefixWord ++ tailWord_5928740) baseStart_5928740 baseEnd_5928740 := by
    simpa [prefixWord, tailWord_5928740, baseEnd_5928740] using wordTrace_append hprefix tailTrace_5928740
  have hstable : (prefixWord ++ tailWord_5928740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928740).length < 2 ^ (prefixWord ++ tailWord_5928740).sum := by decide
  have hdescent : baseEnd_5928740 < baseStart_5928740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928744 : List Nat := [2, 1, 5, 1, 1, 4, 2, 2, 5]
def baseStart_5928744 : Nat := 118140960795 + 5928744 * 2 ^ 59
def prefixEnd_5928744 : Nat := 4983230072969 + 3 ^ 40 * 5928744 * 2
def baseEnd_5928744 : Nat := 338255038828872999503801

theorem tailTrace_5928744 : CollatzResearch.WordTrace tailWord_5928744 prefixEnd_5928744 338255038828872999503801 := by
  unfold tailWord_5928744
  simp only [CollatzResearch.WordTrace]
  refine ⟨108119529216590255853588643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144159372288787007804784857 108119529216590255853588643)
  ·
    refine ⟨162179293824885383780382965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108119529216590255853588643 162179293824885383780382965)
    ·
      refine ⟨15204308796083004729410903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162179293824885383780382965 15204308796083004729410903)
      ·
        refine ⟨22806463194124507094116355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15204308796083004729410903 22806463194124507094116355)
        ·
          refine ⟨34209694791186760641174533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22806463194124507094116355 34209694791186760641174533)
          ·
            refine ⟨6414317773347517620220225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34209694791186760641174533 6414317773347517620220225)
            ·
              refine ⟨4810738330010638215165169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6414317773347517620220225 4810738330010638215165169)
              ·
                refine ⟨3608053747507978661373877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4810738330010638215165169 3608053747507978661373877)
                ·
                  refine ⟨338255038828872999503801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3608053747507978661373877 338255038828872999503801)
                  ·
                    rfl

theorem cell23_5928744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2, 5].length) (baseStart_5928744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928744 prefixEnd_5928744 := by exact prefixLift 5928744
  have htrace : WordTrace (prefixWord ++ tailWord_5928744) baseStart_5928744 baseEnd_5928744 := by
    simpa [prefixWord, tailWord_5928744, baseEnd_5928744] using wordTrace_append hprefix tailTrace_5928744
  have hstable : (prefixWord ++ tailWord_5928744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928744).length < 2 ^ (prefixWord ++ tailWord_5928744).sum := by decide
  have hdescent : baseEnd_5928744 < baseStart_5928744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928760 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 1, 6, 2]
def baseStart_5928760 : Nat := 118140960795 + 5928760 * 2 ^ 59
def prefixEnd_5928760 : Nat := 4983230072969 + 3 ^ 40 * 5928760 * 2
def baseEnd_5928760 : Nat := 3044303565150328932934135

theorem tailTrace_5928760 : CollatzResearch.WordTrace tailWord_5928760 prefixEnd_5928760 3044303565150328932934135 := by
  unfold tailWord_5928760
  simp only [CollatzResearch.WordTrace]
  refine ⟨108119821000561273219879867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144159761334081697626506489 108119821000561273219879867)
  ·
    refine ⟨162179731500841909829819801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108119821000561273219879867 162179731500841909829819801)
    ·
      refine ⟨121634798625631432372364851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162179731500841909829819801 121634798625631432372364851)
      ·
        refine ⟨182452197938447148558547277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121634798625631432372364851 182452197938447148558547277)
        ·
          refine ⟨68419574226917680709455229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182452197938447148558547277 68419574226917680709455229)
          ·
            refine ⟨25657340335094130266045711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68419574226917680709455229 25657340335094130266045711)
            ·
              refine ⟨38486010502641195399068567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25657340335094130266045711 38486010502641195399068567)
              ·
                refine ⟨57729015753961793098602851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38486010502641195399068567 57729015753961793098602851)
                ·
                  refine ⟨86593523630942689647904277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57729015753961793098602851 86593523630942689647904277)
                  ·
                    refine ⟨4059071420200438577245513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86593523630942689647904277 4059071420200438577245513)
                    ·
                      refine ⟨3044303565150328932934135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4059071420200438577245513 3044303565150328932934135)
                      ·
                        rfl

theorem cell23_5928760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 1, 6, 2].length) (baseStart_5928760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928760 prefixEnd_5928760 := by exact prefixLift 5928760
  have htrace : WordTrace (prefixWord ++ tailWord_5928760) baseStart_5928760 baseEnd_5928760 := by
    simpa [prefixWord, tailWord_5928760, baseEnd_5928760] using wordTrace_append hprefix tailTrace_5928760
  have hstable : (prefixWord ++ tailWord_5928760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928760).length < 2 ^ (prefixWord ++ tailWord_5928760).sum := by decide
  have hdescent : baseEnd_5928760 < baseStart_5928760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928774 : List Nat := [6, 1, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_5928774 : Nat := 118140960795 + 5928774 * 2 ^ 59
def prefixEnd_5928774 : Nat := 4983230072969 + 3 ^ 40 * 5928774 * 2
def baseEnd_5928774 : Nat := 1014770251293163959386357

theorem tailTrace_5928774 : CollatzResearch.WordTrace tailWord_5928774 prefixEnd_5928774 1014770251293163959386357 := by
  unfold tailWord_5928774
  simp only [CollatzResearch.WordTrace]
  refine ⟨6757504769470994588461543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 144160101748714551220512917 6757504769470994588461543)
  ·
    refine ⟨10136257154206491882692315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6757504769470994588461543 10136257154206491882692315)
    ·
      refine ⟨15204385731309737824038473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10136257154206491882692315 15204385731309737824038473)
      ·
        refine ⟨11403289298482303368028855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15204385731309737824038473 11403289298482303368028855)
        ·
          refine ⟨17104933947723455052043283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11403289298482303368028855 17104933947723455052043283)
          ·
            refine ⟨25657400921585182578064925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17104933947723455052043283 25657400921585182578064925)
            ·
              refine ⟨9621525345594443466774347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25657400921585182578064925 9621525345594443466774347)
              ·
                refine ⟨14432288018391665200161521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9621525345594443466774347 14432288018391665200161521)
                ·
                  refine ⟨10824216013793748900121141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14432288018391665200161521 10824216013793748900121141)
                  ·
                    refine ⟨1014770251293163959386357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10824216013793748900121141 1014770251293163959386357)
                    ·
                      rfl

theorem cell23_5928774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_5928774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928774 prefixEnd_5928774 := by exact prefixLift 5928774
  have htrace : WordTrace (prefixWord ++ tailWord_5928774) baseStart_5928774 baseEnd_5928774 := by
    simpa [prefixWord, tailWord_5928774, baseEnd_5928774] using wordTrace_append hprefix tailTrace_5928774
  have hstable : (prefixWord ++ tailWord_5928774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928774).length < 2 ^ (prefixWord ++ tailWord_5928774).sum := by decide
  have hdescent : baseEnd_5928774 < baseStart_5928774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928800 : List Nat := [2, 1, 1, 3, 3, 2, 3, 2, 6]
def baseStart_5928800 : Nat := 118140960795 + 5928800 * 2 ^ 59
def prefixEnd_5928800 : Nat := 4983230072969 + 3 ^ 40 * 5928800 * 2
def baseEnd_5928800 : Nat := 338258233819612086270439

theorem tailTrace_5928800 : CollatzResearch.WordTrace tailWord_5928800 prefixEnd_5928800 338258233819612086270439 := by
  unfold tailWord_5928800
  simp only [CollatzResearch.WordTrace]
  refine ⟨108120550460488816635607927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144160733947318422180810569 108120550460488816635607927)
  ·
    refine ⟨162180825690733224953411891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108120550460488816635607927 162180825690733224953411891)
    ·
      refine ⟨243271238536099837430117837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162180825690733224953411891 243271238536099837430117837)
      ·
        refine ⟨91226714451037439036294189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243271238536099837430117837 91226714451037439036294189)
        ·
          refine ⟨34210017919139039638610321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91226714451037439036294189 34210017919139039638610321)
          ·
            refine ⟨25657513439354279728957741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34210017919139039638610321 25657513439354279728957741)
            ·
              refine ⟨9621567539757854898359153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25657513439354279728957741 9621567539757854898359153)
              ·
                refine ⟨7216175654818391173769365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9621567539757854898359153 7216175654818391173769365)
                ·
                  refine ⟨338258233819612086270439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7216175654818391173769365 338258233819612086270439)
                  ·
                    rfl

theorem cell23_5928800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 6].length) (baseStart_5928800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928800 prefixEnd_5928800 := by exact prefixLift 5928800
  have htrace : WordTrace (prefixWord ++ tailWord_5928800) baseStart_5928800 baseEnd_5928800 := by
    simpa [prefixWord, tailWord_5928800, baseEnd_5928800] using wordTrace_append hprefix tailTrace_5928800
  have hstable : (prefixWord ++ tailWord_5928800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928800).length < 2 ^ (prefixWord ++ tailWord_5928800).sum := by decide
  have hdescent : baseEnd_5928800 < baseStart_5928800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928837 : List Nat := [1, 3, 1, 1, 3, 2, 2, 3, 2, 3, 2]
def baseStart_5928837 : Nat := 118140960795 + 5928837 * 2 ^ 59
def prefixEnd_5928837 : Nat := 4983230072969 + 3 ^ 40 * 5928837 * 2
def baseEnd_5928837 : Nat := 3044343103160725131671281

theorem tailTrace_5928837 : CollatzResearch.WordTrace tailWord_5928837 prefixEnd_5928837 3044343103160725131671281 := by
  unfold tailWord_5928837
  simp only [CollatzResearch.WordTrace]
  refine ⟨216242450421843588590312765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144161633614562392393541843 216242450421843588590312765)
  ·
    refine ⟨81090918908191345721367287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216242450421843588590312765 81090918908191345721367287)
    ·
      refine ⟨121636378362287018582050931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81090918908191345721367287 121636378362287018582050931)
      ·
        refine ⟨182454567543430527873076397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121636378362287018582050931 182454567543430527873076397)
        ·
          refine ⟨68420462828786447952403649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182454567543430527873076397 68420462828786447952403649)
          ·
            refine ⟨51315347121589835964302737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68420462828786447952403649 51315347121589835964302737)
            ·
              refine ⟨38486510341192376973227053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51315347121589835964302737 38486510341192376973227053)
              ·
                refine ⟨14432441377947141364960145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38486510341192376973227053 14432441377947141364960145)
                ·
                  refine ⟨10824331033460356023720109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14432441377947141364960145 10824331033460356023720109)
                  ·
                    refine ⟨4059124137547633508895041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10824331033460356023720109 4059124137547633508895041)
                    ·
                      refine ⟨3044343103160725131671281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4059124137547633508895041 3044343103160725131671281)
                      ·
                        rfl

theorem cell23_5928837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 3, 2].length) (baseStart_5928837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928837 prefixEnd_5928837 := by exact prefixLift 5928837
  have htrace : WordTrace (prefixWord ++ tailWord_5928837) baseStart_5928837 baseEnd_5928837 := by
    simpa [prefixWord, tailWord_5928837, baseEnd_5928837] using wordTrace_append hprefix tailTrace_5928837
  have hstable : (prefixWord ++ tailWord_5928837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928837).length < 2 ^ (prefixWord ++ tailWord_5928837).sum := by decide
  have hdescent : baseEnd_5928837 < baseStart_5928837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928843 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 3, 6]
def baseStart_5928843 : Nat := 118140960795 + 5928843 * 2 ^ 59
def prefixEnd_5928843 : Nat := 4983230072969 + 3 ^ 40 * 5928843 * 2
def baseEnd_5928843 : Nat := 1014782061348217369398751

theorem tailTrace_5928843 : CollatzResearch.WordTrace tailWord_5928843 prefixEnd_5928843 1014782061348217369398751 := by
  unfold tailWord_5928843
  simp only [CollatzResearch.WordTrace]
  refine ⟨216242669259821851615031183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144161779506547901076687455 216242669259821851615031183)
  ·
    refine ⟨324364003889732777422546775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216242669259821851615031183 324364003889732777422546775)
    ·
      refine ⟨486546005834599166133820163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324364003889732777422546775 486546005834599166133820163)
      ·
        refine ⟨729819008751898749200730245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486546005834599166133820163 729819008751898749200730245)
        ·
          refine ⟨136841064140981015475136921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 729819008751898749200730245 136841064140981015475136921)
          ·
            refine ⟨102630798105735761606352691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136841064140981015475136921 102630798105735761606352691)
            ·
              refine ⟨153946197158603642409529037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102630798105735761606352691 153946197158603642409529037)
              ·
                refine ⟨57729823934476365903573389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153946197158603642409529037 57729823934476365903573389)
                ·
                  refine ⟨21648683975428637213840021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57729823934476365903573389 21648683975428637213840021)
                  ·
                    refine ⟨1014782061348217369398751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21648683975428637213840021 1014782061348217369398751)
                    ·
                      rfl

theorem cell23_5928843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 6].length) (baseStart_5928843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928843 prefixEnd_5928843 := by exact prefixLift 5928843
  have htrace : WordTrace (prefixWord ++ tailWord_5928843) baseStart_5928843 baseEnd_5928843 := by
    simpa [prefixWord, tailWord_5928843, baseEnd_5928843] using wordTrace_append hprefix tailTrace_5928843
  have hstable : (prefixWord ++ tailWord_5928843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928843).length < 2 ^ (prefixWord ++ tailWord_5928843).sum := by decide
  have hdescent : baseEnd_5928843 < baseStart_5928843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5928960 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 3]
def baseStart_5928960 : Nat := 118140960795 + 5928960 * 2 ^ 59
def prefixEnd_5928960 : Nat := 4983230072969 + 3 ^ 40 * 5928960 * 2
def baseEnd_5928960 : Nat := 3044406261281228150433215

theorem tailTrace_5928960 : CollatzResearch.WordTrace tailWord_5928960 prefixEnd_5928960 3044406261281228150433215 := by
  unfold tailWord_5928960
  simp only [CollatzResearch.WordTrace]
  refine ⟨108123468300198990298520167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144164624400265320398026889 108123468300198990298520167)
  ·
    refine ⟨162185202450298485447780251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108123468300198990298520167 162185202450298485447780251)
    ·
      refine ⟨243277803675447728171670377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162185202450298485447780251 243277803675447728171670377)
      ·
        refine ⟨182458352756585796128752783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243277803675447728171670377 182458352756585796128752783)
        ·
          refine ⟨273687529134878694193129175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182458352756585796128752783 273687529134878694193129175)
          ·
            refine ⟨410531293702318041289693763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273687529134878694193129175 410531293702318041289693763)
            ·
              refine ⟨615796940553477061934540645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410531293702318041289693763 615796940553477061934540645)
              ·
                refine ⟨115461926353776949112726371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 615796940553477061934540645 115461926353776949112726371)
                ·
                  refine ⟨173192889530665423669089557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115461926353776949112726371 173192889530665423669089557)
                  ·
                    refine ⟨8118416696749941734488573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 173192889530665423669089557 8118416696749941734488573)
                    ·
                      refine ⟨3044406261281228150433215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8118416696749941734488573 3044406261281228150433215)
                      ·
                        rfl

theorem cell23_5928960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 3].length) (baseStart_5928960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5928960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5928960 prefixEnd_5928960 := by exact prefixLift 5928960
  have htrace : WordTrace (prefixWord ++ tailWord_5928960) baseStart_5928960 baseEnd_5928960 := by
    simpa [prefixWord, tailWord_5928960, baseEnd_5928960] using wordTrace_append hprefix tailTrace_5928960
  have hstable : (prefixWord ++ tailWord_5928960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5928960).length < 2 ^ (prefixWord ++ tailWord_5928960).sum := by decide
  have hdescent : baseEnd_5928960 < baseStart_5928960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5928960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929042 : List Nat := [3, 2, 2, 1, 5, 1, 2, 1, 2, 2, 2]
def baseStart_5929042 : Nat := 118140960795 + 5929042 * 2 ^ 59
def prefixEnd_5929042 : Nat := 4983230072969 + 3 ^ 40 * 5929042 * 2
def baseEnd_5929042 : Nat := 3044448366694896829607839

theorem tailTrace_5929042 : CollatzResearch.WordTrace tailWord_5929042 prefixEnd_5929042 3044448366694896829607839 := by
  unfold tailWord_5929042
  simp only [CollatzResearch.WordTrace]
  refine ⟨54062481846525227150381345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144166618257400605734350253 54062481846525227150381345)
  ·
    refine ⟨40546861384893920362786009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54062481846525227150381345 40546861384893920362786009)
    ·
      refine ⟨30410146038670440272089507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40546861384893920362786009 30410146038670440272089507)
      ·
        refine ⟨45615219058005660408134261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30410146038670440272089507 45615219058005660408134261)
        ·
          refine ⟨4276426786688030663262587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45615219058005660408134261 4276426786688030663262587)
          ·
            refine ⟨6414640180032045994893881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4276426786688030663262587 6414640180032045994893881)
            ·
              refine ⟨4810980135024034496170411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6414640180032045994893881 4810980135024034496170411)
              ·
                refine ⟨7216470202536051744255617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4810980135024034496170411 7216470202536051744255617)
                ·
                  refine ⟨5412352651902038808191713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7216470202536051744255617 5412352651902038808191713)
                  ·
                    refine ⟨4059264488926529106143785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5412352651902038808191713 4059264488926529106143785)
                    ·
                      refine ⟨3044448366694896829607839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4059264488926529106143785 3044448366694896829607839)
                      ·
                        rfl

theorem cell23_5929042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_5929042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929042 prefixEnd_5929042 := by exact prefixLift 5929042
  have htrace : WordTrace (prefixWord ++ tailWord_5929042) baseStart_5929042 baseEnd_5929042 := by
    simpa [prefixWord, tailWord_5929042, baseEnd_5929042] using wordTrace_append hprefix tailTrace_5929042
  have hstable : (prefixWord ++ tailWord_5929042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929042).length < 2 ^ (prefixWord ++ tailWord_5929042).sum := by decide
  have hdescent : baseEnd_5929042 < baseStart_5929042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929057 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 5, 4]
def baseStart_5929057 : Nat := 118140960795 + 5929057 * 2 ^ 59
def prefixEnd_5929057 : Nat := 4983230072969 + 3 ^ 40 * 5929057 * 2
def baseEnd_5929057 : Nat := 1014818689634904756973423

theorem tailTrace_5929057 : CollatzResearch.WordTrace tailWord_5929057 prefixEnd_5929057 1014818689634904756973423 := by
  unfold tailWord_5929057
  simp only [CollatzResearch.WordTrace]
  refine ⟨216250474481046566163321425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144166982987364377442214283 216250474481046566163321425)
  ·
    refine ⟨162187855860784924622491069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216250474481046566163321425 162187855860784924622491069)
    ·
      refine ⟨60820445947794346733434151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162187855860784924622491069 60820445947794346733434151)
      ·
        refine ⟨91230668921691520100151227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60820445947794346733434151 91230668921691520100151227)
        ·
          refine ⟨136846003382537280150226841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91230668921691520100151227 136846003382537280150226841)
          ·
            refine ⟨102634502536902960112670131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136846003382537280150226841 102634502536902960112670131)
            ·
              refine ⟨153951753805354440169005197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102634502536902960112670131 153951753805354440169005197)
              ·
                refine ⟨57731907677007915063376949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153951753805354440169005197 57731907677007915063376949)
                ·
                  refine ⟨5412366344719492037191589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57731907677007915063376949 5412366344719492037191589)
                  ·
                    refine ⟨1014818689634904756973423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5412366344719492037191589 1014818689634904756973423)
                    ·
                      rfl

theorem cell23_5929057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_5929057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929057 prefixEnd_5929057 := by exact prefixLift 5929057
  have htrace : WordTrace (prefixWord ++ tailWord_5929057) baseStart_5929057 baseEnd_5929057 := by
    simpa [prefixWord, tailWord_5929057, baseEnd_5929057] using wordTrace_append hprefix tailTrace_5929057
  have hstable : (prefixWord ++ tailWord_5929057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929057).length < 2 ^ (prefixWord ++ tailWord_5929057).sum := by decide
  have hdescent : baseEnd_5929057 < baseStart_5929057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929084 : List Nat := [2, 2, 2, 1, 1, 4, 2, 2, 2, 2, 3]
def baseStart_5929084 : Nat := 118140960795 + 5929084 * 2 ^ 59
def prefixEnd_5929084 : Nat := 4983230072969 + 3 ^ 40 * 5929084 * 2
def baseEnd_5929084 : Nat := 3044469932882385665282645

theorem tailTrace_5929084 : CollatzResearch.WordTrace tailWord_5929084 prefixEnd_5929084 3044469932882385665282645 := by
  unfold tailWord_5929084
  simp only [CollatzResearch.WordTrace]
  refine ⟨108125729625974374887277153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144167639501299166516369537 108125729625974374887277153)
  ·
    refine ⟨81094297219480781165457865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108125729625974374887277153 81094297219480781165457865)
    ·
      refine ⟨60820722914610585874093399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81094297219480781165457865 60820722914610585874093399)
      ·
        refine ⟨91231084371915878811140099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60820722914610585874093399 91231084371915878811140099)
        ·
          refine ⟨136846626557873818216710149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91231084371915878811140099 136846626557873818216710149)
          ·
            refine ⟨25658742479601340915633153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136846626557873818216710149 25658742479601340915633153)
            ·
              refine ⟨19244056859701005686724865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25658742479601340915633153 19244056859701005686724865)
              ·
                refine ⟨14433042644775754265043649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19244056859701005686724865 14433042644775754265043649)
                ·
                  refine ⟨10824781983581815698782737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14433042644775754265043649 10824781983581815698782737)
                  ·
                    refine ⟨8118586487686361774087053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10824781983581815698782737 8118586487686361774087053)
                    ·
                      refine ⟨3044469932882385665282645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8118586487686361774087053 3044469932882385665282645)
                      ·
                        rfl

theorem cell23_5929084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_5929084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929084 prefixEnd_5929084 := by exact prefixLift 5929084
  have htrace : WordTrace (prefixWord ++ tailWord_5929084) baseStart_5929084 baseEnd_5929084 := by
    simpa [prefixWord, tailWord_5929084, baseEnd_5929084] using wordTrace_append hprefix tailTrace_5929084
  have hstable : (prefixWord ++ tailWord_5929084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929084).length < 2 ^ (prefixWord ++ tailWord_5929084).sum := by decide
  have hdescent : baseEnd_5929084 < baseStart_5929084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929091 : List Nat := [1, 1, 1, 3, 3, 4, 1, 4, 1, 4]
def baseStart_5929091 : Nat := 118140960795 + 5929091 * 2 ^ 59
def prefixEnd_5929091 : Nat := 4983230072969 + 3 ^ 40 * 5929091 * 2
def baseEnd_5929091 : Nat := 1014824509082322379298371

theorem tailTrace_5929091 : CollatzResearch.WordTrace tailWord_5929091 prefixEnd_5929091 1014824509082322379298371 := by
  unfold tailWord_5929091
  simp only [CollatzResearch.WordTrace]
  refine ⟨216251714562923389970059127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144167809708615593313372751 216251714562923389970059127)
  ·
    refine ⟨324377571844385084955088691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216251714562923389970059127 324377571844385084955088691)
    ·
      refine ⟨486566357766577627432633037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324377571844385084955088691 486566357766577627432633037)
      ·
        refine ⟨182462384162466610287237389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 486566357766577627432633037 182462384162466610287237389)
        ·
          refine ⟨68423394060924978857714021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182462384162466610287237389 68423394060924978857714021)
          ·
            refine ⟨12829386386423433535821379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68423394060924978857714021 12829386386423433535821379)
            ·
              refine ⟨19244079579635150303732069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12829386386423433535821379 19244079579635150303732069)
              ·
                refine ⟨3608264921181590681949763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19244079579635150303732069 3608264921181590681949763)
                ·
                  refine ⟨5412397381772386022924645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3608264921181590681949763 5412397381772386022924645)
                  ·
                    refine ⟨1014824509082322379298371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5412397381772386022924645 1014824509082322379298371)
                    ·
                      rfl

theorem cell23_5929091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4, 1, 4].length) (baseStart_5929091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929091 prefixEnd_5929091 := by exact prefixLift 5929091
  have htrace : WordTrace (prefixWord ++ tailWord_5929091) baseStart_5929091 baseEnd_5929091 := by
    simpa [prefixWord, tailWord_5929091, baseEnd_5929091] using wordTrace_append hprefix tailTrace_5929091
  have hstable : (prefixWord ++ tailWord_5929091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929091).length < 2 ^ (prefixWord ++ tailWord_5929091).sum := by decide
  have hdescent : baseEnd_5929091 < baseStart_5929091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929108 : List Nat := [2, 4, 2, 3, 1, 1, 1, 2, 3, 4]
def baseStart_5929108 : Nat := 118140960795 + 5929108 * 2 ^ 59
def prefixEnd_5929108 : Nat := 4983230072969 + 3 ^ 40 * 5929108 * 2
def baseEnd_5929108 : Nat := 1014827418806031190460845

theorem tailTrace_5929108 : CollatzResearch.WordTrace tailWord_5929108 prefixEnd_5929108 1014827418806031190460845 := by
  unfold tailWord_5929108
  simp only [CollatzResearch.WordTrace]
  refine ⟨108126167301930900936713989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144168223069241201248951985 108126167301930900936713989)
  ·
    refine ⟨20273656369112043925633873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108126167301930900936713989 20273656369112043925633873)
    ·
      refine ⟨15205242276834032944225405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20273656369112043925633873 15205242276834032944225405)
      ·
        refine ⟨5701965853812762354084527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15205242276834032944225405 5701965853812762354084527)
        ·
          refine ⟨8552948780719143531126791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5701965853812762354084527 8552948780719143531126791)
          ·
            refine ⟨12829423171078715296690187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8552948780719143531126791 12829423171078715296690187)
            ·
              refine ⟨19244134756618072945035281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12829423171078715296690187 19244134756618072945035281)
              ·
                refine ⟨14433101067463554708776461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19244134756618072945035281 14433101067463554708776461)
                ·
                  refine ⟨5412412900298833015791173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14433101067463554708776461 5412412900298833015791173)
                  ·
                    refine ⟨1014827418806031190460845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5412412900298833015791173 1014827418806031190460845)
                    ·
                      rfl

theorem cell23_5929108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_5929108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929108 prefixEnd_5929108 := by exact prefixLift 5929108
  have htrace : WordTrace (prefixWord ++ tailWord_5929108) baseStart_5929108 baseEnd_5929108 := by
    simpa [prefixWord, tailWord_5929108, baseEnd_5929108] using wordTrace_append hprefix tailTrace_5929108
  have hstable : (prefixWord ++ tailWord_5929108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929108).length < 2 ^ (prefixWord ++ tailWord_5929108).sum := by decide
  have hdescent : baseEnd_5929108 < baseStart_5929108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929148 : List Nat := [2, 2, 2, 3, 3, 1, 2, 1, 3, 1, 3]
def baseStart_5929148 : Nat := 118140960795 + 5929148 * 2 ^ 59
def prefixEnd_5929148 : Nat := 4983230072969 + 3 ^ 40 * 5929148 * 2
def baseEnd_5929148 : Nat := 3044502795644273414882351

theorem tailTrace_5929148 : CollatzResearch.WordTrace tailWord_5929148 prefixEnd_5929148 3044502795644273414882351 := by
  unfold tailWord_5929148
  simp only [CollatzResearch.WordTrace]
  refine ⟨108126896761858444352442049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144169195682477925803256065 108126896761858444352442049)
  ·
    refine ⟨81095172571393833264331537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108126896761858444352442049 81095172571393833264331537)
    ·
      refine ⟨60821379428545374948248653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81095172571393833264331537 60821379428545374948248653)
      ·
        refine ⟨22808017285704515605593245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60821379428545374948248653 22808017285704515605593245)
        ·
          refine ⟨8553006482139193352097467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22808017285704515605593245 8553006482139193352097467)
          ·
            refine ⟨12829509723208790028146201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8553006482139193352097467 12829509723208790028146201)
            ·
              refine ⟨9622132292406592521109651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12829509723208790028146201 9622132292406592521109651)
              ·
                refine ⟨14433198438609888781664477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9622132292406592521109651 14433198438609888781664477)
                ·
                  refine ⟨5412449414478708293124179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14433198438609888781664477 5412449414478708293124179)
                  ·
                    refine ⟨8118674121718062439686269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5412449414478708293124179 8118674121718062439686269)
                    ·
                      refine ⟨3044502795644273414882351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8118674121718062439686269 3044502795644273414882351)
                      ·
                        rfl

theorem cell23_5929148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_5929148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929148 prefixEnd_5929148 := by exact prefixLift 5929148
  have htrace : WordTrace (prefixWord ++ tailWord_5929148) baseStart_5929148 baseEnd_5929148 := by
    simpa [prefixWord, tailWord_5929148, baseEnd_5929148] using wordTrace_append hprefix tailTrace_5929148
  have hstable : (prefixWord ++ tailWord_5929148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929148).length < 2 ^ (prefixWord ++ tailWord_5929148).sum := by decide
  have hdescent : baseEnd_5929148 < baseStart_5929148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929157 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 3, 1, 5]
def baseStart_5929157 : Nat := 118140960795 + 5929157 * 2 ^ 59
def prefixEnd_5929157 : Nat := 4983230072969 + 3 ^ 40 * 5929157 * 2
def baseEnd_5929157 : Nat := 3044507416970163879669809

theorem tailTrace_5929157 : CollatzResearch.WordTrace tailWord_5929157 prefixEnd_5929157 3044507416970163879669809 := by
  unfold tailWord_5929157
  simp only [CollatzResearch.WordTrace]
  refine ⟨216254121780684283241961725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144169414520456188827974483 216254121780684283241961725)
  ·
    refine ⟨81095295667756606215735647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216254121780684283241961725 81095295667756606215735647)
    ·
      refine ⟨121642943501634909323603471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81095295667756606215735647 121642943501634909323603471)
      ·
        refine ⟨182464415252452363985405207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121642943501634909323603471 182464415252452363985405207)
        ·
          refine ⟨273696622878678545978107811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182464415252452363985405207 273696622878678545978107811)
          ·
            refine ⟨410544934318017818967161717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273696622878678545978107811 410544934318017818967161717)
            ·
              refine ⟨38488587592314170528171411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 410544934318017818967161717 38488587592314170528171411)
              ·
                refine ⟨57732881388471255792257117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38488587592314170528171411 57732881388471255792257117)
                ·
                  refine ⟨21649830520676720922096419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57732881388471255792257117 21649830520676720922096419)
                  ·
                    refine ⟨32474745781015081383144629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21649830520676720922096419 32474745781015081383144629)
                    ·
                      refine ⟨3044507416970163879669809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32474745781015081383144629 3044507416970163879669809)
                      ·
                        rfl

theorem cell23_5929157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_5929157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929157 prefixEnd_5929157 := by exact prefixLift 5929157
  have htrace : WordTrace (prefixWord ++ tailWord_5929157) baseStart_5929157 baseEnd_5929157 := by
    simpa [prefixWord, tailWord_5929157, baseEnd_5929157] using wordTrace_append hprefix tailTrace_5929157
  have hstable : (prefixWord ++ tailWord_5929157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929157).length < 2 ^ (prefixWord ++ tailWord_5929157).sum := by decide
  have hdescent : baseEnd_5929157 < baseStart_5929157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929167 : List Nat := [1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 6]
def baseStart_5929167 : Nat := 118140960795 + 5929167 * 2 ^ 59
def prefixEnd_5929167 : Nat := 4983230072969 + 3 ^ 40 * 5929167 * 2
def baseEnd_5929167 : Nat := 3044512551776708840544763

theorem tailTrace_5929167 : CollatzResearch.WordTrace tailWord_5929167 prefixEnd_5929167 3044512551776708840544763 := by
  unfold tailWord_5929167
  simp only [CollatzResearch.WordTrace]
  refine ⟨216254486510648054949825755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144169657673765369966550503 216254486510648054949825755)
  ·
    refine ⟨324381729765972082424738633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216254486510648054949825755 324381729765972082424738633)
    ·
      refine ⟨243286297324479061818553975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324381729765972082424738633 243286297324479061818553975)
      ·
        refine ⟨364929445986718592727830963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243286297324479061818553975 364929445986718592727830963)
        ·
          refine ⟨547394168980077889091746445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364929445986718592727830963 547394168980077889091746445)
          ·
            refine ⟨205272813367529208409404917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 547394168980077889091746445 205272813367529208409404917)
            ·
              refine ⟨19244326253205863288381711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 205272813367529208409404917 19244326253205863288381711)
              ·
                refine ⟨28866489379808794932572567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19244326253205863288381711 28866489379808794932572567)
                ·
                  refine ⟨43299734069713192398858851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28866489379808794932572567 43299734069713192398858851)
                  ·
                    refine ⟨64949601104569788598288277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43299734069713192398858851 64949601104569788598288277)
                    ·
                      refine ⟨3044512551776708840544763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64949601104569788598288277 3044512551776708840544763)
                      ·
                        rfl

theorem cell23_5929167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 6].length) (baseStart_5929167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929167 prefixEnd_5929167 := by exact prefixLift 5929167
  have htrace : WordTrace (prefixWord ++ tailWord_5929167) baseStart_5929167 baseEnd_5929167 := by
    simpa [prefixWord, tailWord_5929167, baseEnd_5929167] using wordTrace_append hprefix tailTrace_5929167
  have hstable : (prefixWord ++ tailWord_5929167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929167).length < 2 ^ (prefixWord ++ tailWord_5929167).sum := by decide
  have hdescent : baseEnd_5929167 < baseStart_5929167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929181 : List Nat := [1, 4, 3, 2, 1, 1, 1, 2, 4, 4]
def baseStart_5929181 : Nat := 118140960795 + 5929181 * 2 ^ 59
def prefixEnd_5929181 : Nat := 4983230072969 + 3 ^ 40 * 5929181 * 2
def baseEnd_5929181 : Nat := 1014839913501957261923233

theorem tailTrace_5929181 : CollatzResearch.WordTrace tailWord_5929181 prefixEnd_5929181 1014839913501957261923233 := by
  unfold tailWord_5929181
  simp only [CollatzResearch.WordTrace]
  refine ⟨216254997132597335340835397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144169998088398223560556931 216254997132597335340835397)
  ·
    refine ⟨40547811962362000376406637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216254997132597335340835397 40547811962362000376406637)
    ·
      refine ⟨15205429485885750141152489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40547811962362000376406637 15205429485885750141152489)
      ·
        refine ⟨11404072114414312605864367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15205429485885750141152489 11404072114414312605864367)
        ·
          refine ⟨17106108171621468908796551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11404072114414312605864367 17106108171621468908796551)
          ·
            refine ⟨25659162257432203363194827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17106108171621468908796551 25659162257432203363194827)
            ·
              refine ⟨38488743386148305044792241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25659162257432203363194827 38488743386148305044792241)
              ·
                refine ⟨28866557539611228783594181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38488743386148305044792241 28866557539611228783594181)
                ·
                  refine ⟨5412479538677105396923909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28866557539611228783594181 5412479538677105396923909)
                  ·
                    refine ⟨1014839913501957261923233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5412479538677105396923909 1014839913501957261923233)
                    ·
                      rfl

theorem cell23_5929181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_5929181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929181 prefixEnd_5929181 := by exact prefixLift 5929181
  have htrace : WordTrace (prefixWord ++ tailWord_5929181) baseStart_5929181 baseEnd_5929181 := by
    simpa [prefixWord, tailWord_5929181, baseEnd_5929181] using wordTrace_append hprefix tailTrace_5929181
  have hstable : (prefixWord ++ tailWord_5929181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929181).length < 2 ^ (prefixWord ++ tailWord_5929181).sum := by decide
  have hdescent : baseEnd_5929181 < baseStart_5929181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929191 : List Nat := [1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 5]
def baseStart_5929191 : Nat := 118140960795 + 5929191 * 2 ^ 59
def prefixEnd_5929191 : Nat := 4983230072969 + 3 ^ 40 * 5929191 * 2
def baseEnd_5929191 : Nat := 3044524875312416746644653

theorem tailTrace_5929191 : CollatzResearch.WordTrace tailWord_5929191 prefixEnd_5929191 3044524875312416746644653 := by
  unfold tailWord_5929191
  simp only [CollatzResearch.WordTrace]
  refine ⟨216255361862561107048699427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144170241241707404699132951 216255361862561107048699427)
  ·
    refine ⟨324383042793841660573049141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216255361862561107048699427 324383042793841660573049141)
    ·
      refine ⟨30410910261922655678723357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 324383042793841660573049141 30410910261922655678723357)
      ·
        refine ⟨11404091348220995879521259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30410910261922655678723357 11404091348220995879521259)
        ·
          refine ⟨17106137022331493819281889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11404091348220995879521259 17106137022331493819281889)
          ·
            refine ⟨12829602766748620364461417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17106137022331493819281889 12829602766748620364461417)
            ·
              refine ⟨9622202075061465273346063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12829602766748620364461417 9622202075061465273346063)
              ·
                refine ⟨14433303112592197910019095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9622202075061465273346063 14433303112592197910019095)
                ·
                  refine ⟨21649954668888296865028643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14433303112592197910019095 21649954668888296865028643)
                  ·
                    refine ⟨32474932003332445297542965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21649954668888296865028643 32474932003332445297542965)
                    ·
                      refine ⟨3044524875312416746644653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32474932003332445297542965 3044524875312416746644653)
                      ·
                        rfl

theorem cell23_5929191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_5929191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929191 prefixEnd_5929191 := by exact prefixLift 5929191
  have htrace : WordTrace (prefixWord ++ tailWord_5929191) baseStart_5929191 baseEnd_5929191 := by
    simpa [prefixWord, tailWord_5929191, baseEnd_5929191] using wordTrace_append hprefix tailTrace_5929191
  have hstable : (prefixWord ++ tailWord_5929191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929191).length < 2 ^ (prefixWord ++ tailWord_5929191).sum := by decide
  have hdescent : baseEnd_5929191 < baseStart_5929191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929214 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_5929214 : Nat := 118140960795 + 5929214 * 2 ^ 59
def prefixEnd_5929214 : Nat := 4983230072969 + 3 ^ 40 * 5929214 * 2
def baseEnd_5929214 : Nat := 3044536685367470156657047

theorem tailTrace_5929214 : CollatzResearch.WordTrace tailWord_5929214 prefixEnd_5929214 3044536685367470156657047 := by
  unfold tailWord_5929214
  simp only [CollatzResearch.WordTrace]
  refine ⟨27032025092684722747098337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144170800494318521317857797 27032025092684722747098337)
  ·
    refine ⟨20274018819513542060323753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27032025092684722747098337 20274018819513542060323753)
    ·
      refine ⟨15205514114635156545242815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20274018819513542060323753 15205514114635156545242815)
      ·
        refine ⟨22808271171952734817864223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15205514114635156545242815 22808271171952734817864223)
        ·
          refine ⟨34212406757929102226796335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22808271171952734817864223 34212406757929102226796335)
          ·
            refine ⟨51318610136893653340194503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34212406757929102226796335 51318610136893653340194503)
            ·
              refine ⟨76977915205340480010291755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51318610136893653340194503 76977915205340480010291755)
              ·
                refine ⟨115466872808010720015437633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76977915205340480010291755 115466872808010720015437633)
                ·
                  refine ⟨86600154606008040011578225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115466872808010720015437633 86600154606008040011578225)
                  ·
                    refine ⟨64950115954506030008683669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86600154606008040011578225 64950115954506030008683669)
                    ·
                      refine ⟨3044536685367470156657047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64950115954506030008683669 3044536685367470156657047)
                      ·
                        rfl

theorem cell23_5929214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_5929214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929214 prefixEnd_5929214 := by exact prefixLift 5929214
  have htrace : WordTrace (prefixWord ++ tailWord_5929214) baseStart_5929214 baseEnd_5929214 := by
    simpa [prefixWord, tailWord_5929214, baseEnd_5929214] using wordTrace_append hprefix tailTrace_5929214
  have hstable : (prefixWord ++ tailWord_5929214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929214).length < 2 ^ (prefixWord ++ tailWord_5929214).sum := by decide
  have hdescent : baseEnd_5929214 < baseStart_5929214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929256 : List Nat := [2, 1, 5, 1, 4, 1, 2, 2, 1, 2, 2]
def baseStart_5929256 : Nat := 118140960795 + 5929256 * 2 ^ 59
def prefixEnd_5929256 : Nat := 4983230072969 + 3 ^ 40 * 5929256 * 2
def baseEnd_5929256 : Nat := 3044558251554958992331855

theorem tailTrace_5929256 : CollatzResearch.WordTrace tailWord_5929256 prefixEnd_5929256 3044558251554958992331855 := by
  unfold tailWord_5929256
  simp only [CollatzResearch.WordTrace]
  refine ⟨108128866303662811574907811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144171821738217082099877081 108128866303662811574907811)
  ·
    refine ⟨162193299455494217362361717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108128866303662811574907811 162193299455494217362361717)
    ·
      refine ⟨15205621823952582877721411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162193299455494217362361717 15205621823952582877721411)
      ·
        refine ⟨22808432735928874316582117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15205621823952582877721411 22808432735928874316582117)
        ·
          refine ⟨4276581137986663934359147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22808432735928874316582117 4276581137986663934359147)
          ·
            refine ⟨6414871706979995901538721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4276581137986663934359147 6414871706979995901538721)
            ·
              refine ⟨4811153780234996926154041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6414871706979995901538721 4811153780234996926154041)
              ·
                refine ⟨3608365335176247694615531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4811153780234996926154041 3608365335176247694615531)
                ·
                  refine ⟨5412548002764371541923297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3608365335176247694615531 5412548002764371541923297)
                  ·
                    refine ⟨4059411002073278656442473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5412548002764371541923297 4059411002073278656442473)
                    ·
                      refine ⟨3044558251554958992331855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4059411002073278656442473 3044558251554958992331855)
                      ·
                        rfl

theorem cell23_5929256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_5929256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929256 prefixEnd_5929256 := by exact prefixLift 5929256
  have htrace : WordTrace (prefixWord ++ tailWord_5929256) baseStart_5929256 baseEnd_5929256 := by
    simpa [prefixWord, tailWord_5929256, baseEnd_5929256] using wordTrace_append hprefix tailTrace_5929256
  have hstable : (prefixWord ++ tailWord_5929256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929256).length < 2 ^ (prefixWord ++ tailWord_5929256).sum := by decide
  have hdescent : baseEnd_5929256 < baseStart_5929256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929274 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4]
def baseStart_5929274 : Nat := 118140960795 + 5929274 * 2 ^ 59
def prefixEnd_5929274 : Nat := 4983230072969 + 3 ^ 40 * 5929274 * 2
def baseEnd_5929274 : Nat := 3044567494206739921906771

theorem tailTrace_5929274 : CollatzResearch.WordTrace tailWord_5929274 prefixEnd_5929274 3044567494206739921906771 := by
  unfold tailWord_5929274
  simp only [CollatzResearch.WordTrace]
  refine ⟨54064597280315103055992719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144172259414173608149313917 54064597280315103055992719)
  ·
    refine ⟨81096895920472654583989079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54064597280315103055992719 81096895920472654583989079)
    ·
      refine ⟨121645343880708981875983619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81096895920472654583989079 121645343880708981875983619)
      ·
        refine ⟨182468015821063472813975429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121645343880708981875983619 182468015821063472813975429)
        ·
          refine ⟨34212752966449401152620393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182468015821063472813975429 34212752966449401152620393)
          ·
            refine ⟨25659564724837050864465295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34212752966449401152620393 25659564724837050864465295)
            ·
              refine ⟨38489347087255576296697943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25659564724837050864465295 38489347087255576296697943)
              ·
                refine ⟨57734020630883364445046915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38489347087255576296697943 57734020630883364445046915)
                ·
                  refine ⟨86601030946325046667570373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57734020630883364445046915 86601030946325046667570373)
                  ·
                    refine ⟨16237693302435946250169445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86601030946325046667570373 16237693302435946250169445)
                    ·
                      refine ⟨3044567494206739921906771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16237693302435946250169445 3044567494206739921906771)
                      ·
                        rfl

theorem cell23_5929274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_5929274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929274 prefixEnd_5929274 := by exact prefixLift 5929274
  have htrace : WordTrace (prefixWord ++ tailWord_5929274) baseStart_5929274 baseEnd_5929274 := by
    simpa [prefixWord, tailWord_5929274, baseEnd_5929274] using wordTrace_append hprefix tailTrace_5929274
  have hstable : (prefixWord ++ tailWord_5929274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929274).length < 2 ^ (prefixWord ++ tailWord_5929274).sum := by decide
  have hdescent : baseEnd_5929274 < baseStart_5929274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929278 : List Nat := [4, 2, 1, 2, 1, 2, 1, 3, 1, 4, 2]
def baseStart_5929278 : Nat := 118140960795 + 5929278 * 2 ^ 59
def prefixEnd_5929278 : Nat := 4983230072969 + 3 ^ 40 * 5929278 * 2
def baseEnd_5929278 : Nat := 3044569548129357906256753

theorem tailTrace_5929278 : CollatzResearch.WordTrace tailWord_5929278 prefixEnd_5929278 3044569548129357906256753 := by
  unfold tailWord_5929278
  simp only [CollatzResearch.WordTrace]
  refine ⟨27032316876655740113389561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144172356675497280604744325 27032316876655740113389561)
  ·
    refine ⟨20274237657491805085042171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27032316876655740113389561 20274237657491805085042171)
    ·
      refine ⟨30411356486237707627563257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20274237657491805085042171 30411356486237707627563257)
      ·
        refine ⟨22808517364678280720672443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30411356486237707627563257 22808517364678280720672443)
        ·
          refine ⟨34212776047017421081008665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22808517364678280720672443 34212776047017421081008665)
          ·
            refine ⟨25659582035263065810756499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34212776047017421081008665 25659582035263065810756499)
            ·
              refine ⟨38489373052894598716134749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25659582035263065810756499 38489373052894598716134749)
              ·
                refine ⟨14433514894835474518550531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38489373052894598716134749 14433514894835474518550531)
                ·
                  refine ⟨21650272342253211777825797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14433514894835474518550531 21650272342253211777825797)
                  ·
                    refine ⟨4059426064172477208342337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21650272342253211777825797 4059426064172477208342337)
                    ·
                      refine ⟨3044569548129357906256753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4059426064172477208342337 3044569548129357906256753)
                      ·
                        rfl

theorem cell23_5929278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_5929278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929278 prefixEnd_5929278 := by exact prefixLift 5929278
  have htrace : WordTrace (prefixWord ++ tailWord_5929278) baseStart_5929278 baseEnd_5929278 := by
    simpa [prefixWord, tailWord_5929278, baseEnd_5929278] using wordTrace_append hprefix tailTrace_5929278
  have hstable : (prefixWord ++ tailWord_5929278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929278).length < 2 ^ (prefixWord ++ tailWord_5929278).sum := by decide
  have hdescent : baseEnd_5929278 < baseStart_5929278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929312 : List Nat := [2, 1, 1, 3, 5, 2, 1, 2, 2, 2, 2]
def baseStart_5929312 : Nat := 118140960795 + 5929312 * 2 ^ 59
def prefixEnd_5929312 : Nat := 4983230072969 + 3 ^ 40 * 5929312 * 2
def baseEnd_5929312 : Nat := 3044587006471610773231597

theorem tailTrace_5929312 : CollatzResearch.WordTrace tailWord_5929312 prefixEnd_5929312 3044587006471610773231597 := by
  unfold tailWord_5929312
  simp only [CollatzResearch.WordTrace]
  refine ⟨108129887547561372356927095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144173183396748496475902793 108129887547561372356927095)
  ·
    refine ⟨162194831321342058535390643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108129887547561372356927095 162194831321342058535390643)
    ·
      refine ⟨243292246982013087803085965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162194831321342058535390643 243292246982013087803085965)
      ·
        refine ⟨91234592618254907926157237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243292246982013087803085965 91234592618254907926157237)
        ·
          refine ⟨8553243057961397618077241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91234592618254907926157237 8553243057961397618077241)
          ·
            refine ⟨6414932293471048213557931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8553243057961397618077241 6414932293471048213557931)
            ·
              refine ⟨9622398440206572320336897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6414932293471048213557931 9622398440206572320336897)
              ·
                refine ⟨7216798830154929240252673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9622398440206572320336897 7216798830154929240252673)
                ·
                  refine ⟨5412599122616196930189505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7216798830154929240252673 5412599122616196930189505)
                  ·
                    refine ⟨4059449341962147697642129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5412599122616196930189505 4059449341962147697642129)
                    ·
                      refine ⟨3044587006471610773231597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4059449341962147697642129 3044587006471610773231597)
                      ·
                        rfl

theorem cell23_5929312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 2, 2, 2].length) (baseStart_5929312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929312 prefixEnd_5929312 := by exact prefixLift 5929312
  have htrace : WordTrace (prefixWord ++ tailWord_5929312) baseStart_5929312 baseEnd_5929312 := by
    simpa [prefixWord, tailWord_5929312, baseEnd_5929312] using wordTrace_append hprefix tailTrace_5929312
  have hstable : (prefixWord ++ tailWord_5929312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929312).length < 2 ^ (prefixWord ++ tailWord_5929312).sum := by decide
  have hdescent : baseEnd_5929312 < baseStart_5929312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929351 : List Nat := [1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 4]
def baseStart_5929351 : Nat := 118140960795 + 5929351 * 2 ^ 59
def prefixEnd_5929351 : Nat := 4983230072969 + 3 ^ 40 * 5929351 * 2
def baseEnd_5929351 : Nat := 3044607032217136120643917

theorem tailTrace_5929351 : CollatzResearch.WordTrace tailWord_5929351 prefixEnd_5929351 3044607032217136120643917 := by
  unfold tailWord_5929351
  simp only [CollatzResearch.WordTrace]
  refine ⟨216261197541981454374523907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144174131694654302916349271 216261197541981454374523907)
  ·
    refine ⟨324391796312972181561785861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216261197541981454374523907 324391796312972181561785861)
    ·
      refine ⟨60823461808682284042834849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 324391796312972181561785861 60823461808682284042834849)
      ·
        refine ⟨45617596356511713032126137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60823461808682284042834849 45617596356511713032126137)
        ·
          refine ⟨34213197267383784774094603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45617596356511713032126137 34213197267383784774094603)
          ·
            refine ⟨51319795901075677161141905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34213197267383784774094603 51319795901075677161141905)
            ·
              refine ⟨38489846925806757870856429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51319795901075677161141905 38489846925806757870856429)
              ·
                refine ⟨14433692597177534201571161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38489846925806757870856429 14433692597177534201571161)
                ·
                  refine ⟨10825269447883150651178371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14433692597177534201571161 10825269447883150651178371)
                  ·
                    refine ⟨16237904171824725976767557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10825269447883150651178371 16237904171824725976767557)
                    ·
                      refine ⟨3044607032217136120643917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16237904171824725976767557 3044607032217136120643917)
                      ·
                        rfl

theorem cell23_5929351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_5929351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929351 prefixEnd_5929351 := by exact prefixLift 5929351
  have htrace : WordTrace (prefixWord ++ tailWord_5929351) baseStart_5929351 baseEnd_5929351 := by
    simpa [prefixWord, tailWord_5929351, baseEnd_5929351] using wordTrace_append hprefix tailTrace_5929351
  have hstable : (prefixWord ++ tailWord_5929351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929351).length < 2 ^ (prefixWord ++ tailWord_5929351).sum := by decide
  have hdescent : baseEnd_5929351 < baseStart_5929351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929368 : List Nat := [2, 1, 2, 5, 1, 2, 1, 2, 2, 1, 4]
def baseStart_5929368 : Nat := 118140960795 + 5929368 * 2 ^ 59
def prefixEnd_5929368 : Nat := 4983230072969 + 3 ^ 40 * 5929368 * 2
def baseEnd_5929368 : Nat := 3044615761388262554131339

theorem tailTrace_5929368 : CollatzResearch.WordTrace tailWord_5929368 prefixEnd_5929368 3044615761388262554131339 := by
  unfold tailWord_5929368
  simp only [CollatzResearch.WordTrace]
  refine ⟨108130908791459933138946379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144174545055279910851928505 108130908791459933138946379)
  ·
    refine ⟨162196363187189899708419569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108130908791459933138946379 162196363187189899708419569)
    ·
      refine ⟨121647272390392424781314677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162196363187189899708419569 121647272390392424781314677)
      ·
        refine ⟨11404431786599289823248251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121647272390392424781314677 11404431786599289823248251)
        ·
          refine ⟨17106647679898934734872377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11404431786599289823248251 17106647679898934734872377)
          ·
            refine ⟨12829985759924201051154283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17106647679898934734872377 12829985759924201051154283)
            ·
              refine ⟨19244978639886301576731425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12829985759924201051154283 19244978639886301576731425)
              ·
                refine ⟨14433733979914726182548569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19244978639886301576731425 14433733979914726182548569)
                ·
                  refine ⟨10825300484936044636911427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14433733979914726182548569 10825300484936044636911427)
                  ·
                    refine ⟨16237950727404066955367141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10825300484936044636911427 16237950727404066955367141)
                    ·
                      refine ⟨3044615761388262554131339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16237950727404066955367141 3044615761388262554131339)
                      ·
                        rfl

theorem cell23_5929368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_5929368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929368 prefixEnd_5929368 := by exact prefixLift 5929368
  have htrace : WordTrace (prefixWord ++ tailWord_5929368) baseStart_5929368 baseEnd_5929368 := by
    simpa [prefixWord, tailWord_5929368, baseEnd_5929368] using wordTrace_append hprefix tailTrace_5929368
  have hstable : (prefixWord ++ tailWord_5929368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929368).length < 2 ^ (prefixWord ++ tailWord_5929368).sum := by decide
  have hdescent : baseEnd_5929368 < baseStart_5929368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929441 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 5, 1, 4]
def baseStart_5929441 : Nat := 118140960795 + 5929441 * 2 ^ 59
def prefixEnd_5929441 : Nat := 4983230072969 + 3 ^ 40 * 5929441 * 2
def baseEnd_5929441 : Nat := 3044653245476040768518503

theorem tailTrace_5929441 : CollatzResearch.WordTrace tailWord_5929441 prefixEnd_5929441 3044653245476040768518503 := by
  unfold tailWord_5929441
  simp only [CollatzResearch.WordTrace]
  refine ⟨216264480111655399745300177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144176320074436933163533451 216264480111655399745300177)
  ·
    refine ⟨162198360083741549808975133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216264480111655399745300177 162198360083741549808975133)
    ·
      refine ⟨60824385031403081178365675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162198360083741549808975133 60824385031403081178365675)
      ·
        refine ⟨91236577547104621767548513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60824385031403081178365675 91236577547104621767548513)
        ·
          refine ⟨68427433160328466325661385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91236577547104621767548513 68427433160328466325661385)
          ·
            refine ⟨51320574870246349744246039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68427433160328466325661385 51320574870246349744246039)
            ·
              refine ⟨76980862305369524616369059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51320574870246349744246039 76980862305369524616369059)
              ·
                refine ⟨115471293458054286924553589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76980862305369524616369059 115471293458054286924553589)
                ·
                  refine ⟨10825433761692589399176899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115471293458054286924553589 10825433761692589399176899)
                  ·
                    refine ⟨16238150642538884098765349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10825433761692589399176899 16238150642538884098765349)
                    ·
                      refine ⟨3044653245476040768518503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16238150642538884098765349 3044653245476040768518503)
                      ·
                        rfl

theorem cell23_5929441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_5929441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929441 prefixEnd_5929441 := by exact prefixLift 5929441
  have htrace : WordTrace (prefixWord ++ tailWord_5929441) baseStart_5929441 baseEnd_5929441 := by
    simpa [prefixWord, tailWord_5929441, baseEnd_5929441] using wordTrace_append hprefix tailTrace_5929441
  have hstable : (prefixWord ++ tailWord_5929441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929441).length < 2 ^ (prefixWord ++ tailWord_5929441).sum := by decide
  have hdescent : baseEnd_5929441 < baseStart_5929441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929451 : List Nat := [1, 1, 1, 1, 2, 3, 6, 1, 1, 6]
def baseStart_5929451 : Nat := 118140960795 + 5929451 * 2 ^ 59
def prefixEnd_5929451 : Nat := 4983230072969 + 3 ^ 40 * 5929451 * 2
def baseEnd_5929451 : Nat := 1014886126760861909797819

theorem tailTrace_5929451 : CollatzResearch.WordTrace tailWord_5929451 prefixEnd_5929451 1014886126760861909797819 := by
  unfold tailWord_5929451
  simp only [CollatzResearch.WordTrace]
  refine ⟨216264844841619171453164207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144176563227746114302109471 216264844841619171453164207)
  ·
    refine ⟨324397267262428757179746311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216264844841619171453164207 324397267262428757179746311)
    ·
      refine ⟨486595900893643135769619467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324397267262428757179746311 486595900893643135769619467)
      ·
        refine ⟨729893851340464703654429201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486595900893643135769619467 729893851340464703654429201)
        ·
          refine ⟨547420388505348527740821901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 729893851340464703654429201 547420388505348527740821901)
          ·
            refine ⟨205282645689505697902808213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 547420388505348527740821901 205282645689505697902808213)
            ·
              refine ⟨9622624016695579589194135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 205282645689505697902808213 9622624016695579589194135)
              ·
                refine ⟨14433936025043369383791203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9622624016695579589194135 14433936025043369383791203)
                ·
                  refine ⟨21650904037565054075686805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14433936025043369383791203 21650904037565054075686805)
                  ·
                    refine ⟨1014886126760861909797819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21650904037565054075686805 1014886126760861909797819)
                    ·
                      rfl

theorem cell23_5929451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 6].length) (baseStart_5929451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929451 prefixEnd_5929451 := by exact prefixLift 5929451
  have htrace : WordTrace (prefixWord ++ tailWord_5929451) baseStart_5929451 baseEnd_5929451 := by
    simpa [prefixWord, tailWord_5929451, baseEnd_5929451] using wordTrace_append hprefix tailTrace_5929451
  have hstable : (prefixWord ++ tailWord_5929451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929451).length < 2 ^ (prefixWord ++ tailWord_5929451).sum := by decide
  have hdescent : baseEnd_5929451 < baseStart_5929451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929471 : List Nat := [1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 4]
def baseStart_5929471 : Nat := 118140960795 + 5929471 * 2 ^ 59
def prefixEnd_5929471 : Nat := 4983230072969 + 3 ^ 40 * 5929471 * 2
def baseEnd_5929471 : Nat := 3044668649895675651143365

theorem tailTrace_5929471 : CollatzResearch.WordTrace tailWord_5929471 prefixEnd_5929471 3044668649895675651143365 := by
  unfold tailWord_5929471
  simp only [CollatzResearch.WordTrace]
  refine ⟨216265574301546714868892267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144177049534364476579261511 216265574301546714868892267)
  ·
    refine ⟨324398361452320072303338401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216265574301546714868892267 324398361452320072303338401)
    ·
      refine ⟨243298771089240054227503801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324398361452320072303338401 243298771089240054227503801)
      ·
        refine ⟨182474078316930040670627851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243298771089240054227503801 182474078316930040670627851)
        ·
          refine ⟨273711117475395061005941777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182474078316930040670627851 273711117475395061005941777)
          ·
            refine ⟨205283338106546295754456333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273711117475395061005941777 205283338106546295754456333)
            ·
              refine ⟨76981251789954860907921125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 205283338106546295754456333 76981251789954860907921125)
              ·
                refine ⟨14433984710616536420235211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76981251789954860907921125 14433984710616536420235211)
                ·
                  refine ⟨21650977065924804630352817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14433984710616536420235211 21650977065924804630352817)
                  ·
                    refine ⟨16238232799443603472764613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21650977065924804630352817 16238232799443603472764613)
                    ·
                      refine ⟨3044668649895675651143365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16238232799443603472764613 3044668649895675651143365)
                      ·
                        rfl

theorem cell23_5929471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_5929471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929471 prefixEnd_5929471 := by exact prefixLift 5929471
  have htrace : WordTrace (prefixWord ++ tailWord_5929471) baseStart_5929471 baseEnd_5929471 := by
    simpa [prefixWord, tailWord_5929471, baseEnd_5929471] using wordTrace_append hprefix tailTrace_5929471
  have hstable : (prefixWord ++ tailWord_5929471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929471).length < 2 ^ (prefixWord ++ tailWord_5929471).sum := by decide
  have hdescent : baseEnd_5929471 < baseStart_5929471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929495 : List Nat := [1, 1, 3, 6, 1, 1, 1, 2, 1, 1, 5]
def baseStart_5929495 : Nat := 118140960795 + 5929495 * 2 ^ 59
def prefixEnd_5929495 : Nat := 4983230072969 + 3 ^ 40 * 5929495 * 2
def baseEnd_5929495 : Nat := 3044680973431383557243255

theorem tailTrace_5929495 : CollatzResearch.WordTrace tailWord_5929495 prefixEnd_5929495 3044680973431383557243255 := by
  unfold tailWord_5929495
  simp only [CollatzResearch.WordTrace]
  refine ⟨216266449653459766967765939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144177633102306511311843959 216266449653459766967765939)
  ·
    refine ⟨324399674480189650451648909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216266449653459766967765939 324399674480189650451648909)
    ·
      refine ⟨121649877930071118919368341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324399674480189650451648909 121649877930071118919368341)
      ·
        refine ⟨5702338027972083699345391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 121649877930071118919368341 5702338027972083699345391)
        ·
          refine ⟨8553507041958125549018087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5702338027972083699345391 8553507041958125549018087)
          ·
            refine ⟨12830260562937188323527131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8553507041958125549018087 12830260562937188323527131)
            ·
              refine ⟨19245390844405782485290697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12830260562937188323527131 19245390844405782485290697)
              ·
                refine ⟨14434043133304336863968023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19245390844405782485290697 14434043133304336863968023)
                ·
                  refine ⟨21651064699956505295952035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14434043133304336863968023 21651064699956505295952035)
                  ·
                    refine ⟨32476597049934757943928053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21651064699956505295952035 32476597049934757943928053)
                    ·
                      refine ⟨3044680973431383557243255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32476597049934757943928053 3044680973431383557243255)
                      ·
                        rfl

theorem cell23_5929495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_5929495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929495 prefixEnd_5929495 := by exact prefixLift 5929495
  have htrace : WordTrace (prefixWord ++ tailWord_5929495) baseStart_5929495 baseEnd_5929495 := by
    simpa [prefixWord, tailWord_5929495, baseEnd_5929495] using wordTrace_append hprefix tailTrace_5929495
  have hstable : (prefixWord ++ tailWord_5929495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929495).length < 2 ^ (prefixWord ++ tailWord_5929495).sum := by decide
  have hdescent : baseEnd_5929495 < baseStart_5929495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929512 : List Nat := [2, 1, 5, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_5929512 : Nat := 118140960795 + 5929512 * 2 ^ 59
def prefixEnd_5929512 : Nat := 4983230072969 + 3 ^ 40 * 5929512 * 2
def baseEnd_5929512 : Nat := 3044689702602509990730677

theorem tailTrace_5929512 : CollatzResearch.WordTrace tailWord_5929512 prefixEnd_5929512 3044689702602509990730677 := by
  unfold tailWord_5929512
  simp only [CollatzResearch.WordTrace]
  refine ⟨108133534847199089435567395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144178046462932119247423193 108133534847199089435567395)
  ·
    refine ⟨162200302270798634153351093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108133534847199089435567395 162200302270798634153351093)
    ·
      refine ⟨15206278337887371951876665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162200302270798634153351093 15206278337887371951876665)
      ·
        refine ⟨11404708753415528963907499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15206278337887371951876665 11404708753415528963907499)
        ·
          refine ⟨17107063130123293445861249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11404708753415528963907499 17107063130123293445861249)
          ·
            refine ⟨12830297347592470084395937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17107063130123293445861249 12830297347592470084395937)
            ·
              refine ⟨9622723010694352563296953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12830297347592470084395937 9622723010694352563296953)
              ·
                refine ⟨7217042258020764422472715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9622723010694352563296953 7217042258020764422472715)
                ·
                  refine ⟨10825563387031146633709073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7217042258020764422472715 10825563387031146633709073)
                  ·
                    refine ⟨8119172540273359975281805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10825563387031146633709073 8119172540273359975281805)
                    ·
                      refine ⟨3044689702602509990730677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8119172540273359975281805 3044689702602509990730677)
                      ·
                        rfl

theorem cell23_5929512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_5929512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929512 prefixEnd_5929512 := by exact prefixLift 5929512
  have htrace : WordTrace (prefixWord ++ tailWord_5929512) baseStart_5929512 baseEnd_5929512 := by
    simpa [prefixWord, tailWord_5929512, baseEnd_5929512] using wordTrace_append hprefix tailTrace_5929512
  have hstable : (prefixWord ++ tailWord_5929512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929512).length < 2 ^ (prefixWord ++ tailWord_5929512).sum := by decide
  have hdescent : baseEnd_5929512 < baseStart_5929512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929521 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 2, 2, 5]
def baseStart_5929521 : Nat := 118140960795 + 5929521 * 2 ^ 59
def prefixEnd_5929521 : Nat := 4983230072969 + 3 ^ 40 * 5929521 * 2
def baseEnd_5929521 : Nat := 3044694323928400455518135

theorem tailTrace_5929521 : CollatzResearch.WordTrace tailWord_5929521 prefixEnd_5929521 3044694323928400455518135 := by
  unfold tailWord_5929521
  simp only [CollatzResearch.WordTrace]
  refine ⟨216267397951365573408212417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144178265300910382272141611 216267397951365573408212417)
  ·
    refine ⟨162200548463524180056159313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216267397951365573408212417 162200548463524180056159313)
    ·
      refine ⟨121650411347643135042119485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162200548463524180056159313 121650411347643135042119485)
      ·
        refine ⟨45618904255366175640794807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121650411347643135042119485 45618904255366175640794807)
        ·
          refine ⟨68428356383049263461192211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45618904255366175640794807 68428356383049263461192211)
          ·
            refine ⟨102642534574573895191788317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68428356383049263461192211 102642534574573895191788317)
            ·
              refine ⟨38490950465465210696920619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102642534574573895191788317 38490950465465210696920619)
              ·
                refine ⟨57736425698197816045380929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38490950465465210696920619 57736425698197816045380929)
                ·
                  refine ⟨43302319273648362034035697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57736425698197816045380929 43302319273648362034035697)
                  ·
                    refine ⟨32476739455236271525526773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43302319273648362034035697 32476739455236271525526773)
                    ·
                      refine ⟨3044694323928400455518135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32476739455236271525526773 3044694323928400455518135)
                      ·
                        rfl

theorem cell23_5929521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_5929521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929521 prefixEnd_5929521 := by exact prefixLift 5929521
  have htrace : WordTrace (prefixWord ++ tailWord_5929521) baseStart_5929521 baseEnd_5929521 := by
    simpa [prefixWord, tailWord_5929521, baseEnd_5929521] using wordTrace_append hprefix tailTrace_5929521
  have hstable : (prefixWord ++ tailWord_5929521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929521).length < 2 ^ (prefixWord ++ tailWord_5929521).sum := by decide
  have hdescent : baseEnd_5929521 < baseStart_5929521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929526 : List Nat := [5, 1, 2, 1, 2, 1, 3, 3, 1, 2, 2]
def baseStart_5929526 : Nat := 118140960795 + 5929526 * 2 ^ 59
def prefixEnd_5929526 : Nat := 4983230072969 + 3 ^ 40 * 5929526 * 2
def baseEnd_5929526 : Nat := 3044696891331672935955613

theorem tailTrace_5929526 : CollatzResearch.WordTrace tailWord_5929526 prefixEnd_5929526 3044696891331672935955613 := by
  unfold tailWord_5929526
  simp only [CollatzResearch.WordTrace]
  refine ⟨13516723769771716203884027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144178386877564972841429621 13516723769771716203884027)
  ·
    refine ⟨20275085654657574305826041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13516723769771716203884027 20275085654657574305826041)
    ·
      refine ⟨15206314240993180729369531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20275085654657574305826041 15206314240993180729369531)
      ·
        refine ⟨22809471361489771094054297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15206314240993180729369531 22809471361489771094054297)
        ·
          refine ⟨17107103521117328320540723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22809471361489771094054297 17107103521117328320540723)
          ·
            refine ⟨25660655281675992480811085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17107103521117328320540723 25660655281675992480811085)
            ·
              refine ⟨9622745730628497180304157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25660655281675992480811085 9622745730628497180304157)
              ·
                refine ⟨3608529648985686442614059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9622745730628497180304157 3608529648985686442614059)
                ·
                  refine ⟨5412794473478529663921089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3608529648985686442614059 5412794473478529663921089)
                  ·
                    refine ⟨4059595855108897247940817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5412794473478529663921089 4059595855108897247940817)
                    ·
                      refine ⟨3044696891331672935955613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4059595855108897247940817 3044696891331672935955613)
                      ·
                        rfl

theorem cell23_5929526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_5929526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929526 prefixEnd_5929526 := by exact prefixLift 5929526
  have htrace : WordTrace (prefixWord ++ tailWord_5929526) baseStart_5929526 baseEnd_5929526 := by
    simpa [prefixWord, tailWord_5929526, baseEnd_5929526] using wordTrace_append hprefix tailTrace_5929526
  have hstable : (prefixWord ++ tailWord_5929526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929526).length < 2 ^ (prefixWord ++ tailWord_5929526).sum := by decide
  have hdescent : baseEnd_5929526 < baseStart_5929526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929535 : List Nat := [1, 1, 2, 2, 3, 2, 1, 5, 1, 3, 2]
def baseStart_5929535 : Nat := 118140960795 + 5929535 * 2 ^ 59
def prefixEnd_5929535 : Nat := 4983230072969 + 3 ^ 40 * 5929535 * 2
def baseEnd_5929535 : Nat := 3044701512657563400743071

theorem tailTrace_5929535 : CollatzResearch.WordTrace tailWord_5929535 prefixEnd_5929535 3044701512657563400743071 := by
  unfold tailWord_5929535
  simp only [CollatzResearch.WordTrace]
  refine ⟨216267908573314853799222059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144178605715543235866148039 216267908573314853799222059)
  ·
    refine ⟨324401862859972280698833089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216267908573314853799222059 324401862859972280698833089)
    ·
      refine ⟨243301397144979210524124817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324401862859972280698833089 243301397144979210524124817)
      ·
        refine ⟨182476047858734407893093613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243301397144979210524124817 182476047858734407893093613)
        ·
          refine ⟨68428517947025402959910105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182476047858734407893093613 68428517947025402959910105)
          ·
            refine ⟨51321388460269052219932579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68428517947025402959910105 51321388460269052219932579)
            ·
              refine ⟨76982082690403578329898869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51321388460269052219932579 76982082690403578329898869)
              ·
                refine ⟨7217070252225335468428019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76982082690403578329898869 7217070252225335468428019)
                ·
                  refine ⟨10825605378338003202642029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7217070252225335468428019 10825605378338003202642029)
                  ·
                    refine ⟨4059602016876751200990761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10825605378338003202642029 4059602016876751200990761)
                    ·
                      refine ⟨3044701512657563400743071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4059602016876751200990761 3044701512657563400743071)
                      ·
                        rfl

theorem cell23_5929535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 3, 2].length) (baseStart_5929535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929535 prefixEnd_5929535 := by exact prefixLift 5929535
  have htrace : WordTrace (prefixWord ++ tailWord_5929535) baseStart_5929535 baseEnd_5929535 := by
    simpa [prefixWord, tailWord_5929535, baseEnd_5929535] using wordTrace_append hprefix tailTrace_5929535
  have hstable : (prefixWord ++ tailWord_5929535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929535).length < 2 ^ (prefixWord ++ tailWord_5929535).sum := by decide
  have hdescent : baseEnd_5929535 < baseStart_5929535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929571 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 9]
def baseStart_5929571 : Nat := 118140960795 + 5929571 * 2 ^ 59
def prefixEnd_5929571 : Nat := 4983230072969 + 3 ^ 40 * 5929571 * 2
def baseEnd_5929571 : Nat := 338302221995680584432545

theorem tailTrace_5929571 : CollatzResearch.WordTrace tailWord_5929571 prefixEnd_5929571 338302221995680584432545 := by
  unfold tailWord_5929571
  simp only [CollatzResearch.WordTrace]
  refine ⟨216269221601184431947532567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144179481067456287965021711 216269221601184431947532567)
  ·
    refine ⟨324403832401776647921298851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216269221601184431947532567 324403832401776647921298851)
    ·
      refine ⟨486605748602664971881948277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324403832401776647921298851 486605748602664971881948277)
      ·
        refine ⟨45619288931499841113932651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 486605748602664971881948277 45619288931499841113932651)
        ·
          refine ⟨68428933397249761670898977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45619288931499841113932651 68428933397249761670898977)
          ·
            refine ⟨51321700047937321253174233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68428933397249761670898977 51321700047937321253174233)
            ·
              refine ⟨38491275035952990939880675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51321700047937321253174233 38491275035952990939880675)
              ·
                refine ⟨57736912553929486409821013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38491275035952990939880675 57736912553929486409821013)
                ·
                  refine ⟨338302221995680584432545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 57736912553929486409821013 338302221995680584432545)
                  ·
                    rfl

theorem cell23_5929571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 9].length) (baseStart_5929571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929571 prefixEnd_5929571 := by exact prefixLift 5929571
  have htrace : WordTrace (prefixWord ++ tailWord_5929571) baseStart_5929571 baseEnd_5929571 := by
    simpa [prefixWord, tailWord_5929571, baseEnd_5929571] using wordTrace_append hprefix tailTrace_5929571
  have hstable : (prefixWord ++ tailWord_5929571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929571).length < 2 ^ (prefixWord ++ tailWord_5929571).sum := by decide
  have hdescent : baseEnd_5929571 < baseStart_5929571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929582 : List Nat := [4, 1, 2, 2, 2, 2, 1, 2, 1, 4, 2]
def baseStart_5929582 : Nat := 118140960795 + 5929582 * 2 ^ 59
def prefixEnd_5929582 : Nat := 4983230072969 + 3 ^ 40 * 5929582 * 2
def baseEnd_5929582 : Nat := 3044725646248324716855355

theorem tailTrace_5929582 : CollatzResearch.WordTrace tailWord_5929582 prefixEnd_5929582 3044725646248324716855355 := by
  unfold tailWord_5929582
  simp only [CollatzResearch.WordTrace]
  refine ⟨27033702850518072603272875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144179748536096387217455333 27033702850518072603272875)
  ·
    refine ⟨40550554275777108904909313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27033702850518072603272875 40550554275777108904909313)
    ·
      refine ⟨30412915706832831678681985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40550554275777108904909313 30412915706832831678681985)
      ·
        refine ⟨22809686780124623759011489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30412915706832831678681985 22809686780124623759011489)
        ·
          refine ⟨17107265085093467819258617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22809686780124623759011489 17107265085093467819258617)
          ·
            refine ⟨12830448813820100864443963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17107265085093467819258617 12830448813820100864443963)
            ·
              refine ⟨19245673220730151296665945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12830448813820100864443963 19245673220730151296665945)
              ·
                refine ⟨14434254915547613472499459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19245673220730151296665945 14434254915547613472499459)
                ·
                  refine ⟨21651382373321420208749189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14434254915547613472499459 21651382373321420208749189)
                  ·
                    refine ⟨4059634194997766289140473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21651382373321420208749189 4059634194997766289140473)
                    ·
                      refine ⟨3044725646248324716855355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4059634194997766289140473 3044725646248324716855355)
                      ·
                        rfl

theorem cell23_5929582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_5929582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929582 prefixEnd_5929582 := by exact prefixLift 5929582
  have htrace : WordTrace (prefixWord ++ tailWord_5929582) baseStart_5929582 baseEnd_5929582 := by
    simpa [prefixWord, tailWord_5929582, baseEnd_5929582] using wordTrace_append hprefix tailTrace_5929582
  have hstable : (prefixWord ++ tailWord_5929582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929582).length < 2 ^ (prefixWord ++ tailWord_5929582).sum := by decide
  have hdescent : baseEnd_5929582 < baseStart_5929582 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929605 : List Nat := [1, 3, 1, 1, 4, 3, 1, 4, 5]
def baseStart_5929605 : Nat := 118140960795 + 5929605 * 2 ^ 59
def prefixEnd_5929605 : Nat := 4983230072969 + 3 ^ 40 * 5929605 * 2
def baseEnd_5929605 : Nat := 338304161811486458540861

theorem tailTrace_5929605 : CollatzResearch.WordTrace tailWord_5929605 prefixEnd_5929605 338304161811486458540861 := by
  unfold tailWord_5929605
  simp only [CollatzResearch.WordTrace]
  refine ⟨216270461683061255754270269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144180307788707503836180179 216270461683061255754270269)
  ·
    refine ⟨81101423131147970907851351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216270461683061255754270269 81101423131147970907851351)
    ·
      refine ⟨121652134696721956361777027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81101423131147970907851351 121652134696721956361777027)
      ·
        refine ⟨182478202045082934542665541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121652134696721956361777027 182478202045082934542665541)
        ·
          refine ⟨34214662883453050226749789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182478202045082934542665541 34214662883453050226749789)
          ·
            refine ⟨12830498581294893835031171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34214662883453050226749789 12830498581294893835031171)
            ·
              refine ⟨19245747871942340752546757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12830498581294893835031171 19245747871942340752546757)
              ·
                refine ⟨3608577725989188891102517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19245747871942340752546757 3608577725989188891102517)
                ·
                  refine ⟨338304161811486458540861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3608577725989188891102517 338304161811486458540861)
                  ·
                    rfl

theorem cell23_5929605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4, 5].length) (baseStart_5929605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929605 prefixEnd_5929605 := by exact prefixLift 5929605
  have htrace : WordTrace (prefixWord ++ tailWord_5929605) baseStart_5929605 baseEnd_5929605 := by
    simpa [prefixWord, tailWord_5929605, baseEnd_5929605] using wordTrace_append hprefix tailTrace_5929605
  have hstable : (prefixWord ++ tailWord_5929605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929605).length < 2 ^ (prefixWord ++ tailWord_5929605).sum := by decide
  have hdescent : baseEnd_5929605 < baseStart_5929605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929611 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 7]
def baseStart_5929611 : Nat := 118140960795 + 5929611 * 2 ^ 59
def prefixEnd_5929611 : Nat := 4983230072969 + 3 ^ 40 * 5929611 * 2
def baseEnd_5929611 : Nat := 3044740537187305103392721

theorem tailTrace_5929611 : CollatzResearch.WordTrace tailWord_5929611 prefixEnd_5929611 3044740537187305103392721 := by
  unfold tailWord_5929611
  simp only [CollatzResearch.WordTrace]
  refine ⟨216270680521039518778988687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144180453680693012519325791 216270680521039518778988687)
  ·
    refine ⟨324406020781559278168483031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216270680521039518778988687 324406020781559278168483031)
    ·
      refine ⟨486609031172338917252724547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324406020781559278168483031 486609031172338917252724547)
      ·
        refine ⟨729913546758508375879086821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486609031172338917252724547 729913546758508375879086821)
        ·
          refine ⟨136858790017220320477328779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 729913546758508375879086821 136858790017220320477328779)
          ·
            refine ⟨205288185025830480715993169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136858790017220320477328779 205288185025830480715993169)
            ·
              refine ⟨153966138769372860536994877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205288185025830480715993169 153966138769372860536994877)
              ·
                refine ⟨57737302038514822701373079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153966138769372860536994877 57737302038514822701373079)
                ·
                  refine ⟨86605953057772234052059619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57737302038514822701373079 86605953057772234052059619)
                  ·
                    refine ⟨129908929586658351078089429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86605953057772234052059619 129908929586658351078089429)
                    ·
                      refine ⟨3044740537187305103392721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129908929586658351078089429 3044740537187305103392721)
                      ·
                        rfl

theorem cell23_5929611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 7].length) (baseStart_5929611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929611 prefixEnd_5929611 := by exact prefixLift 5929611
  have htrace : WordTrace (prefixWord ++ tailWord_5929611) baseStart_5929611 baseEnd_5929611 := by
    simpa [prefixWord, tailWord_5929611, baseEnd_5929611] using wordTrace_append hprefix tailTrace_5929611
  have hstable : (prefixWord ++ tailWord_5929611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929611).length < 2 ^ (prefixWord ++ tailWord_5929611).sum := by decide
  have hdescent : baseEnd_5929611 < baseStart_5929611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929639 : List Nat := [1, 1, 6, 3, 1, 1, 2, 3, 5]
def baseStart_5929639 : Nat := 118140960795 + 5929639 * 2 ^ 59
def prefixEnd_5929639 : Nat := 4983230072969 + 3 ^ 40 * 5929639 * 2
def baseEnd_5929639 : Nat := 338306101627292332649177

theorem tailTrace_5929639 : CollatzResearch.WordTrace tailWord_5929639 prefixEnd_5929639 338306101627292332649177 := by
  unfold tailWord_5929639
  simp only [CollatzResearch.WordTrace]
  refine ⟨216271701764938079561007971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144181134509958719707338647 216271701764938079561007971)
  ·
    refine ⟨324407552647407119341511957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216271701764938079561007971 324407552647407119341511957)
    ·
      refine ⟨15206604030347208719133373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 324407552647407119341511957 15206604030347208719133373)
      ·
        refine ⟨5702476511380203269675015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15206604030347208719133373 5702476511380203269675015)
        ·
          refine ⟨8553714767070304904512523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5702476511380203269675015 8553714767070304904512523)
          ·
            refine ⟨12830572150605457356768785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8553714767070304904512523 12830572150605457356768785)
            ·
              refine ⟨9622929112954093017576589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12830572150605457356768785 9622929112954093017576589)
              ·
                refine ⟨3608598417357784881591221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9622929112954093017576589 3608598417357784881591221)
                ·
                  refine ⟨338306101627292332649177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3608598417357784881591221 338306101627292332649177)
                  ·
                    rfl

theorem cell23_5929639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3, 5].length) (baseStart_5929639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929639 prefixEnd_5929639 := by exact prefixLift 5929639
  have htrace : WordTrace (prefixWord ++ tailWord_5929639) baseStart_5929639 baseEnd_5929639 := by
    simpa [prefixWord, tailWord_5929639, baseEnd_5929639] using wordTrace_append hprefix tailTrace_5929639
  have hstable : (prefixWord ++ tailWord_5929639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929639).length < 2 ^ (prefixWord ++ tailWord_5929639).sum := by decide
  have hdescent : baseEnd_5929639 < baseStart_5929639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929648 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 7, 4]
def baseStart_5929648 : Nat := 118140960795 + 5929648 * 2 ^ 59
def prefixEnd_5929648 : Nat := 4983230072969 + 3 ^ 40 * 5929648 * 2
def baseEnd_5929648 : Nat := 1014919845323840486210017

theorem tailTrace_5929648 : CollatzResearch.WordTrace tailWord_5929648 prefixEnd_5929648 1014919845323840486210017 := by
  unfold tailWord_5929648
  simp only [CollatzResearch.WordTrace]
  refine ⟨108136015010952737049042799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144181353347936982732057065 108136015010952737049042799)
  ·
    refine ⟨162204022516429105573564199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108136015010952737049042799 162204022516429105573564199)
    ·
      refine ⟨243306033774643658360346299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162204022516429105573564199 243306033774643658360346299)
      ·
        refine ⟨364959050661965487540519449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243306033774643658360346299 364959050661965487540519449)
        ·
          refine ⟨273719287996474115655389587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364959050661965487540519449 273719287996474115655389587)
          ·
            refine ⟨410578931994711173483084381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273719287996474115655389587 410578931994711173483084381)
            ·
              refine ⟨153967099498016690056156643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 410578931994711173483084381 153967099498016690056156643)
              ·
                refine ⟨230950649247025035084234965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153967099498016690056156643 230950649247025035084234965)
                ·
                  refine ⟨5412905841727149259786757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 230950649247025035084234965 5412905841727149259786757)
                  ·
                    refine ⟨1014919845323840486210017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5412905841727149259786757 1014919845323840486210017)
                    ·
                      rfl

theorem cell23_5929648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 7, 4].length) (baseStart_5929648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929648 prefixEnd_5929648 := by exact prefixLift 5929648
  have htrace : WordTrace (prefixWord ++ tailWord_5929648) baseStart_5929648 baseEnd_5929648 := by
    simpa [prefixWord, tailWord_5929648, baseEnd_5929648] using wordTrace_append hprefix tailTrace_5929648
  have hstable : (prefixWord ++ tailWord_5929648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929648).length < 2 ^ (prefixWord ++ tailWord_5929648).sum := by decide
  have hdescent : baseEnd_5929648 < baseStart_5929648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929692 : List Nat := [2, 2, 5, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_5929692 : Nat := 118140960795 + 5929692 * 2 ^ 59
def prefixEnd_5929692 : Nat := 4983230072969 + 3 ^ 40 * 5929692 * 2
def baseEnd_5929692 : Nat := 3044782129120319286479849

theorem tailTrace_5929692 : CollatzResearch.WordTrace tailWord_5929692 prefixEnd_5929692 3044782129120319286479849 := by
  unfold tailWord_5929692
  simp only [CollatzResearch.WordTrace]
  refine ⟨108136817416873034806343665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144182423222497379741791553 108136817416873034806343665)
  ·
    refine ⟨81102613062654776104757749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108136817416873034806343665 81102613062654776104757749)
    ·
      refine ⟨7603369974623885259821039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81102613062654776104757749 7603369974623885259821039)
      ·
        refine ⟨11405054961935827889731559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7603369974623885259821039 11405054961935827889731559)
        ·
          refine ⟨17107582442903741834597339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11405054961935827889731559 17107582442903741834597339)
          ·
            refine ⟨25661373664355612751896009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17107582442903741834597339 25661373664355612751896009)
            ·
              refine ⟨19246030248266709563922007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25661373664355612751896009 19246030248266709563922007)
              ·
                refine ⟨28869045372400064345883011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19246030248266709563922007 28869045372400064345883011)
                ·
                  refine ⟨43303568058600096518824517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28869045372400064345883011 43303568058600096518824517)
                  ·
                    refine ⟨8119419010987518097279597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43303568058600096518824517 8119419010987518097279597)
                    ·
                      refine ⟨3044782129120319286479849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8119419010987518097279597 3044782129120319286479849)
                      ·
                        rfl

theorem cell23_5929692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_5929692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929692 prefixEnd_5929692 := by exact prefixLift 5929692
  have htrace : WordTrace (prefixWord ++ tailWord_5929692) baseStart_5929692 baseEnd_5929692 := by
    simpa [prefixWord, tailWord_5929692, baseEnd_5929692] using wordTrace_append hprefix tailTrace_5929692
  have hstable : (prefixWord ++ tailWord_5929692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929692).length < 2 ^ (prefixWord ++ tailWord_5929692).sum := by decide
  have hdescent : baseEnd_5929692 < baseStart_5929692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929699 : List Nat := [1, 1, 1, 7, 1, 1, 3, 3, 1, 4]
def baseStart_5929699 : Nat := 118140960795 + 5929699 * 2 ^ 59
def prefixEnd_5929699 : Nat := 4983230072969 + 3 ^ 40 * 5929699 * 2
def baseEnd_5929699 : Nat := 1014928574494966919697439

theorem tailTrace_5929699 : CollatzResearch.WordTrace tailWord_5929699 prefixEnd_5929699 1014928574494966919697439 := by
  unfold tailWord_5929699
  simp only [CollatzResearch.WordTrace]
  refine ⟨216273890144720709808192151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144182593429813806538794767 216273890144720709808192151)
  ·
    refine ⟨324410835217081064712288227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216273890144720709808192151 324410835217081064712288227)
    ·
      refine ⟨486616252825621597068432341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324410835217081064712288227 486616252825621597068432341)
      ·
        refine ⟨11405068425600506181291383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 486616252825621597068432341 11405068425600506181291383)
        ·
          refine ⟨17107602638400759271937075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11405068425600506181291383 17107602638400759271937075)
          ·
            refine ⟨25661403957601138907905613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17107602638400759271937075 25661403957601138907905613)
            ·
              refine ⟨9623026484100427090464605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25661403957601138907905613 9623026484100427090464605)
              ·
                refine ⟨3608634931537660158924227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9623026484100427090464605 3608634931537660158924227)
                ·
                  refine ⟨5412952397306490238386341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3608634931537660158924227 5412952397306490238386341)
                  ·
                    refine ⟨1014928574494966919697439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5412952397306490238386341 1014928574494966919697439)
                    ·
                      rfl

theorem cell23_5929699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3, 1, 4].length) (baseStart_5929699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929699 prefixEnd_5929699 := by exact prefixLift 5929699
  have htrace : WordTrace (prefixWord ++ tailWord_5929699) baseStart_5929699 baseEnd_5929699 := by
    simpa [prefixWord, tailWord_5929699, baseEnd_5929699] using wordTrace_append hprefix tailTrace_5929699
  have hstable : (prefixWord ++ tailWord_5929699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929699).length < 2 ^ (prefixWord ++ tailWord_5929699).sum := by decide
  have hdescent : baseEnd_5929699 < baseStart_5929699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929705 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 5, 1, 3]
def baseStart_5929705 : Nat := 118140960795 + 5929705 * 2 ^ 59
def prefixEnd_5929705 : Nat := 4983230072969 + 3 ^ 40 * 5929705 * 2
def baseEnd_5929705 : Nat := 3044788804368827735617289

theorem tailTrace_5929705 : CollatzResearch.WordTrace tailWord_5929705 prefixEnd_5929705 3044788804368827735617289 := by
  unfold tailWord_5929705
  simp only [CollatzResearch.WordTrace]
  refine ⟨216274108982698972832910569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144182739321799315221940379 216274108982698972832910569)
  ·
    refine ⟨162205581737024229624682927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216274108982698972832910569 162205581737024229624682927)
    ·
      refine ⟨243308372605536344437024391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162205581737024229624682927 243308372605536344437024391)
      ·
        refine ⟨364962558908304516655536587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243308372605536344437024391 364962558908304516655536587)
        ·
          refine ⟨547443838362456774983304881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364962558908304516655536587 547443838362456774983304881)
          ·
            refine ⟨410582878771842581237478661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 547443838362456774983304881 410582878771842581237478661)
            ·
              refine ⟨76984289769720483982027249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 410582878771842581237478661 76984289769720483982027249)
              ·
                refine ⟨57738217327290362986520437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76984289769720483982027249 57738217327290362986520437)
                ·
                  refine ⟨5412957874433471529986291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57738217327290362986520437 5412957874433471529986291)
                  ·
                    refine ⟨8119436811650207294979437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5412957874433471529986291 8119436811650207294979437)
                    ·
                      refine ⟨3044788804368827735617289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8119436811650207294979437 3044788804368827735617289)
                      ·
                        rfl

theorem cell23_5929705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 5, 1, 3].length) (baseStart_5929705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929705 prefixEnd_5929705 := by exact prefixLift 5929705
  have htrace : WordTrace (prefixWord ++ tailWord_5929705) baseStart_5929705 baseEnd_5929705 := by
    simpa [prefixWord, tailWord_5929705, baseEnd_5929705] using wordTrace_append hprefix tailTrace_5929705
  have hstable : (prefixWord ++ tailWord_5929705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929705).length < 2 ^ (prefixWord ++ tailWord_5929705).sum := by decide
  have hdescent : baseEnd_5929705 < baseStart_5929705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929708 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 5, 5]
def baseStart_5929708 : Nat := 118140960795 + 5929708 * 2 ^ 59
def prefixEnd_5929708 : Nat := 4983230072969 + 3 ^ 40 * 5929708 * 2
def baseEnd_5929708 : Nat := 1014930114936930407959925

theorem tailTrace_5929708 : CollatzResearch.WordTrace tailWord_5929708 prefixEnd_5929708 1014930114936930407959925 := by
  unfold tailWord_5929708
  simp only [CollatzResearch.WordTrace]
  refine ⟨108137109200844052172634889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144182812267792069563513185 108137109200844052172634889)
  ·
    refine ⟨81102831900633039129476167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108137109200844052172634889 81102831900633039129476167)
    ·
      refine ⟨121654247850949558694214251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81102831900633039129476167 121654247850949558694214251)
      ·
        refine ⟨182481371776424338041321377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121654247850949558694214251 182481371776424338041321377)
        ·
          refine ⟨136861028832318253530991033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182481371776424338041321377 136861028832318253530991033)
          ·
            refine ⟨102645771624238690148243275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136861028832318253530991033 102645771624238690148243275)
            ·
              refine ⟨153968657436358035222364913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102645771624238690148243275 153968657436358035222364913)
              ·
                refine ⟨115476493077268526416773685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153968657436358035222364913 115476493077268526416773685)
                ·
                  refine ⟨10825921225993924351572533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115476493077268526416773685 10825921225993924351572533)
                  ·
                    refine ⟨1014930114936930407959925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10825921225993924351572533 1014930114936930407959925)
                    ·
                      rfl

theorem cell23_5929708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 5].length) (baseStart_5929708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929708 prefixEnd_5929708 := by exact prefixLift 5929708
  have htrace : WordTrace (prefixWord ++ tailWord_5929708) baseStart_5929708 baseEnd_5929708 := by
    simpa [prefixWord, tailWord_5929708, baseEnd_5929708] using wordTrace_append hprefix tailTrace_5929708
  have hstable : (prefixWord ++ tailWord_5929708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929708).length < 2 ^ (prefixWord ++ tailWord_5929708).sum := by decide
  have hdescent : baseEnd_5929708 < baseStart_5929708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929722 : List Nat := [3, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3]
def baseStart_5929722 : Nat := 118140960795 + 5929722 * 2 ^ 59
def prefixEnd_5929722 : Nat := 4983230072969 + 3 ^ 40 * 5929722 * 2
def baseEnd_5929722 : Nat := 3044797533539954169104711

theorem tailTrace_5929722 : CollatzResearch.WordTrace tailWord_5929722 prefixEnd_5929722 3044797533539954169104711 := by
  unfold tailWord_5929722
  simp only [CollatzResearch.WordTrace]
  refine ⟨54068682255909346184069855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144183152682424923157519613 54068682255909346184069855)
  ·
    refine ⟨81103023383864019276104783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54068682255909346184069855 81103023383864019276104783)
    ·
      refine ⟨121654535075796028914157175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81103023383864019276104783 121654535075796028914157175)
      ·
        refine ⟨182481802613694043371235763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121654535075796028914157175 182481802613694043371235763)
        ·
          refine ⟨273722703920541065056853645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182481802613694043371235763 273722703920541065056853645)
          ·
            refine ⟨102646013970202899396320117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273722703920541065056853645 102646013970202899396320117)
            ·
              refine ⟨9623063809706521818405011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102646013970202899396320117 9623063809706521818405011)
              ·
                refine ⟨14434595714559782727607517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9623063809706521818405011 14434595714559782727607517)
                ·
                  refine ⟨5412973392959918522852819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14434595714559782727607517 5412973392959918522852819)
                  ·
                    refine ⟨8119460089439877784279229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5412973392959918522852819 8119460089439877784279229)
                    ·
                      refine ⟨3044797533539954169104711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8119460089439877784279229 3044797533539954169104711)
                      ·
                        rfl

theorem cell23_5929722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3].length) (baseStart_5929722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929722 prefixEnd_5929722 := by exact prefixLift 5929722
  have htrace : WordTrace (prefixWord ++ tailWord_5929722) baseStart_5929722 baseEnd_5929722 := by
    simpa [prefixWord, tailWord_5929722, baseEnd_5929722] using wordTrace_append hprefix tailTrace_5929722
  have hstable : (prefixWord ++ tailWord_5929722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929722).length < 2 ^ (prefixWord ++ tailWord_5929722).sum := by decide
  have hdescent : baseEnd_5929722 < baseStart_5929722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929732 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 4, 3, 2]
def baseStart_5929732 : Nat := 118140960795 + 5929732 * 2 ^ 59
def prefixEnd_5929732 : Nat := 4983230072969 + 3 ^ 40 * 5929732 * 2
def baseEnd_5929732 : Nat := 3044802668346499129979665

theorem tailTrace_5929732 : CollatzResearch.WordTrace tailWord_5929732 prefixEnd_5929732 3044802668346499129979665 := by
  unfold tailWord_5929732
  simp only [CollatzResearch.WordTrace]
  refine ⟨108137546876800578222071725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144183395835734104296095633 108137546876800578222071725)
  ·
    refine ⟨40551580078800216833276897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108137546876800578222071725 40551580078800216833276897)
    ·
      refine ⟨30413685059100162624957673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40551580078800216833276897 30413685059100162624957673)
      ·
        refine ⟨22810263794325121968718255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30413685059100162624957673 22810263794325121968718255)
        ·
          refine ⟨34215395691487682953077383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22810263794325121968718255 34215395691487682953077383)
          ·
            refine ⟨51323093537231524429616075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34215395691487682953077383 51323093537231524429616075)
            ·
              refine ⟨76984640305847286644424113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51323093537231524429616075 76984640305847286644424113)
              ·
                refine ⟨57738480229385464983318085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76984640305847286644424113 57738480229385464983318085)
                ·
                  refine ⟨10825965043009774684372141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57738480229385464983318085 10825965043009774684372141)
                  ·
                    refine ⟨4059736891128665506639553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10825965043009774684372141 4059736891128665506639553)
                    ·
                      refine ⟨3044802668346499129979665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4059736891128665506639553 3044802668346499129979665)
                      ·
                        rfl

theorem cell23_5929732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 4, 3, 2].length) (baseStart_5929732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929732 prefixEnd_5929732 := by exact prefixLift 5929732
  have htrace : WordTrace (prefixWord ++ tailWord_5929732) baseStart_5929732 baseEnd_5929732 := by
    simpa [prefixWord, tailWord_5929732, baseEnd_5929732] using wordTrace_append hprefix tailTrace_5929732
  have hstable : (prefixWord ++ tailWord_5929732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929732).length < 2 ^ (prefixWord ++ tailWord_5929732).sum := by decide
  have hdescent : baseEnd_5929732 < baseStart_5929732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929745 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 2, 6, 2]
def baseStart_5929745 : Nat := 118140960795 + 5929745 * 2 ^ 59
def prefixEnd_5929745 : Nat := 4983230072969 + 3 ^ 40 * 5929745 * 2
def baseEnd_5929745 : Nat := 3044809343595007579117105

theorem tailTrace_5929745 : CollatzResearch.WordTrace tailWord_5929745 prefixEnd_5929745 3044809343595007579117105 := by
  unfold tailWord_5929745
  simp only [CollatzResearch.WordTrace]
  refine ⟨216275567902554059664366689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144183711935036039776244459 216275567902554059664366689)
  ·
    refine ⟨162206675926915544748275017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216275567902554059664366689 162206675926915544748275017)
    ·
      refine ⟨121655006945186658561206263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162206675926915544748275017 121655006945186658561206263)
      ·
        refine ⟨182482510417779987841809395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121655006945186658561206263 182482510417779987841809395)
        ·
          refine ⟨273723765626669981762714093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182482510417779987841809395 273723765626669981762714093)
          ·
            refine ⟨102646412110001243161017785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273723765626669981762714093 102646412110001243161017785)
            ·
              refine ⟨76984809082500932370763339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102646412110001243161017785 76984809082500932370763339)
              ·
                refine ⟨115477213623751398556145009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76984809082500932370763339 115477213623751398556145009)
                ·
                  refine ⟨86607910217813548917108757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115477213623751398556145009 86607910217813548917108757)
                  ·
                    refine ⟨4059745791460010105489473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86607910217813548917108757 4059745791460010105489473)
                    ·
                      refine ⟨3044809343595007579117105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4059745791460010105489473 3044809343595007579117105)
                      ·
                        rfl

theorem cell23_5929745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 6, 2].length) (baseStart_5929745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929745 prefixEnd_5929745 := by exact prefixLift 5929745
  have htrace : WordTrace (prefixWord ++ tailWord_5929745) baseStart_5929745 baseEnd_5929745 := by
    simpa [prefixWord, tailWord_5929745, baseEnd_5929745] using wordTrace_append hprefix tailTrace_5929745
  have hstable : (prefixWord ++ tailWord_5929745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929745).length < 2 ^ (prefixWord ++ tailWord_5929745).sum := by decide
  have hdescent : baseEnd_5929745 < baseStart_5929745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929772 : List Nat := [2, 2, 1, 1, 1, 4, 4, 2, 2, 4]
def baseStart_5929772 : Nat := 118140960795 + 5929772 * 2 ^ 59
def prefixEnd_5929772 : Nat := 4983230072969 + 3 ^ 40 * 5929772 * 2
def baseEnd_5929772 : Nat := 1014941069190892991159827

theorem tailTrace_5929772 : CollatzResearch.WordTrace tailWord_5929772 prefixEnd_5929772 1014941069190892991159827 := by
  unfold tailWord_5929772
  simp only [CollatzResearch.WordTrace]
  refine ⟨108138276336728121637799785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144184368448970828850399713 108138276336728121637799785)
  ·
    refine ⟨81103707252546091228349839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108138276336728121637799785 81103707252546091228349839)
    ·
      refine ⟨121655560878819136842524759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81103707252546091228349839 121655560878819136842524759)
      ·
        refine ⟨182483341318228705263787139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121655560878819136842524759 182483341318228705263787139)
        ·
          refine ⟨273725011977343057895680709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182483341318228705263787139 273725011977343057895680709)
          ·
            refine ⟨51323439745751823355440133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 273725011977343057895680709 51323439745751823355440133)
            ·
              refine ⟨9623144952328466879145025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51323439745751823355440133 9623144952328466879145025)
              ·
                refine ⟨7217358714246350159358769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9623144952328466879145025 7217358714246350159358769)
                ·
                  refine ⟨5413019035684762619519077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7217358714246350159358769 5413019035684762619519077)
                  ·
                    refine ⟨1014941069190892991159827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5413019035684762619519077 1014941069190892991159827)
                    ·
                      rfl

theorem cell23_5929772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 4].length) (baseStart_5929772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929772 prefixEnd_5929772 := by exact prefixLift 5929772
  have htrace : WordTrace (prefixWord ++ tailWord_5929772) baseStart_5929772 baseEnd_5929772 := by
    simpa [prefixWord, tailWord_5929772, baseEnd_5929772] using wordTrace_append hprefix tailTrace_5929772
  have hstable : (prefixWord ++ tailWord_5929772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929772).length < 2 ^ (prefixWord ++ tailWord_5929772).sum := by decide
  have hdescent : baseEnd_5929772 < baseStart_5929772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929829 : List Nat := [1, 3, 1, 3, 1, 1, 5, 2, 2, 1, 3]
def baseStart_5929829 : Nat := 118140960795 + 5929829 * 2 ^ 59
def prefixEnd_5929829 : Nat := 4983230072969 + 3 ^ 40 * 5929829 * 2
def baseEnd_5929829 : Nat := 3044852475969985250466719

theorem tailTrace_5929829 : CollatzResearch.WordTrace tailWord_5929829 prefixEnd_5929829 3044852475969985250466719 := by
  unfold tailWord_5929829
  simp only [CollatzResearch.WordTrace]
  refine ⟨216278631634249742010424541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144185754422833161340283027 216278631634249742010424541)
  ·
    refine ⟨81104486862843653253909203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216278631634249742010424541 81104486862843653253909203)
    ·
      refine ⟨121656730294265479880863805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81104486862843653253909203 121656730294265479880863805)
      ·
        refine ⟨45621273860349554955323927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121656730294265479880863805 45621273860349554955323927)
        ·
          refine ⟨68431910790524332432985891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45621273860349554955323927 68431910790524332432985891)
          ·
            refine ⟨102647866185786498649478837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68431910790524332432985891 102647866185786498649478837)
            ·
              refine ⟨9623237454917484248388641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102647866185786498649478837 9623237454917484248388641)
              ·
                refine ⟨7217428091188113186291481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9623237454917484248388641 7217428091188113186291481)
                ·
                  refine ⟨5413071068391084889718611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7217428091188113186291481 5413071068391084889718611)
                  ·
                    refine ⟨8119606602586627334577917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5413071068391084889718611 8119606602586627334577917)
                    ·
                      refine ⟨3044852475969985250466719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8119606602586627334577917 3044852475969985250466719)
                      ·
                        rfl

theorem cell23_5929829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_5929829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929829 prefixEnd_5929829 := by exact prefixLift 5929829
  have htrace : WordTrace (prefixWord ++ tailWord_5929829) baseStart_5929829 baseEnd_5929829 := by
    simpa [prefixWord, tailWord_5929829, baseEnd_5929829] using wordTrace_append hprefix tailTrace_5929829
  have hstable : (prefixWord ++ tailWord_5929829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929829).length < 2 ^ (prefixWord ++ tailWord_5929829).sum := by decide
  have hdescent : baseEnd_5929829 < baseStart_5929829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929846 : List Nat := [5, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3]
def baseStart_5929846 : Nat := 118140960795 + 5929846 * 2 ^ 59
def prefixEnd_5929846 : Nat := 4983230072969 + 3 ^ 40 * 5929846 * 2
def baseEnd_5929846 : Nat := 3044861205141111683954141

theorem tailTrace_5929846 : CollatzResearch.WordTrace tailWord_5929846 prefixEnd_5929846 3044861205141111683954141 := by
  unfold tailWord_5929846
  simp only [CollatzResearch.WordTrace]
  refine ⟨13517453229699259619612087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144186167783458769275862261 13517453229699259619612087)
  ·
    refine ⟨20276179844548889429418131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13517453229699259619612087 20276179844548889429418131)
    ·
      refine ⟨30414269766823334144127197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20276179844548889429418131 30414269766823334144127197)
      ·
        refine ⟨11405351162558750304047699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30414269766823334144127197 11405351162558750304047699)
        ·
          refine ⟨17108026743838125456071549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11405351162558750304047699 17108026743838125456071549)
          ·
            refine ⟨6415510028939297046026831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17108026743838125456071549 6415510028939297046026831)
            ·
              refine ⟨9623265043408945569040247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6415510028939297046026831 9623265043408945569040247)
              ·
                refine ⟨14434897565113418353560371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9623265043408945569040247 14434897565113418353560371)
                ·
                  refine ⟨21652346347670127530340557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14434897565113418353560371 21652346347670127530340557)
                  ·
                    refine ⟨8119629880376297823877709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21652346347670127530340557 8119629880376297823877709)
                    ·
                      refine ⟨3044861205141111683954141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8119629880376297823877709 3044861205141111683954141)
                      ·
                        rfl

theorem cell23_5929846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_5929846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929846 prefixEnd_5929846 := by exact prefixLift 5929846
  have htrace : WordTrace (prefixWord ++ tailWord_5929846) baseStart_5929846 baseEnd_5929846 := by
    simpa [prefixWord, tailWord_5929846, baseEnd_5929846] using wordTrace_append hprefix tailTrace_5929846
  have hstable : (prefixWord ++ tailWord_5929846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929846).length < 2 ^ (prefixWord ++ tailWord_5929846).sum := by decide
  have hdescent : baseEnd_5929846 < baseStart_5929846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929855 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 2, 4, 3]
def baseStart_5929855 : Nat := 118140960795 + 5929855 * 2 ^ 59
def prefixEnd_5929855 : Nat := 4983230072969 + 3 ^ 40 * 5929855 * 2
def baseEnd_5929855 : Nat := 3044865826467002148741599

theorem tailTrace_5929855 : CollatzResearch.WordTrace tailWord_5929855 prefixEnd_5929855 3044865826467002148741599 := by
  unfold tailWord_5929855
  simp only [CollatzResearch.WordTrace]
  refine ⟨216279579932155548450871019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144186386621437032300580679 216279579932155548450871019)
  ·
    refine ⟨324419369898233322676306529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216279579932155548450871019 324419369898233322676306529)
    ·
      refine ⟨243314527423674992007229897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324419369898233322676306529 243314527423674992007229897)
      ·
        refine ⟨182485895567756244005422423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243314527423674992007229897 182485895567756244005422423)
        ·
          refine ⟨273728843351634366008133635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182485895567756244005422423 273728843351634366008133635)
          ·
            refine ⟨410593265027451549012200453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273728843351634366008133635 410593265027451549012200453)
            ·
              refine ⟨76986237192647165439787585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 410593265027451549012200453 76986237192647165439787585)
              ·
                refine ⟨57739677894485374079840689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76986237192647165439787585 57739677894485374079840689)
                ·
                  refine ⟨43304758420864030559880517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57739677894485374079840689 43304758420864030559880517)
                  ·
                    refine ⟨8119642203912005729977597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43304758420864030559880517 8119642203912005729977597)
                    ·
                      refine ⟨3044865826467002148741599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8119642203912005729977597 3044865826467002148741599)
                      ·
                        rfl

theorem cell23_5929855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4, 3].length) (baseStart_5929855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929855 prefixEnd_5929855 := by exact prefixLift 5929855
  have htrace : WordTrace (prefixWord ++ tailWord_5929855) baseStart_5929855 baseEnd_5929855 := by
    simpa [prefixWord, tailWord_5929855, baseEnd_5929855] using wordTrace_append hprefix tailTrace_5929855
  have hstable : (prefixWord ++ tailWord_5929855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929855).length < 2 ^ (prefixWord ++ tailWord_5929855).sum := by decide
  have hdescent : baseEnd_5929855 < baseStart_5929855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929885 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_5929885 : Nat := 118140960795 + 5929885 * 2 ^ 59
def prefixEnd_5929885 : Nat := 4983230072969 + 3 ^ 40 * 5929885 * 2
def baseEnd_5929885 : Nat := 3044881230886637031366461

theorem tailTrace_5929885 : CollatzResearch.WordTrace tailWord_5929885 prefixEnd_5929885 3044881230886637031366461 := by
  unfold tailWord_5929885
  simp only [CollatzResearch.WordTrace]
  refine ⟨216280674122046863574463109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144187116081364575716308739 216280674122046863574463109)
  ·
    refine ⟨40552626397883786920211833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216280674122046863574463109 40552626397883786920211833)
    ·
      refine ⟨30414469798412840190158875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40552626397883786920211833 30414469798412840190158875)
      ·
        refine ⟨45621704697619260285238313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30414469798412840190158875 45621704697619260285238313)
        ·
          refine ⟨34216278523214445213928735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45621704697619260285238313 34216278523214445213928735)
          ·
            refine ⟨51324417784821667820893103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34216278523214445213928735 51324417784821667820893103)
            ·
              refine ⟨76986626677232501731339655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51324417784821667820893103 76986626677232501731339655)
              ·
                refine ⟨115479940015848752597009483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76986626677232501731339655 115479940015848752597009483)
                ·
                  refine ⟨173219910023773128895514225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115479940015848752597009483 173219910023773128895514225)
                  ·
                    refine ⟨129914932517829846671635669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 173219910023773128895514225 129914932517829846671635669)
                    ·
                      refine ⟨3044881230886637031366461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129914932517829846671635669 3044881230886637031366461)
                      ·
                        rfl

theorem cell23_5929885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_5929885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929885 prefixEnd_5929885 := by exact prefixLift 5929885
  have htrace : WordTrace (prefixWord ++ tailWord_5929885) baseStart_5929885 baseEnd_5929885 := by
    simpa [prefixWord, tailWord_5929885, baseEnd_5929885] using wordTrace_append hprefix tailTrace_5929885
  have hstable : (prefixWord ++ tailWord_5929885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929885).length < 2 ^ (prefixWord ++ tailWord_5929885).sum := by decide
  have hdescent : baseEnd_5929885 < baseStart_5929885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929925 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 5, 3, 4]
def baseStart_5929925 : Nat := 118140960795 + 5929925 * 2 ^ 59
def prefixEnd_5929925 : Nat := 4983230072969 + 3 ^ 40 * 5929925 * 2
def baseEnd_5929925 : Nat := 3044901770112816874866277

theorem tailTrace_5929925 : CollatzResearch.WordTrace tailWord_5929925 prefixEnd_5929925 3044901770112816874866277 := by
  unfold tailWord_5929925
  simp only [CollatzResearch.WordTrace]
  refine ⟨216282133041901950405919229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144188088694601300270612819 216282133041901950405919229)
  ·
    refine ⟨81105799890713231402219711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216282133041901950405919229 81105799890713231402219711)
    ·
      refine ⟨121658699836069847103329567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81105799890713231402219711 121658699836069847103329567)
      ·
        refine ⟨182488049754104770654994351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121658699836069847103329567 182488049754104770654994351)
        ·
          refine ⟨273732074631157155982491527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182488049754104770654994351 273732074631157155982491527)
          ·
            refine ⟨410598111946735733973737291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273732074631157155982491527 410598111946735733973737291)
            ·
              refine ⟨615897167920103600960605937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410598111946735733973737291 615897167920103600960605937)
              ·
                refine ⟨461922875940077700720454453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 615897167920103600960605937 461922875940077700720454453)
                ·
                  refine ⟨43305269619382284442542605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 461922875940077700720454453 43305269619382284442542605)
                  ·
                    refine ⟨16239476107268356665953477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43305269619382284442542605 16239476107268356665953477)
                    ·
                      refine ⟨3044901770112816874866277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16239476107268356665953477 3044901770112816874866277)
                      ·
                        rfl

theorem cell23_5929925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 3, 4].length) (baseStart_5929925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929925 prefixEnd_5929925 := by exact prefixLift 5929925
  have htrace : WordTrace (prefixWord ++ tailWord_5929925) baseStart_5929925 baseEnd_5929925 := by
    simpa [prefixWord, tailWord_5929925, baseEnd_5929925] using wordTrace_append hprefix tailTrace_5929925
  have hstable : (prefixWord ++ tailWord_5929925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929925).length < 2 ^ (prefixWord ++ tailWord_5929925).sum := by decide
  have hdescent : baseEnd_5929925 < baseStart_5929925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929959 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 1, 6, 2]
def baseStart_5929959 : Nat := 118140960795 + 5929959 * 2 ^ 59
def prefixEnd_5929959 : Nat := 4983230072969 + 3 ^ 40 * 5929959 * 2
def baseEnd_5929959 : Nat := 3044919228455069741841121

theorem tailTrace_5929959 : CollatzResearch.WordTrace tailWord_5929959 prefixEnd_5929959 3044919228455069741841121 := by
  unfold tailWord_5929959
  simp only [CollatzResearch.WordTrace]
  refine ⟨216283373123778774212656931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144188915415852516141771287 216283373123778774212656931)
  ·
    refine ⟨324425059685668161318985397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216283373123778774212656931 324425059685668161318985397)
    ·
      refine ⟨30414849345531390123654881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 324425059685668161318985397 30414849345531390123654881)
      ·
        refine ⟨22811137009148542592741161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30414849345531390123654881 22811137009148542592741161)
        ·
          refine ⟨17108352756861406944555871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22811137009148542592741161 17108352756861406944555871)
          ·
            refine ⟨25662529135292110416833807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17108352756861406944555871 25662529135292110416833807)
            ·
              refine ⟨38493793702938165625250711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25662529135292110416833807 38493793702938165625250711)
              ·
                refine ⟨57740690554407248437876067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38493793702938165625250711 57740690554407248437876067)
                ·
                  refine ⟨86611035831610872656814101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57740690554407248437876067 86611035831610872656814101)
                  ·
                    refine ⟨4059892304606759655788161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86611035831610872656814101 4059892304606759655788161)
                    ·
                      refine ⟨3044919228455069741841121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4059892304606759655788161 3044919228455069741841121)
                      ·
                        rfl

theorem cell23_5929959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_5929959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929959 prefixEnd_5929959 := by exact prefixLift 5929959
  have htrace : WordTrace (prefixWord ++ tailWord_5929959) baseStart_5929959 baseEnd_5929959 := by
    simpa [prefixWord, tailWord_5929959, baseEnd_5929959] using wordTrace_append hprefix tailTrace_5929959
  have hstable : (prefixWord ++ tailWord_5929959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929959).length < 2 ^ (prefixWord ++ tailWord_5929959).sum := by decide
  have hdescent : baseEnd_5929959 < baseStart_5929959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929969 : List Nat := [1, 2, 2, 2, 4, 2, 1, 2, 3, 4]
def baseStart_5929969 : Nat := 118140960795 + 5929969 * 2 ^ 59
def prefixEnd_5929969 : Nat := 4983230072969 + 3 ^ 40 * 5929969 * 2
def baseEnd_5929969 : Nat := 1014974787753871567572025

theorem tailTrace_5929969 : CollatzResearch.WordTrace tailWord_5929969 prefixEnd_5929969 1014974787753871567572025 := by
  unfold tailWord_5929969
  simp only [CollatzResearch.WordTrace]
  refine ⟨216283737853742545920520961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144189158569161697280347307 216283737853742545920520961)
  ·
    refine ⟨162212803390306909440390721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216283737853742545920520961 162212803390306909440390721)
    ·
      refine ⟨121659602542730182080293041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162212803390306909440390721 121659602542730182080293041)
      ·
        refine ⟨91244701907047636560219781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121659602542730182080293041 91244701907047636560219781)
        ·
          refine ⟨17108381607571431855041209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91244701907047636560219781 17108381607571431855041209)
          ·
            refine ⟨12831286205678573891280907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17108381607571431855041209 12831286205678573891280907)
            ·
              refine ⟨19246929308517860836921361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12831286205678573891280907 19246929308517860836921361)
              ·
                refine ⟨14435196981388395627691021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19246929308517860836921361 14435196981388395627691021)
                ·
                  refine ⟨5413198868020648360384133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14435196981388395627691021 5413198868020648360384133)
                  ·
                    refine ⟨1014974787753871567572025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5413198868020648360384133 1014974787753871567572025)
                    ·
                      rfl

theorem cell23_5929969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3, 4].length) (baseStart_5929969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929969 prefixEnd_5929969 := by exact prefixLift 5929969
  have htrace : WordTrace (prefixWord ++ tailWord_5929969) baseStart_5929969 baseEnd_5929969 := by
    simpa [prefixWord, tailWord_5929969, baseEnd_5929969] using wordTrace_append hprefix tailTrace_5929969
  have hstable : (prefixWord ++ tailWord_5929969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929969).length < 2 ^ (prefixWord ++ tailWord_5929969).sum := by decide
  have hdescent : baseEnd_5929969 < baseStart_5929969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5929973 : List Nat := [1, 3, 5, 2, 1, 2, 1, 1, 2, 5]
def baseStart_5929973 : Nat := 118140960795 + 5929973 * 2 ^ 59
def prefixEnd_5929973 : Nat := 4983230072969 + 3 ^ 40 * 5929973 * 2
def baseEnd_5929973 : Nat := 1014975472394744229022019

theorem tailTrace_5929973 : CollatzResearch.WordTrace tailWord_5929973 prefixEnd_5929973 1014975472394744229022019 := by
  unfold tailWord_5929973
  simp only [CollatzResearch.WordTrace]
  refine ⟨216283883745728054603666573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144189255830485369735777715 216283883745728054603666573)
  ·
    refine ⟨81106456404648020476374965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216283883745728054603666573 81106456404648020476374965)
    ·
      refine ⟨7603730287935751919660153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81106456404648020476374965 7603730287935751919660153)
      ·
        refine ⟨5702797715951813939745115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7603730287935751919660153 5702797715951813939745115)
        ·
          refine ⟨8554196573927720909617673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5702797715951813939745115 8554196573927720909617673)
          ·
            refine ⟨6415647430445790682213255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8554196573927720909617673 6415647430445790682213255)
            ·
              refine ⟨9623471145668686023319883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6415647430445790682213255 9623471145668686023319883)
              ·
                refine ⟨14435206718503029034979825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9623471145668686023319883 14435206718503029034979825)
                ·
                  refine ⟨10826405038877271776234869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14435206718503029034979825 10826405038877271776234869)
                  ·
                    refine ⟨1014975472394744229022019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10826405038877271776234869 1014975472394744229022019)
                    ·
                      rfl

theorem cell23_5929973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_5929973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5929973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5929973 prefixEnd_5929973 := by exact prefixLift 5929973
  have htrace : WordTrace (prefixWord ++ tailWord_5929973) baseStart_5929973 baseEnd_5929973 := by
    simpa [prefixWord, tailWord_5929973, baseEnd_5929973] using wordTrace_append hprefix tailTrace_5929973
  have hstable : (prefixWord ++ tailWord_5929973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5929973).length < 2 ^ (prefixWord ++ tailWord_5929973).sum := by decide
  have hdescent : baseEnd_5929973 < baseStart_5929973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5929973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930009 : List Nat := [1, 2, 1, 2, 1, 1, 5, 3, 3, 1, 3]
def baseStart_5930009 : Nat := 118140960795 + 5930009 * 2 ^ 59
def prefixEnd_5930009 : Nat := 4983230072969 + 3 ^ 40 * 5930009 * 2
def baseEnd_5930009 : Nat := 3044944902487794546215891

theorem tailTrace_5930009 : CollatzResearch.WordTrace tailWord_5930009 prefixEnd_5930009 3044944902487794546215891 := by
  unfold tailWord_5930009
  simp only [CollatzResearch.WordTrace]
  refine ⟨216285196773597632751977081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144190131182398421834651387 216285196773597632751977081)
  ·
    refine ⟨162213897580198224563982811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216285196773597632751977081 162213897580198224563982811)
    ·
      refine ⟨243320846370297336845974217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162213897580198224563982811 243320846370297336845974217)
      ·
        refine ⟨182490634777723002634480663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243320846370297336845974217 182490634777723002634480663)
        ·
          refine ⟨273735952166584503951720995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182490634777723002634480663 273735952166584503951720995)
          ·
            refine ⟨410603928249876755927581493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273735952166584503951720995 410603928249876755927581493)
            ·
              refine ⟨38494118273425945868210765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 410603928249876755927581493 38494118273425945868210765)
              ·
                refine ⟨14435294352534729700579037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38494118273425945868210765 14435294352534729700579037)
                ·
                  refine ⟨5413235382200523637717139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14435294352534729700579037 5413235382200523637717139)
                  ·
                    refine ⟨8119853073300785456575709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5413235382200523637717139 8119853073300785456575709)
                    ·
                      refine ⟨3044944902487794546215891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8119853073300785456575709 3044944902487794546215891)
                      ·
                        rfl

theorem cell23_5930009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 3, 1, 3].length) (baseStart_5930009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930009 prefixEnd_5930009 := by exact prefixLift 5930009
  have htrace : WordTrace (prefixWord ++ tailWord_5930009) baseStart_5930009 baseEnd_5930009 := by
    simpa [prefixWord, tailWord_5930009, baseEnd_5930009] using wordTrace_append hprefix tailTrace_5930009
  have hstable : (prefixWord ++ tailWord_5930009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930009).length < 2 ^ (prefixWord ++ tailWord_5930009).sum := by decide
  have hdescent : baseEnd_5930009 < baseStart_5930009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930019 : List Nat := [1, 1, 1, 4, 3, 2, 1, 2, 1, 5, 2]
def baseStart_5930019 : Nat := 118140960795 + 5930019 * 2 ^ 59
def prefixEnd_5930019 : Nat := 4983230072969 + 3 ^ 40 * 5930019 * 2
def baseEnd_5930019 : Nat := 3044950037294339507090845

theorem tailTrace_5930019 : CollatzResearch.WordTrace tailWord_5930019 prefixEnd_5930019 3044950037294339507090845 := by
  unfold tailWord_5930019
  simp only [CollatzResearch.WordTrace]
  refine ⟨216285561503561404459841111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144190374335707602973227407 216285561503561404459841111)
  ·
    refine ⟨324428342255342106689761667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216285561503561404459841111 324428342255342106689761667)
    ·
      refine ⟨486642513383013160034642501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324428342255342106689761667 486642513383013160034642501)
      ·
        refine ⟨91245471259314967506495469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 486642513383013160034642501 91245471259314967506495469)
        ·
          refine ⟨34217051722243112814935801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91245471259314967506495469 34217051722243112814935801)
          ·
            refine ⟨25662788791682334611201851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34217051722243112814935801 25662788791682334611201851)
            ·
              refine ⟨38494183187523501916802777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25662788791682334611201851 38494183187523501916802777)
              ·
                refine ⟨28870637390642626437602083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38494183187523501916802777 28870637390642626437602083)
                ·
                  refine ⟨43305956085963939656403125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28870637390642626437602083 43305956085963939656403125)
                  ·
                    refine ⟨4059933383059119342787793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43305956085963939656403125 4059933383059119342787793)
                    ·
                      refine ⟨3044950037294339507090845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4059933383059119342787793 3044950037294339507090845)
                      ·
                        rfl

theorem cell23_5930019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 5, 2].length) (baseStart_5930019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930019 prefixEnd_5930019 := by exact prefixLift 5930019
  have htrace : WordTrace (prefixWord ++ tailWord_5930019) baseStart_5930019 baseEnd_5930019 := by
    simpa [prefixWord, tailWord_5930019, baseEnd_5930019] using wordTrace_append hprefix tailTrace_5930019
  have hstable : (prefixWord ++ tailWord_5930019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930019).length < 2 ^ (prefixWord ++ tailWord_5930019).sum := by decide
  have hdescent : baseEnd_5930019 < baseStart_5930019 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930042 : List Nat := [3, 1, 1, 1, 3, 1, 2, 4, 1, 6]
def baseStart_5930042 : Nat := 118140960795 + 5930042 * 2 ^ 59
def prefixEnd_5930042 : Nat := 4983230072969 + 3 ^ 40 * 5930042 * 2
def baseEnd_5930042 : Nat := 1014987282449797639034413

theorem tailTrace_5930042 : CollatzResearch.WordTrace tailWord_5930042 prefixEnd_5930042 1014987282449797639034413 := by
  unfold tailWord_5930042
  simp only [CollatzResearch.WordTrace]
  refine ⟨54071600095619519846982095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144190933588318719591952253 54071600095619519846982095)
  ·
    refine ⟨81107400143429279770473143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54071600095619519846982095 81107400143429279770473143)
    ·
      refine ⟨121661100215143919655709715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81107400143429279770473143 121661100215143919655709715)
      ·
        refine ⟨182491650322715879483564573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121661100215143919655709715 182491650322715879483564573)
        ·
          refine ⟨68434368871018454806336715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182491650322715879483564573 68434368871018454806336715)
          ·
            refine ⟨102651553306527682209505073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68434368871018454806336715 102651553306527682209505073)
            ·
              refine ⟨76988664979895761657128805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102651553306527682209505073 76988664979895761657128805)
              ·
                refine ⟨14435374683730455310711651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76988664979895761657128805 14435374683730455310711651)
                ·
                  refine ⟨21653062025595682966067477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14435374683730455310711651 21653062025595682966067477)
                  ·
                    refine ⟨1014987282449797639034413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21653062025595682966067477 1014987282449797639034413)
                    ·
                      rfl

theorem cell23_5930042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 1, 6].length) (baseStart_5930042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930042 prefixEnd_5930042 := by exact prefixLift 5930042
  have htrace : WordTrace (prefixWord ++ tailWord_5930042) baseStart_5930042 baseEnd_5930042 := by
    simpa [prefixWord, tailWord_5930042, baseEnd_5930042] using wordTrace_append hprefix tailTrace_5930042
  have hstable : (prefixWord ++ tailWord_5930042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930042).length < 2 ^ (prefixWord ++ tailWord_5930042).sum := by decide
  have hdescent : baseEnd_5930042 < baseStart_5930042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930046 : List Nat := [4, 2, 1, 3, 1, 1, 2, 3, 1, 5]
def baseStart_5930046 : Nat := 118140960795 + 5930046 * 2 ^ 59
def prefixEnd_5930046 : Nat := 4983230072969 + 3 ^ 40 * 5930046 * 2
def baseEnd_5930046 : Nat := 1014987967090670300484407

theorem tailTrace_5930046 : CollatzResearch.WordTrace tailWord_5930046 prefixEnd_5930046 1014987967090670300484407 := by
  unfold tailWord_5930046
  simp only [CollatzResearch.WordTrace]
  refine ⟨27035818284307948508884249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144191030849642392047382661 27035818284307948508884249)
  ·
    refine ⟨20276863713230961381663187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27035818284307948508884249 20276863713230961381663187)
    ·
      refine ⟨30415295569846442072494781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20276863713230961381663187 30415295569846442072494781)
      ·
        refine ⟨11405735838692415777185543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30415295569846442072494781 11405735838692415777185543)
        ·
          refine ⟨17108603758038623665778315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11405735838692415777185543 17108603758038623665778315)
          ·
            refine ⟨25662905637057935498667473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17108603758038623665778315 25662905637057935498667473)
            ·
              refine ⟨19247179227793451624000605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25662905637057935498667473 19247179227793451624000605)
              ·
                refine ⟨7217692210422544359000227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19247179227793451624000605 7217692210422544359000227)
                ·
                  refine ⟨10826538315633816538500341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7217692210422544359000227 10826538315633816538500341)
                  ·
                    refine ⟨1014987967090670300484407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10826538315633816538500341 1014987967090670300484407)
                    ·
                      rfl

theorem cell23_5930046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_5930046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930046 prefixEnd_5930046 := by exact prefixLift 5930046
  have htrace : WordTrace (prefixWord ++ tailWord_5930046) baseStart_5930046 baseEnd_5930046 := by
    simpa [prefixWord, tailWord_5930046, baseEnd_5930046] using wordTrace_append hprefix tailTrace_5930046
  have hstable : (prefixWord ++ tailWord_5930046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930046).length < 2 ^ (prefixWord ++ tailWord_5930046).sum := by decide
  have hdescent : baseEnd_5930046 < baseStart_5930046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930062 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6]
def baseStart_5930062 : Nat := 118140960795 + 5930062 * 2 ^ 59
def prefixEnd_5930062 : Nat := 4983230072969 + 3 ^ 40 * 5930062 * 2
def baseEnd_5930062 : Nat := 3044972116962482838853147

theorem tailTrace_5930062 : CollatzResearch.WordTrace tailWord_5930062 prefixEnd_5930062 3044972116962482838853147 := by
  unfold tailWord_5930062
  simp only [CollatzResearch.WordTrace]
  refine ⟨27035891230300702850457055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144191419894937081869104293 27035891230300702850457055)
  ·
    refine ⟨40553836845451054275685583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27035891230300702850457055 40553836845451054275685583)
    ·
      refine ⟨60830755268176581413528375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40553836845451054275685583 60830755268176581413528375)
      ·
        refine ⟨91246132902264872120292563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60830755268176581413528375 91246132902264872120292563)
        ·
          refine ⟨136869199353397308180438845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91246132902264872120292563 136869199353397308180438845)
          ·
            refine ⟨51325949757523990567664567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136869199353397308180438845 51325949757523990567664567)
            ·
              refine ⟨76988924636285985851496851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51325949757523990567664567 76988924636285985851496851)
              ·
                refine ⟨115483386954428978777245277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76988924636285985851496851 115483386954428978777245277)
                ·
                  refine ⟨43306270107910867041466979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 115483386954428978777245277 43306270107910867041466979)
                  ·
                    refine ⟨64959405161866300562200469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43306270107910867041466979 64959405161866300562200469)
                    ·
                      refine ⟨3044972116962482838853147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64959405161866300562200469 3044972116962482838853147)
                      ·
                        rfl

theorem cell23_5930062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_5930062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930062 prefixEnd_5930062 := by exact prefixLift 5930062
  have htrace : WordTrace (prefixWord ++ tailWord_5930062) baseStart_5930062 baseEnd_5930062 := by
    simpa [prefixWord, tailWord_5930062, baseEnd_5930062] using wordTrace_append hprefix tailTrace_5930062
  have hstable : (prefixWord ++ tailWord_5930062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930062).length < 2 ^ (prefixWord ++ tailWord_5930062).sum := by decide
  have hdescent : baseEnd_5930062 < baseStart_5930062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930069 : List Nat := [1, 3, 2, 2, 1, 2, 2, 2, 3, 2, 3]
def baseStart_5930069 : Nat := 118140960795 + 5930069 * 2 ^ 59
def prefixEnd_5930069 : Nat := 4983230072969 + 3 ^ 40 * 5930069 * 2
def baseEnd_5930069 : Nat := 3044975711327064311465615

theorem tailTrace_5930069 : CollatzResearch.WordTrace tailWord_5930069 prefixEnd_5930069 3044975711327064311465615 := by
  unfold tailWord_5930069
  simp only [CollatzResearch.WordTrace]
  refine ⟨216287385153380262999161261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144191590102253508666107507 216287385153380262999161261)
  ·
    refine ⟨81107769432517598624685473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216287385153380262999161261 81107769432517598624685473)
    ·
      refine ⟨60830827074388198968514105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81107769432517598624685473 60830827074388198968514105)
      ·
        refine ⟨45623120305791149226385579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60830827074388198968514105 45623120305791149226385579)
        ·
          refine ⟨68434680458686723839578369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45623120305791149226385579 68434680458686723839578369)
          ·
            refine ⟨51326010344015042879683777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68434680458686723839578369 51326010344015042879683777)
            ·
              refine ⟨38494507758011282159762833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51326010344015042879683777 38494507758011282159762833)
              ·
                refine ⟨28870880818508461619822125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38494507758011282159762833 28870880818508461619822125)
                ·
                  refine ⟨10826580306940673107433297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28870880818508461619822125 10826580306940673107433297)
                  ·
                    refine ⟨8119935230205504830574973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10826580306940673107433297 8119935230205504830574973)
                    ·
                      refine ⟨3044975711327064311465615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8119935230205504830574973 3044975711327064311465615)
                      ·
                        rfl

theorem cell23_5930069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_5930069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930069 prefixEnd_5930069 := by exact prefixLift 5930069
  have htrace : WordTrace (prefixWord ++ tailWord_5930069) baseStart_5930069 baseEnd_5930069 := by
    simpa [prefixWord, tailWord_5930069, baseEnd_5930069] using wordTrace_append hprefix tailTrace_5930069
  have hstable : (prefixWord ++ tailWord_5930069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930069).length < 2 ^ (prefixWord ++ tailWord_5930069).sum := by decide
  have hdescent : baseEnd_5930069 < baseStart_5930069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930072 : List Nat := [2, 1, 2, 2, 1, 3, 4, 8]
def baseStart_5930072 : Nat := 118140960795 + 5930072 * 2 ^ 59
def prefixEnd_5930072 : Nat := 4983230072969 + 3 ^ 40 * 5930072 * 2
def baseEnd_5930072 : Nat := 112776935250704733323263

theorem tailTrace_5930072 : CollatzResearch.WordTrace tailWord_5930072 prefixEnd_5930072 112776935250704733323263 := by
  unfold tailWord_5930072
  simp only [CollatzResearch.WordTrace]
  refine ⟨108143747286184697255760235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144191663048246263007680313 108143747286184697255760235)
  ·
    refine ⟨162215620929277045883640353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108143747286184697255760235 162215620929277045883640353)
    ·
      refine ⟨121661715696957784412730265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162215620929277045883640353 121661715696957784412730265)
      ·
        refine ⟨91246286772718338309547699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121661715696957784412730265 91246286772718338309547699)
        ·
          refine ⟨136869430159077507464321549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91246286772718338309547699 136869430159077507464321549)
          ·
            refine ⟨51326036309654065299120581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136869430159077507464321549 51326036309654065299120581)
            ·
              refine ⟨9623631808060137243585109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51326036309654065299120581 9623631808060137243585109)
              ·
                refine ⟨112776935250704733323263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9623631808060137243585109 112776935250704733323263)
                ·
                  rfl

theorem cell23_5930072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 8].length) (baseStart_5930072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930072 prefixEnd_5930072 := by exact prefixLift 5930072
  have htrace : WordTrace (prefixWord ++ tailWord_5930072) baseStart_5930072 baseEnd_5930072 := by
    simpa [prefixWord, tailWord_5930072, baseEnd_5930072] using wordTrace_append hprefix tailTrace_5930072
  have hstable : (prefixWord ++ tailWord_5930072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930072).length < 2 ^ (prefixWord ++ tailWord_5930072).sum := by decide
  have hdescent : baseEnd_5930072 < baseStart_5930072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930076 : List Nat := [2, 2, 4, 1, 1, 1, 3, 3, 2, 4]
def baseStart_5930076 : Nat := 118140960795 + 5930076 * 2 ^ 59
def prefixEnd_5930076 : Nat := 4983230072969 + 3 ^ 40 * 5930076 * 2
def baseEnd_5930076 : Nat := 1014993101897215261359361

theorem tailTrace_5930076 : CollatzResearch.WordTrace tailWord_5930076 prefixEnd_5930076 1014993101897215261359361 := by
  unfold tailWord_5930076
  simp only [CollatzResearch.WordTrace]
  refine ⟨108143820232177451597333041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144191760309569935463110721 108143820232177451597333041)
  ·
    refine ⟨81107865174133088697999781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108143820232177451597333041 81107865174133088697999781)
    ·
      refine ⟨15207724720149954130874959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81107865174133088697999781 15207724720149954130874959)
      ·
        refine ⟨22811587080224931196312439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15207724720149954130874959 22811587080224931196312439)
        ·
          refine ⟨34217380620337396794468659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22811587080224931196312439 34217380620337396794468659)
          ·
            refine ⟨51326070930506095191702989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34217380620337396794468659 51326070930506095191702989)
            ·
              refine ⟨19247276598939785696888621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51326070930506095191702989 19247276598939785696888621)
              ·
                refine ⟨7217728724602419636333233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19247276598939785696888621 7217728724602419636333233)
                ·
                  refine ⟨5413296543451814727249925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7217728724602419636333233 5413296543451814727249925)
                  ·
                    refine ⟨1014993101897215261359361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5413296543451814727249925 1014993101897215261359361)
                    ·
                      rfl

theorem cell23_5930076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_5930076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930076 prefixEnd_5930076 := by exact prefixLift 5930076
  have htrace : WordTrace (prefixWord ++ tailWord_5930076) baseStart_5930076 baseEnd_5930076 := by
    simpa [prefixWord, tailWord_5930076, baseEnd_5930076] using wordTrace_append hprefix tailTrace_5930076
  have hstable : (prefixWord ++ tailWord_5930076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930076).length < 2 ^ (prefixWord ++ tailWord_5930076).sum := by decide
  have hdescent : baseEnd_5930076 < baseStart_5930076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930112 : List Nat := [2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 5]
def baseStart_5930112 : Nat := 118140960795 + 5930112 * 2 ^ 59
def prefixEnd_5930112 : Nat := 4983230072969 + 3 ^ 40 * 5930112 * 2
def baseEnd_5930112 : Nat := 3044997790995207643227917

theorem tailTrace_5930112 : CollatzResearch.WordTrace tailWord_5930112 prefixEnd_5930112 3044997790995207643227917 := by
  unfold tailWord_5930112
  simp only [CollatzResearch.WordTrace]
  refine ⟨108144476746112240671488295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144192635661482987561984393 108144476746112240671488295)
  ·
    refine ⟨162216715119168361007232443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108144476746112240671488295 162216715119168361007232443)
    ·
      refine ⟨243325072678752541510848665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162216715119168361007232443 243325072678752541510848665)
      ·
        refine ⟨182493804509064406133136499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243325072678752541510848665 182493804509064406133136499)
        ·
          refine ⟨273740706763596609199704749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182493804509064406133136499 273740706763596609199704749)
          ·
            refine ⟨102652765036348728449889281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273740706763596609199704749 102652765036348728449889281)
            ·
              refine ⟨76989573777261546337416961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102652765036348728449889281 76989573777261546337416961)
              ·
                refine ⟨57742180332946159753062721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76989573777261546337416961 57742180332946159753062721)
                ·
                  refine ⟨43306635249709619814797041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57742180332946159753062721 43306635249709619814797041)
                  ·
                    refine ⟨32479976437282214861097781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43306635249709619814797041 32479976437282214861097781)
                    ·
                      refine ⟨3044997790995207643227917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32479976437282214861097781 3044997790995207643227917)
                      ·
                        rfl

theorem cell23_5930112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_5930112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930112 prefixEnd_5930112 := by exact prefixLift 5930112
  have htrace : WordTrace (prefixWord ++ tailWord_5930112) baseStart_5930112 baseEnd_5930112 := by
    simpa [prefixWord, tailWord_5930112, baseEnd_5930112] using wordTrace_append hprefix tailTrace_5930112
  have hstable : (prefixWord ++ tailWord_5930112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930112).length < 2 ^ (prefixWord ++ tailWord_5930112).sum := by decide
  have hdescent : baseEnd_5930112 < baseStart_5930112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930169 : List Nat := [1, 2, 1, 4, 1, 3, 1, 2, 2, 2, 4]
def baseStart_5930169 : Nat := 118140960795 + 5930169 * 2 ^ 59
def prefixEnd_5930169 : Nat := 4983230072969 + 3 ^ 40 * 5930169 * 2
def baseEnd_5930169 : Nat := 3045027059392513920215155

theorem tailTrace_5930169 : CollatzResearch.WordTrace tailWord_5930169 prefixEnd_5930169 3045027059392513920215155 := by
  unfold tailWord_5930169
  simp only [CollatzResearch.WordTrace]
  refine ⟨216291032453017980077801561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144194021635345320051867707 216291032453017980077801561)
  ·
    refine ⟨162218274339763485058351171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216291032453017980077801561 162218274339763485058351171)
    ·
      refine ⟨243327411509645227587526757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162218274339763485058351171 243327411509645227587526757)
      ·
        refine ⟨45623889658058480172661267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 243327411509645227587526757 45623889658058480172661267)
        ·
          refine ⟨68435834487087720258991901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45623889658058480172661267 68435834487087720258991901)
          ·
            refine ⟨25663437932657895097121963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68435834487087720258991901 25663437932657895097121963)
            ·
              refine ⟨38495156898986842645682945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25663437932657895097121963 38495156898986842645682945)
              ·
                refine ⟨28871367674240131984262209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38495156898986842645682945 28871367674240131984262209)
                ·
                  refine ⟨21653525755680098988196657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28871367674240131984262209 21653525755680098988196657)
                  ·
                    refine ⟨16240144316760074241147493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21653525755680098988196657 16240144316760074241147493)
                    ·
                      refine ⟨3045027059392513920215155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16240144316760074241147493 3045027059392513920215155)
                      ·
                        rfl

theorem cell23_5930169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_5930169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930169 prefixEnd_5930169 := by exact prefixLift 5930169
  have htrace : WordTrace (prefixWord ++ tailWord_5930169) baseStart_5930169 baseEnd_5930169 := by
    simpa [prefixWord, tailWord_5930169, baseEnd_5930169] using wordTrace_append hprefix tailTrace_5930169
  have hstable : (prefixWord ++ tailWord_5930169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930169).length < 2 ^ (prefixWord ++ tailWord_5930169).sum := by decide
  have hdescent : baseEnd_5930169 < baseStart_5930169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930190 : List Nat := [4, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2]
def baseStart_5930190 : Nat := 118140960795 + 5930190 * 2 ^ 59
def prefixEnd_5930190 : Nat := 4983230072969 + 3 ^ 40 * 5930190 * 2
def baseEnd_5930190 : Nat := 3045037842486258338052559

theorem tailTrace_5930190 : CollatzResearch.WordTrace tailWord_5930190 prefixEnd_5930190 3045037842486258338052559 := by
  unfold tailWord_5930190
  simp only [CollatzResearch.WordTrace]
  refine ⟨27036474798242737583039503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144194532257294600442877349 27036474798242737583039503)
  ·
    refine ⟨40554712197364106374559255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27036474798242737583039503 40554712197364106374559255)
    ·
      refine ⟨60832068296046159561838883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40554712197364106374559255 60832068296046159561838883)
      ·
        refine ⟨91248102444069239342758325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60832068296046159561838883 91248102444069239342758325)
        ·
          refine ⟨8554509604131491188383593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91248102444069239342758325 8554509604131491188383593)
          ·
            refine ⟨6415882203098618391287695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8554509604131491188383593 6415882203098618391287695)
            ·
              refine ⟨9623823304647927586931543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6415882203098618391287695 9623823304647927586931543)
              ·
                refine ⟨14435734956971891380397315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9623823304647927586931543 14435734956971891380397315)
                ·
                  refine ⟨21653602435457837070595973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14435734956971891380397315 21653602435457837070595973)
                  ·
                    refine ⟨4060050456648344450736745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21653602435457837070595973 4060050456648344450736745)
                    ·
                      refine ⟨3045037842486258338052559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4060050456648344450736745 3045037842486258338052559)
                      ·
                        rfl

theorem cell23_5930190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2].length) (baseStart_5930190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930190 prefixEnd_5930190 := by exact prefixLift 5930190
  have htrace : WordTrace (prefixWord ++ tailWord_5930190) baseStart_5930190 baseEnd_5930190 := by
    simpa [prefixWord, tailWord_5930190, baseEnd_5930190] using wordTrace_append hprefix tailTrace_5930190
  have hstable : (prefixWord ++ tailWord_5930190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930190).length < 2 ^ (prefixWord ++ tailWord_5930190).sum := by decide
  have hdescent : baseEnd_5930190 < baseStart_5930190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930209 : List Nat := [1, 2, 3, 1, 3, 2, 2, 1, 1, 7]
def baseStart_5930209 : Nat := 118140960795 + 5930209 * 2 ^ 59
def prefixEnd_5930209 : Nat := 4983230072969 + 3 ^ 40 * 5930209 * 2
def baseEnd_5930209 : Nat := 1015015866206231254571657

theorem tailTrace_5930209 : CollatzResearch.WordTrace tailWord_5930209 prefixEnd_5930209 1015015866206231254571657 := by
  unfold tailWord_5930209
  simp only [CollatzResearch.WordTrace]
  refine ⟨216292491372873066909257681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144194994248582044606171787 216292491372873066909257681)
  ·
    refine ⟨162219368529654800181943261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216292491372873066909257681 162219368529654800181943261)
    ·
      refine ⟨60832263198620550068228723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162219368529654800181943261 60832263198620550068228723)
      ·
        refine ⟨91248394797930825102343085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60832263198620550068228723 91248394797930825102343085)
        ·
          refine ⟨34218148049224059413378657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91248394797930825102343085 34218148049224059413378657)
          ·
            refine ⟨25663611036918044560033993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34218148049224059413378657 25663611036918044560033993)
            ·
              refine ⟨19247708277688533420025495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25663611036918044560033993 19247708277688533420025495)
              ·
                refine ⟨28871562416532800130038243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19247708277688533420025495 28871562416532800130038243)
                ·
                  refine ⟨43307343624799200195057365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28871562416532800130038243 43307343624799200195057365)
                  ·
                    refine ⟨1015015866206231254571657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43307343624799200195057365 1015015866206231254571657)
                    ·
                      rfl

theorem cell23_5930209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_5930209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930209 prefixEnd_5930209 := by exact prefixLift 5930209
  have htrace : WordTrace (prefixWord ++ tailWord_5930209) baseStart_5930209 baseEnd_5930209 := by
    simpa [prefixWord, tailWord_5930209, baseEnd_5930209] using wordTrace_append hprefix tailTrace_5930209
  have hstable : (prefixWord ++ tailWord_5930209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930209).length < 2 ^ (prefixWord ++ tailWord_5930209).sum := by decide
  have hdescent : baseEnd_5930209 < baseStart_5930209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930236 : List Nat := [2, 2, 2, 1, 5, 1, 1, 1, 1, 2, 5]
def baseStart_5930236 : Nat := 118140960795 + 5930236 * 2 ^ 59
def prefixEnd_5930236 : Nat := 4983230072969 + 3 ^ 40 * 5930236 * 2
def baseEnd_5930236 : Nat := 3045061462596365158077347

theorem tailTrace_5930236 : CollatzResearch.WordTrace tailWord_5930236 prefixEnd_5930236 3045061462596365158077347 := by
  unfold tailWord_5930236
  simp only [CollatzResearch.WordTrace]
  refine ⟨108146738071887625260245281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144195650762516833680327041 108146738071887625260245281)
  ·
    refine ⟨81110053553915718945183961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108146738071887625260245281 81110053553915718945183961)
    ·
      refine ⟨60832540165436789208887971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81110053553915718945183961 60832540165436789208887971)
      ·
        refine ⟨91248810248155183813331957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60832540165436789208887971 91248810248155183813331957)
        ·
          refine ⟨8554575960764548482499871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91248810248155183813331957 8554575960764548482499871)
          ·
            refine ⟨12831863941146822723749807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8554575960764548482499871 12831863941146822723749807)
            ·
              refine ⟨19247795911720234085624711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12831863941146822723749807 19247795911720234085624711)
              ·
                refine ⟨28871693867580351128437067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19247795911720234085624711 28871693867580351128437067)
                ·
                  refine ⟨43307540801370526692655601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28871693867580351128437067 43307540801370526692655601)
                  ·
                    refine ⟨32480655601027895019491701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43307540801370526692655601 32480655601027895019491701)
                    ·
                      refine ⟨3045061462596365158077347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32480655601027895019491701 3045061462596365158077347)
                      ·
                        rfl

theorem cell23_5930236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_5930236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930236 prefixEnd_5930236 := by exact prefixLift 5930236
  have htrace : WordTrace (prefixWord ++ tailWord_5930236) baseStart_5930236 baseEnd_5930236 := by
    simpa [prefixWord, tailWord_5930236, baseEnd_5930236] using wordTrace_append hprefix tailTrace_5930236
  have hstable : (prefixWord ++ tailWord_5930236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930236).length < 2 ^ (prefixWord ++ tailWord_5930236).sum := by decide
  have hdescent : baseEnd_5930236 < baseStart_5930236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930273 : List Nat := [1, 2, 3, 2, 1, 1, 1, 7, 1, 4]
def baseStart_5930273 : Nat := 118140960795 + 5930273 * 2 ^ 59
def prefixEnd_5930273 : Nat := 4983230072969 + 3 ^ 40 * 5930273 * 2
def baseEnd_5930273 : Nat := 1015026820460193837771559

theorem tailTrace_5930273 : CollatzResearch.WordTrace tailWord_5930273 prefixEnd_5930273 1015026820460193837771559 := by
  unfold tailWord_5930273
  simp only [CollatzResearch.WordTrace]
  refine ⟨216294825644641205839587473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144196550429760803893058315 216294825644641205839587473)
  ·
    refine ⟨162221119233480904379690605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216294825644641205839587473 162221119233480904379690605)
    ·
      refine ⟨60832919712555339142383977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162221119233480904379690605 60832919712555339142383977)
      ·
        refine ⟨45624689784416504356787983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60832919712555339142383977 45624689784416504356787983)
        ·
          refine ⟨68437034676624756535181975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45624689784416504356787983 68437034676624756535181975)
          ·
            refine ⟨102655552014937134802772963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68437034676624756535181975 102655552014937134802772963)
            ·
              refine ⟨153983328022405702204159445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102655552014937134802772963 153983328022405702204159445)
              ·
                refine ⟨3608984250525133645409987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 153983328022405702204159445 3608984250525133645409987)
                ·
                  refine ⟨5413476375787700468114981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3608984250525133645409987 5413476375787700468114981)
                  ·
                    refine ⟨1015026820460193837771559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5413476375787700468114981 1015026820460193837771559)
                    ·
                      rfl

theorem cell23_5930273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_5930273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930273 prefixEnd_5930273 := by exact prefixLift 5930273
  have htrace : WordTrace (prefixWord ++ tailWord_5930273) baseStart_5930273 baseEnd_5930273 := by
    simpa [prefixWord, tailWord_5930273, baseEnd_5930273] using wordTrace_append hprefix tailTrace_5930273
  have hstable : (prefixWord ++ tailWord_5930273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930273).length < 2 ^ (prefixWord ++ tailWord_5930273).sum := by decide
  have hdescent : baseEnd_5930273 < baseStart_5930273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930290 : List Nat := [3, 2, 1, 1, 4, 2, 1, 4, 1, 4]
def baseStart_5930290 : Nat := 118140960795 + 5930290 * 2 ^ 59
def prefixEnd_5930290 : Nat := 4983230072969 + 3 ^ 40 * 5930290 * 2
def baseEnd_5930290 : Nat := 1015029730183902648934033

theorem tailTrace_5930290 : CollatzResearch.WordTrace tailWord_5930290 prefixEnd_5930290 1015029730183902648934033 := by
  unfold tailWord_5930290
  simp only [CollatzResearch.WordTrace]
  refine ⟨54073861421394904435739081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144196963790386411828637549 54073861421394904435739081)
  ·
    refine ⟨40555396066046178326804311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54073861421394904435739081 40555396066046178326804311)
    ·
      refine ⟨60833094099069267490206467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40555396066046178326804311 60833094099069267490206467)
      ·
        refine ⟨91249641148603901235309701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60833094099069267490206467 91249641148603901235309701)
        ·
          refine ⟨17109307715363231481620569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91249641148603901235309701 17109307715363231481620569)
          ·
            refine ⟨12831980786522423611215427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17109307715363231481620569 12831980786522423611215427)
            ·
              refine ⟨19247971179783635416823141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12831980786522423611215427 19247971179783635416823141)
              ·
                refine ⟨3608994596209431640654339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19247971179783635416823141 3608994596209431640654339)
                ·
                  refine ⟨5413491894314147460981509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3608994596209431640654339 5413491894314147460981509)
                  ·
                    refine ⟨1015029730183902648934033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5413491894314147460981509 1015029730183902648934033)
                    ·
                      rfl

theorem cell23_5930290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4, 1, 4].length) (baseStart_5930290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930290 prefixEnd_5930290 := by exact prefixLift 5930290
  have htrace : WordTrace (prefixWord ++ tailWord_5930290) baseStart_5930290 baseEnd_5930290 := by
    simpa [prefixWord, tailWord_5930290, baseEnd_5930290] using wordTrace_append hprefix tailTrace_5930290
  have hstable : (prefixWord ++ tailWord_5930290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930290).length < 2 ^ (prefixWord ++ tailWord_5930290).sum := by decide
  have hdescent : baseEnd_5930290 < baseStart_5930290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930316 : List Nat := [2, 2, 1, 3, 2, 2, 2, 1, 3, 5]
def baseStart_5930316 : Nat := 118140960795 + 5930316 * 2 ^ 59
def prefixEnd_5930316 : Nat := 4983230072969 + 3 ^ 40 * 5930316 * 2
def baseEnd_5930316 : Nat := 1015034180349574948358993

theorem tailTrace_5930316 : CollatzResearch.WordTrace tailWord_5930316 prefixEnd_5930316 1015034180349574948358993 := by
  unfold tailWord_5930316
  simp only [CollatzResearch.WordTrace]
  refine ⟨108148196991742712091701401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144197595988990282788935201 108148196991742712091701401)
  ·
    refine ⟨81111147743807034068776051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108148196991742712091701401 81111147743807034068776051)
    ·
      refine ⟨121666721615710551103164077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81111147743807034068776051 121666721615710551103164077)
      ·
        refine ⟨45625020605891456663686529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121666721615710551103164077 45625020605891456663686529)
        ·
          refine ⟨34218765454418592497764897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45625020605891456663686529 34218765454418592497764897)
          ·
            refine ⟨25664074090813944373323673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34218765454418592497764897 25664074090813944373323673)
            ·
              refine ⟨19248055568110458279992755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25664074090813944373323673 19248055568110458279992755)
              ·
                refine ⟨28872083352165687419989133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19248055568110458279992755 28872083352165687419989133)
                ·
                  refine ⟨10827031257062132782495925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28872083352165687419989133 10827031257062132782495925)
                  ·
                    refine ⟨1015034180349574948358993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10827031257062132782495925 1015034180349574948358993)
                    ·
                      rfl

theorem cell23_5930316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 3, 5].length) (baseStart_5930316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930316 prefixEnd_5930316 := by exact prefixLift 5930316
  have htrace : WordTrace (prefixWord ++ tailWord_5930316) baseStart_5930316 baseEnd_5930316 := by
    simpa [prefixWord, tailWord_5930316, baseEnd_5930316] using wordTrace_append hprefix tailTrace_5930316
  have hstable : (prefixWord ++ tailWord_5930316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930316).length < 2 ^ (prefixWord ++ tailWord_5930316).sum := by decide
  have hdescent : baseEnd_5930316 < baseStart_5930316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930330 : List Nat := [3, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3]
def baseStart_5930330 : Nat := 118140960795 + 5930330 * 2 ^ 59
def prefixEnd_5930330 : Nat := 4983230072969 + 3 ^ 40 * 5930330 * 2
def baseEnd_5930330 : Nat := 3045109729777887790301915

theorem tailTrace_5930330 : CollatzResearch.WordTrace tailWord_5930330 prefixEnd_5930330 3045109729777887790301915 := by
  unfold tailWord_5930330
  simp only [CollatzResearch.WordTrace]
  refine ⟨54074226151358676143603111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144197936403623136382941629 54074226151358676143603111)
  ·
    refine ⟨81111339227038014215404667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54074226151358676143603111 81111339227038014215404667)
    ·
      refine ⟨121667008840557021323107001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81111339227038014215404667 121667008840557021323107001)
      ·
        refine ⟨91250256630417765992330251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121667008840557021323107001 91250256630417765992330251)
        ·
          refine ⟨136875384945626648988495377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91250256630417765992330251 136875384945626648988495377)
          ·
            refine ⟨102656538709219986741371533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136875384945626648988495377 102656538709219986741371533)
            ·
              refine ⟨38496202015957495028014325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102656538709219986741371533 38496202015957495028014325)
              ·
                refine ⟨3609018938996015158876343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38496202015957495028014325 3609018938996015158876343)
                ·
                  refine ⟨5413528408494022738314515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3609018938996015158876343 5413528408494022738314515)
                  ·
                    refine ⟨8120292612741034107471773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5413528408494022738314515 8120292612741034107471773)
                    ·
                      refine ⟨3045109729777887790301915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8120292612741034107471773 3045109729777887790301915)
                      ·
                        rfl

theorem cell23_5930330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3].length) (baseStart_5930330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930330 prefixEnd_5930330 := by exact prefixLift 5930330
  have htrace : WordTrace (prefixWord ++ tailWord_5930330) baseStart_5930330 baseEnd_5930330 := by
    simpa [prefixWord, tailWord_5930330, baseEnd_5930330] using wordTrace_append hprefix tailTrace_5930330
  have hstable : (prefixWord ++ tailWord_5930330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930330).length < 2 ^ (prefixWord ++ tailWord_5930330).sum := by decide
  have hdescent : baseEnd_5930330 < baseStart_5930330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930359 : List Nat := [1, 1, 3, 1, 1, 2, 4, 10]
def baseStart_5930359 : Nat := 118140960795 + 5930359 * 2 ^ 59
def prefixEnd_5930359 : Nat := 4983230072969 + 3 ^ 40 * 5930359 * 2
def baseEnd_5930359 : Nat := 112782393359884006549603

theorem tailTrace_5930359 : CollatzResearch.WordTrace tailWord_5930359 prefixEnd_5930359 112782393359884006549603 := by
  unfold tailWord_5930359
  simp only [CollatzResearch.WordTrace]
  refine ⟨216297962322329642527218131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144198641548219761684812087 216297962322329642527218131)
  ·
    refine ⟨324446943483494463790827197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216297962322329642527218131 324446943483494463790827197)
    ·
      refine ⟨121667603806310423921560199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324446943483494463790827197 121667603806310423921560199)
      ·
        refine ⟨182501405709465635882340299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121667603806310423921560199 182501405709465635882340299)
        ·
          refine ⟨273752108564198453823510449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182501405709465635882340299 273752108564198453823510449)
          ·
            refine ⟨205314081423148840367632837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273752108564198453823510449 205314081423148840367632837)
            ·
              refine ⟨38496390266840407568931157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 205314081423148840367632837 38496390266840407568931157)
              ·
                refine ⟨112782393359884006549603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38496390266840407568931157 112782393359884006549603)
                ·
                  rfl

theorem cell23_5930359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 10].length) (baseStart_5930359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930359 prefixEnd_5930359 := by exact prefixLift 5930359
  have htrace : WordTrace (prefixWord ++ tailWord_5930359) baseStart_5930359 baseEnd_5930359 := by
    simpa [prefixWord, tailWord_5930359, baseEnd_5930359] using wordTrace_append hprefix tailTrace_5930359
  have hstable : (prefixWord ++ tailWord_5930359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930359).length < 2 ^ (prefixWord ++ tailWord_5930359).sum := by decide
  have hdescent : baseEnd_5930359 < baseStart_5930359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930373 : List Nat := [1, 3, 1, 1, 3, 1, 3, 4, 1, 2, 3]
def baseStart_5930373 : Nat := 118140960795 + 5930373 * 2 ^ 59
def prefixEnd_5930373 : Nat := 4983230072969 + 3 ^ 40 * 5930373 * 2
def baseEnd_5930373 : Nat := 3045131809446031122064217

theorem tailTrace_5930373 : CollatzResearch.WordTrace tailWord_5930373 prefixEnd_5930373 3045131809446031122064217 := by
  unfold tailWord_5930373
  simp only [CollatzResearch.WordTrace]
  refine ⟨216298472944278922918227773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144198981962852615278818515 216298472944278922918227773)
  ·
    refine ⟨81111927354104596094335415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216298472944278922918227773 81111927354104596094335415)
    ·
      refine ⟨121667891031156894141503123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81111927354104596094335415 121667891031156894141503123)
      ·
        refine ⟨182501836546735341212254685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121667891031156894141503123 182501836546735341212254685)
        ·
          refine ⟨68438188705025752954595507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182501836546735341212254685 68438188705025752954595507)
          ·
            refine ⟨102657283057538629431893261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68438188705025752954595507 102657283057538629431893261)
            ·
              refine ⟨38496481146576986036959973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102657283057538629431893261 38496481146576986036959973)
              ·
                refine ⟨7218090214983184881929995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38496481146576986036959973 7218090214983184881929995)
                ·
                  refine ⟨10827135322474777322894993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7218090214983184881929995 10827135322474777322894993)
                  ·
                    refine ⟨8120351491856082992171245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10827135322474777322894993 8120351491856082992171245)
                    ·
                      refine ⟨3045131809446031122064217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8120351491856082992171245 3045131809446031122064217)
                      ·
                        rfl

theorem cell23_5930373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 2, 3].length) (baseStart_5930373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930373 prefixEnd_5930373 := by exact prefixLift 5930373
  have htrace : WordTrace (prefixWord ++ tailWord_5930373) baseStart_5930373 baseEnd_5930373 := by
    simpa [prefixWord, tailWord_5930373, baseEnd_5930373] using wordTrace_append hprefix tailTrace_5930373
  have hstable : (prefixWord ++ tailWord_5930373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930373).length < 2 ^ (prefixWord ++ tailWord_5930373).sum := by decide
  have hdescent : baseEnd_5930373 < baseStart_5930373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930376 : List Nat := [2, 1, 3, 3, 1, 3, 1, 9]
def baseStart_5930376 : Nat := 118140960795 + 5930376 * 2 ^ 59
def prefixEnd_5930376 : Nat := 4983230072969 + 3 ^ 40 * 5930376 * 2
def baseEnd_5930376 : Nat := 112782716662518318900989

theorem tailTrace_5930376 : CollatzResearch.WordTrace tailWord_5930376 prefixEnd_5930376 112782716662518318900989 := by
  unfold tailWord_5930376
  simp only [CollatzResearch.WordTrace]
  refine ⟨108149291181634027215293491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144199054908845369620391321 108149291181634027215293491)
  ·
    refine ⟨162223936772451040822940237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108149291181634027215293491 162223936772451040822940237)
    ·
      refine ⟨60833976289669140308602589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162223936772451040822940237 60833976289669140308602589)
      ·
        refine ⟨22812741108625927615725971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60833976289669140308602589 22812741108625927615725971)
        ·
          refine ⟨34219111662938891423588957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22812741108625927615725971 34219111662938891423588957)
          ·
            refine ⟨12832166873602084283845859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34219111662938891423588957 12832166873602084283845859)
            ·
              refine ⟨19248250310403126425768789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12832166873602084283845859 19248250310403126425768789)
              ·
                refine ⟨112782716662518318900989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19248250310403126425768789 112782716662518318900989)
                ·
                  rfl

theorem cell23_5930376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 9].length) (baseStart_5930376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930376 prefixEnd_5930376 := by exact prefixLift 5930376
  have htrace : WordTrace (prefixWord ++ tailWord_5930376) baseStart_5930376 baseEnd_5930376 := by
    simpa [prefixWord, tailWord_5930376, baseEnd_5930376] using wordTrace_append hprefix tailTrace_5930376
  have hstable : (prefixWord ++ tailWord_5930376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930376).length < 2 ^ (prefixWord ++ tailWord_5930376).sum := by decide
  have hdescent : baseEnd_5930376 < baseStart_5930376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930403 : List Nat := [1, 1, 1, 4, 1, 3, 1, 3, 4, 1, 3]
def baseStart_5930403 : Nat := 118140960795 + 5930403 * 2 ^ 59
def prefixEnd_5930403 : Nat := 4983230072969 + 3 ^ 40 * 5930403 * 2
def baseEnd_5930403 : Nat := 3045147213865666004689079

theorem tailTrace_5930403 : CollatzResearch.WordTrace tailWord_5930403 prefixEnd_5930403 3045147213865666004689079 := by
  unfold tailWord_5930403
  simp only [CollatzResearch.WordTrace]
  refine ⟨216299567134170238041819863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144199711422780158694546575 216299567134170238041819863)
  ·
    refine ⟨324449350701255357062729795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216299567134170238041819863 324449350701255357062729795)
    ·
      refine ⟨486674026051883035594094693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324449350701255357062729795 486674026051883035594094693)
      ·
        refine ⟨91251379884728069173892755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 486674026051883035594094693 91251379884728069173892755)
        ·
          refine ⟨136877069827092103760839133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91251379884728069173892755 136877069827092103760839133)
          ·
            refine ⟨51328901185159538910314675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136877069827092103760839133 51328901185159538910314675)
            ·
              refine ⟨76993351777739308365472013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51328901185159538910314675 76993351777739308365472013)
              ·
                refine ⟨28872506916652240637052005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76993351777739308365472013 28872506916652240637052005)
                ·
                  refine ⟨5413595046872295119447251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28872506916652240637052005 5413595046872295119447251)
                  ·
                    refine ⟨8120392570308442679170877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5413595046872295119447251 8120392570308442679170877)
                    ·
                      refine ⟨3045147213865666004689079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8120392570308442679170877 3045147213865666004689079)
                      ·
                        rfl

theorem cell23_5930403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_5930403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930403 prefixEnd_5930403 := by exact prefixLift 5930403
  have htrace : WordTrace (prefixWord ++ tailWord_5930403) baseStart_5930403 baseEnd_5930403 := by
    simpa [prefixWord, tailWord_5930403, baseEnd_5930403] using wordTrace_append hprefix tailTrace_5930403
  have hstable : (prefixWord ++ tailWord_5930403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930403).length < 2 ^ (prefixWord ++ tailWord_5930403).sum := by decide
  have hdescent : baseEnd_5930403 < baseStart_5930403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930443 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 3, 4, 2]
def baseStart_5930443 : Nat := 118140960795 + 5930443 * 2 ^ 59
def prefixEnd_5930443 : Nat := 4983230072969 + 3 ^ 40 * 5930443 * 2
def baseEnd_5930443 : Nat := 3045167753091845848188895

theorem tailTrace_5930443 : CollatzResearch.WordTrace tailWord_5930443 prefixEnd_5930443 3045167753091845848188895 := by
  unfold tailWord_5930443
  simp only [CollatzResearch.WordTrace]
  refine ⟨216301026054025324873275983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144200684036016883248850655 216301026054025324873275983)
  ·
    refine ⟨324451539081037987309913975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216301026054025324873275983 324451539081037987309913975)
    ·
      refine ⟨486677308621556980964870963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324451539081037987309913975 486677308621556980964870963)
      ·
        refine ⟨730015962932335471447306445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486677308621556980964870963 730015962932335471447306445)
        ·
          refine ⟨273755986099625801792739917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 730015962932335471447306445 273755986099625801792739917)
          ·
            refine ⟨102658494787359675672277469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273755986099625801792739917 102658494787359675672277469)
            ·
              refine ⟨38496935545259878377104051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102658494787359675672277469 38496935545259878377104051)
              ·
                refine ⟨57745403317889817565656077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38496935545259878377104051 57745403317889817565656077)
                ·
                  refine ⟨21654526244208681587121029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57745403317889817565656077 21654526244208681587121029)
                  ·
                    refine ⟨4060223670789127797585193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21654526244208681587121029 4060223670789127797585193)
                    ·
                      refine ⟨3045167753091845848188895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4060223670789127797585193 3045167753091845848188895)
                      ·
                        rfl

theorem cell23_5930443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 4, 2].length) (baseStart_5930443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930443 prefixEnd_5930443 := by exact prefixLift 5930443
  have htrace : WordTrace (prefixWord ++ tailWord_5930443) baseStart_5930443 baseEnd_5930443 := by
    simpa [prefixWord, tailWord_5930443, baseEnd_5930443] using wordTrace_append hprefix tailTrace_5930443
  have hstable : (prefixWord ++ tailWord_5930443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930443).length < 2 ^ (prefixWord ++ tailWord_5930443).sum := by decide
  have hdescent : baseEnd_5930443 < baseStart_5930443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930454 : List Nat := [5, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_5930454 : Nat := 118140960795 + 5930454 * 2 ^ 59
def prefixEnd_5930454 : Nat := 4983230072969 + 3 ^ 40 * 5930454 * 2
def baseEnd_5930454 : Nat := 3045173401379045305151345

theorem tailTrace_5930454 : CollatzResearch.WordTrace tailWord_5930454 prefixEnd_5930454 3045173401379045305151345 := by
  unfold tailWord_5930454
  simp only [CollatzResearch.WordTrace]
  refine ⟨13518839203561592109495401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144200951504656982501284277 13518839203561592109495401)
  ·
    refine ⟨10139129402671194082121551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13518839203561592109495401 10139129402671194082121551)
    ·
      refine ⟨15208694104006791123182327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10139129402671194082121551 15208694104006791123182327)
      ·
        refine ⟨22813041156010186684773491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15208694104006791123182327 22813041156010186684773491)
        ·
          refine ⟨34219561734015280027160237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22813041156010186684773491 34219561734015280027160237)
          ·
            refine ⟨12832335650255730010185089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34219561734015280027160237 12832335650255730010185089)
            ·
              refine ⟨9624251737691797507638817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12832335650255730010185089 9624251737691797507638817)
              ·
                refine ⟨7218188803268848130729113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9624251737691797507638817 7218188803268848130729113)
                ·
                  refine ⟨5413641602451636098046835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7218188803268848130729113 5413641602451636098046835)
                  ·
                    refine ⟨8120462403677454147070253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5413641602451636098046835 8120462403677454147070253)
                    ·
                      refine ⟨3045173401379045305151345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8120462403677454147070253 3045173401379045305151345)
                      ·
                        rfl

theorem cell23_5930454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_5930454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930454 prefixEnd_5930454 := by exact prefixLift 5930454
  have htrace : WordTrace (prefixWord ++ tailWord_5930454) baseStart_5930454 baseEnd_5930454 := by
    simpa [prefixWord, tailWord_5930454, baseEnd_5930454] using wordTrace_append hprefix tailTrace_5930454
  have hstable : (prefixWord ++ tailWord_5930454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930454).length < 2 ^ (prefixWord ++ tailWord_5930454).sum := by decide
  have hdescent : baseEnd_5930454 < baseStart_5930454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930570 : List Nat := [3, 1, 2, 1, 1, 3, 3, 2, 2, 2, 3]
def baseStart_5930570 : Nat := 118140960795 + 5930570 * 2 ^ 59
def prefixEnd_5930570 : Nat := 4983230072969 + 3 ^ 40 * 5930570 * 2
def baseEnd_5930570 : Nat := 3045232965134966851300811

theorem tailTrace_5930570 : CollatzResearch.WordTrace tailWord_5930570 prefixEnd_5930570 3045232965134966851300811 := by
  unfold tailWord_5930570
  simp only [CollatzResearch.WordTrace]
  refine ⟨54076414531141306390787291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144203772083043483708766109 54076414531141306390787291)
  ·
    refine ⟨81114621796711959586180937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54076414531141306390787291 81114621796711959586180937)
    ·
      refine ⟨60835966347533969689635703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81114621796711959586180937 60835966347533969689635703)
      ·
        refine ⟨91253949521300954534453555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60835966347533969689635703 91253949521300954534453555)
        ·
          refine ⟨136880924281951431801680333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91253949521300954534453555 136880924281951431801680333)
          ·
            refine ⟨51330346605731786925630125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136880924281951431801680333 51330346605731786925630125)
            ·
              refine ⟨19248879977149420097111297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51330346605731786925630125 19248879977149420097111297)
              ·
                refine ⟨14436659982862065072833473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19248879977149420097111297 14436659982862065072833473)
                ·
                  refine ⟨10827494987146548804625105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14436659982862065072833473 10827494987146548804625105)
                  ·
                    refine ⟨8120621240359911603468829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10827494987146548804625105 8120621240359911603468829)
                    ·
                      refine ⟨3045232965134966851300811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8120621240359911603468829 3045232965134966851300811)
                      ·
                        rfl

theorem cell23_5930570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_5930570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930570 prefixEnd_5930570 := by exact prefixLift 5930570
  have htrace : WordTrace (prefixWord ++ tailWord_5930570) baseStart_5930570 baseEnd_5930570 := by
    simpa [prefixWord, tailWord_5930570, baseEnd_5930570] using wordTrace_append hprefix tailTrace_5930570
  have hstable : (prefixWord ++ tailWord_5930570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930570).length < 2 ^ (prefixWord ++ tailWord_5930570).sum := by decide
  have hdescent : baseEnd_5930570 < baseStart_5930570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930628 : List Nat := [2, 3, 2, 1, 5, 1, 2, 2, 1, 4]
def baseStart_5930628 : Nat := 118140960795 + 5930628 * 2 ^ 59
def prefixEnd_5930628 : Nat := 4983230072969 + 3 ^ 40 * 5930628 * 2
def baseEnd_5930628 : Nat := 1015087582337642541458515

theorem tailTrace_5930628 : CollatzResearch.WordTrace tailWord_5930628 prefixEnd_5930628 1015087582337642541458515 := by
  unfold tailWord_5930628
  simp only [CollatzResearch.WordTrace]
  refine ⟨108153886779177550734380269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144205182372236734312507025 108153886779177550734380269)
  ·
    refine ⟨40557707542191581525392601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108153886779177550734380269 40557707542191581525392601)
    ·
      refine ⟨30418280656643686144044451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40557707542191581525392601 30418280656643686144044451)
      ·
        refine ⟨45627420984965529216066677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30418280656643686144044451 45627420984965529216066677)
        ·
          refine ⟨4277570717340518364006251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45627420984965529216066677 4277570717340518364006251)
          ·
            refine ⟨6416356076010777546009377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4277570717340518364006251 6416356076010777546009377)
            ·
              refine ⟨4812267057008083159507033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6416356076010777546009377 4812267057008083159507033)
              ·
                refine ⟨3609200292756062369630275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4812267057008083159507033 3609200292756062369630275)
                ·
                  refine ⟨5413800439134093554445413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3609200292756062369630275 5413800439134093554445413)
                  ·
                    refine ⟨1015087582337642541458515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5413800439134093554445413 1015087582337642541458515)
                    ·
                      rfl

theorem cell23_5930628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_5930628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930628 prefixEnd_5930628 := by exact prefixLift 5930628
  have htrace : WordTrace (prefixWord ++ tailWord_5930628) baseStart_5930628 baseEnd_5930628 := by
    simpa [prefixWord, tailWord_5930628, baseEnd_5930628] using wordTrace_append hprefix tailTrace_5930628
  have hstable : (prefixWord ++ tailWord_5930628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930628).length < 2 ^ (prefixWord ++ tailWord_5930628).sum := by decide
  have hdescent : baseEnd_5930628 < baseStart_5930628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930643 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 1, 8, 3]
def baseStart_5930643 : Nat := 118140960795 + 5930643 * 2 ^ 59
def prefixEnd_5930643 : Nat := 4983230072969 + 3 ^ 40 * 5930643 * 2
def baseEnd_5930643 : Nat := 3045270449222745065687975

theorem tailTrace_5930643 : CollatzResearch.WordTrace tailWord_5930643 prefixEnd_5930643 3045270449222745065687975 := by
  unfold tailWord_5930643
  simp only [CollatzResearch.WordTrace]
  refine ⟨216308320653300759030556583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144205547102200506020371055 216308320653300759030556583)
  ·
    refine ⟨324462480979951138545834875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216308320653300759030556583 324462480979951138545834875)
    ·
      refine ⟨486693721469926707818752313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324462480979951138545834875 486693721469926707818752313)
      ·
        refine ⟨365020291102445030864064235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 486693721469926707818752313 365020291102445030864064235)
        ·
          refine ⟨547530436653667546296096353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365020291102445030864064235 547530436653667546296096353)
          ·
            refine ⟨410647827490250659722072265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 547530436653667546296096353 410647827490250659722072265)
            ·
              refine ⟨307985870617687994791554199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 410647827490250659722072265 307985870617687994791554199)
              ·
                refine ⟨461978805926531992187331299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307985870617687994791554199 461978805926531992187331299)
                ·
                  refine ⟨692968208889797988280996949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 461978805926531992187331299 692968208889797988280996949)
                  ·
                    refine ⟨8120721197927320175167933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 692968208889797988280996949 8120721197927320175167933)
                    ·
                      refine ⟨3045270449222745065687975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8120721197927320175167933 3045270449222745065687975)
                      ·
                        rfl

theorem cell23_5930643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8, 3].length) (baseStart_5930643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930643 prefixEnd_5930643 := by exact prefixLift 5930643
  have htrace : WordTrace (prefixWord ++ tailWord_5930643) baseStart_5930643 baseEnd_5930643 := by
    simpa [prefixWord, tailWord_5930643, baseEnd_5930643] using wordTrace_append hprefix tailTrace_5930643
  have hstable : (prefixWord ++ tailWord_5930643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930643).length < 2 ^ (prefixWord ++ tailWord_5930643).sum := by decide
  have hdescent : baseEnd_5930643 < baseStart_5930643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930684 : List Nat := [2, 2, 2, 3, 1, 4, 1, 2, 2, 4]
def baseStart_5930684 : Nat := 118140960795 + 5930684 * 2 ^ 59
def prefixEnd_5930684 : Nat := 4983230072969 + 3 ^ 40 * 5930684 * 2
def baseEnd_5930684 : Nat := 1015097167309859801758429

theorem tailTrace_5930684 : CollatzResearch.WordTrace tailWord_5930684 prefixEnd_5930684 1015097167309859801758429 := by
  unfold tailWord_5930684
  simp only [CollatzResearch.WordTrace]
  refine ⟨108154908023076111516399553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144206544030768148688532737 108154908023076111516399553)
  ·
    refine ⟨81116181017307083637299665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108154908023076111516399553 81116181017307083637299665)
    ·
      refine ⟨60837135762980312727974749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81116181017307083637299665 60837135762980312727974749)
      ·
        refine ⟨22813925911117617272990531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60837135762980312727974749 22813925911117617272990531)
        ·
          refine ⟨34220888866676425909485797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22813925911117617272990531 34220888866676425909485797)
          ·
            refine ⟨6416416662501829858028587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34220888866676425909485797 6416416662501829858028587)
            ·
              refine ⟨9624624993752744787042881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6416416662501829858028587 9624624993752744787042881)
              ·
                refine ⟨7218468745314558590282161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9624624993752744787042881 7218468745314558590282161)
                ·
                  refine ⟨5413851558985918942711621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7218468745314558590282161 5413851558985918942711621)
                  ·
                    refine ⟨1015097167309859801758429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5413851558985918942711621 1015097167309859801758429)
                    ·
                      rfl

theorem cell23_5930684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_5930684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930684 prefixEnd_5930684 := by exact prefixLift 5930684
  have htrace : WordTrace (prefixWord ++ tailWord_5930684) baseStart_5930684 baseEnd_5930684 := by
    simpa [prefixWord, tailWord_5930684, baseEnd_5930684] using wordTrace_append hprefix tailTrace_5930684
  have hstable : (prefixWord ++ tailWord_5930684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930684).length < 2 ^ (prefixWord ++ tailWord_5930684).sum := by decide
  have hdescent : baseEnd_5930684 < baseStart_5930684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930694 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_5930694 : Nat := 118140960795 + 5930694 * 2 ^ 59
def prefixEnd_5930694 : Nat := 4983230072969 + 3 ^ 40 * 5930694 * 2
def baseEnd_5930694 : Nat := 3045296636736124366150241

theorem tailTrace_5930694 : CollatzResearch.WordTrace tailWord_5930694 prefixEnd_5930694 3045296636736124366150241 := by
  unfold tailWord_5930694
  simp only [CollatzResearch.WordTrace]
  refine ⟨6759693149253624835645723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 144206787184077329827108757 6759693149253624835645723)
  ·
    refine ⟨10139539723880437253468585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6759693149253624835645723 10139539723880437253468585)
    ·
      refine ⟨7604654792910327940101439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10139539723880437253468585 7604654792910327940101439)
      ·
        refine ⟨11406982189365491910152159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7604654792910327940101439 11406982189365491910152159)
        ·
          refine ⟨17110473284048237865228239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11406982189365491910152159 17110473284048237865228239)
          ·
            refine ⟨25665709926072356797842359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17110473284048237865228239 25665709926072356797842359)
            ·
              refine ⟨38498564889108535196763539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25665709926072356797842359 38498564889108535196763539)
              ·
                refine ⟨57747847333662802795145309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38498564889108535196763539 57747847333662802795145309)
                ·
                  refine ⟨21655442750123551048179491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57747847333662802795145309 21655442750123551048179491)
                  ·
                    refine ⟨32483164125185326572269237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21655442750123551048179491 32483164125185326572269237)
                    ·
                      refine ⟨3045296636736124366150241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32483164125185326572269237 3045296636736124366150241)
                      ·
                        rfl

theorem cell23_5930694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_5930694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930694 prefixEnd_5930694 := by exact prefixLift 5930694
  have htrace : WordTrace (prefixWord ++ tailWord_5930694) baseStart_5930694 baseEnd_5930694 := by
    simpa [prefixWord, tailWord_5930694, baseEnd_5930694] using wordTrace_append hprefix tailTrace_5930694
  have hstable : (prefixWord ++ tailWord_5930694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930694).length < 2 ^ (prefixWord ++ tailWord_5930694).sum := by decide
  have hdescent : baseEnd_5930694 < baseStart_5930694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930703 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 5]
def baseStart_5930703 : Nat := 118140960795 + 5930703 * 2 ^ 59
def prefixEnd_5930703 : Nat := 4983230072969 + 3 ^ 40 * 5930703 * 2
def baseEnd_5930703 : Nat := 3045301258062014830937699

theorem tailTrace_5930703 : CollatzResearch.WordTrace tailWord_5930703 prefixEnd_5930703 3045301258062014830937699 := by
  unfold tailWord_5930703
  simp only [CollatzResearch.WordTrace]
  refine ⟨216310509033083389277740763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144207006022055592851827175 216310509033083389277740763)
  ·
    refine ⟨324465763549625083916611145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216310509033083389277740763 324465763549625083916611145)
    ·
      refine ⟨243349322662218812937458359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324465763549625083916611145 243349322662218812937458359)
      ·
        refine ⟨365023983993328219406187539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243349322662218812937458359 365023983993328219406187539)
        ·
          refine ⟨547535975989992329109281309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365023983993328219406187539 547535975989992329109281309)
          ·
            refine ⟨205325990996247123415980491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 547535975989992329109281309 205325990996247123415980491)
            ·
              refine ⟨307988986494370685123970737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205325990996247123415980491 307988986494370685123970737)
              ·
                refine ⟨230991739870778013842978053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 307988986494370685123970737 230991739870778013842978053)
                ·
                  refine ⟨43310951225770877595558385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 230991739870778013842978053 43310951225770877595558385)
                  ·
                    refine ⟨32483213419328158196668789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43310951225770877595558385 32483213419328158196668789)
                    ·
                      refine ⟨3045301258062014830937699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32483213419328158196668789 3045301258062014830937699)
                      ·
                        rfl

theorem cell23_5930703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 5].length) (baseStart_5930703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930703 prefixEnd_5930703 := by exact prefixLift 5930703
  have htrace : WordTrace (prefixWord ++ tailWord_5930703) baseStart_5930703 baseEnd_5930703 := by
    simpa [prefixWord, tailWord_5930703, baseEnd_5930703] using wordTrace_append hprefix tailTrace_5930703
  have hstable : (prefixWord ++ tailWord_5930703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930703).length < 2 ^ (prefixWord ++ tailWord_5930703).sum := by decide
  have hdescent : baseEnd_5930703 < baseStart_5930703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930734 : List Nat := [4, 1, 2, 1, 1, 2, 1, 5, 1, 3, 2]
def baseStart_5930734 : Nat := 118140960795 + 5930734 * 2 ^ 59
def prefixEnd_5930734 : Nat := 4983230072969 + 3 ^ 40 * 5930734 * 2
def baseEnd_5930734 : Nat := 3045317175962304209650057

theorem tailTrace_5930734 : CollatzResearch.WordTrace tailWord_5930734 prefixEnd_5930734 3045317175962304209650057 := by
  unfold tailWord_5930734
  simp only [CollatzResearch.WordTrace]
  refine ⟨27038954961996385196514907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144207759797314054381412837 27038954961996385196514907)
  ·
    refine ⟨40558432442994577794772361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27038954961996385196514907 40558432442994577794772361)
    ·
      refine ⟨30418824332245933346079271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40558432442994577794772361 30418824332245933346079271)
      ·
        refine ⟨45628236498368900019118907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30418824332245933346079271 45628236498368900019118907)
        ·
          refine ⟨68442354747553350028678361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45628236498368900019118907 68442354747553350028678361)
          ·
            refine ⟨51331766060665012521508771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68442354747553350028678361 51331766060665012521508771)
            ·
              refine ⟨76997649090997518782263157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51331766060665012521508771 76997649090997518782263157)
              ·
                refine ⟨7218529602281017385837171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76997649090997518782263157 7218529602281017385837171)
                ·
                  refine ⟨10827794403421526078755757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7218529602281017385837171 10827794403421526078755757)
                  ·
                    refine ⟨4060422901283072279533409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10827794403421526078755757 4060422901283072279533409)
                    ·
                      refine ⟨3045317175962304209650057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4060422901283072279533409 3045317175962304209650057)
                      ·
                        rfl

theorem cell23_5930734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_5930734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930734 prefixEnd_5930734 := by exact prefixLift 5930734
  have htrace : WordTrace (prefixWord ++ tailWord_5930734) baseStart_5930734 baseEnd_5930734 := by
    simpa [prefixWord, tailWord_5930734, baseEnd_5930734] using wordTrace_append hprefix tailTrace_5930734
  have hstable : (prefixWord ++ tailWord_5930734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930734).length < 2 ^ (prefixWord ++ tailWord_5930734).sum := by decide
  have hdescent : baseEnd_5930734 < baseStart_5930734 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930760 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 1, 4, 4]
def baseStart_5930760 : Nat := 118140960795 + 5930760 * 2 ^ 59
def prefixEnd_5930760 : Nat := 4983230072969 + 3 ^ 40 * 5930760 * 2
def baseEnd_5930760 : Nat := 3045330526459321107924937

theorem tailTrace_5930760 : CollatzResearch.WordTrace tailWord_5930760 prefixEnd_5930760 3045330526459321107924937 := by
  unfold tailWord_5930760
  simp only [CollatzResearch.WordTrace]
  refine ⟨108156293996938444006282867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144208391995917925341710489 108156293996938444006282867)
  ·
    refine ⟨162234440995407666009424301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108156293996938444006282867 162234440995407666009424301)
    ·
      refine ⟨60837915373277874753534113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162234440995407666009424301 60837915373277874753534113)
      ·
        refine ⟨45628436529958406065150585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60837915373277874753534113 45628436529958406065150585)
        ·
          refine ⟨34221327397468804548862939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45628436529958406065150585 34221327397468804548862939)
          ·
            refine ⟨51331991096203206823294409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34221327397468804548862939 51331991096203206823294409)
            ·
              refine ⟨38498993322152405117470807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51331991096203206823294409 38498993322152405117470807)
              ·
                refine ⟨57748489983228607676206211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38498993322152405117470807 57748489983228607676206211)
                ·
                  refine ⟨86622734974842911514309317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57748489983228607676206211 86622734974842911514309317)
                  ·
                    refine ⟨16241762807783045908932997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86622734974842911514309317 16241762807783045908932997)
                    ·
                      refine ⟨3045330526459321107924937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16241762807783045908932997 3045330526459321107924937)
                      ·
                        rfl

theorem cell23_5930760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_5930760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930760 prefixEnd_5930760 := by exact prefixLift 5930760
  have htrace : WordTrace (prefixWord ++ tailWord_5930760) baseStart_5930760 baseEnd_5930760 := by
    simpa [prefixWord, tailWord_5930760, baseEnd_5930760] using wordTrace_append hprefix tailTrace_5930760
  have hstable : (prefixWord ++ tailWord_5930760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930760).length < 2 ^ (prefixWord ++ tailWord_5930760).sum := by decide
  have hdescent : baseEnd_5930760 < baseStart_5930760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930814 : List Nat := [4, 2, 1, 2, 2, 2, 1, 1, 2, 3, 3]
def baseStart_5930814 : Nat := 118140960795 + 5930814 * 2 ^ 59
def prefixEnd_5930814 : Nat := 4983230072969 + 3 ^ 40 * 5930814 * 2
def baseEnd_5930814 : Nat := 3045358254414663896649689

theorem tailTrace_5930814 : CollatzResearch.WordTrace tailWord_5930814 prefixEnd_5930814 3045358254414663896649689 := by
  unfold tailWord_5930814
  simp only [CollatzResearch.WordTrace]
  refine ⟨27039319691960156904378937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144209705023787503490020997 27039319691960156904378937)
  ·
    refine ⟨20279489768970117678284203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27039319691960156904378937 20279489768970117678284203)
    ·
      refine ⟨30419234653455176517426305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20279489768970117678284203 30419234653455176517426305)
      ·
        refine ⟨22814425990091382388069729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30419234653455176517426305 22814425990091382388069729)
        ·
          refine ⟨17110819492568536791052297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22814425990091382388069729 17110819492568536791052297)
          ·
            refine ⟨12833114619426402593289223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17110819492568536791052297 12833114619426402593289223)
            ·
              refine ⟨19249671929139603889933835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12833114619426402593289223 19249671929139603889933835)
              ·
                refine ⟨28874507893709405834900753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19249671929139603889933835 28874507893709405834900753)
                ·
                  refine ⟨21655880920282054376175565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28874507893709405834900753 21655880920282054376175565)
                  ·
                    refine ⟨8120955345105770391065837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21655880920282054376175565 8120955345105770391065837)
                    ·
                      refine ⟨3045358254414663896649689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8120955345105770391065837 3045358254414663896649689)
                      ·
                        rfl

theorem cell23_5930814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_5930814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930814 prefixEnd_5930814 := by exact prefixLift 5930814
  have htrace : WordTrace (prefixWord ++ tailWord_5930814) baseStart_5930814 baseEnd_5930814 := by
    simpa [prefixWord, tailWord_5930814, baseEnd_5930814] using wordTrace_append hprefix tailTrace_5930814
  have hstable : (prefixWord ++ tailWord_5930814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930814).length < 2 ^ (prefixWord ++ tailWord_5930814).sum := by decide
  have hdescent : baseEnd_5930814 < baseStart_5930814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930834 : List Nat := [3, 2, 2, 1, 1, 5, 1, 1, 2, 5]
def baseStart_5930834 : Nat := 118140960795 + 5930834 * 2 ^ 59
def prefixEnd_5930834 : Nat := 4983230072969 + 3 ^ 40 * 5930834 * 2
def baseEnd_5930834 : Nat := 1015122841342584606133199

theorem tailTrace_5930834 : CollatzResearch.WordTrace tailWord_5930834 prefixEnd_5930834 1015122841342584606133199 := by
  unfold tailWord_5930834
  simp only [CollatzResearch.WordTrace]
  refine ⟨54078821748902199662689889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144210191330405865767173037 54078821748902199662689889)
  ·
    refine ⟨40559116311676649747017417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54078821748902199662689889 40559116311676649747017417)
    ·
      refine ⟨30419337233757487310263063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40559116311676649747017417 30419337233757487310263063)
      ·
        refine ⟨45629005850636230965394595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30419337233757487310263063 45629005850636230965394595)
        ·
          refine ⟨68443508775954346448091893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45629005850636230965394595 68443508775954346448091893)
          ·
            refine ⟨6416578947745719979508615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68443508775954346448091893 6416578947745719979508615)
            ·
              refine ⟨9624868421618579969262923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6416578947745719979508615 9624868421618579969262923)
              ·
                refine ⟨14437302632427869953894385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9624868421618579969262923 14437302632427869953894385)
                ·
                  refine ⟨10827976974320902465420789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14437302632427869953894385 10827976974320902465420789)
                  ·
                    refine ⟨1015122841342584606133199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10827976974320902465420789 1015122841342584606133199)
                    ·
                      rfl

theorem cell23_5930834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_5930834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930834 prefixEnd_5930834 := by exact prefixLift 5930834
  have htrace : WordTrace (prefixWord ++ tailWord_5930834) baseStart_5930834 baseEnd_5930834 := by
    simpa [prefixWord, tailWord_5930834, baseEnd_5930834] using wordTrace_append hprefix tailTrace_5930834
  have hstable : (prefixWord ++ tailWord_5930834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930834).length < 2 ^ (prefixWord ++ tailWord_5930834).sum := by decide
  have hdescent : baseEnd_5930834 < baseStart_5930834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930837 : List Nat := [1, 3, 2, 2, 2, 3, 1, 1, 1, 3, 4]
def baseStart_5930837 : Nat := 118140960795 + 5930837 * 2 ^ 59
def prefixEnd_5930837 : Nat := 4983230072969 + 3 ^ 40 * 5930837 * 2
def baseEnd_5930837 : Nat := 3045370064469717306662083

theorem tailTrace_5930837 : CollatzResearch.WordTrace tailWord_5930837 prefixEnd_5930837 3045370064469717306662083 := by
  unfold tailWord_5930837
  simp only [CollatzResearch.WordTrace]
  refine ⟨216315396414597930163118765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144210264276398620108745843 216315396414597930163118765)
  ·
    refine ⟨81118273655474223811169537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216315396414597930163118765 81118273655474223811169537)
    ·
      refine ⟨60838705241605667858377153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81118273655474223811169537 60838705241605667858377153)
      ·
        refine ⟨45629028931204250893782865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60838705241605667858377153 45629028931204250893782865)
        ·
          refine ⟨34221771698403188170337149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45629028931204250893782865 34221771698403188170337149)
          ·
            refine ⟨12833164386901195563876431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34221771698403188170337149 12833164386901195563876431)
            ·
              refine ⟨19249746580351793345814647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12833164386901195563876431 19249746580351793345814647)
              ·
                refine ⟨28874619870527690018721971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19249746580351793345814647 28874619870527690018721971)
                ·
                  refine ⟨43311929805791535028082957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28874619870527690018721971 43311929805791535028082957)
                  ·
                    refine ⟨16241973677171825635531109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43311929805791535028082957 16241973677171825635531109)
                    ·
                      refine ⟨3045370064469717306662083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16241973677171825635531109 3045370064469717306662083)
                      ·
                        rfl

theorem cell23_5930837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_5930837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930837 prefixEnd_5930837 := by exact prefixLift 5930837
  have htrace : WordTrace (prefixWord ++ tailWord_5930837) baseStart_5930837 baseEnd_5930837 := by
    simpa [prefixWord, tailWord_5930837, baseEnd_5930837] using wordTrace_append hprefix tailTrace_5930837
  have hstable : (prefixWord ++ tailWord_5930837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930837).length < 2 ^ (prefixWord ++ tailWord_5930837).sum := by decide
  have hdescent : baseEnd_5930837 < baseStart_5930837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930857 : List Nat := [1, 2, 1, 1, 1, 3, 1, 6, 2, 2, 3]
def baseStart_5930857 : Nat := 118140960795 + 5930857 * 2 ^ 59
def prefixEnd_5930857 : Nat := 4983230072969 + 3 ^ 40 * 5930857 * 2
def baseEnd_5930857 : Nat := 3045380334082807228411991

theorem tailTrace_5930857 : CollatzResearch.WordTrace tailWord_5930857 prefixEnd_5930857 3045380334082807228411991 := by
  unfold tailWord_5930857
  simp only [CollatzResearch.WordTrace]
  refine ⟨216316125874525473578846825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144210750583016982385897883 216316125874525473578846825)
  ·
    refine ⟨162237094405894105184135119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216316125874525473578846825 162237094405894105184135119)
    ·
      refine ⟨243355641608841157776202679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162237094405894105184135119 243355641608841157776202679)
      ·
        refine ⟨365033462413261736664304019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243355641608841157776202679 365033462413261736664304019)
        ·
          refine ⟨547550193619892604996456029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365033462413261736664304019 547550193619892604996456029)
          ·
            refine ⟨205331322607459726873671011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 547550193619892604996456029 205331322607459726873671011)
            ·
              refine ⟨307996983911189590310506517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205331322607459726873671011 307996983911189590310506517)
              ·
                refine ⟨14437358620837012045804993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 307996983911189590310506517 14437358620837012045804993)
                ·
                  refine ⟨10828018965627759034353745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14437358620837012045804993 10828018965627759034353745)
                  ·
                    refine ⟨8121014224220819275765309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10828018965627759034353745 8121014224220819275765309)
                    ·
                      refine ⟨3045380334082807228411991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8121014224220819275765309 3045380334082807228411991)
                      ·
                        rfl

theorem cell23_5930857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 2, 2, 3].length) (baseStart_5930857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930857 prefixEnd_5930857 := by exact prefixLift 5930857
  have htrace : WordTrace (prefixWord ++ tailWord_5930857) baseStart_5930857 baseEnd_5930857 := by
    simpa [prefixWord, tailWord_5930857, baseEnd_5930857] using wordTrace_append hprefix tailTrace_5930857
  have hstable : (prefixWord ++ tailWord_5930857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930857).length < 2 ^ (prefixWord ++ tailWord_5930857).sum := by decide
  have hdescent : baseEnd_5930857 < baseStart_5930857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930880 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 6]
def baseStart_5930880 : Nat := 118140960795 + 5930880 * 2 ^ 59
def prefixEnd_5930880 : Nat := 4983230072969 + 3 ^ 40 * 5930880 * 2
def baseEnd_5930880 : Nat := 3045392144137860638424385

theorem tailTrace_5930880 : CollatzResearch.WordTrace tailWord_5930880 prefixEnd_5930880 3045392144137860638424385 := by
  unfold tailWord_5930880
  simp only [CollatzResearch.WordTrace]
  refine ⟨108158482376721074253467047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144211309835628099004622729 108158482376721074253467047)
  ·
    refine ⟨162237723565081611380200571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108158482376721074253467047 162237723565081611380200571)
    ·
      refine ⟨243356585347622417070300857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162237723565081611380200571 243356585347622417070300857)
      ·
        refine ⟨182517439010716812802725643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243356585347622417070300857 182517439010716812802725643)
        ·
          refine ⟨273776158516075219204088465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182517439010716812802725643 273776158516075219204088465)
          ·
            refine ⟨205332118887056414403066349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273776158516075219204088465 205332118887056414403066349)
            ·
              refine ⟨76999544582646155401149881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 205332118887056414403066349 76999544582646155401149881)
              ·
                refine ⟨57749658436984616550862411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76999544582646155401149881 57749658436984616550862411)
                ·
                  refine ⟨86624487655476924826293617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57749658436984616550862411 86624487655476924826293617)
                  ·
                    refine ⟨64968365741607693619720213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86624487655476924826293617 64968365741607693619720213)
                    ·
                      refine ⟨3045392144137860638424385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64968365741607693619720213 3045392144137860638424385)
                      ·
                        rfl

theorem cell23_5930880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_5930880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930880 prefixEnd_5930880 := by exact prefixLift 5930880
  have htrace : WordTrace (prefixWord ++ tailWord_5930880) baseStart_5930880 baseEnd_5930880 := by
    simpa [prefixWord, tailWord_5930880, baseEnd_5930880] using wordTrace_append hprefix tailTrace_5930880
  have hstable : (prefixWord ++ tailWord_5930880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930880).length < 2 ^ (prefixWord ++ tailWord_5930880).sum := by decide
  have hdescent : baseEnd_5930880 < baseStart_5930880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930898 : List Nat := [3, 2, 3, 2, 1, 1, 3, 3, 1, 4]
def baseStart_5930898 : Nat := 118140960795 + 5930898 * 2 ^ 59
def prefixEnd_5930898 : Nat := 4983230072969 + 3 ^ 40 * 5930898 * 2
def baseEnd_5930898 : Nat := 1015133795596547189333101

theorem tailTrace_5930898 : CollatzResearch.WordTrace tailWord_5930898 prefixEnd_5930898 1015133795596547189333101 := by
  unfold tailWord_5930898
  simp only [CollatzResearch.WordTrace]
  refine ⟨54079405316844234395272337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144211747511584625054059565 54079405316844234395272337)
  ·
    refine ⟨40559553987633175796454253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54079405316844234395272337 40559553987633175796454253)
    ·
      refine ⟨15209832745362440923670345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40559553987633175796454253 15209832745362440923670345)
      ·
        refine ⟨11407374559021830692752759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15209832745362440923670345 11407374559021830692752759)
        ·
          refine ⟨17111061838532746039129139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11407374559021830692752759 17111061838532746039129139)
          ·
            refine ⟨25666592757799119058693709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17111061838532746039129139 25666592757799119058693709)
            ·
              refine ⟨9624972284174669647010141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25666592757799119058693709 9624972284174669647010141)
              ·
                refine ⟨3609364606565501117628803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9624972284174669647010141 3609364606565501117628803)
                ·
                  refine ⟨5414046909848251676443205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3609364606565501117628803 5414046909848251676443205)
                  ·
                    refine ⟨1015133795596547189333101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5414046909848251676443205 1015133795596547189333101)
                    ·
                      rfl

theorem cell23_5930898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_5930898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930898 prefixEnd_5930898 := by exact prefixLift 5930898
  have htrace : WordTrace (prefixWord ++ tailWord_5930898) baseStart_5930898 baseEnd_5930898 := by
    simpa [prefixWord, tailWord_5930898, baseEnd_5930898] using wordTrace_append hprefix tailTrace_5930898
  have hstable : (prefixWord ++ tailWord_5930898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930898).length < 2 ^ (prefixWord ++ tailWord_5930898).sum := by decide
  have hdescent : baseEnd_5930898 < baseStart_5930898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930927 : List Nat := [1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 4]
def baseStart_5930927 : Nat := 118140960795 + 5930927 * 2 ^ 59
def prefixEnd_5930927 : Nat := 4983230072969 + 3 ^ 40 * 5930927 * 2
def baseEnd_5930927 : Nat := 3045416277728621954536669

theorem tailTrace_5930927 : CollatzResearch.WordTrace tailWord_5930927 prefixEnd_5930927 3045416277728621954536669 := by
  unfold tailWord_5930927
  simp only [CollatzResearch.WordTrace]
  refine ⟨216318678984271875533895035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144212452656181250355930023 216318678984271875533895035)
  ·
    refine ⟨324478018476407813300842553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216318678984271875533895035 324478018476407813300842553)
    ·
      refine ⟨243358513857305859975631915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324478018476407813300842553 243358513857305859975631915)
      ·
        refine ⟨365037770785958789963447873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243358513857305859975631915 365037770785958789963447873)
        ·
          refine ⟨273778328089469092472585905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365037770785958789963447873 273778328089469092472585905)
          ·
            refine ⟨205333746067101819354439429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273778328089469092472585905 205333746067101819354439429)
            ·
              refine ⟨38500077387581591128957393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 205333746067101819354439429 38500077387581591128957393)
              ·
                refine ⟨28875058040686193346718045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38500077387581591128957393 28875058040686193346718045)
                ·
                  refine ⟨10828146765257322505019267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28875058040686193346718045 10828146765257322505019267)
                  ·
                    refine ⟨16242220147885983757528901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10828146765257322505019267 16242220147885983757528901)
                    ·
                      refine ⟨3045416277728621954536669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16242220147885983757528901 3045416277728621954536669)
                      ·
                        rfl

theorem cell23_5930927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 1, 4].length) (baseStart_5930927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930927 prefixEnd_5930927 := by exact prefixLift 5930927
  have htrace : WordTrace (prefixWord ++ tailWord_5930927) baseStart_5930927 baseEnd_5930927 := by
    simpa [prefixWord, tailWord_5930927, baseEnd_5930927] using wordTrace_append hprefix tailTrace_5930927
  have hstable : (prefixWord ++ tailWord_5930927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930927).length < 2 ^ (prefixWord ++ tailWord_5930927).sum := by decide
  have hdescent : baseEnd_5930927 < baseStart_5930927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930937 : List Nat := [1, 2, 1, 4, 2, 1, 2, 3, 1, 6]
def baseStart_5930937 : Nat := 118140960795 + 5930937 * 2 ^ 59
def prefixEnd_5930937 : Nat := 4983230072969 + 3 ^ 40 * 5930937 * 2
def baseEnd_5930937 : Nat := 1015140470845055638470541

theorem tailTrace_5930937 : CollatzResearch.WordTrace tailWord_5930937 prefixEnd_5930937 1015140470845055638470541 := by
  unfold tailWord_5930937
  simp only [CollatzResearch.WordTrace]
  refine ⟨216319043714235647241759065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144212695809490431494506043 216319043714235647241759065)
  ·
    refine ⟨162239282785676735431319299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216319043714235647241759065 162239282785676735431319299)
    ·
      refine ⟨243358924178515103146978949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162239282785676735431319299 243358924178515103146978949)
      ·
        refine ⟨45629798283471581840058553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 243358924178515103146978949 45629798283471581840058553)
        ·
          refine ⟨34222348712603686380043915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45629798283471581840058553 34222348712603686380043915)
          ·
            refine ⟨51333523068905529570065873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34222348712603686380043915 51333523068905529570065873)
            ·
              refine ⟨38500142301679147177549405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51333523068905529570065873 38500142301679147177549405)
              ·
                refine ⟨14437553363129680191581027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38500142301679147177549405 14437553363129680191581027)
                ·
                  refine ⟨21656330044694520287371541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14437553363129680191581027 21656330044694520287371541)
                  ·
                    refine ⟨1015140470845055638470541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21656330044694520287371541 1015140470845055638470541)
                    ·
                      rfl

theorem cell23_5930937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 6].length) (baseStart_5930937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930937 prefixEnd_5930937 := by exact prefixLift 5930937
  have htrace : WordTrace (prefixWord ++ tailWord_5930937) baseStart_5930937 baseEnd_5930937 := by
    simpa [prefixWord, tailWord_5930937, baseEnd_5930937] using wordTrace_append hprefix tailTrace_5930937
  have hstable : (prefixWord ++ tailWord_5930937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930937).length < 2 ^ (prefixWord ++ tailWord_5930937).sum := by decide
  have hdescent : baseEnd_5930937 < baseStart_5930937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5930941 : List Nat := [1, 4, 1, 2, 3, 3, 1, 2, 1, 5]
def baseStart_5930941 : Nat := 118140960795 + 5930941 * 2 ^ 59
def prefixEnd_5930941 : Nat := 4983230072969 + 3 ^ 40 * 5930941 * 2
def baseEnd_5930941 : Nat := 1015141155485928299920535

theorem tailTrace_5930941 : CollatzResearch.WordTrace tailWord_5930941 prefixEnd_5930941 1015141155485928299920535 := by
  unfold tailWord_5930941
  simp only [CollatzResearch.WordTrace]
  refine ⟨216319189606221155924904677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144212793070814103949936451 216319189606221155924904677)
  ·
    refine ⟨40559848051166466735919627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216319189606221155924904677 40559848051166466735919627)
    ·
      refine ⟨60839772076749700103879441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40559848051166466735919627 60839772076749700103879441)
      ·
        refine ⟨45629829057562275077909581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60839772076749700103879441 45629829057562275077909581)
        ·
          refine ⟨17111185896585853154216093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45629829057562275077909581 17111185896585853154216093)
          ·
            refine ⟨6416694711219694932831035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17111185896585853154216093 6416694711219694932831035)
            ·
              refine ⟨9625042066829542399246553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6416694711219694932831035 9625042066829542399246553)
              ·
                refine ⟨7218781550122156799434915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9625042066829542399246553 7218781550122156799434915)
                ·
                  refine ⟨10828172325183235199152373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7218781550122156799434915 10828172325183235199152373)
                  ·
                    refine ⟨1015141155485928299920535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10828172325183235199152373 1015141155485928299920535)
                    ·
                      rfl

theorem cell23_5930941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_5930941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5930941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5930941 prefixEnd_5930941 := by exact prefixLift 5930941
  have htrace : WordTrace (prefixWord ++ tailWord_5930941) baseStart_5930941 baseEnd_5930941 := by
    simpa [prefixWord, tailWord_5930941, baseEnd_5930941] using wordTrace_append hprefix tailTrace_5930941
  have hstable : (prefixWord ++ tailWord_5930941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5930941).length < 2 ^ (prefixWord ++ tailWord_5930941).sum := by decide
  have hdescent : baseEnd_5930941 < baseStart_5930941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5930941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931012 : List Nat := [2, 3, 2, 4, 2, 1, 2, 1, 1, 1, 4]
def baseStart_5931012 : Nat := 118140960795 + 5931012 * 2 ^ 59
def prefixEnd_5931012 : Nat := 4983230072969 + 3 ^ 40 * 5931012 * 2
def baseEnd_5931012 : Nat := 3045459923584254121973779

theorem tailTrace_5931012 : CollatzResearch.WordTrace tailWord_5931012 prefixEnd_5931012 3045459923584254121973779 := by
  unfold tailWord_5931012
  simp only [CollatzResearch.WordTrace]
  refine ⟨108160889594481967525369645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144214519459309290033826193 108160889594481967525369645)
  ·
    refine ⟨40560333597930737822013617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108160889594481967525369645 40560333597930737822013617)
    ·
      refine ⟨30420250198448053366510213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40560333597930737822013617 30420250198448053366510213)
      ·
        refine ⟨5703796912209010006220665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30420250198448053366510213 5703796912209010006220665)
        ·
          refine ⟨4277847684156757504665499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5703796912209010006220665 4277847684156757504665499)
          ·
            refine ⟨6416771526235136256998249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4277847684156757504665499 6416771526235136256998249)
            ·
              refine ⟨4812578644676352192748687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6416771526235136256998249 4812578644676352192748687)
              ·
                refine ⟨7218867967014528289123031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4812578644676352192748687 7218867967014528289123031)
                ·
                  refine ⟨10828301950521792433684547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7218867967014528289123031 10828301950521792433684547)
                  ·
                    refine ⟨16242452925782688650526821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10828301950521792433684547 16242452925782688650526821)
                    ·
                      refine ⟨3045459923584254121973779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16242452925782688650526821 3045459923584254121973779)
                      ·
                        rfl

theorem cell23_5931012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_5931012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931012 prefixEnd_5931012 := by exact prefixLift 5931012
  have htrace : WordTrace (prefixWord ++ tailWord_5931012) baseStart_5931012 baseEnd_5931012 := by
    simpa [prefixWord, tailWord_5931012, baseEnd_5931012] using wordTrace_append hprefix tailTrace_5931012
  have hstable : (prefixWord ++ tailWord_5931012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931012).length < 2 ^ (prefixWord ++ tailWord_5931012).sum := by decide
  have hdescent : baseEnd_5931012 < baseStart_5931012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931027 : List Nat := [1, 1, 1, 2, 1, 4, 3, 2, 2, 6]
def baseStart_5931027 : Nat := 118140960795 + 5931027 * 2 ^ 59
def prefixEnd_5931027 : Nat := 4983230072969 + 3 ^ 40 * 5931027 * 2
def baseEnd_5931027 : Nat := 1015155875264690521095403

theorem tailTrace_5931027 : CollatzResearch.WordTrace tailWord_5931027 prefixEnd_5931027 1015155875264690521095403 := by
  unfold tailWord_5931027
  simp only [CollatzResearch.WordTrace]
  refine ⟨216322326283909592612535335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144214884189273061741690223 216322326283909592612535335)
  ·
    refine ⟨324483489425864388918803003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216322326283909592612535335 324483489425864388918803003)
    ·
      refine ⟨486725234138796583378204505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324483489425864388918803003 486725234138796583378204505)
      ·
        refine ⟨365043925604097437533653379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 486725234138796583378204505 365043925604097437533653379)
        ·
          refine ⟨547565888406146156300480069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365043925604097437533653379 547565888406146156300480069)
          ·
            refine ⟨102668604076152404306340013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 547565888406146156300480069 102668604076152404306340013)
            ·
              refine ⟨38500726528557151614877505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102668604076152404306340013 38500726528557151614877505)
              ·
                refine ⟨28875544896417863711158129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38500726528557151614877505 28875544896417863711158129)
                ·
                  refine ⟨21656658672313397783368597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28875544896417863711158129 21656658672313397783368597)
                  ·
                    refine ⟨1015155875264690521095403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21656658672313397783368597 1015155875264690521095403)
                    ·
                      rfl

theorem cell23_5931027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 6].length) (baseStart_5931027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931027 prefixEnd_5931027 := by exact prefixLift 5931027
  have htrace : WordTrace (prefixWord ++ tailWord_5931027) baseStart_5931027 baseEnd_5931027 := by
    simpa [prefixWord, tailWord_5931027, baseEnd_5931027] using wordTrace_append hprefix tailTrace_5931027
  have hstable : (prefixWord ++ tailWord_5931027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931027).length < 2 ^ (prefixWord ++ tailWord_5931027).sum := by decide
  have hdescent : baseEnd_5931027 < baseStart_5931027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931084 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 4, 3, 3]
def baseStart_5931084 : Nat := 118140960795 + 5931084 * 2 ^ 59
def prefixEnd_5931084 : Nat := 4983230072969 + 3 ^ 40 * 5931084 * 2
def baseEnd_5931084 : Nat := 3045496894191377840273447

theorem tailTrace_5931084 : CollatzResearch.WordTrace tailWord_5931084 prefixEnd_5931084 3045496894191377840273447 := by
  unfold tailWord_5931084
  simp only [CollatzResearch.WordTrace]
  refine ⟨108162202622351545673680153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144216270163135394231573537 108162202622351545673680153)
  ·
    refine ⟨81121651966763659255260115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108162202622351545673680153 81121651966763659255260115)
    ·
      refine ⟨121682477950145488882890173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81121651966763659255260115 121682477950145488882890173)
      ·
        refine ⟨45630929231304558331083815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121682477950145488882890173 45630929231304558331083815)
        ·
          refine ⟨68446393846956837496625723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45630929231304558331083815 68446393846956837496625723)
          ·
            refine ⟨102669590770435256244938585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68446393846956837496625723 102669590770435256244938585)
            ·
              refine ⟨77002193077826442183703939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102669590770435256244938585 77002193077826442183703939)
              ·
                refine ⟨115503289616739663275555909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77002193077826442183703939 115503289616739663275555909)
                ·
                  refine ⟨21656866803138686864166733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115503289616739663275555909 21656866803138686864166733)
                  ·
                    refine ⟨8121325051177007574062525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21656866803138686864166733 8121325051177007574062525)
                    ·
                      refine ⟨3045496894191377840273447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8121325051177007574062525 3045496894191377840273447)
                      ·
                        rfl

theorem cell23_5931084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_5931084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931084 prefixEnd_5931084 := by exact prefixLift 5931084
  have htrace : WordTrace (prefixWord ++ tailWord_5931084) baseStart_5931084 baseEnd_5931084 := by
    simpa [prefixWord, tailWord_5931084, baseEnd_5931084] using wordTrace_append hprefix tailTrace_5931084
  have hstable : (prefixWord ++ tailWord_5931084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931084).length < 2 ^ (prefixWord ++ tailWord_5931084).sum := by decide
  have hdescent : baseEnd_5931084 < baseStart_5931084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931085 : List Nat := [1, 6, 1, 1, 1, 1, 2, 4, 2, 2, 2]
def baseStart_5931085 : Nat := 118140960795 + 5931085 * 2 ^ 59
def prefixEnd_5931085 : Nat := 4983230072969 + 3 ^ 40 * 5931085 * 2
def baseEnd_5931085 : Nat := 3045497407672032336360943

theorem tailTrace_5931085 : CollatzResearch.WordTrace tailWord_5931085 prefixEnd_5931085 3045497407672032336360943 := by
  unfold tailWord_5931085
  simp only [CollatzResearch.WordTrace]
  refine ⟨216324441717699468518146709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144216294478466312345431139 216324441717699468518146709)
  ·
    refine ⟨10140208205517162586788127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 216324441717699468518146709 10140208205517162586788127)
    ·
      refine ⟨15210312308275743880182191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10140208205517162586788127 15210312308275743880182191)
      ·
        refine ⟨22815468462413615820273287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15210312308275743880182191 22815468462413615820273287)
        ·
          refine ⟨34223202693620423730409931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22815468462413615820273287 34223202693620423730409931)
          ·
            refine ⟨51334804040430635595614897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34223202693620423730409931 51334804040430635595614897)
            ·
              refine ⟨38501103030322976696711173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51334804040430635595614897 38501103030322976696711173)
              ·
                refine ⟨7218956818185558130633345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38501103030322976696711173 7218956818185558130633345)
                ·
                  refine ⟨5414217613639168597975009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7218956818185558130633345 5414217613639168597975009)
                  ·
                    refine ⟨4060663210229376448481257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5414217613639168597975009 4060663210229376448481257)
                    ·
                      refine ⟨3045497407672032336360943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4060663210229376448481257 3045497407672032336360943)
                      ·
                        rfl

theorem cell23_5931085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_5931085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931085 prefixEnd_5931085 := by exact prefixLift 5931085
  have htrace : WordTrace (prefixWord ++ tailWord_5931085) baseStart_5931085 baseEnd_5931085 := by
    simpa [prefixWord, tailWord_5931085, baseEnd_5931085] using wordTrace_append hprefix tailTrace_5931085
  have hstable : (prefixWord ++ tailWord_5931085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931085).length < 2 ^ (prefixWord ++ tailWord_5931085).sum := by decide
  have hdescent : baseEnd_5931085 < baseStart_5931085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931141 : List Nat := [1, 3, 1, 1, 5, 1, 2, 2, 2, 1, 4]
def baseStart_5931141 : Nat := 118140960795 + 5931141 * 2 ^ 59
def prefixEnd_5931141 : Nat := 4983230072969 + 3 ^ 40 * 5931141 * 2
def baseEnd_5931141 : Nat := 3045526162588684117260685

theorem tailTrace_5931141 : CollatzResearch.WordTrace tailWord_5931141 prefixEnd_5931141 3045526162588684117260685 := by
  unfold tailWord_5931141
  simp only [CollatzResearch.WordTrace]
  refine ⟨216326484205496590082185277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144217656136997726721456851 216326484205496590082185277)
  ·
    refine ⟨81122431577061221280819479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216326484205496590082185277 81122431577061221280819479)
    ·
      refine ⟨121683647365591831921229219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81122431577061221280819479 121683647365591831921229219)
      ·
        refine ⟨182525471048387747881843829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121683647365591831921229219 182525471048387747881843829)
        ·
          refine ⟨17111762910786351363922859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 182525471048387747881843829 17111762910786351363922859)
          ·
            refine ⟨25667644366179527045884289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17111762910786351363922859 25667644366179527045884289)
            ·
              refine ⟨19250733274634645284413217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25667644366179527045884289 19250733274634645284413217)
              ·
                refine ⟨14438049955975983963309913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19250733274634645284413217 14438049955975983963309913)
                ·
                  refine ⟨10828537466981987972482435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14438049955975983963309913 10828537466981987972482435)
                  ·
                    refine ⟨16242806200472981958723653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10828537466981987972482435 16242806200472981958723653)
                    ·
                      refine ⟨3045526162588684117260685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16242806200472981958723653 3045526162588684117260685)
                      ·
                        rfl

theorem cell23_5931141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 1, 4].length) (baseStart_5931141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931141 prefixEnd_5931141 := by exact prefixLift 5931141
  have htrace : WordTrace (prefixWord ++ tailWord_5931141) baseStart_5931141 baseEnd_5931141 := by
    simpa [prefixWord, tailWord_5931141, baseEnd_5931141] using wordTrace_append hprefix tailTrace_5931141
  have hstable : (prefixWord ++ tailWord_5931141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931141).length < 2 ^ (prefixWord ++ tailWord_5931141).sum := by decide
  have hdescent : baseEnd_5931141 < baseStart_5931141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931175 : List Nat := [1, 1, 6, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_5931175 : Nat := 118140960795 + 5931175 * 2 ^ 59
def prefixEnd_5931175 : Nat := 4983230072969 + 3 ^ 40 * 5931175 * 2
def baseEnd_5931175 : Nat := 3045543620930936984235529

theorem tailTrace_5931175 : CollatzResearch.WordTrace tailWord_5931175 prefixEnd_5931175 3045543620930936984235529 := by
  unfold tailWord_5931175
  simp only [CollatzResearch.WordTrace]
  refine ⟨216327724287373413888922979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144218482858248942592615319 216327724287373413888922979)
  ·
    refine ⟨324491586431060120833384469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216327724287373413888922979 324491586431060120833384469)
    ·
      refine ⟨15210543113955943164064897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 324491586431060120833384469 15210543113955943164064897)
      ·
        refine ⟨11407907335466957373048673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15210543113955943164064897 11407907335466957373048673)
        ·
          refine ⟨8555930501600218029786505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11407907335466957373048673 8555930501600218029786505)
          ·
            refine ⟨6416947876200163522339879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8555930501600218029786505 6416947876200163522339879)
            ·
              refine ⟨9625421814300245283509819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6416947876200163522339879 9625421814300245283509819)
              ·
                refine ⟨14438132721450367925264729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9625421814300245283509819 14438132721450367925264729)
                ·
                  refine ⟨10828599541087775943948547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14438132721450367925264729 10828599541087775943948547)
                  ·
                    refine ⟨16242899311631663915922821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10828599541087775943948547 16242899311631663915922821)
                    ·
                      refine ⟨3045543620930936984235529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16242899311631663915922821 3045543620930936984235529)
                      ·
                        rfl

theorem cell23_5931175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_5931175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931175 prefixEnd_5931175 := by exact prefixLift 5931175
  have htrace : WordTrace (prefixWord ++ tailWord_5931175) baseStart_5931175 baseEnd_5931175 := by
    simpa [prefixWord, tailWord_5931175, baseEnd_5931175] using wordTrace_append hprefix tailTrace_5931175
  have hstable : (prefixWord ++ tailWord_5931175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931175).length < 2 ^ (prefixWord ++ tailWord_5931175).sum := by decide
  have hdescent : baseEnd_5931175 < baseStart_5931175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931202 : List Nat := [3, 5, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_5931202 : Nat := 118140960795 + 5931202 * 2 ^ 59
def prefixEnd_5931202 : Nat := 4983230072969 + 3 ^ 40 * 5931202 * 2
def baseEnd_5931202 : Nat := 1015185828302869459532635

theorem tailTrace_5931202 : CollatzResearch.WordTrace tailWord_5931202 prefixEnd_5931202 1015185828302869459532635 := by
  unfold tailWord_5931202
  simp only [CollatzResearch.WordTrace]
  refine ⟨54082177264568899375038965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144219139372183731666770573 54082177264568899375038965)
  ·
    refine ⟨5070204118553334316409903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54082177264568899375038965 5070204118553334316409903)
    ·
      refine ⟨7605306177830001474614855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5070204118553334316409903 7605306177830001474614855)
      ·
        refine ⟨11407959266745002211922283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7605306177830001474614855 11407959266745002211922283)
        ·
          refine ⟨17111938900117503317883425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11407959266745002211922283 17111938900117503317883425)
          ·
            refine ⟨12833954175088127488412569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17111938900117503317883425 12833954175088127488412569)
            ·
              refine ⟨9625465631316095616309427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12833954175088127488412569 9625465631316095616309427)
              ·
                refine ⟨14438198446974143424464141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9625465631316095616309427 14438198446974143424464141)
                ·
                  refine ⟨5414324417615303784174053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14438198446974143424464141 5414324417615303784174053)
                  ·
                    refine ⟨1015185828302869459532635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5414324417615303784174053 1015185828302869459532635)
                    ·
                      rfl

theorem cell23_5931202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_5931202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931202 prefixEnd_5931202 := by exact prefixLift 5931202
  have htrace : WordTrace (prefixWord ++ tailWord_5931202) baseStart_5931202 baseEnd_5931202 := by
    simpa [prefixWord, tailWord_5931202, baseEnd_5931202] using wordTrace_append hprefix tailTrace_5931202
  have hstable : (prefixWord ++ tailWord_5931202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931202).length < 2 ^ (prefixWord ++ tailWord_5931202).sum := by decide
  have hdescent : baseEnd_5931202 < baseStart_5931202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931218 : List Nat := [3, 2, 2, 2, 1, 2, 1, 2, 1, 5, 2]
def baseStart_5931218 : Nat := 118140960795 + 5931218 * 2 ^ 59
def prefixEnd_5931218 : Nat := 4983230072969 + 3 ^ 40 * 5931218 * 2
def baseEnd_5931218 : Nat := 3045565700599080315997831

theorem tailTrace_5931218 : CollatzResearch.WordTrace tailWord_5931218 prefixEnd_5931218 3045565700599080315997831 := by
  unfold tailWord_5931218
  simp only [CollatzResearch.WordTrace]
  refine ⟨54082323156554408058184577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144219528417478421488492205 54082323156554408058184577)
  ·
    refine ⟨40561742367415806043638433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54082323156554408058184577 40561742367415806043638433)
    ·
      refine ⟨30421306775561854532728825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40561742367415806043638433 30421306775561854532728825)
      ·
        refine ⟨22815980081671390899546619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30421306775561854532728825 22815980081671390899546619)
        ·
          refine ⟨34223970122507086349319929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22815980081671390899546619 34223970122507086349319929)
          ·
            refine ⟨25667977591880314761989947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34223970122507086349319929 25667977591880314761989947)
            ·
              refine ⟨38501966387820472142984921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25667977591880314761989947 38501966387820472142984921)
              ·
                refine ⟨28876474790865354107238691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38501966387820472142984921 28876474790865354107238691)
                ·
                  refine ⟨43314712186298031160858037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28876474790865354107238691 43314712186298031160858037)
                  ·
                    refine ⟨4060754267465440421330441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43314712186298031160858037 4060754267465440421330441)
                    ·
                      refine ⟨3045565700599080315997831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4060754267465440421330441 3045565700599080315997831)
                      ·
                        rfl

theorem cell23_5931218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_5931218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931218 prefixEnd_5931218 := by exact prefixLift 5931218
  have htrace : WordTrace (prefixWord ++ tailWord_5931218) baseStart_5931218 baseEnd_5931218 := by
    simpa [prefixWord, tailWord_5931218, baseEnd_5931218] using wordTrace_append hprefix tailTrace_5931218
  have hstable : (prefixWord ++ tailWord_5931218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931218).length < 2 ^ (prefixWord ++ tailWord_5931218).sum := by decide
  have hdescent : baseEnd_5931218 < baseStart_5931218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931231 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 1, 8, 2]
def baseStart_5931231 : Nat := 118140960795 + 5931231 * 2 ^ 59
def prefixEnd_5931231 : Nat := 4983230072969 + 3 ^ 40 * 5931231 * 2
def baseEnd_5931231 : Nat := 3045572375847588765135271

theorem tailTrace_5931231 : CollatzResearch.WordTrace tailWord_5931231 prefixEnd_5931231 3045572375847588765135271 := by
  unfold tailWord_5931231
  simp only [CollatzResearch.WordTrace]
  refine ⟨216329766775170535452961547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144219844516780356968641031 216329766775170535452961547)
  ·
    refine ⟨324494650162755803179442321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216329766775170535452961547 324494650162755803179442321)
    ·
      refine ⟨243370987622066852384581741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324494650162755803179442321 243370987622066852384581741)
      ·
        refine ⟨91264120358275069644218153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243370987622066852384581741 91264120358275069644218153)
        ·
          refine ⟨68448090268706302233163615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91264120358275069644218153 68448090268706302233163615)
          ·
            refine ⟨102672135403059453349745423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68448090268706302233163615 102672135403059453349745423)
            ·
              refine ⟨154008203104589180024618135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102672135403059453349745423 154008203104589180024618135)
              ·
                refine ⟨231012304656883770036927203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154008203104589180024618135 231012304656883770036927203)
                ·
                  refine ⟨346518456985325655055390805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231012304656883770036927203 346518456985325655055390805)
                  ·
                    refine ⟨4060763167796785020180361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 346518456985325655055390805 4060763167796785020180361)
                    ·
                      refine ⟨3045572375847588765135271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4060763167796785020180361 3045572375847588765135271)
                      ·
                        rfl

theorem cell23_5931231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 8, 2].length) (baseStart_5931231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931231 prefixEnd_5931231 := by exact prefixLift 5931231
  have htrace : WordTrace (prefixWord ++ tailWord_5931231) baseStart_5931231 baseEnd_5931231 := by
    simpa [prefixWord, tailWord_5931231, baseEnd_5931231] using wordTrace_append hprefix tailTrace_5931231
  have hstable : (prefixWord ++ tailWord_5931231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931231).length < 2 ^ (prefixWord ++ tailWord_5931231).sum := by decide
  have hdescent : baseEnd_5931231 < baseStart_5931231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931248 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 5, 2, 2]
def baseStart_5931248 : Nat := 118140960795 + 5931248 * 2 ^ 59
def prefixEnd_5931248 : Nat := 4983230072969 + 3 ^ 40 * 5931248 * 2
def baseEnd_5931248 : Nat := 3045581105018715198622693

theorem tailTrace_5931248 : CollatzResearch.WordTrace tailWord_5931248 prefixEnd_5931248 3045581105018715198622693 := by
  unfold tailWord_5931248
  simp only [CollatzResearch.WordTrace]
  refine ⟨108165193408054473678165199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144220257877405964904220265 108165193408054473678165199)
  ·
    refine ⟨162247790112081710517247799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108165193408054473678165199 162247790112081710517247799)
    ·
      refine ⟨243371685168122565775871699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162247790112081710517247799 243371685168122565775871699)
      ·
        refine ⟨365057527752183848663807549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243371685168122565775871699 365057527752183848663807549)
        ·
          refine ⟨136896572907068943248927831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 365057527752183848663807549 136896572907068943248927831)
          ·
            refine ⟨205344859360603414873391747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136896572907068943248927831 205344859360603414873391747)
            ·
              refine ⟨308017289040905122310087621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205344859360603414873391747 308017289040905122310087621)
              ·
                refine ⟨57753241695169710433141429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 308017289040905122310087621 57753241695169710433141429)
                ·
                  refine ⟨5414366408922160353107009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57753241695169710433141429 5414366408922160353107009)
                  ·
                    refine ⟨4060774806691620264830257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5414366408922160353107009 4060774806691620264830257)
                    ·
                      refine ⟨3045581105018715198622693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4060774806691620264830257 3045581105018715198622693)
                      ·
                        rfl

theorem cell23_5931248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 5, 2, 2].length) (baseStart_5931248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931248 prefixEnd_5931248 := by exact prefixLift 5931248
  have htrace : WordTrace (prefixWord ++ tailWord_5931248) baseStart_5931248 baseEnd_5931248 := by
    simpa [prefixWord, tailWord_5931248, baseEnd_5931248] using wordTrace_append hprefix tailTrace_5931248
  have hstable : (prefixWord ++ tailWord_5931248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931248).length < 2 ^ (prefixWord ++ tailWord_5931248).sum := by decide
  have hdescent : baseEnd_5931248 < baseStart_5931248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931251 : List Nat := [1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 5]
def baseStart_5931251 : Nat := 118140960795 + 5931251 * 2 ^ 59
def prefixEnd_5931251 : Nat := 4983230072969 + 3 ^ 40 * 5931251 * 2
def baseEnd_5931251 : Nat := 3045582645460678686885179

theorem tailTrace_5931251 : CollatzResearch.WordTrace tailWord_5931251 prefixEnd_5931251 3045582645460678686885179 := by
  unfold tailWord_5931251
  simp only [CollatzResearch.WordTrace]
  refine ⟨216330496235098078868689607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144220330823398719245793071 216330496235098078868689607)
  ·
    refine ⟨324495744352647118303034411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216330496235098078868689607 324495744352647118303034411)
    ·
      refine ⟨486743616528970677454551617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324495744352647118303034411 486743616528970677454551617)
      ·
        refine ⟨365057712396728008090913713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 486743616528970677454551617 365057712396728008090913713)
        ·
          refine ⟨273793284297546006068185285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365057712396728008090913713 273793284297546006068185285)
          ·
            refine ⟨51336240805789876137784741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 273793284297546006068185285 51336240805789876137784741)
            ·
              refine ⟨9625545151085601775834639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51336240805789876137784741 9625545151085601775834639)
              ·
                refine ⟨14438317726628402663751959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9625545151085601775834639 14438317726628402663751959)
                ·
                  refine ⟨21657476589942603995627939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14438317726628402663751959 21657476589942603995627939)
                  ·
                    refine ⟨32486214884913905993441909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21657476589942603995627939 32486214884913905993441909)
                    ·
                      refine ⟨3045582645460678686885179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32486214884913905993441909 3045582645460678686885179)
                      ·
                        rfl

theorem cell23_5931251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 5].length) (baseStart_5931251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931251 prefixEnd_5931251 := by exact prefixLift 5931251
  have htrace : WordTrace (prefixWord ++ tailWord_5931251) baseStart_5931251 baseEnd_5931251 := by
    simpa [prefixWord, tailWord_5931251, baseEnd_5931251] using wordTrace_append hprefix tailTrace_5931251
  have hstable : (prefixWord ++ tailWord_5931251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931251).length < 2 ^ (prefixWord ++ tailWord_5931251).sum := by decide
  have hdescent : baseEnd_5931251 < baseStart_5931251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931298 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 3, 3, 3]
def baseStart_5931298 : Nat := 118140960795 + 5931298 * 2 ^ 59
def prefixEnd_5931298 : Nat := 4983230072969 + 3 ^ 40 * 5931298 * 2
def baseEnd_5931298 : Nat := 3045606779051440002997463

theorem tailTrace_5931298 : CollatzResearch.WordTrace tailWord_5931298 prefixEnd_5931298 3045606779051440002997463 := by
  unfold tailWord_5931298
  simp only [CollatzResearch.WordTrace]
  refine ⟨54083052616481951473912637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144221473643951870597100365 54083052616481951473912637)
  ·
    refine ⟨20281144731180731802717239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54083052616481951473912637 20281144731180731802717239)
    ·
      refine ⟨30421717096771097704075859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20281144731180731802717239 30421717096771097704075859)
      ·
        refine ⟨45632575645156646556113789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30421717096771097704075859 45632575645156646556113789)
        ·
          refine ⟨17112215866933742458542671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45632575645156646556113789 17112215866933742458542671)
          ·
            refine ⟨25668323800400613687814007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17112215866933742458542671 25668323800400613687814007)
            ·
              refine ⟨38502485700600920531721011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25668323800400613687814007 38502485700600920531721011)
              ·
                refine ⟨57753728550901380797581517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38502485700600920531721011 57753728550901380797581517)
                ·
                  refine ⟨21657648206588017799093069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57753728550901380797581517 21657648206588017799093069)
                  ·
                    refine ⟨8121618077470506674659901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21657648206588017799093069 8121618077470506674659901)
                    ·
                      refine ⟨3045606779051440002997463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8121618077470506674659901 3045606779051440002997463)
                      ·
                        rfl

theorem cell23_5931298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_5931298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931298 prefixEnd_5931298 := by exact prefixLift 5931298
  have htrace : WordTrace (prefixWord ++ tailWord_5931298) baseStart_5931298 baseEnd_5931298 := by
    simpa [prefixWord, tailWord_5931298, baseEnd_5931298] using wordTrace_append hprefix tailTrace_5931298
  have hstable : (prefixWord ++ tailWord_5931298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931298).length < 2 ^ (prefixWord ++ tailWord_5931298).sum := by decide
  have hdescent : baseEnd_5931298 < baseStart_5931298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931315 : List Nat := [1, 1, 1, 2, 5, 1, 4, 2, 2, 1, 3]
def baseStart_5931315 : Nat := 118140960795 + 5931315 * 2 ^ 59
def prefixEnd_5931315 : Nat := 4983230072969 + 3 ^ 40 * 5931315 * 2
def baseEnd_5931315 : Nat := 3045615508222566436484885

theorem tailTrace_5931315 : CollatzResearch.WordTrace tailWord_5931315 prefixEnd_5931315 3045615508222566436484885 := by
  unfold tailWord_5931315
  simp only [CollatzResearch.WordTrace]
  refine ⟨216332830506866217799019399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144221887004577478532679599 216332830506866217799019399)
  ·
    refine ⟨324499245760299326698529099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216332830506866217799019399 324499245760299326698529099)
    ·
      refine ⟨486748868640448990047793649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324499245760299326698529099 486748868640448990047793649)
      ·
        refine ⟨365061651480336742535845237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 486748868640448990047793649 365061651480336742535845237)
        ·
          refine ⟨34224529826281569612735491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 365061651480336742535845237 34224529826281569612735491)
          ·
            refine ⟨51336794739422354419103237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34224529826281569612735491 51336794739422354419103237)
            ·
              refine ⟨9625649013641691453581857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51336794739422354419103237 9625649013641691453581857)
              ·
                refine ⟨7219236760231268590186393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9625649013641691453581857 7219236760231268590186393)
                ·
                  refine ⟨5414427570173451442639795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7219236760231268590186393 5414427570173451442639795)
                  ·
                    refine ⟨8121641355260177163959693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5414427570173451442639795 8121641355260177163959693)
                    ·
                      refine ⟨3045615508222566436484885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8121641355260177163959693 3045615508222566436484885)
                      ·
                        rfl

theorem cell23_5931315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 2, 1, 3].length) (baseStart_5931315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931315 prefixEnd_5931315 := by exact prefixLift 5931315
  have htrace : WordTrace (prefixWord ++ tailWord_5931315) baseStart_5931315 baseEnd_5931315 := by
    simpa [prefixWord, tailWord_5931315, baseEnd_5931315] using wordTrace_append hprefix tailTrace_5931315
  have hstable : (prefixWord ++ tailWord_5931315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931315).length < 2 ^ (prefixWord ++ tailWord_5931315).sum := by decide
  have hdescent : baseEnd_5931315 < baseStart_5931315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931316 : List Nat := [2, 5, 1, 1, 1, 2, 4, 2, 1, 2, 2]
def baseStart_5931316 : Nat := 118140960795 + 5931316 * 2 ^ 59
def prefixEnd_5931316 : Nat := 4983230072969 + 3 ^ 40 * 5931316 * 2
def baseEnd_5931316 : Nat := 3045616021703220932572381

theorem tailTrace_5931316 : CollatzResearch.WordTrace tailWord_5931316 prefixEnd_5931316 3045616021703220932572381 := by
  unfold tailWord_5931316
  simp only [CollatzResearch.WordTrace]
  refine ⟨108166433489931297484902901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144221911319908396646537201 108166433489931297484902901)
  ·
    refine ⟨10140603139681059139209647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108166433489931297484902901 10140603139681059139209647)
    ·
      refine ⟨15210904709521588708814471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10140603139681059139209647 15210904709521588708814471)
      ·
        refine ⟨22816357064282383063221707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15210904709521588708814471 22816357064282383063221707)
        ·
          refine ⟨34224535596423574594832561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22816357064282383063221707 34224535596423574594832561)
          ·
            refine ⟨25668401697317680946124421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34224535596423574594832561 25668401697317680946124421)
            ·
              refine ⟨4812825318247065177398329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25668401697317680946124421 4812825318247065177398329)
              ·
                refine ⟨3609618988685298883048747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4812825318247065177398329 3609618988685298883048747)
                ·
                  refine ⟨5414428483027948324573121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3609618988685298883048747 5414428483027948324573121)
                  ·
                    refine ⟨4060821362270961243429841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5414428483027948324573121 4060821362270961243429841)
                    ·
                      refine ⟨3045616021703220932572381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4060821362270961243429841 3045616021703220932572381)
                      ·
                        rfl

theorem cell23_5931316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_5931316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931316 prefixEnd_5931316 := by exact prefixLift 5931316
  have htrace : WordTrace (prefixWord ++ tailWord_5931316) baseStart_5931316 baseEnd_5931316 := by
    simpa [prefixWord, tailWord_5931316, baseEnd_5931316] using wordTrace_append hprefix tailTrace_5931316
  have hstable : (prefixWord ++ tailWord_5931316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931316).length < 2 ^ (prefixWord ++ tailWord_5931316).sum := by decide
  have hdescent : baseEnd_5931316 < baseStart_5931316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931332 : List Nat := [2, 3, 4, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_5931332 : Nat := 118140960795 + 5931332 * 2 ^ 59
def prefixEnd_5931332 : Nat := 4983230072969 + 3 ^ 40 * 5931332 * 2
def baseEnd_5931332 : Nat := 3045624237393692869972307

theorem tailTrace_5931332 : CollatzResearch.WordTrace tailWord_5931332 prefixEnd_5931332 3045624237393692869972307 := by
  unfold tailWord_5931332
  simp only [CollatzResearch.WordTrace]
  refine ⟨108166725273902314851194125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144222300365203086468258833 108166725273902314851194125)
  ·
    refine ⟨40562521977713368069197797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108166725273902314851194125 40562521977713368069197797)
    ·
      refine ⟨7605472870821256512974587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40562521977713368069197797 7605472870821256512974587)
      ·
        refine ⟨11408209306231884769461881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7605472870821256512974587 11408209306231884769461881)
        ·
          refine ⟨8556156979673913577096411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11408209306231884769461881 8556156979673913577096411)
          ·
            refine ⟨12834235469510870365644617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8556156979673913577096411 12834235469510870365644617)
            ·
              refine ⟨9625676602133152774233463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12834235469510870365644617 9625676602133152774233463)
              ·
                refine ⟨14438514903199729161350195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9625676602133152774233463 14438514903199729161350195)
                ·
                  refine ⟨21657772354799593742025293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14438514903199729161350195 21657772354799593742025293)
                  ·
                    refine ⟨8121664633049847653259485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21657772354799593742025293 8121664633049847653259485)
                    ·
                      refine ⟨3045624237393692869972307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8121664633049847653259485 3045624237393692869972307)
                      ·
                        rfl

theorem cell23_5931332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_5931332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931332 prefixEnd_5931332 := by exact prefixLift 5931332
  have htrace : WordTrace (prefixWord ++ tailWord_5931332) baseStart_5931332 baseEnd_5931332 := by
    simpa [prefixWord, tailWord_5931332, baseEnd_5931332] using wordTrace_append hprefix tailTrace_5931332
  have hstable : (prefixWord ++ tailWord_5931332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931332).length < 2 ^ (prefixWord ++ tailWord_5931332).sum := by decide
  have hdescent : baseEnd_5931332 < baseStart_5931332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931351 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 4]
def baseStart_5931351 : Nat := 118140960795 + 5931351 * 2 ^ 59
def prefixEnd_5931351 : Nat := 4983230072969 + 3 ^ 40 * 5931351 * 2
def baseEnd_5931351 : Nat := 3045633993526128295634719

theorem tailTrace_5931351 : CollatzResearch.WordTrace tailWord_5931351 prefixEnd_5931351 3045633993526128295634719 := by
  unfold tailWord_5931351
  simp only [CollatzResearch.WordTrace]
  refine ⟨216334143534735795947329907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144222762356490530631553271 216334143534735795947329907)
  ·
    refine ⟨324501215302103693920994861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216334143534735795947329907 324501215302103693920994861)
    ·
      refine ⟨121687955738288885220373073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324501215302103693920994861 121687955738288885220373073)
      ·
        refine ⟨91265966803716663915279805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121687955738288885220373073 91265966803716663915279805)
        ·
          refine ⟨34224737551393748968229927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91265966803716663915279805 34224737551393748968229927)
          ·
            refine ⟨51337106327090623452344891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34224737551393748968229927 51337106327090623452344891)
            ·
              refine ⟨77005659490635935178517337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51337106327090623452344891 77005659490635935178517337)
              ·
                refine ⟨57754244617976951383888003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77005659490635935178517337 57754244617976951383888003)
                ·
                  refine ⟨86631366926965427075832005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57754244617976951383888003 86631366926965427075832005)
                  ·
                    refine ⟨16243381298806017576718501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86631366926965427075832005 16243381298806017576718501)
                    ·
                      refine ⟨3045633993526128295634719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16243381298806017576718501 3045633993526128295634719)
                      ·
                        rfl

theorem cell23_5931351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_5931351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931351 prefixEnd_5931351 := by exact prefixLift 5931351
  have htrace : WordTrace (prefixWord ++ tailWord_5931351) baseStart_5931351 baseEnd_5931351 := by
    simpa [prefixWord, tailWord_5931351, baseEnd_5931351] using wordTrace_append hprefix tailTrace_5931351
  have hstable : (prefixWord ++ tailWord_5931351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931351).length < 2 ^ (prefixWord ++ tailWord_5931351).sum := by decide
  have hdescent : baseEnd_5931351 < baseStart_5931351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931368 : List Nat := [2, 1, 4, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_5931368 : Nat := 118140960795 + 5931368 * 2 ^ 59
def prefixEnd_5931368 : Nat := 4983230072969 + 3 ^ 40 * 5931368 * 2
def baseEnd_5931368 : Nat := 3045642722697254729122141

theorem tailTrace_5931368 : CollatzResearch.WordTrace tailWord_5931368 prefixEnd_5931368 3045642722697254729122141 := by
  unfold tailWord_5931368
  simp only [CollatzResearch.WordTrace]
  refine ⟨108167381787837103925349379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144223175717116138567132505 108167381787837103925349379)
  ·
    refine ⟨162251072681755655888024069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108167381787837103925349379 162251072681755655888024069)
    ·
      refine ⟨30422076127829185479004513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162251072681755655888024069 30422076127829185479004513)
      ·
        refine ⟨22816557095871889109253385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30422076127829185479004513 22816557095871889109253385)
        ·
          refine ⟨17112417821903916831940039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22816557095871889109253385 17112417821903916831940039)
          ·
            refine ⟨25668626732855875247910059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17112417821903916831940039 25668626732855875247910059)
            ·
              refine ⟨38502940099283812871865089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25668626732855875247910059 38502940099283812871865089)
              ·
                refine ⟨28877205074462859653898817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38502940099283812871865089 28877205074462859653898817)
                ·
                  refine ⟨21657903805847144740424113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28877205074462859653898817 21657903805847144740424113)
                  ·
                    refine ⟨16243427854385358555318085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21657903805847144740424113 16243427854385358555318085)
                    ·
                      refine ⟨3045642722697254729122141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16243427854385358555318085 3045642722697254729122141)
                      ·
                        rfl

theorem cell23_5931368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_5931368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931368 prefixEnd_5931368 := by exact prefixLift 5931368
  have htrace : WordTrace (prefixWord ++ tailWord_5931368) baseStart_5931368 baseEnd_5931368 := by
    simpa [prefixWord, tailWord_5931368, baseEnd_5931368] using wordTrace_append hprefix tailTrace_5931368
  have hstable : (prefixWord ++ tailWord_5931368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931368).length < 2 ^ (prefixWord ++ tailWord_5931368).sum := by decide
  have hdescent : baseEnd_5931368 < baseStart_5931368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931371 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 3]
def baseStart_5931371 : Nat := 118140960795 + 5931371 * 2 ^ 59
def prefixEnd_5931371 : Nat := 4983230072969 + 3 ^ 40 * 5931371 * 2
def baseEnd_5931371 : Nat := 3045644263139218217384627

theorem tailTrace_5931371 : CollatzResearch.WordTrace tailWord_5931371 prefixEnd_5931371 3045644263139218217384627 := by
  unfold tailWord_5931371
  simp only [CollatzResearch.WordTrace]
  refine ⟨216334872994663339363057967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144223248663108892908705311 216334872994663339363057967)
  ·
    refine ⟨324502309491995009044586951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216334872994663339363057967 324502309491995009044586951)
    ·
      refine ⟨486753464237992513566880427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324502309491995009044586951 486753464237992513566880427)
      ·
        refine ⟨730130196356988770350320641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486753464237992513566880427 730130196356988770350320641)
        ·
          refine ⟨547597647267741577762740481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 730130196356988770350320641 547597647267741577762740481)
          ·
            refine ⟨410698235450806183322055361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 547597647267741577762740481 410698235450806183322055361)
            ·
              refine ⟨308023676588104637491541521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 410698235450806183322055361 308023676588104637491541521)
              ·
                refine ⟨231017757441078478118656141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308023676588104637491541521 231017757441078478118656141)
                ·
                  refine ⟨86631659040404429294496053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 231017757441078478118656141 86631659040404429294496053)
                  ·
                    refine ⟨8121718035037915246359005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86631659040404429294496053 8121718035037915246359005)
                    ·
                      refine ⟨3045644263139218217384627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8121718035037915246359005 3045644263139218217384627)
                      ·
                        rfl

theorem cell23_5931371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 3].length) (baseStart_5931371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931371 prefixEnd_5931371 := by exact prefixLift 5931371
  have htrace : WordTrace (prefixWord ++ tailWord_5931371) baseStart_5931371 baseEnd_5931371 := by
    simpa [prefixWord, tailWord_5931371, baseEnd_5931371] using wordTrace_append hprefix tailTrace_5931371
  have hstable : (prefixWord ++ tailWord_5931371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931371).length < 2 ^ (prefixWord ++ tailWord_5931371).sum := by decide
  have hdescent : baseEnd_5931371 < baseStart_5931371 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931372 : List Nat := [2, 2, 1, 1, 6, 1, 1, 1, 4, 2, 2]
def baseStart_5931372 : Nat := 118140960795 + 5931372 * 2 ^ 59
def prefixEnd_5931372 : Nat := 4983230072969 + 3 ^ 40 * 5931372 * 2
def baseEnd_5931372 : Nat := 3045644776619872713472123

theorem tailTrace_5931372 : CollatzResearch.WordTrace tailWord_5931372 prefixEnd_5931372 3045644776619872713472123 := by
  unfold tailWord_5931372
  simp only [CollatzResearch.WordTrace]
  refine ⟨108167454733829858266922185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144223272978439811022562913 108167454733829858266922185)
  ·
    refine ⟨81125591050372393700191639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108167454733829858266922185 81125591050372393700191639)
    ·
      refine ⟨121688386575558590550287459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81125591050372393700191639 121688386575558590550287459)
      ·
        refine ⟨182532579863337885825431189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121688386575558590550287459 182532579863337885825431189)
        ·
          refine ⟨8556214681093963398067087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 182532579863337885825431189 8556214681093963398067087)
          ·
            refine ⟨12834322021640945097100631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8556214681093963398067087 12834322021640945097100631)
            ·
              refine ⟨19251483032461417645650947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12834322021640945097100631 19251483032461417645650947)
              ·
                refine ⟨28877224548692126468476421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19251483032461417645650947 28877224548692126468476421)
                ·
                  refine ⟨5414479602879773712839329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28877224548692126468476421 5414479602879773712839329)
                  ·
                    refine ⟨4060859702159830284629497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5414479602879773712839329 4060859702159830284629497)
                    ·
                      refine ⟨3045644776619872713472123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4060859702159830284629497 3045644776619872713472123)
                      ·
                        rfl

theorem cell23_5931372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 2, 2].length) (baseStart_5931372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931372 prefixEnd_5931372 := by exact prefixLift 5931372
  have htrace : WordTrace (prefixWord ++ tailWord_5931372) baseStart_5931372 baseEnd_5931372 := by
    simpa [prefixWord, tailWord_5931372, baseEnd_5931372] using wordTrace_append hprefix tailTrace_5931372
  have hstable : (prefixWord ++ tailWord_5931372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931372).length < 2 ^ (prefixWord ++ tailWord_5931372).sum := by decide
  have hdescent : baseEnd_5931372 < baseStart_5931372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931378 : List Nat := [3, 2, 1, 2, 1, 4, 2, 1, 7]
def baseStart_5931378 : Nat := 118140960795 + 5931378 * 2 ^ 59
def prefixEnd_5931378 : Nat := 4983230072969 + 3 ^ 40 * 5931378 * 2
def baseEnd_5931378 : Nat := 338405317500422187777455

theorem tailTrace_5931378 : CollatzResearch.WordTrace tailWord_5931378 prefixEnd_5931378 338405317500422187777455 := by
  unfold tailWord_5931378
  simp only [CollatzResearch.WordTrace]
  refine ⟨54083782076409494889640697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144223418870425319705708525 54083782076409494889640697)
  ·
    refine ⟨40562836557307121167230523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54083782076409494889640697 40562836557307121167230523)
    ·
      refine ⟨60844254835960681750845785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40562836557307121167230523 60844254835960681750845785)
      ·
        refine ⟨45633191126970511313134339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60844254835960681750845785 45633191126970511313134339)
        ·
          refine ⟨68449786690455766969701509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45633191126970511313134339 68449786690455766969701509)
          ·
            refine ⟨12834335004460456306819033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68449786690455766969701509 12834335004460456306819033)
            ·
              refine ⟨9625751253345342230114275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12834335004460456306819033 9625751253345342230114275)
              ·
                refine ⟨14438626880018013345171413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9625751253345342230114275 14438626880018013345171413)
                ·
                  refine ⟨338405317500422187777455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14438626880018013345171413 338405317500422187777455)
                  ·
                    rfl

theorem cell23_5931378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 7].length) (baseStart_5931378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931378 prefixEnd_5931378 := by exact prefixLift 5931378
  have htrace : WordTrace (prefixWord ++ tailWord_5931378) baseStart_5931378 baseEnd_5931378 := by
    simpa [prefixWord, tailWord_5931378, baseEnd_5931378] using wordTrace_append hprefix tailTrace_5931378
  have hstable : (prefixWord ++ tailWord_5931378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931378).length < 2 ^ (prefixWord ++ tailWord_5931378).sum := by decide
  have hdescent : baseEnd_5931378 < baseStart_5931378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931389 : List Nat := [1, 4, 1, 1, 2, 4, 3, 1, 2, 2, 2]
def baseStart_5931389 : Nat := 118140960795 + 5931389 * 2 ^ 59
def prefixEnd_5931389 : Nat := 4983230072969 + 3 ^ 40 * 5931389 * 2
def baseEnd_5931389 : Nat := 3045653505790999146959545

theorem tailTrace_5931389 : CollatzResearch.WordTrace tailWord_5931389 prefixEnd_5931389 3045653505790999146959545 := by
  unfold tailWord_5931389
  simp only [CollatzResearch.WordTrace]
  refine ⟨216335529508598128437213221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144223686339065418958142147 216335529508598128437213221)
  ·
    refine ⟨40562911782862149081977479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216335529508598128437213221 40562911782862149081977479)
    ·
      refine ⟨60844367674293223622966219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40562911782862149081977479 60844367674293223622966219)
      ·
        refine ⟨91266551511439835434449329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60844367674293223622966219 91266551511439835434449329)
        ·
          refine ⟨68449913633579876575836997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91266551511439835434449329 68449913633579876575836997)
          ·
            refine ⟨12834358806296226857969437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68449913633579876575836997 12834358806296226857969437)
            ·
              refine ⟨4812884552361085071738539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12834358806296226857969437 4812884552361085071738539)
              ·
                refine ⟨7219326828541627607607809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4812884552361085071738539 7219326828541627607607809)
                ·
                  refine ⟨5414495121406220705705857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7219326828541627607607809 5414495121406220705705857)
                  ·
                    refine ⟨4060871341054665529279393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5414495121406220705705857 4060871341054665529279393)
                    ·
                      refine ⟨3045653505790999146959545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4060871341054665529279393 3045653505790999146959545)
                      ·
                        rfl

theorem cell23_5931389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 2, 2, 2].length) (baseStart_5931389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931389 prefixEnd_5931389 := by exact prefixLift 5931389
  have htrace : WordTrace (prefixWord ++ tailWord_5931389) baseStart_5931389 baseEnd_5931389 := by
    simpa [prefixWord, tailWord_5931389, baseEnd_5931389] using wordTrace_append hprefix tailTrace_5931389
  have hstable : (prefixWord ++ tailWord_5931389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931389).length < 2 ^ (prefixWord ++ tailWord_5931389).sum := by decide
  have hdescent : baseEnd_5931389 < baseStart_5931389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931391 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 4, 5]
def baseStart_5931391 : Nat := 118140960795 + 5931391 * 2 ^ 59
def prefixEnd_5931391 : Nat := 4983230072969 + 3 ^ 40 * 5931391 * 2
def baseEnd_5931391 : Nat := 1015218177584102713044845

theorem tailTrace_5931391 : CollatzResearch.WordTrace tailWord_5931391 prefixEnd_5931391 1015218177584102713044845 := by
  unfold tailWord_5931391
  simp only [CollatzResearch.WordTrace]
  refine ⟨216335602454590882778786027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144223734969727255185857351 216335602454590882778786027)
  ·
    refine ⟨324503403681886324168179041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216335602454590882778786027 324503403681886324168179041)
    ·
      refine ⟨243377552761414743126134281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324503403681886324168179041 243377552761414743126134281)
      ·
        refine ⟨182533164571061057344600711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243377552761414743126134281 182533164571061057344600711)
        ·
          refine ⟨273799746856591586016901067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182533164571061057344600711 273799746856591586016901067)
          ·
            refine ⟨410699620284887379025351601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273799746856591586016901067 410699620284887379025351601)
            ·
              refine ⟨308024715213665534269013701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 410699620284887379025351601 308024715213665534269013701)
              ·
                refine ⟨57754634102562287675440069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 308024715213665534269013701 57754634102562287675440069)
                ·
                  refine ⟨10828993894230428939145013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57754634102562287675440069 10828993894230428939145013)
                  ·
                    refine ⟨1015218177584102713044845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10828993894230428939145013 1015218177584102713044845)
                    ·
                      rfl

theorem cell23_5931391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 5].length) (baseStart_5931391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931391 prefixEnd_5931391 := by exact prefixLift 5931391
  have htrace : WordTrace (prefixWord ++ tailWord_5931391) baseStart_5931391 baseEnd_5931391 := by
    simpa [prefixWord, tailWord_5931391, baseEnd_5931391] using wordTrace_append hprefix tailTrace_5931391
  have hstable : (prefixWord ++ tailWord_5931391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931391).length < 2 ^ (prefixWord ++ tailWord_5931391).sum := by decide
  have hdescent : baseEnd_5931391 < baseStart_5931391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931428 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 4, 1, 4]
def baseStart_5931428 : Nat := 118140960795 + 5931428 * 2 ^ 59
def prefixEnd_5931428 : Nat := 4983230072969 + 3 ^ 40 * 5931428 * 2
def baseEnd_5931428 : Nat := 3045673531536524494371865

theorem tailTrace_5931428 : CollatzResearch.WordTrace tailWord_5931428 prefixEnd_5931428 3045673531536524494371865 := by
  unfold tailWord_5931428
  simp only [CollatzResearch.WordTrace]
  refine ⟨108168475977728419048941469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144224634636971225398588625 108168475977728419048941469)
  ·
    refine ⟨40563178491648157143353051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108168475977728419048941469 40563178491648157143353051)
    ·
      refine ⟨60844767737472235715029577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40563178491648157143353051 60844767737472235715029577)
      ·
        refine ⟨45633575803104176786272183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60844767737472235715029577 45633575803104176786272183)
        ·
          refine ⟨68450363704656265179408275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45633575803104176786272183 68450363704656265179408275)
          ·
            refine ⟨102675545556984397769112413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68450363704656265179408275 102675545556984397769112413)
            ·
              refine ⟨38503329583869149163417155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102675545556984397769112413 38503329583869149163417155)
              ·
                refine ⟨57754994375803723745125733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38503329583869149163417155 57754994375803723745125733)
                ·
                  refine ⟨10829061445463198202211075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57754994375803723745125733 10829061445463198202211075)
                  ·
                    refine ⟨16243592168194797303316613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10829061445463198202211075 16243592168194797303316613)
                    ·
                      refine ⟨3045673531536524494371865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16243592168194797303316613 3045673531536524494371865)
                      ·
                        rfl

theorem cell23_5931428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_5931428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931428 prefixEnd_5931428 := by exact prefixLift 5931428
  have htrace : WordTrace (prefixWord ++ tailWord_5931428) baseStart_5931428 baseEnd_5931428 := by
    simpa [prefixWord, tailWord_5931428, baseEnd_5931428] using wordTrace_append hprefix tailTrace_5931428
  have hstable : (prefixWord ++ tailWord_5931428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931428).length < 2 ^ (prefixWord ++ tailWord_5931428).sum := by decide
  have hdescent : baseEnd_5931428 < baseStart_5931428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931448 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 6, 2, 3]
def baseStart_5931448 : Nat := 118140960795 + 5931448 * 2 ^ 59
def prefixEnd_5931448 : Nat := 4983230072969 + 3 ^ 40 * 5931448 * 2
def baseEnd_5931448 : Nat := 3045683801149614416121773

theorem tailTrace_5931448 : CollatzResearch.WordTrace tailWord_5931448 prefixEnd_5931448 3045683801149614416121773 := by
  unfold tailWord_5931448
  simp only [CollatzResearch.WordTrace]
  refine ⟨108168840707692190756805499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144225120943589587675740665 108168840707692190756805499)
  ·
    refine ⟨162253261061538286135208249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108168840707692190756805499 162253261061538286135208249)
    ·
      refine ⟨121689945796153714601406187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162253261061538286135208249 121689945796153714601406187)
      ·
        refine ⟨182534918694230571902109281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121689945796153714601406187 182534918694230571902109281)
        ·
          refine ⟨136901189020672928926581961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182534918694230571902109281 136901189020672928926581961)
          ·
            refine ⟨102675891765504696694936471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136901189020672928926581961 102675891765504696694936471)
            ·
              refine ⟨154013837648257045042404707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102675891765504696694936471 154013837648257045042404707)
              ·
                refine ⟨231020756472385567563607061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154013837648257045042404707 231020756472385567563607061)
                ·
                  refine ⟨10829097959643073479544081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 231020756472385567563607061 10829097959643073479544081)
                  ·
                    refine ⟨8121823469732305109658061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10829097959643073479544081 8121823469732305109658061)
                    ·
                      refine ⟨3045683801149614416121773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8121823469732305109658061 3045683801149614416121773)
                      ·
                        rfl

theorem cell23_5931448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 6, 2, 3].length) (baseStart_5931448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931448 prefixEnd_5931448 := by exact prefixLift 5931448
  have htrace : WordTrace (prefixWord ++ tailWord_5931448) baseStart_5931448 baseEnd_5931448 := by
    simpa [prefixWord, tailWord_5931448, baseEnd_5931448] using wordTrace_append hprefix tailTrace_5931448
  have hstable : (prefixWord ++ tailWord_5931448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931448).length < 2 ^ (prefixWord ++ tailWord_5931448).sum := by decide
  have hdescent : baseEnd_5931448 < baseStart_5931448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931471 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 8]
def baseStart_5931471 : Nat := 118140960795 + 5931471 * 2 ^ 59
def prefixEnd_5931471 : Nat := 4983230072969 + 3 ^ 40 * 5931471 * 2
def baseEnd_5931471 : Nat := 3045695611204667826134167

theorem tailTrace_5931471 : CollatzResearch.WordTrace tailWord_5931471 prefixEnd_5931471 3045695611204667826134167 := by
  unfold tailWord_5931471
  simp only [CollatzResearch.WordTrace]
  refine ⟨216338520294301056441698267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144225680196200704294465511 216338520294301056441698267)
  ·
    refine ⟨324507780441451584662547401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216338520294301056441698267 324507780441451584662547401)
    ·
      refine ⟨243380835331088688496910551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324507780441451584662547401 243380835331088688496910551)
      ·
        refine ⟨365071252996633032745365827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243380835331088688496910551 365071252996633032745365827)
        ·
          refine ⟨547606879494949549118048741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365071252996633032745365827 547606879494949549118048741)
          ·
            refine ⟨102676289905303040459634139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 547606879494949549118048741 102676289905303040459634139)
            ·
              refine ⟨154014434857954560689451209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102676289905303040459634139 154014434857954560689451209)
              ·
                refine ⟨115510826143465920517088407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154014434857954560689451209 115510826143465920517088407)
                ·
                  refine ⟨173266239215198880775632611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115510826143465920517088407 173266239215198880775632611)
                  ·
                    refine ⟨259899358822798321163448917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 173266239215198880775632611 259899358822798321163448917)
                    ·
                      refine ⟨3045695611204667826134167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 259899358822798321163448917 3045695611204667826134167)
                      ·
                        rfl

theorem cell23_5931471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_5931471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931471 prefixEnd_5931471 := by exact prefixLift 5931471
  have htrace : WordTrace (prefixWord ++ tailWord_5931471) baseStart_5931471 baseEnd_5931471 := by
    simpa [prefixWord, tailWord_5931471, baseEnd_5931471] using wordTrace_append hprefix tailTrace_5931471
  have hstable : (prefixWord ++ tailWord_5931471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931471).length < 2 ^ (prefixWord ++ tailWord_5931471).sum := by decide
  have hdescent : baseEnd_5931471 < baseStart_5931471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931485 : List Nat := [1, 4, 3, 1, 1, 1, 4, 2, 6]
def baseStart_5931485 : Nat := 118140960795 + 5931485 * 2 ^ 59
def prefixEnd_5931485 : Nat := 4983230072969 + 3 ^ 40 * 5931485 * 2
def baseEnd_5931485 : Nat := 338411422214870085706567

theorem tailTrace_5931485 : CollatzResearch.WordTrace tailWord_5931485 prefixEnd_5931485 338411422214870085706567 := by
  unfold tailWord_5931485
  simp only [CollatzResearch.WordTrace]
  refine ⟨216339030916250336832707909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144226020610833557888471939 216339030916250336832707909)
  ·
    refine ⟨40563568296796938156132733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 216339030916250336832707909 40563568296796938156132733)
    ·
      refine ⟨15211338111298851808549775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40563568296796938156132733 15211338111298851808549775)
      ·
        refine ⟨22817007166948277712824663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15211338111298851808549775 22817007166948277712824663)
        ·
          refine ⟨34225510750422416569236995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22817007166948277712824663 34225510750422416569236995)
          ·
            refine ⟨51338266125633624853855493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34225510750422416569236995 51338266125633624853855493)
            ·
              refine ⟨9625924898556304660097905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51338266125633624853855493 9625924898556304660097905)
              ·
                refine ⟨7219443673917228495073429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9625924898556304660097905 7219443673917228495073429)
                ·
                  refine ⟨338411422214870085706567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7219443673917228495073429 338411422214870085706567)
                  ·
                    rfl

theorem cell23_5931485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 6].length) (baseStart_5931485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931485 prefixEnd_5931485 := by exact prefixLift 5931485
  have htrace : WordTrace (prefixWord ++ tailWord_5931485) baseStart_5931485 baseEnd_5931485 := by
    simpa [prefixWord, tailWord_5931485, baseEnd_5931485] using wordTrace_append hprefix tailTrace_5931485
  have hstable : (prefixWord ++ tailWord_5931485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931485).length < 2 ^ (prefixWord ++ tailWord_5931485).sum := by decide
  have hdescent : baseEnd_5931485 < baseStart_5931485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931505 : List Nat := [1, 2, 2, 2, 3, 1, 2, 2, 1, 5, 2]
def baseStart_5931505 : Nat := 118140960795 + 5931505 * 2 ^ 59
def prefixEnd_5931505 : Nat := 4983230072969 + 3 ^ 40 * 5931505 * 2
def baseEnd_5931505 : Nat := 3045713069546920693109011

theorem tailTrace_5931505 : CollatzResearch.WordTrace tailWord_5931505 prefixEnd_5931505 3045713069546920693109011 := by
  unfold tailWord_5931505
  simp only [CollatzResearch.WordTrace]
  refine ⟨216339760376177880248435969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144226506917451920165623979 216339760376177880248435969)
  ·
    refine ⟨162254820282133410186326977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216339760376177880248435969 162254820282133410186326977)
    ·
      refine ⟨121691115211600057639745233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162254820282133410186326977 121691115211600057639745233)
      ·
        refine ⟨91268336408700043229808925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121691115211600057639745233 91268336408700043229808925)
        ·
          refine ⟨34225626153262516211178347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91268336408700043229808925 34225626153262516211178347)
          ·
            refine ⟨51338439229893774316767521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34225626153262516211178347 51338439229893774316767521)
            ·
              refine ⟨38503829422420330737575641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51338439229893774316767521 38503829422420330737575641)
              ·
                refine ⟨28877872066815248053181731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38503829422420330737575641 28877872066815248053181731)
                ·
                  refine ⟨43316808100222872079772597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28877872066815248053181731 43316808100222872079772597)
                  ·
                    refine ⟨4060950759395894257478681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43316808100222872079772597 4060950759395894257478681)
                    ·
                      refine ⟨3045713069546920693109011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4060950759395894257478681 3045713069546920693109011)
                      ·
                        rfl

theorem cell23_5931505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 5, 2].length) (baseStart_5931505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931505 prefixEnd_5931505 := by exact prefixLift 5931505
  have htrace : WordTrace (prefixWord ++ tailWord_5931505) baseStart_5931505 baseEnd_5931505 := by
    simpa [prefixWord, tailWord_5931505, baseEnd_5931505] using wordTrace_append hprefix tailTrace_5931505
  have hstable : (prefixWord ++ tailWord_5931505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931505).length < 2 ^ (prefixWord ++ tailWord_5931505).sum := by decide
  have hdescent : baseEnd_5931505 < baseStart_5931505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931532 : List Nat := [2, 2, 1, 2, 4, 1, 4, 1, 1, 5]
def baseStart_5931532 : Nat := 118140960795 + 5931532 * 2 ^ 59
def prefixEnd_5931532 : Nat := 4983230072969 + 3 ^ 40 * 5931532 * 2
def baseEnd_5931532 : Nat := 1015242311174864029157129

theorem tailTrace_5931532 : CollatzResearch.WordTrace tailWord_5931532 prefixEnd_5931532 1015242311174864029157129 := by
  unfold tailWord_5931532
  simp only [CollatzResearch.WordTrace]
  refine ⟨108170372573540031929834425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144227163431386709239779233 108170372573540031929834425)
  ·
    refine ⟨81127779430155023947375819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108170372573540031929834425 81127779430155023947375819)
    ·
      refine ⟨121691669145232535921063729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81127779430155023947375819 121691669145232535921063729)
      ·
        refine ⟨91268751858924401940797797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121691669145232535921063729 91268751858924401940797797)
        ·
          refine ⟨17112890973548325363899587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91268751858924401940797797 17112890973548325363899587)
          ·
            refine ⟨25669336460322488045849381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17112890973548325363899587 25669336460322488045849381)
            ·
              refine ⟨4813000586310466508596759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25669336460322488045849381 4813000586310466508596759)
              ·
                refine ⟨7219500879465699762895139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4813000586310466508596759 7219500879465699762895139)
                ·
                  refine ⟨10829251319198549644342709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7219500879465699762895139 10829251319198549644342709)
                  ·
                    refine ⟨1015242311174864029157129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10829251319198549644342709 1015242311174864029157129)
                    ·
                      rfl

theorem cell23_5931532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 1, 5].length) (baseStart_5931532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931532 prefixEnd_5931532 := by exact prefixLift 5931532
  have htrace : WordTrace (prefixWord ++ tailWord_5931532) baseStart_5931532 baseEnd_5931532 := by
    simpa [prefixWord, tailWord_5931532, baseEnd_5931532] using wordTrace_append hprefix tailTrace_5931532
  have hstable : (prefixWord ++ tailWord_5931532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931532).length < 2 ^ (prefixWord ++ tailWord_5931532).sum := by decide
  have hdescent : baseEnd_5931532 < baseStart_5931532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931555 : List Nat := [1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 5]
def baseStart_5931555 : Nat := 118140960795 + 5931555 * 2 ^ 59
def prefixEnd_5931555 : Nat := 4983230072969 + 3 ^ 40 * 5931555 * 2
def baseEnd_5931555 : Nat := 3045738743579645497483781

theorem tailTrace_5931555 : CollatzResearch.WordTrace tailWord_5931555 prefixEnd_5931555 3045738743579645497483781 := by
  unfold tailWord_5931555
  simp only [CollatzResearch.WordTrace]
  refine ⟨216341584025996738787756119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144227722683997825858504079 216341584025996738787756119)
  ·
    refine ⟨324512376038995108181634179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216341584025996738787756119 324512376038995108181634179)
    ·
      refine ⟨486768564058492662272451269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324512376038995108181634179 486768564058492662272451269)
      ·
        refine ⟨91269105760967374176084613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 486768564058492662272451269 91269105760967374176084613)
        ·
          refine ⟨17112957330181382658015865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91269105760967374176084613 17112957330181382658015865)
          ·
            refine ⟨12834717997636036993511899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17112957330181382658015865 12834717997636036993511899)
            ·
              refine ⟨19252076996454055490267849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12834717997636036993511899 19252076996454055490267849)
              ·
                refine ⟨14439057747340541617700887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19252076996454055490267849 14439057747340541617700887)
                ·
                  refine ⟨21658586621010812426551331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14439057747340541617700887 21658586621010812426551331)
                  ·
                    refine ⟨32487879931516218639826997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21658586621010812426551331 32487879931516218639826997)
                    ·
                      refine ⟨3045738743579645497483781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32487879931516218639826997 3045738743579645497483781)
                      ·
                        rfl

theorem cell23_5931555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_5931555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931555 prefixEnd_5931555 := by exact prefixLift 5931555
  have htrace : WordTrace (prefixWord ++ tailWord_5931555) baseStart_5931555 baseEnd_5931555 := by
    simpa [prefixWord, tailWord_5931555, baseEnd_5931555] using wordTrace_append hprefix tailTrace_5931555
  have hstable : (prefixWord ++ tailWord_5931555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931555).length < 2 ^ (prefixWord ++ tailWord_5931555).sum := by decide
  have hdescent : baseEnd_5931555 < baseStart_5931555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931562 : List Nat := [3, 1, 4, 1, 1, 4, 1, 1, 1, 6]
def baseStart_5931562 : Nat := 118140960795 + 5931562 * 2 ^ 59
def prefixEnd_5931562 : Nat := 4983230072969 + 3 ^ 40 * 5931562 * 2
def baseEnd_5931562 : Nat := 1015247445981408990032083

theorem tailTrace_5931562 : CollatzResearch.WordTrace tailWord_5931562 prefixEnd_5931562 1015247445981408990032083 := by
  unfold tailWord_5931562
  simp only [CollatzResearch.WordTrace]
  refine ⟨54085459834242844745815235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144227892891314252655507293 54085459834242844745815235)
  ·
    refine ⟨81128189751364267118722853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54085459834242844745815235 81128189751364267118722853)
    ·
      refine ⟨15211535578380800084760535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81128189751364267118722853 15211535578380800084760535)
      ·
        refine ⟨22817303367571200127140803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15211535578380800084760535 22817303367571200127140803)
        ·
          refine ⟨34225955051356800190711205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22817303367571200127140803 34225955051356800190711205)
          ·
            refine ⟨6417366572129400035758351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34225955051356800190711205 6417366572129400035758351)
            ·
              refine ⟨9626049858194100053637527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6417366572129400035758351 9626049858194100053637527)
              ·
                refine ⟨14439074787291150080456291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9626049858194100053637527 14439074787291150080456291)
                ·
                  refine ⟨21658612180936725120684437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14439074787291150080456291 21658612180936725120684437)
                  ·
                    refine ⟨1015247445981408990032083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21658612180936725120684437 1015247445981408990032083)
                    ·
                      rfl

theorem cell23_5931562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_5931562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931562 prefixEnd_5931562 := by exact prefixLift 5931562
  have htrace : WordTrace (prefixWord ++ tailWord_5931562) baseStart_5931562 baseEnd_5931562 := by
    simpa [prefixWord, tailWord_5931562, baseEnd_5931562] using wordTrace_append hprefix tailTrace_5931562
  have hstable : (prefixWord ++ tailWord_5931562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931562).length < 2 ^ (prefixWord ++ tailWord_5931562).sum := by decide
  have hdescent : baseEnd_5931562 < baseStart_5931562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931602 : List Nat := [3, 2, 2, 1, 2, 1, 1, 3, 4, 1, 3]
def baseStart_5931602 : Nat := 118140960795 + 5931602 * 2 ^ 59
def prefixEnd_5931602 : Nat := 4983230072969 + 3 ^ 40 * 5931602 * 2
def baseEnd_5931602 : Nat := 3045762877170406813596065

theorem tailTrace_5931602 : CollatzResearch.WordTrace tailWord_5931602 prefixEnd_5931602 3045762877170406813596065 := by
  unfold tailWord_5931602
  simp only [CollatzResearch.WordTrace]
  refine ⟨54085824564206616453679265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144228865504550977209811373 54085824564206616453679265)
  ·
    refine ⟨40564368423154962340259449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54085824564206616453679265 40564368423154962340259449)
    ·
      refine ⟨30423276317366221755194587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40564368423154962340259449 30423276317366221755194587)
      ·
        refine ⟨45634914476049332632791881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30423276317366221755194587 45634914476049332632791881)
        ·
          refine ⟨34226185857036999474593911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45634914476049332632791881 34226185857036999474593911)
          ·
            refine ⟨51339278785555499211890867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34226185857036999474593911 51339278785555499211890867)
            ·
              refine ⟨77008918178333248817836301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51339278785555499211890867 77008918178333248817836301)
              ·
                refine ⟨28878344316874968306688613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77008918178333248817836301 28878344316874968306688613)
                ·
                  refine ⟨5414689559414056557504115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28878344316874968306688613 5414689559414056557504115)
                  ·
                    refine ⟨8122034339121084836256173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5414689559414056557504115 8122034339121084836256173)
                    ·
                      refine ⟨3045762877170406813596065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8122034339121084836256173 3045762877170406813596065)
                      ·
                        rfl

theorem cell23_5931602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_5931602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931602 prefixEnd_5931602 := by exact prefixLift 5931602
  have htrace : WordTrace (prefixWord ++ tailWord_5931602) baseStart_5931602 baseEnd_5931602 := by
    simpa [prefixWord, tailWord_5931602, baseEnd_5931602] using wordTrace_append hprefix tailTrace_5931602
  have hstable : (prefixWord ++ tailWord_5931602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931602).length < 2 ^ (prefixWord ++ tailWord_5931602).sum := by decide
  have hdescent : baseEnd_5931602 < baseStart_5931602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931629 : List Nat := [1, 5, 1, 1, 3, 2, 1, 1, 3, 3, 2]
def baseStart_5931629 : Nat := 118140960795 + 5931629 * 2 ^ 59
def prefixEnd_5931629 : Nat := 4983230072969 + 3 ^ 40 * 5931629 * 2
def baseEnd_5931629 : Nat := 3045776741148078207958441

theorem tailTrace_5931629 : CollatzResearch.WordTrace tailWord_5931629 prefixEnd_5931629 3045776741148078207958441 := by
  unfold tailWord_5931629
  simp only [CollatzResearch.WordTrace]
  refine ⟨216344283027728649425949941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144229522018485766283966627 216344283027728649425949941)
  ·
    refine ⟨20282276533849560883682807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 216344283027728649425949941 20282276533849560883682807)
    ·
      refine ⟨30423414800774341325524211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20282276533849560883682807 30423414800774341325524211)
      ·
        refine ⟨45635122201161511988286317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30423414800774341325524211 45635122201161511988286317)
        ·
          refine ⟨17113170825435566995607369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45635122201161511988286317 17113170825435566995607369)
          ·
            refine ⟨12834878119076675246705527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17113170825435566995607369 12834878119076675246705527)
            ·
              refine ⟨19252317178615012870058291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12834878119076675246705527 19252317178615012870058291)
              ·
                refine ⟨28878475767922519305087437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19252317178615012870058291 28878475767922519305087437)
                ·
                  refine ⟨10829428412970944739407789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28878475767922519305087437 10829428412970944739407789)
                  ·
                    refine ⟨4061035654864104277277921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10829428412970944739407789 4061035654864104277277921)
                    ·
                      refine ⟨3045776741148078207958441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4061035654864104277277921 3045776741148078207958441)
                      ·
                        rfl

theorem cell23_5931629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_5931629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931629 prefixEnd_5931629 := by exact prefixLift 5931629
  have htrace : WordTrace (prefixWord ++ tailWord_5931629) baseStart_5931629 baseEnd_5931629 := by
    simpa [prefixWord, tailWord_5931629, baseEnd_5931629] using wordTrace_append hprefix tailTrace_5931629
  have hstable : (prefixWord ++ tailWord_5931629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931629).length < 2 ^ (prefixWord ++ tailWord_5931629).sum := by decide
  have hdescent : baseEnd_5931629 < baseStart_5931629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931655 : List Nat := [1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 4]
def baseStart_5931655 : Nat := 118140960795 + 5931655 * 2 ^ 59
def prefixEnd_5931655 : Nat := 4983230072969 + 3 ^ 40 * 5931655 * 2
def baseEnd_5931655 : Nat := 3045790091645095106233321

theorem tailTrace_5931655 : CollatzResearch.WordTrace tailWord_5931655 prefixEnd_5931655 3045790091645095106233321 := by
  unfold tailWord_5931655
  simp only [CollatzResearch.WordTrace]
  refine ⟨216345231325634455866396419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144230154217089637244264279 216345231325634455866396419)
  ·
    refine ⟨324517846988451683799594629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216345231325634455866396419 324517846988451683799594629)
    ·
      refine ⟨60847096310334690712423993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 324517846988451683799594629 60847096310334690712423993)
      ·
        refine ⟨45635322232751018034317995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60847096310334690712423993 45635322232751018034317995)
        ·
          refine ⟨68452983349126527051476993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45635322232751018034317995 68452983349126527051476993)
          ·
            refine ⟨51339737511844895288607745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68452983349126527051476993 51339737511844895288607745)
            ·
              refine ⟨38504803133883671466455809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51339737511844895288607745 38504803133883671466455809)
              ·
                refine ⟨28878602350412753599841857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38504803133883671466455809 28878602350412753599841857)
                ·
                  refine ⟨21658951762809565199881393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28878602350412753599841857 21658951762809565199881393)
                  ·
                    refine ⟨16244213822107173899911045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21658951762809565199881393 16244213822107173899911045)
                    ·
                      refine ⟨3045790091645095106233321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16244213822107173899911045 3045790091645095106233321)
                      ·
                        rfl

theorem cell23_5931655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_5931655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931655 prefixEnd_5931655 := by exact prefixLift 5931655
  have htrace : WordTrace (prefixWord ++ tailWord_5931655) baseStart_5931655 baseEnd_5931655 := by
    simpa [prefixWord, tailWord_5931655, baseEnd_5931655] using wordTrace_append hprefix tailTrace_5931655
  have hstable : (prefixWord ++ tailWord_5931655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931655).length < 2 ^ (prefixWord ++ tailWord_5931655).sum := by decide
  have hdescent : baseEnd_5931655 < baseStart_5931655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931676 : List Nat := [2, 2, 3, 2, 2, 1, 2, 3, 2, 2, 2]
def baseStart_5931676 : Nat := 118140960795 + 5931676 * 2 ^ 59
def prefixEnd_5931676 : Nat := 4983230072969 + 3 ^ 40 * 5931676 * 2
def baseEnd_5931676 : Nat := 3045800874738839524070725

theorem tailTrace_5931676 : CollatzResearch.WordTrace tailWord_5931676 prefixEnd_5931676 3045800874738839524070725 := by
  unfold tailWord_5931676
  simp only [CollatzResearch.WordTrace]
  refine ⟨108172998629279188226455441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144230664839038917635273921 108172998629279188226455441)
  ·
    refine ⟨81129748971959391169841581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108172998629279188226455441 81129748971959391169841581)
    ·
      refine ⟨30423655864484771688690593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81129748971959391169841581 30423655864484771688690593)
      ·
        refine ⟨22817741898363578766517945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30423655864484771688690593 22817741898363578766517945)
        ·
          refine ⟨17113306423772684074888459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22817741898363578766517945 17113306423772684074888459)
          ·
            refine ⟨25669959635659026112332689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17113306423772684074888459 25669959635659026112332689)
            ·
              refine ⟨19252469726744269584249517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25669959635659026112332689 19252469726744269584249517)
              ·
                refine ⟨7219676147529101094093569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19252469726744269584249517 7219676147529101094093569)
                ·
                  refine ⟨5414757110646825820570177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7219676147529101094093569 5414757110646825820570177)
                  ·
                    refine ⟨4061067832985119365427633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5414757110646825820570177 4061067832985119365427633)
                    ·
                      refine ⟨3045800874738839524070725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4061067832985119365427633 3045800874738839524070725)
                      ·
                        rfl

theorem cell23_5931676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_5931676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931676 prefixEnd_5931676 := by exact prefixLift 5931676
  have htrace : WordTrace (prefixWord ++ tailWord_5931676) baseStart_5931676 baseEnd_5931676 := by
    simpa [prefixWord, tailWord_5931676, baseEnd_5931676] using wordTrace_append hprefix tailTrace_5931676
  have hstable : (prefixWord ++ tailWord_5931676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931676).length < 2 ^ (prefixWord ++ tailWord_5931676).sum := by decide
  have hdescent : baseEnd_5931676 < baseStart_5931676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931695 : List Nat := [1, 1, 2, 1, 2, 6, 1, 1, 1, 7]
def baseStart_5931695 : Nat := 118140960795 + 5931695 * 2 ^ 59
def prefixEnd_5931695 : Nat := 4983230072969 + 3 ^ 40 * 5931695 * 2
def baseEnd_5931695 : Nat := 1015270210290424983244379

theorem tailTrace_5931695 : CollatzResearch.WordTrace tailWord_5931695 prefixEnd_5931695 1015270210290424983244379 := by
  unfold tailWord_5931695
  simp only [CollatzResearch.WordTrace]
  refine ⟨216346690245489542697852539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144231126830326361798568359 216346690245489542697852539)
  ·
    refine ⟨324520035368234314046778809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216346690245489542697852539 324520035368234314046778809)
    ·
      refine ⟨243390026526175735535084107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324520035368234314046778809 243390026526175735535084107)
      ·
        refine ⟨365085039789263603302626161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243390026526175735535084107 365085039789263603302626161)
        ·
          refine ⟨273813779841947702476969621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365085039789263603302626161 273813779841947702476969621)
          ·
            refine ⟨12835020930091298553607951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 273813779841947702476969621 12835020930091298553607951)
            ·
              refine ⟨19252531395136947830411927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12835020930091298553607951 19252531395136947830411927)
              ·
                refine ⟨28878797092705421745617891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19252531395136947830411927 28878797092705421745617891)
                ·
                  refine ⟨43318195639058132618426837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28878797092705421745617891 43318195639058132618426837)
                  ·
                    refine ⟨1015270210290424983244379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43318195639058132618426837 1015270210290424983244379)
                    ·
                      rfl

theorem cell23_5931695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 7].length) (baseStart_5931695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931695 prefixEnd_5931695 := by exact prefixLift 5931695
  have htrace : WordTrace (prefixWord ++ tailWord_5931695) baseStart_5931695 baseEnd_5931695 := by
    simpa [prefixWord, tailWord_5931695, baseEnd_5931695] using wordTrace_append hprefix tailTrace_5931695
  have hstable : (prefixWord ++ tailWord_5931695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931695).length < 2 ^ (prefixWord ++ tailWord_5931695).sum := by decide
  have hdescent : baseEnd_5931695 < baseStart_5931695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931802 : List Nat := [3, 1, 1, 3, 2, 1, 3, 1, 3, 5]
def baseStart_5931802 : Nat := 118140960795 + 5931802 * 2 ^ 59
def prefixEnd_5931802 : Nat := 4983230072969 + 3 ^ 40 * 5931802 * 2
def baseEnd_5931802 : Nat := 1015288524433768677031715

theorem tailTrace_5931802 : CollatzResearch.WordTrace tailWord_5931802 prefixEnd_5931802 1015288524433768677031715 := by
  unfold tailWord_5931802
  simp only [CollatzResearch.WordTrace]
  refine ⟨54087648214025474992999415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144233728570734599981331773 54087648214025474992999415)
  ·
    refine ⟨81131472321038212489499123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54087648214025474992999415 81131472321038212489499123)
    ·
      refine ⟨121697208481557318734248685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81131472321038212489499123 121697208481557318734248685)
      ·
        refine ⟨45636453180583994525343257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121697208481557318734248685 45636453180583994525343257)
        ·
          refine ⟨34227339885437995894007443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45636453180583994525343257 34227339885437995894007443)
          ·
            refine ⟨51341009828156993841011165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34227339885437995894007443 51341009828156993841011165)
            ·
              refine ⟨19252878685558872690379187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51341009828156993841011165 19252878685558872690379187)
              ·
                refine ⟨28879318028338309035568781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19252878685558872690379187 28879318028338309035568781)
                ·
                  refine ⟨10829744260626865888338293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28879318028338309035568781 10829744260626865888338293)
                  ·
                    refine ⟨1015288524433768677031715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10829744260626865888338293 1015288524433768677031715)
                    ·
                      rfl

theorem cell23_5931802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 3, 5].length) (baseStart_5931802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931802 prefixEnd_5931802 := by exact prefixLift 5931802
  have htrace : WordTrace (prefixWord ++ tailWord_5931802) baseStart_5931802 baseEnd_5931802 := by
    simpa [prefixWord, tailWord_5931802, baseEnd_5931802] using wordTrace_append hprefix tailTrace_5931802
  have hstable : (prefixWord ++ tailWord_5931802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931802).length < 2 ^ (prefixWord ++ tailWord_5931802).sum := by decide
  have hdescent : baseEnd_5931802 < baseStart_5931802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931845 : List Nat := [1, 3, 1, 1, 1, 2, 2, 12]
def baseStart_5931845 : Nat := 118140960795 + 5931845 * 2 ^ 59
def prefixEnd_5931845 : Nat := 4983230072969 + 3 ^ 40 * 5931845 * 2
def baseEnd_5931845 : Nat := 112810653813683309735461

theorem tailTrace_5931845 : CollatzResearch.WordTrace tailWord_5931845 prefixEnd_5931845 112810653813683309735461 := by
  unfold tailWord_5931845
  simp only [CollatzResearch.WordTrace]
  refine ⟨216352161194946118315812989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144234774129964078877208659 216352161194946118315812989)
  ·
    refine ⟨81132060448104794368429871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216352161194946118315812989 81132060448104794368429871)
    ·
      refine ⟨121698090672157191552644807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81132060448104794368429871 121698090672157191552644807)
      ·
        refine ⟨182547136008235787328967211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121698090672157191552644807 182547136008235787328967211)
        ·
          refine ⟨273820704012353680993450817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182547136008235787328967211 273820704012353680993450817)
          ·
            refine ⟨205365528009265260745088113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273820704012353680993450817 205365528009265260745088113)
            ·
              refine ⟨154024146006948945558816085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205365528009265260745088113 154024146006948945558816085)
              ·
                refine ⟨112810653813683309735461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 154024146006948945558816085 112810653813683309735461)
                ·
                  rfl

theorem cell23_5931845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 12].length) (baseStart_5931845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931845 prefixEnd_5931845 := by exact prefixLift 5931845
  have htrace : WordTrace (prefixWord ++ tailWord_5931845) baseStart_5931845 baseEnd_5931845 := by
    simpa [prefixWord, tailWord_5931845, baseEnd_5931845] using wordTrace_append hprefix tailTrace_5931845
  have hstable : (prefixWord ++ tailWord_5931845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931845).length < 2 ^ (prefixWord ++ tailWord_5931845).sum := by decide
  have hdescent : baseEnd_5931845 < baseStart_5931845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931849 : List Nat := [1, 2, 1, 1, 2, 5, 2, 3, 2, 4]
def baseStart_5931849 : Nat := 118140960795 + 5931849 * 2 ^ 59
def prefixEnd_5931849 : Nat := 4983230072969 + 3 ^ 40 * 5931849 * 2
def baseEnd_5931849 : Nat := 1015296568964022449069143

theorem tailTrace_5931849 : CollatzResearch.WordTrace tailWord_5931849 prefixEnd_5931849 1015296568964022449069143 := by
  unfold tailWord_5931849
  simp only [CollatzResearch.WordTrace]
  refine ⟨216352307086931626998958601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144234871391287751332639067 216352307086931626998958601)
  ·
    refine ⟨162264230315198720249218951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216352307086931626998958601 162264230315198720249218951)
    ·
      refine ⟨243396345472798080373828427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162264230315198720249218951 243396345472798080373828427)
      ·
        refine ⟨365094518209197120560742641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243396345472798080373828427 365094518209197120560742641)
        ·
          refine ⟨273820888656897840420556981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365094518209197120560742641 273820888656897840420556981)
          ·
            refine ⟨25670708311584172539427217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 273820888656897840420556981 25670708311584172539427217)
            ·
              refine ⟨19253031233688129404570413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25670708311584172539427217 19253031233688129404570413)
              ·
                refine ⟨7219886712633048526713905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19253031233688129404570413 7219886712633048526713905)
                ·
                  refine ⟨5414915034474786395035429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7219886712633048526713905 5414915034474786395035429)
                  ·
                    refine ⟨1015296568964022449069143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5414915034474786395035429 1015296568964022449069143)
                    ·
                      rfl

theorem cell23_5931849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2, 4].length) (baseStart_5931849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931849 prefixEnd_5931849 := by exact prefixLift 5931849
  have htrace : WordTrace (prefixWord ++ tailWord_5931849) baseStart_5931849 baseEnd_5931849 := by
    simpa [prefixWord, tailWord_5931849, baseEnd_5931849] using wordTrace_append hprefix tailTrace_5931849
  have hstable : (prefixWord ++ tailWord_5931849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931849).length < 2 ^ (prefixWord ++ tailWord_5931849).sum := by decide
  have hdescent : baseEnd_5931849 < baseStart_5931849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931855 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 7]
def baseStart_5931855 : Nat := 118140960795 + 5931855 * 2 ^ 59
def prefixEnd_5931855 : Nat := 4983230072969 + 3 ^ 40 * 5931855 * 2
def baseEnd_5931855 : Nat := 3045892787775994323732401

theorem tailTrace_5931855 : CollatzResearch.WordTrace tailWord_5931855 prefixEnd_5931855 3045892787775994323732401 := by
  unfold tailWord_5931855
  simp only [CollatzResearch.WordTrace]
  refine ⟨216352525924909890023677019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144235017283273260015784679 216352525924909890023677019)
  ·
    refine ⟨324528788887364835035515529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216352525924909890023677019 324528788887364835035515529)
    ·
      refine ⟨243396591665523626276636647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324528788887364835035515529 243396591665523626276636647)
      ·
        refine ⟨365094887498285439414954971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243396591665523626276636647 365094887498285439414954971)
        ·
          refine ⟨547642331247428159122432457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365094887498285439414954971 547642331247428159122432457)
          ·
            refine ⟨410731748435571119341824343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 547642331247428159122432457 410731748435571119341824343)
            ·
              refine ⟨616097622653356679012736515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410731748435571119341824343 616097622653356679012736515)
              ·
                refine ⟨924146433980035018519104773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616097622653356679012736515 924146433980035018519104773)
                ·
                  refine ⟨173277456371256565972332145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 924146433980035018519104773 173277456371256565972332145)
                  ·
                    refine ⟨129958092278442424479249109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 173277456371256565972332145 129958092278442424479249109)
                    ·
                      refine ⟨3045892787775994323732401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 129958092278442424479249109 3045892787775994323732401)
                      ·
                        rfl

theorem cell23_5931855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_5931855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931855 prefixEnd_5931855 := by exact prefixLift 5931855
  have htrace : WordTrace (prefixWord ++ tailWord_5931855) baseStart_5931855 baseEnd_5931855 := by
    simpa [prefixWord, tailWord_5931855, baseEnd_5931855] using wordTrace_append hprefix tailTrace_5931855
  have hstable : (prefixWord ++ tailWord_5931855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931855).length < 2 ^ (prefixWord ++ tailWord_5931855).sum := by decide
  have hdescent : baseEnd_5931855 < baseStart_5931855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931860 : List Nat := [2, 4, 1, 1, 5, 1, 1, 1, 2, 3, 2]
def baseStart_5931860 : Nat := 118140960795 + 5931860 * 2 ^ 59
def prefixEnd_5931860 : Nat := 4983230072969 + 3 ^ 40 * 5931860 * 2
def baseEnd_5931860 : Nat := 3045895355179266804169879

theorem tailTrace_5931860 : CollatzResearch.WordTrace tailWord_5931860 prefixEnd_5931860 3045895355179266804169879 := by
  unfold tailWord_5931860
  simp only [CollatzResearch.WordTrace]
  refine ⟨108176354144945887938804517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144235138859927850585072689 108176354144945887938804517)
  ·
    refine ⟨20283066402177353988525847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108176354144945887938804517 20283066402177353988525847)
    ·
      refine ⟨30424599603266030982788771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20283066402177353988525847 30424599603266030982788771)
      ·
        refine ⟨45636899404899046474183157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30424599603266030982788771 45636899404899046474183157)
        ·
          refine ⟨4278459319209285606954671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45636899404899046474183157 4278459319209285606954671)
          ·
            refine ⟨6417688978813928410432007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4278459319209285606954671 6417688978813928410432007)
            ·
              refine ⟨9626533468220892615648011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6417688978813928410432007 9626533468220892615648011)
              ·
                refine ⟨14439800202331338923472017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9626533468220892615648011 14439800202331338923472017)
                ·
                  refine ⟨10829850151748504192604013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14439800202331338923472017 10829850151748504192604013)
                  ·
                    refine ⟨4061193806905689072226505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10829850151748504192604013 4061193806905689072226505)
                    ·
                      refine ⟨3045895355179266804169879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4061193806905689072226505 3045895355179266804169879)
                      ·
                        rfl

theorem cell23_5931860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_5931860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931860 prefixEnd_5931860 := by exact prefixLift 5931860
  have htrace : WordTrace (prefixWord ++ tailWord_5931860) baseStart_5931860 baseEnd_5931860 := by
    simpa [prefixWord, tailWord_5931860, baseEnd_5931860] using wordTrace_append hprefix tailTrace_5931860
  have hstable : (prefixWord ++ tailWord_5931860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931860).length < 2 ^ (prefixWord ++ tailWord_5931860).sum := by decide
  have hdescent : baseEnd_5931860 < baseStart_5931860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931876 : List Nat := [2, 3, 1, 1, 4, 2, 1, 3, 1, 2, 3]
def baseStart_5931876 : Nat := 118140960795 + 5931876 * 2 ^ 59
def prefixEnd_5931876 : Nat := 4983230072969 + 3 ^ 40 * 5931876 * 2
def baseEnd_5931876 : Nat := 3045903570869738741569805

theorem tailTrace_5931876 : CollatzResearch.WordTrace tailWord_5931876 prefixEnd_5931876 3045903570869738741569805 := by
  unfold tailWord_5931876
  simp only [CollatzResearch.WordTrace]
  refine ⟨108176645928916905305095741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144235527905222540406794321 108176645928916905305095741)
  ·
    refine ⟨40566242223343839489410903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108176645928916905305095741 40566242223343839489410903)
    ·
      refine ⟨60849363335015759234116355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40566242223343839489410903 60849363335015759234116355)
      ·
        refine ⟨91274045002523638851174533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60849363335015759234116355 91274045002523638851174533)
        ·
          refine ⟨17113883437973182284595225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91274045002523638851174533 17113883437973182284595225)
          ·
            refine ⟨12835412578479886713446419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17113883437973182284595225 12835412578479886713446419)
            ·
              refine ⟨19253118867719830070169629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12835412578479886713446419 19253118867719830070169629)
              ·
                refine ⟨7219919575394936276313611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19253118867719830070169629 7219919575394936276313611)
                ·
                  refine ⟨10829879363092404414470417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7219919575394936276313611 10829879363092404414470417)
                  ·
                    refine ⟨8122409522319303310852813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10829879363092404414470417 8122409522319303310852813)
                    ·
                      refine ⟨3045903570869738741569805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8122409522319303310852813 3045903570869738741569805)
                      ·
                        rfl

theorem cell23_5931876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_5931876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931876 prefixEnd_5931876 := by exact prefixLift 5931876
  have htrace : WordTrace (prefixWord ++ tailWord_5931876) baseStart_5931876 baseEnd_5931876 := by
    simpa [prefixWord, tailWord_5931876, baseEnd_5931876] using wordTrace_append hprefix tailTrace_5931876
  have hstable : (prefixWord ++ tailWord_5931876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931876).length < 2 ^ (prefixWord ++ tailWord_5931876).sum := by decide
  have hdescent : baseEnd_5931876 < baseStart_5931876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931899 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 5, 3, 2]
def baseStart_5931899 : Nat := 118140960795 + 5931899 * 2 ^ 59
def prefixEnd_5931899 : Nat := 4983230072969 + 3 ^ 40 * 5931899 * 2
def baseEnd_5931899 : Nat := 3045915380924792151582199

theorem tailTrace_5931899 : CollatzResearch.WordTrace tailWord_5931899 prefixEnd_5931899 3045915380924792151582199 := by
  unfold tailWord_5931899
  simp only [CollatzResearch.WordTrace]
  refine ⟨216354130736750485538278751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144236087157833657025519167 216354130736750485538278751)
  ·
    refine ⟨324531196105125728307418127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216354130736750485538278751 324531196105125728307418127)
    ·
      refine ⟨486796794157688592461127191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324531196105125728307418127 486796794157688592461127191)
      ·
        refine ⟨730195191236532888691690787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486796794157688592461127191 730195191236532888691690787)
        ·
          refine ⟨1095292786854799333037536181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730195191236532888691690787 1095292786854799333037536181)
          ·
            refine ⟨102683698767637437472269017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1095292786854799333037536181 102683698767637437472269017)
            ·
              refine ⟨77012774075728078104201763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102683698767637437472269017 77012774075728078104201763)
              ·
                refine ⟨115519161113592117156302645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77012774075728078104201763 115519161113592117156302645)
                ·
                  refine ⟨10829921354399260983403373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115519161113592117156302645 10829921354399260983403373)
                  ·
                    refine ⟨4061220507899722868776265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10829921354399260983403373 4061220507899722868776265)
                    ·
                      refine ⟨3045915380924792151582199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4061220507899722868776265 3045915380924792151582199)
                      ·
                        rfl

theorem cell23_5931899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 3, 2].length) (baseStart_5931899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931899 prefixEnd_5931899 := by exact prefixLift 5931899
  have htrace : WordTrace (prefixWord ++ tailWord_5931899) baseStart_5931899 baseEnd_5931899 := by
    simpa [prefixWord, tailWord_5931899, baseEnd_5931899] using wordTrace_append hprefix tailTrace_5931899
  have hstable : (prefixWord ++ tailWord_5931899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931899).length < 2 ^ (prefixWord ++ tailWord_5931899).sum := by decide
  have hdescent : baseEnd_5931899 < baseStart_5931899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931916 : List Nat := [2, 2, 1, 2, 1, 2, 3, 4, 1, 3, 2]
def baseStart_5931916 : Nat := 118140960795 + 5931916 * 2 ^ 59
def prefixEnd_5931916 : Nat := 4983230072969 + 3 ^ 40 * 5931916 * 2
def baseEnd_5931916 : Nat := 3045924110095918585069621

theorem tailTrace_5931916 : CollatzResearch.WordTrace tailWord_5931916 prefixEnd_5931916 3045924110095918585069621 := by
  unfold tailWord_5931916
  simp only [CollatzResearch.WordTrace]
  refine ⟨108177375388844448720823801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144236500518459264961098401 108177375388844448720823801)
  ·
    refine ⟨81133031541633336540617851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108177375388844448720823801 81133031541633336540617851)
    ·
      refine ⟨121699547312450004810926777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81133031541633336540617851 121699547312450004810926777)
      ·
        refine ⟨91274660484337503608195083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121699547312450004810926777 91274660484337503608195083)
        ·
          refine ⟨136911990726506255412292625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91274660484337503608195083 136911990726506255412292625)
          ·
            refine ⟨102683993044879691559219469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136911990726506255412292625 102683993044879691559219469)
            ·
              refine ⟨38506497391829884334707301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102683993044879691559219469 38506497391829884334707301)
              ·
                refine ⟨7219968260968103312757619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38506497391829884334707301 7219968260968103312757619)
                ·
                  refine ⟨10829952391452154969136429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7219968260968103312757619 10829952391452154969136429)
                  ·
                    refine ⟨4061232146794558113426161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10829952391452154969136429 4061232146794558113426161)
                    ·
                      refine ⟨3045924110095918585069621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4061232146794558113426161 3045924110095918585069621)
                      ·
                        rfl

theorem cell23_5931916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 1, 3, 2].length) (baseStart_5931916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931916 prefixEnd_5931916 := by exact prefixLift 5931916
  have htrace : WordTrace (prefixWord ++ tailWord_5931916) baseStart_5931916 baseEnd_5931916 := by
    simpa [prefixWord, tailWord_5931916, baseEnd_5931916] using wordTrace_append hprefix tailTrace_5931916
  have hstable : (prefixWord ++ tailWord_5931916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931916).length < 2 ^ (prefixWord ++ tailWord_5931916).sum := by decide
  have hdescent : baseEnd_5931916 < baseStart_5931916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5931929 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 3, 4, 2]
def baseStart_5931929 : Nat := 118140960795 + 5931929 * 2 ^ 59
def prefixEnd_5931929 : Nat := 4983230072969 + 3 ^ 40 * 5931929 * 2
def baseEnd_5931929 : Nat := 3045930785344427034207061

theorem tailTrace_5931929 : CollatzResearch.WordTrace tailWord_5931929 prefixEnd_5931929 3045930785344427034207061 := by
  unfold tailWord_5931929
  simp only [CollatzResearch.WordTrace]
  refine ⟨216355224926641800661870841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144236816617761200441247227 216355224926641800661870841)
  ·
    refine ⟨162266418694981350496403131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216355224926641800661870841 162266418694981350496403131)
    ·
      refine ⟨243399628042472025744604697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162266418694981350496403131 243399628042472025744604697)
      ·
        refine ⟨182549721031854019308453523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243399628042472025744604697 182549721031854019308453523)
        ·
          refine ⟨273824581547781028962680285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182549721031854019308453523 273824581547781028962680285)
          ·
            refine ⟨102684218080417885861005107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273824581547781028962680285 102684218080417885861005107)
            ·
              refine ⟨154026327120626828791507661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102684218080417885861005107 154026327120626828791507661)
              ·
                refine ⟨57759872670235060796815373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154026327120626828791507661 57759872670235060796815373)
                ·
                  refine ⟨21659952251338147798805765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57759872670235060796815373 21659952251338147798805765)
                  ·
                    refine ⟨4061241047125902712276081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21659952251338147798805765 4061241047125902712276081)
                    ·
                      refine ⟨3045930785344427034207061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4061241047125902712276081 3045930785344427034207061)
                      ·
                        rfl

theorem cell23_5931929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 4, 2].length) (baseStart_5931929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5931929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5931929 prefixEnd_5931929 := by exact prefixLift 5931929
  have htrace : WordTrace (prefixWord ++ tailWord_5931929) baseStart_5931929 baseEnd_5931929 := by
    simpa [prefixWord, tailWord_5931929, baseEnd_5931929] using wordTrace_append hprefix tailTrace_5931929
  have hstable : (prefixWord ++ tailWord_5931929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5931929).length < 2 ^ (prefixWord ++ tailWord_5931929).sum := by decide
  have hdescent : baseEnd_5931929 < baseStart_5931929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5931929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932012 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 4, 8]
def baseStart_5932012 : Nat := 118140960795 + 5932012 * 2 ^ 59
def prefixEnd_5932012 : Nat := 4983230072969 + 3 ^ 40 * 5932012 * 2
def baseEnd_5932012 : Nat := 1015324468079583403156393

theorem tailTrace_5932012 : CollatzResearch.WordTrace tailWord_5932012 prefixEnd_5932012 1015324468079583403156393 := by
  unfold tailWord_5932012
  simp only [CollatzResearch.WordTrace]
  refine ⟨108179126092670552918571145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144238834790227403891428193 108179126092670552918571145)
  ·
    refine ⟨81134344569502914688928359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108179126092670552918571145 81134344569502914688928359)
    ·
      refine ⟨121701516854254372033392539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81134344569502914688928359 121701516854254372033392539)
      ·
        refine ⟨182552275281381558050088809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121701516854254372033392539 182552275281381558050088809)
        ·
          refine ⟨136914206461036168537566607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182552275281381558050088809 136914206461036168537566607)
          ·
            refine ⟨205371309691554252806349911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136914206461036168537566607 205371309691554252806349911)
            ·
              refine ⟨308056964537331379209524867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205371309691554252806349911 308056964537331379209524867)
              ·
                refine ⟨462085446805997068814287301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308056964537331379209524867 462085446805997068814287301)
                ·
                  refine ⟨86641021276124450402678869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 462085446805997068814287301 86641021276124450402678869)
                  ·
                    refine ⟨1015324468079583403156393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86641021276124450402678869 1015324468079583403156393)
                    ·
                      rfl

theorem cell23_5932012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_5932012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932012 prefixEnd_5932012 := by exact prefixLift 5932012
  have htrace : WordTrace (prefixWord ++ tailWord_5932012) baseStart_5932012 baseEnd_5932012 := by
    simpa [prefixWord, tailWord_5932012, baseEnd_5932012] using wordTrace_append hprefix tailTrace_5932012
  have hstable : (prefixWord ++ tailWord_5932012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932012).length < 2 ^ (prefixWord ++ tailWord_5932012).sum := by decide
  have hdescent : baseEnd_5932012 < baseStart_5932012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932063 : List Nat := [1, 1, 2, 4, 1, 3, 2, 4, 1, 4]
def baseStart_5932063 : Nat := 118140960795 + 5932063 * 2 ^ 59
def prefixEnd_5932063 : Nat := 4983230072969 + 3 ^ 40 * 5932063 * 2
def baseEnd_5932063 : Nat := 1015333197250709836643815

theorem tailTrace_5932063 : CollatzResearch.WordTrace tailWord_5932063 prefixEnd_5932063 1015333197250709836643815 := by
  unfold tailWord_5932063
  simp only [CollatzResearch.WordTrace]
  refine ⟨216360112308156341547248843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144240074872104227698165895 216360112308156341547248843)
  ·
    refine ⟨324540168462234512320873265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216360112308156341547248843 324540168462234512320873265)
    ·
      refine ⟨243405126346675884240654949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324540168462234512320873265 243405126346675884240654949)
      ·
        refine ⟨45638461190001728295122803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 243405126346675884240654949 45638461190001728295122803)
        ·
          refine ⟨68457691785002592442684205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45638461190001728295122803 68457691785002592442684205)
          ·
            refine ⟨25671634419375972166006577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68457691785002592442684205 25671634419375972166006577)
            ·
              refine ⟨19253725814531979124504933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25671634419375972166006577 19253725814531979124504933)
              ·
                refine ⟨3610073590224746085844675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19253725814531979124504933 3610073590224746085844675)
                ·
                  refine ⟨5415110385337119128767013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3610073590224746085844675 5415110385337119128767013)
                  ·
                    refine ⟨1015333197250709836643815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5415110385337119128767013 1015333197250709836643815)
                    ·
                      rfl

theorem cell23_5932063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4, 1, 4].length) (baseStart_5932063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932063 prefixEnd_5932063 := by exact prefixLift 5932063
  have htrace : WordTrace (prefixWord ++ tailWord_5932063) baseStart_5932063 baseEnd_5932063 := by
    simpa [prefixWord, tailWord_5932063, baseEnd_5932063] using wordTrace_append hprefix tailTrace_5932063
  have hstable : (prefixWord ++ tailWord_5932063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932063).length < 2 ^ (prefixWord ++ tailWord_5932063).sum := by decide
  have hdescent : baseEnd_5932063 < baseStart_5932063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932076 : List Nat := [2, 2, 1, 1, 1, 2, 7, 1, 6]
def baseStart_5932076 : Nat := 118140960795 + 5932076 * 2 ^ 59
def prefixEnd_5932076 : Nat := 4983230072969 + 3 ^ 40 * 5932076 * 2
def baseEnd_5932076 : Nat := 338445140777848662118765

theorem tailTrace_5932076 : CollatzResearch.WordTrace tailWord_5932076 prefixEnd_5932076 338445140777848662118765 := by
  unfold tailWord_5932076
  simp only [CollatzResearch.WordTrace]
  refine ⟨108180293228554622383736041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144240390971406163178314721 108180293228554622383736041)
  ·
    refine ⟨81135219921415966787802031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108180293228554622383736041 81135219921415966787802031)
    ·
      refine ⟨121702829882123950181703047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81135219921415966787802031 121702829882123950181703047)
      ·
        refine ⟨182554244823185925272554571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121702829882123950181703047 182554244823185925272554571)
        ·
          refine ⟨273831367234778887908831857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182554244823185925272554571 273831367234778887908831857)
          ·
            refine ⟨205373525426084165931623893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273831367234778887908831857 205373525426084165931623893)
            ·
              refine ⟨4813442002173847639022435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 205373525426084165931623893 4813442002173847639022435)
              ·
                refine ⟨7220163003260771458533653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4813442002173847639022435 7220163003260771458533653)
                ·
                  refine ⟨338445140777848662118765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7220163003260771458533653 338445140777848662118765)
                  ·
                    rfl

theorem cell23_5932076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 6].length) (baseStart_5932076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932076 prefixEnd_5932076 := by exact prefixLift 5932076
  have htrace : WordTrace (prefixWord ++ tailWord_5932076) baseStart_5932076 baseEnd_5932076 := by
    simpa [prefixWord, tailWord_5932076, baseEnd_5932076] using wordTrace_append hprefix tailTrace_5932076
  have hstable : (prefixWord ++ tailWord_5932076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932076).length < 2 ^ (prefixWord ++ tailWord_5932076).sum := by decide
  have hdescent : baseEnd_5932076 < baseStart_5932076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932096 : List Nat := [2, 1, 1, 2, 2, 3, 1, 3, 1, 5, 2]
def baseStart_5932096 : Nat := 118140960795 + 5932096 * 2 ^ 59
def prefixEnd_5932096 : Nat := 4983230072969 + 3 ^ 40 * 5932096 * 2
def baseEnd_5932096 : Nat := 3046016536613727880818793

theorem tailTrace_5932096 : CollatzResearch.WordTrace tailWord_5932096 prefixEnd_5932096 3046016536613727880818793 := by
  unfold tailWord_5932096
  simp only [CollatzResearch.WordTrace]
  refine ⟨108180657958518394091600071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144240877278024525455466761 108180657958518394091600071)
  ·
    refine ⟨162270986937777591137400107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108180657958518394091600071 162270986937777591137400107)
    ·
      refine ⟨243406480406666386706100161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162270986937777591137400107 243406480406666386706100161)
      ·
        refine ⟨182554860304999790029575121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243406480406666386706100161 182554860304999790029575121)
        ·
          refine ⟨136916145228749842522181341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182554860304999790029575121 136916145228749842522181341)
          ·
            refine ⟨51343554460781190945818003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136916145228749842522181341 51343554460781190945818003)
            ·
              refine ⟨77015331691171786418727005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51343554460781190945818003 77015331691171786418727005)
              ·
                refine ⟨28880749384189419907022627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77015331691171786418727005 28880749384189419907022627)
                ·
                  refine ⟨43321124076284129860533941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28880749384189419907022627 43321124076284129860533941)
                  ·
                    refine ⟨4061355382151637174425057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43321124076284129860533941 4061355382151637174425057)
                    ·
                      refine ⟨3046016536613727880818793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4061355382151637174425057 3046016536613727880818793)
                      ·
                        rfl

theorem cell23_5932096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 1, 5, 2].length) (baseStart_5932096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932096 prefixEnd_5932096 := by exact prefixLift 5932096
  have htrace : WordTrace (prefixWord ++ tailWord_5932096) baseStart_5932096 baseEnd_5932096 := by
    simpa [prefixWord, tailWord_5932096, baseEnd_5932096] using wordTrace_append hprefix tailTrace_5932096
  have hstable : (prefixWord ++ tailWord_5932096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932096).length < 2 ^ (prefixWord ++ tailWord_5932096).sum := by decide
  have hdescent : baseEnd_5932096 < baseStart_5932096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932097 : List Nat := [1, 2, 5, 1, 3, 2, 1, 3, 1, 4]
def baseStart_5932097 : Nat := 118140960795 + 5932097 * 2 ^ 59
def prefixEnd_5932097 : Nat := 4983230072969 + 3 ^ 40 * 5932097 * 2
def baseEnd_5932097 : Nat := 1015339016698127458968763

theorem tailTrace_5932097 : CollatzResearch.WordTrace tailWord_5932097 prefixEnd_5932097 1015339016698127458968763 := by
  unfold tailWord_5932097
  simp only [CollatzResearch.WordTrace]
  refine ⟨216361352390033165353986545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144240901593355443569324363 216361352390033165353986545)
  ·
    refine ⟨162271014292524874015489909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216361352390033165353986545 162271014292524874015489909)
    ·
      refine ⟨15212907589924206938952179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162271014292524874015489909 15212907589924206938952179)
      ·
        refine ⟨22819361384886310408428269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15212907589924206938952179 22819361384886310408428269)
        ·
          refine ⟨8557260519332366403160601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22819361384886310408428269 8557260519332366403160601)
          ·
            refine ⟨6417945389499274802370451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8557260519332366403160601 6417945389499274802370451)
            ·
              refine ⟨9626918084248912203555677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6417945389499274802370451 9626918084248912203555677)
              ·
                refine ⟨3610094281593342076333379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9626918084248912203555677 3610094281593342076333379)
                ·
                  refine ⟨5415141422390013114500069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3610094281593342076333379 5415141422390013114500069)
                  ·
                    refine ⟨1015339016698127458968763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5415141422390013114500069 1015339016698127458968763)
                    ·
                      rfl

theorem cell23_5932097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_5932097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932097 prefixEnd_5932097 := by exact prefixLift 5932097
  have htrace : WordTrace (prefixWord ++ tailWord_5932097) baseStart_5932097 baseEnd_5932097 := by
    simpa [prefixWord, tailWord_5932097, baseEnd_5932097] using wordTrace_append hprefix tailTrace_5932097
  have hstable : (prefixWord ++ tailWord_5932097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932097).length < 2 ^ (prefixWord ++ tailWord_5932097).sum := by decide
  have hdescent : baseEnd_5932097 < baseStart_5932097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932106 : List Nat := [3, 1, 2, 1, 1, 2, 4, 3, 1, 5]
def baseStart_5932106 : Nat := 118140960795 + 5932106 * 2 ^ 59
def prefixEnd_5932106 : Nat := 4983230072969 + 3 ^ 40 * 5932106 * 2
def baseEnd_5932106 : Nat := 1015340557140090947231249

theorem tailTrace_5932106 : CollatzResearch.WordTrace tailWord_5932106 prefixEnd_5932106 1015340557140090947231249 := by
  unfold tailWord_5932106
  simp only [CollatzResearch.WordTrace]
  refine ⟨54090420161750139972766043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144241120431333706594042781 54090420161750139972766043)
  ·
    refine ⟨81135630242625209959149065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54090420161750139972766043 81135630242625209959149065)
    ·
      refine ⟨60851722681968907469361799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81135630242625209959149065 60851722681968907469361799)
      ·
        refine ⟨91277584022953361204042699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60851722681968907469361799 91277584022953361204042699)
        ·
          refine ⟨136916376034430041806064049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91277584022953361204042699 136916376034430041806064049)
          ·
            refine ⟨102687282025822531354548037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136916376034430041806064049 102687282025822531354548037)
            ·
              refine ⟨19253865379841724628977757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102687282025822531354548037 19253865379841724628977757)
              ·
                refine ⟨7220199517440646735866659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19253865379841724628977757 7220199517440646735866659)
                ·
                  refine ⟨10830299276160970103799989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7220199517440646735866659 10830299276160970103799989)
                  ·
                    refine ⟨1015340557140090947231249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10830299276160970103799989 1015340557140090947231249)
                    ·
                      rfl

theorem cell23_5932106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_5932106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932106 prefixEnd_5932106 := by exact prefixLift 5932106
  have htrace : WordTrace (prefixWord ++ tailWord_5932106) baseStart_5932106 baseEnd_5932106 := by
    simpa [prefixWord, tailWord_5932106, baseEnd_5932106] using wordTrace_append hprefix tailTrace_5932106
  have hstable : (prefixWord ++ tailWord_5932106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932106).length < 2 ^ (prefixWord ++ tailWord_5932106).sum := by decide
  have hdescent : baseEnd_5932106 < baseStart_5932106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932139 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 4]
def baseStart_5932139 : Nat := 118140960795 + 5932139 * 2 ^ 59
def prefixEnd_5932139 : Nat := 4983230072969 + 3 ^ 40 * 5932139 * 2
def baseEnd_5932139 : Nat := 3046038616281871212581095

theorem tailTrace_5932139 : CollatzResearch.WordTrace tailWord_5932139 prefixEnd_5932139 3046038616281871212581095 := by
  unfold tailWord_5932139
  simp only [CollatzResearch.WordTrace]
  refine ⟨216362884255881006527015471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144241922837254004351343647 216362884255881006527015471)
  ·
    refine ⟨324544326383821509790523207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216362884255881006527015471 324544326383821509790523207)
    ·
      refine ⟨486816489575732264685784811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324544326383821509790523207 486816489575732264685784811)
      ·
        refine ⟨730224734363598397028677217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486816489575732264685784811 730224734363598397028677217)
        ·
          refine ⟨547668550772698797771507913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 730224734363598397028677217 547668550772698797771507913)
          ·
            refine ⟨410751413079524098328630935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 547668550772698797771507913 410751413079524098328630935)
            ·
              refine ⟨616127119619286147492946403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410751413079524098328630935 616127119619286147492946403)
              ·
                refine ⟨924190679428929221239419605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616127119619286147492946403 924190679428929221239419605)
                ·
                  refine ⟨21660719049115528622798897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 924190679428929221239419605 21660719049115528622798897)
                  ·
                    refine ⟨16245539286836646467099173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21660719049115528622798897 16245539286836646467099173)
                    ·
                      refine ⟨3046038616281871212581095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16245539286836646467099173 3046038616281871212581095)
                      ·
                        rfl

theorem cell23_5932139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 4].length) (baseStart_5932139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932139 prefixEnd_5932139 := by exact prefixLift 5932139
  have htrace : WordTrace (prefixWord ++ tailWord_5932139) baseStart_5932139 baseEnd_5932139 := by
    simpa [prefixWord, tailWord_5932139, baseEnd_5932139] using wordTrace_append hprefix tailTrace_5932139
  have hstable : (prefixWord ++ tailWord_5932139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932139).length < 2 ^ (prefixWord ++ tailWord_5932139).sum := by decide
  have hdescent : baseEnd_5932139 < baseStart_5932139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932143 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 5, 2, 2]
def baseStart_5932143 : Nat := 118140960795 + 5932143 * 2 ^ 59
def prefixEnd_5932143 : Nat := 4983230072969 + 3 ^ 40 * 5932143 * 2
def baseEnd_5932143 : Nat := 3046040670204489196931077

theorem tailTrace_5932143 : CollatzResearch.WordTrace tailWord_5932143 prefixEnd_5932143 3046040670204489196931077 := by
  unfold tailWord_5932143
  simp only [CollatzResearch.WordTrace]
  refine ⟨216363030147866515210161083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144242020098577676806774055 216363030147866515210161083)
  ·
    refine ⟨324544545221799772815241625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216363030147866515210161083 324544545221799772815241625)
    ·
      refine ⟨243408408916349829611431219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324544545221799772815241625 243408408916349829611431219)
      ·
        refine ⟨365112613374524744417146829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243408408916349829611431219 365112613374524744417146829)
        ·
          refine ⟨136917230015446779156430061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 365112613374524744417146829 136917230015446779156430061)
          ·
            refine ⟨51343961255792542183661273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136917230015446779156430061 51343961255792542183661273)
            ·
              refine ⟨38507970941844406637745955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51343961255792542183661273 38507970941844406637745955)
              ·
                refine ⟨57761956412766609956618933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38507970941844406637745955 57761956412766609956618933)
                ·
                  refine ⟨5415183413696869683433025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57761956412766609956618933 5415183413696869683433025)
                  ·
                    refine ⟨4061387560272652262574769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5415183413696869683433025 4061387560272652262574769)
                    ·
                      refine ⟨3046040670204489196931077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4061387560272652262574769 3046040670204489196931077)
                      ·
                        rfl

theorem cell23_5932143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5, 2, 2].length) (baseStart_5932143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932143 prefixEnd_5932143 := by exact prefixLift 5932143
  have htrace : WordTrace (prefixWord ++ tailWord_5932143) baseStart_5932143 baseEnd_5932143 := by
    simpa [prefixWord, tailWord_5932143, baseEnd_5932143] using wordTrace_append hprefix tailTrace_5932143
  have hstable : (prefixWord ++ tailWord_5932143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932143).length < 2 ^ (prefixWord ++ tailWord_5932143).sum := by decide
  have hdescent : baseEnd_5932143 < baseStart_5932143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932156 : List Nat := [2, 2, 2, 1, 1, 3, 3, 2, 1, 2, 4]
def baseStart_5932156 : Nat := 118140960795 + 5932156 * 2 ^ 59
def prefixEnd_5932156 : Nat := 4983230072969 + 3 ^ 40 * 5932156 * 2
def baseEnd_5932156 : Nat := 3046047345452997646068517

theorem tailTrace_5932156 : CollatzResearch.WordTrace tailWord_5932156 prefixEnd_5932156 3046047345452997646068517 := by
  unfold tailWord_5932156
  simp only [CollatzResearch.WordTrace]
  refine ⟨108181752148409709215192161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144242336197879612286922881 108181752148409709215192161)
  ·
    refine ⟨81136314111307281911394121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108181752148409709215192161 81136314111307281911394121)
    ·
      refine ⟨60852235583480461433545591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81136314111307281911394121 60852235583480461433545591)
      ·
        refine ⟨91278353375220692150318387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60852235583480461433545591 91278353375220692150318387)
        ·
          refine ⟨136917530062831038225477581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91278353375220692150318387 136917530062831038225477581)
          ·
            refine ⟨51344073773561639334554093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136917530062831038225477581 51344073773561639334554093)
            ·
              refine ⟨19254027665085614750457785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51344073773561639334554093 19254027665085614750457785)
              ·
                refine ⟨14440520748814211062843339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19254027665085614750457785 14440520748814211062843339)
                ·
                  refine ⟨21660781123221316594265009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14440520748814211062843339 21660781123221316594265009)
                  ·
                    refine ⟨16245585842415987445698757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21660781123221316594265009 16245585842415987445698757)
                    ·
                      refine ⟨3046047345452997646068517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16245585842415987445698757 3046047345452997646068517)
                      ·
                        rfl

theorem cell23_5932156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_5932156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932156 prefixEnd_5932156 := by exact prefixLift 5932156
  have htrace : WordTrace (prefixWord ++ tailWord_5932156) baseStart_5932156 baseEnd_5932156 := by
    simpa [prefixWord, tailWord_5932156, baseEnd_5932156] using wordTrace_append hprefix tailTrace_5932156
  have hstable : (prefixWord ++ tailWord_5932156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932156).length < 2 ^ (prefixWord ++ tailWord_5932156).sum := by decide
  have hdescent : baseEnd_5932156 < baseStart_5932156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932179 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 2, 7]
def baseStart_5932179 : Nat := 118140960795 + 5932179 * 2 ^ 59
def prefixEnd_5932179 : Nat := 4983230072969 + 3 ^ 40 * 5932179 * 2
def baseEnd_5932179 : Nat := 1015353051836017018693637

theorem tailTrace_5932179 : CollatzResearch.WordTrace tailWord_5932179 prefixEnd_5932179 1015353051836017018693637 := by
  unfold tailWord_5932179
  simp only [CollatzResearch.WordTrace]
  refine ⟨216364343175736093358471591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144242895450490728905647727 216364343175736093358471591)
  ·
    refine ⟨324546514763604140037707387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216364343175736093358471591 324546514763604140037707387)
    ·
      refine ⟨486819772145406210056561081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324546514763604140037707387 486819772145406210056561081)
      ·
        refine ⟨365114829109054657542420811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 486819772145406210056561081 365114829109054657542420811)
        ·
          refine ⟨547672243663581986313631217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365114829109054657542420811 547672243663581986313631217)
          ·
            refine ⟨410754182747686489735223413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 547672243663581986313631217 410754182747686489735223413)
            ·
              refine ⟨38508204632595608412677195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 410754182747686489735223413 38508204632595608412677195)
              ·
                refine ⟨57762306948893412619015793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38508204632595608412677195 57762306948893412619015793)
                ·
                  refine ⟨43321730211670059464261845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57762306948893412619015793 43321730211670059464261845)
                  ·
                    refine ⟨1015353051836017018693637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43321730211670059464261845 1015353051836017018693637)
                    ·
                      rfl

theorem cell23_5932179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 7].length) (baseStart_5932179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932179 prefixEnd_5932179 := by exact prefixLift 5932179
  have htrace : WordTrace (prefixWord ++ tailWord_5932179) baseStart_5932179 baseEnd_5932179 := by
    simpa [prefixWord, tailWord_5932179, baseEnd_5932179] using wordTrace_append hprefix tailTrace_5932179
  have hstable : (prefixWord ++ tailWord_5932179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932179).length < 2 ^ (prefixWord ++ tailWord_5932179).sum := by decide
  have hdescent : baseEnd_5932179 < baseStart_5932179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932190 : List Nat := [4, 3, 1, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_5932190 : Nat := 118140960795 + 5932190 * 2 ^ 59
def prefixEnd_5932190 : Nat := 4983230072969 + 3 ^ 40 * 5932190 * 2
def baseEnd_5932190 : Nat := 3046064803795250513043361

theorem tailTrace_5932190 : CollatzResearch.WordTrace tailWord_5932190 prefixEnd_5932190 3046064803795250513043361 := by
  unfold tailWord_5932190
  simp only [CollatzResearch.WordTrace]
  refine ⟨27045593047337030279640253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144243162919130828158081349 27045593047337030279640253)
  ·
    refine ⟨10142097392751386354865095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27045593047337030279640253 10142097392751386354865095)
    ·
      refine ⟨15213146089127079532297643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10142097392751386354865095 15213146089127079532297643)
      ·
        refine ⟨22819719133690619298446465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15213146089127079532297643 22819719133690619298446465)
        ·
          refine ⟨17114789350267964473834849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22819719133690619298446465 17114789350267964473834849)
          ·
            refine ⟨12836092012700973355376137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17114789350267964473834849 12836092012700973355376137)
            ·
              refine ⟨9627069009525730016532103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12836092012700973355376137 9627069009525730016532103)
              ·
                refine ⟨14440603514288595024798155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9627069009525730016532103 14440603514288595024798155)
                ·
                  refine ⟨21660905271432892537197233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14440603514288595024798155 21660905271432892537197233)
                  ·
                    refine ⟨16245678953574669402897925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21660905271432892537197233 16245678953574669402897925)
                    ·
                      refine ⟨3046064803795250513043361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16245678953574669402897925 3046064803795250513043361)
                      ·
                        rfl

theorem cell23_5932190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_5932190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932190 prefixEnd_5932190 := by exact prefixLift 5932190
  have htrace : WordTrace (prefixWord ++ tailWord_5932190) baseStart_5932190 baseEnd_5932190 := by
    simpa [prefixWord, tailWord_5932190, baseEnd_5932190] using wordTrace_append hprefix tailTrace_5932190
  have hstable : (prefixWord ++ tailWord_5932190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932190).length < 2 ^ (prefixWord ++ tailWord_5932190).sum := by decide
  have hdescent : baseEnd_5932190 < baseStart_5932190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932193 : List Nat := [1, 2, 3, 3, 1, 1, 4, 1, 1, 3, 3]
def baseStart_5932193 : Nat := 118140960795 + 5932193 * 2 ^ 59
def prefixEnd_5932193 : Nat := 4983230072969 + 3 ^ 40 * 5932193 * 2
def baseEnd_5932193 : Nat := 3046066344237214001305847

theorem tailTrace_5932193 : CollatzResearch.WordTrace tailWord_5932193 prefixEnd_5932193 3046066344237214001305847 := by
  unfold tailWord_5932193
  simp only [CollatzResearch.WordTrace]
  refine ⟨216364853797685373749481233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144243235865123582499654155 216364853797685373749481233)
  ·
    refine ⟨162273640348264030312110925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216364853797685373749481233 162273640348264030312110925)
    ·
      refine ⟨60852615130599011367041597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162273640348264030312110925 60852615130599011367041597)
      ·
        refine ⟨22819730673974629262640599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60852615130599011367041597 22819730673974629262640599)
        ·
          refine ⟨34229596010961943893960899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22819730673974629262640599 34229596010961943893960899)
          ·
            refine ⟨51344394016442915840941349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34229596010961943893960899 51344394016442915840941349)
            ·
              refine ⟨9627073878083046720176503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51344394016442915840941349 9627073878083046720176503)
              ·
                refine ⟨14440610817124570080264755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9627073878083046720176503 14440610817124570080264755)
                ·
                  refine ⟨21660916225686855120397133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14440610817124570080264755 21660916225686855120397133)
                  ·
                    refine ⟨8122843584632570670148925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21660916225686855120397133 8122843584632570670148925)
                    ·
                      refine ⟨3046066344237214001305847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8122843584632570670148925 3046066344237214001305847)
                      ·
                        rfl

theorem cell23_5932193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_5932193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932193 prefixEnd_5932193 := by exact prefixLift 5932193
  have htrace : WordTrace (prefixWord ++ tailWord_5932193) baseStart_5932193 baseEnd_5932193 := by
    simpa [prefixWord, tailWord_5932193, baseEnd_5932193] using wordTrace_append hprefix tailTrace_5932193
  have hstable : (prefixWord ++ tailWord_5932193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932193).length < 2 ^ (prefixWord ++ tailWord_5932193).sum := by decide
  have hdescent : baseEnd_5932193 < baseStart_5932193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932214 : List Nat := [5, 1, 3, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_5932214 : Nat := 118140960795 + 5932214 * 2 ^ 59
def prefixEnd_5932214 : Nat := 4983230072969 + 3 ^ 40 * 5932214 * 2
def baseEnd_5932214 : Nat := 3046077127330958419143251

theorem tailTrace_5932214 : CollatzResearch.WordTrace tailWord_5932214 prefixEnd_5932214 3046077127330958419143251 := by
  unfold tailWord_5932214
  simp only [CollatzResearch.WordTrace]
  refine ⟨13522851233163080895999731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 144243746487072862890663797 13522851233163080895999731)
  ·
    refine ⟨20284276849744621343999597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13522851233163080895999731 20284276849744621343999597)
    ·
      refine ⟨7606603818654233003999849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20284276849744621343999597 7606603818654233003999849)
      ·
        refine ⟨5704952863990674752999887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7606603818654233003999849 5704952863990674752999887)
        ·
          refine ⟨8557429295986012129499831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5704952863990674752999887 8557429295986012129499831)
          ·
            refine ⟨12836143943979018194249747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8557429295986012129499831 12836143943979018194249747)
            ·
              refine ⟨19254215915968527291374621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12836143943979018194249747 19254215915968527291374621)
              ·
                refine ⟨7220330968488197734265483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19254215915968527291374621 7220330968488197734265483)
                ·
                  refine ⟨10830496452732296601398225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7220330968488197734265483 10830496452732296601398225)
                  ·
                    refine ⟨8122872339549222451048669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10830496452732296601398225 8122872339549222451048669)
                    ·
                      refine ⟨3046077127330958419143251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8122872339549222451048669 3046077127330958419143251)
                      ·
                        rfl

theorem cell23_5932214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_5932214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932214 prefixEnd_5932214 := by exact prefixLift 5932214
  have htrace : WordTrace (prefixWord ++ tailWord_5932214) baseStart_5932214 baseEnd_5932214 := by
    simpa [prefixWord, tailWord_5932214, baseEnd_5932214] using wordTrace_append hprefix tailTrace_5932214
  have hstable : (prefixWord ++ tailWord_5932214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932214).length < 2 ^ (prefixWord ++ tailWord_5932214).sum := by decide
  have hdescent : baseEnd_5932214 < baseStart_5932214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932244 : List Nat := [2, 4, 1, 4, 2, 1, 1, 1, 1, 3, 3]
def baseStart_5932244 : Nat := 118140960795 + 5932244 * 2 ^ 59
def prefixEnd_5932244 : Nat := 4983230072969 + 3 ^ 40 * 5932244 * 2
def baseEnd_5932244 : Nat := 3046092531750593301768113

theorem tailTrace_5932244 : CollatzResearch.WordTrace tailWord_5932244 prefixEnd_5932244 3046092531750593301768113 := by
  unfold tailWord_5932244
  simp only [CollatzResearch.WordTrace]
  refine ⟨108183356960250304729793893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144244475947000406306391857 108183356960250304729793893)
  ·
    refine ⟨20284379430046932136836355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108183356960250304729793893 20284379430046932136836355)
    ·
      refine ⟨30426569145070398205254533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20284379430046932136836355 30426569145070398205254533)
      ·
        refine ⟨5704981714700699663485225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30426569145070398205254533 5704981714700699663485225)
        ·
          refine ⟨4278736286025524747613919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5704981714700699663485225 4278736286025524747613919)
          ·
            refine ⟨6418104429038287121420879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4278736286025524747613919 6418104429038287121420879)
            ·
              refine ⟨9627156643557430682131319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6418104429038287121420879 9627156643557430682131319)
              ·
                refine ⟨14440734965336146023196979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9627156643557430682131319 14440734965336146023196979)
                ·
                  refine ⟨21661102448004219034795469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14440734965336146023196979 21661102448004219034795469)
                  ·
                    refine ⟨8122913418001582138048301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21661102448004219034795469 8122913418001582138048301)
                    ·
                      refine ⟨3046092531750593301768113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8122913418001582138048301 3046092531750593301768113)
                      ·
                        rfl

theorem cell23_5932244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_5932244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932244 prefixEnd_5932244 := by exact prefixLift 5932244
  have htrace : WordTrace (prefixWord ++ tailWord_5932244) baseStart_5932244 baseEnd_5932244 := by
    simpa [prefixWord, tailWord_5932244, baseEnd_5932244] using wordTrace_append hprefix tailTrace_5932244
  have hstable : (prefixWord ++ tailWord_5932244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932244).length < 2 ^ (prefixWord ++ tailWord_5932244).sum := by decide
  have hdescent : baseEnd_5932244 < baseStart_5932244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932256 : List Nat := [2, 1, 1, 3, 1, 4, 2, 2, 7]
def baseStart_5932256 : Nat := 118140960795 + 5932256 * 2 ^ 59
def prefixEnd_5932256 : Nat := 4983230072969 + 3 ^ 40 * 5932256 * 2
def baseEnd_5932256 : Nat := 338455410390938583868673

theorem tailTrace_5932256 : CollatzResearch.WordTrace tailWord_5932256 prefixEnd_5932256 338455410390938583868673 := by
  unfold tailWord_5932256
  simp only [CollatzResearch.WordTrace]
  refine ⟨108183575798228567754512311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144244767730971423672683081 108183575798228567754512311)
  ·
    refine ⟨162275363697342851631768467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108183575798228567754512311 162275363697342851631768467)
    ·
      refine ⟨243413045546014277447652701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162275363697342851631768467 243413045546014277447652701)
      ·
        refine ⟨91279892079755354042869763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243413045546014277447652701 91279892079755354042869763)
        ·
          refine ⟨136919838119633031064304645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91279892079755354042869763 136919838119633031064304645)
          ·
            refine ⟨25672469647431193324557121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136919838119633031064304645 25672469647431193324557121)
            ·
              refine ⟨19254352235573394993417841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25672469647431193324557121 19254352235573394993417841)
              ·
                refine ⟨14440764176680046245063381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19254352235573394993417841 14440764176680046245063381)
                ·
                  refine ⟨338455410390938583868673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14440764176680046245063381 338455410390938583868673)
                  ·
                    rfl

theorem cell23_5932256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 7].length) (baseStart_5932256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932256 prefixEnd_5932256 := by exact prefixLift 5932256
  have htrace : WordTrace (prefixWord ++ tailWord_5932256) baseStart_5932256 baseEnd_5932256 := by
    simpa [prefixWord, tailWord_5932256, baseEnd_5932256] using wordTrace_append hprefix tailTrace_5932256
  have hstable : (prefixWord ++ tailWord_5932256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932256).length < 2 ^ (prefixWord ++ tailWord_5932256).sum := by decide
  have hdescent : baseEnd_5932256 < baseStart_5932256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932293 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 2, 5, 2]
def baseStart_5932293 : Nat := 118140960795 + 5932293 * 2 ^ 59
def prefixEnd_5932293 : Nat := 4983230072969 + 3 ^ 40 * 5932293 * 2
def baseEnd_5932293 : Nat := 3046117692302663610055387

theorem tailTrace_5932293 : CollatzResearch.WordTrace tailWord_5932293 prefixEnd_5932293 3046117692302663610055387 := by
  unfold tailWord_5932293
  simp only [CollatzResearch.WordTrace]
  refine ⟨216368501097323090828121533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144245667398215393885414355 216368501097323090828121533)
  ·
    refine ⟨81138187911496159060545575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216368501097323090828121533 81138187911496159060545575)
    ·
      refine ⟨121707281867244238590818363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81138187911496159060545575 121707281867244238590818363)
      ·
        refine ⟨182560922800866357886227545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121707281867244238590818363 182560922800866357886227545)
        ·
          refine ⟨136920692100649768414670659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182560922800866357886227545 136920692100649768414670659)
          ·
            refine ⟨205381038150974652622005989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136920692100649768414670659 205381038150974652622005989)
            ·
              refine ⟨38508944653307747366626123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 205381038150974652622005989 38508944653307747366626123)
              ·
                refine ⟨57763416979961621049939185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38508944653307747366626123 57763416979961621049939185)
                ·
                  refine ⟨43322562734971215787454389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57763416979961621049939185 43322562734971215787454389)
                  ·
                    refine ⟨4061490256403551480073849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43322562734971215787454389 4061490256403551480073849)
                    ·
                      refine ⟨3046117692302663610055387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4061490256403551480073849 3046117692302663610055387)
                      ·
                        rfl

theorem cell23_5932293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 5, 2].length) (baseStart_5932293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932293 prefixEnd_5932293 := by exact prefixLift 5932293
  have htrace : WordTrace (prefixWord ++ tailWord_5932293) baseStart_5932293 baseEnd_5932293 := by
    simpa [prefixWord, tailWord_5932293, baseEnd_5932293] using wordTrace_append hprefix tailTrace_5932293
  have hstable : (prefixWord ++ tailWord_5932293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932293).length < 2 ^ (prefixWord ++ tailWord_5932293).sum := by decide
  have hdescent : baseEnd_5932293 < baseStart_5932293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932316 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 2, 8]
def baseStart_5932316 : Nat := 118140960795 + 5932316 * 2 ^ 59
def prefixEnd_5932316 : Nat := 4983230072969 + 3 ^ 40 * 5932316 * 2
def baseEnd_5932316 : Nat := 1015376500785905673355927

theorem tailTrace_5932316 : CollatzResearch.WordTrace tailWord_5932316 prefixEnd_5932316 1015376500785905673355927 := by
  unfold tailWord_5932316
  simp only [CollatzResearch.WordTrace]
  refine ⟨108184669988119882878104401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144246226650826510504139201 108184669988119882878104401)
  ·
    refine ⟨81138502491089912158578301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108184669988119882878104401 81138502491089912158578301)
    ·
      refine ⟨30426938434158717059466863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81138502491089912158578301 30426938434158717059466863)
      ·
        refine ⟨45640407651238075589200295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30426938434158717059466863 45640407651238075589200295)
        ·
          refine ⟨68460611476857113383800443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45640407651238075589200295 68460611476857113383800443)
          ·
            refine ⟨102690917215285670075700665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68460611476857113383800443 102690917215285670075700665)
            ·
              refine ⟨77018187911464252556775499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102690917215285670075700665 77018187911464252556775499)
              ·
                refine ⟨115527281867196378835163249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77018187911464252556775499 115527281867196378835163249)
                ·
                  refine ⟨86645461400397284126372437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115527281867196378835163249 86645461400397284126372437)
                  ·
                    refine ⟨1015376500785905673355927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86645461400397284126372437 1015376500785905673355927)
                    ·
                      rfl

theorem cell23_5932316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_5932316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932316 prefixEnd_5932316 := by exact prefixLift 5932316
  have htrace : WordTrace (prefixWord ++ tailWord_5932316) baseStart_5932316 baseEnd_5932316 := by
    simpa [prefixWord, tailWord_5932316, baseEnd_5932316] using wordTrace_append hprefix tailTrace_5932316
  have hstable : (prefixWord ++ tailWord_5932316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932316).length < 2 ^ (prefixWord ++ tailWord_5932316).sum := by decide
  have hdescent : baseEnd_5932316 < baseStart_5932316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932320 : List Nat := [2, 1, 1, 5, 3, 1, 2, 1, 2, 5]
def baseStart_5932320 : Nat := 118140960795 + 5932320 * 2 ^ 59
def prefixEnd_5932320 : Nat := 4983230072969 + 3 ^ 40 * 5932320 * 2
def baseEnd_5932320 : Nat := 1015377185426778334805921

theorem tailTrace_5932320 : CollatzResearch.WordTrace tailWord_5932320 prefixEnd_5932320 1015377185426778334805921 := by
  unfold tailWord_5932320
  simp only [CollatzResearch.WordTrace]
  refine ⟨108184742934112637219677207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144246323912150182959569609 108184742934112637219677207)
  ·
    refine ⟨162277114401168955829515811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108184742934112637219677207 162277114401168955829515811)
    ·
      refine ⟨243415671601753433744273717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162277114401168955829515811 243415671601753433744273717)
      ·
        refine ⟨22820219212664384413525661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 243415671601753433744273717 22820219212664384413525661)
        ·
          refine ⟨8557582204749144155072123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22820219212664384413525661 8557582204749144155072123)
          ·
            refine ⟨12836373307123716232608185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8557582204749144155072123 12836373307123716232608185)
            ·
              refine ⟨9627279980342787174456139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12836373307123716232608185 9627279980342787174456139)
              ·
                refine ⟨14440919970514180761684209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9627279980342787174456139 14440919970514180761684209)
                ·
                  refine ⟨10830689977885635571263157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14440919970514180761684209 10830689977885635571263157)
                  ·
                    refine ⟨1015377185426778334805921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10830689977885635571263157 1015377185426778334805921)
                    ·
                      rfl

theorem cell23_5932320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 2, 5].length) (baseStart_5932320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932320 prefixEnd_5932320 := by exact prefixLift 5932320
  have htrace : WordTrace (prefixWord ++ tailWord_5932320) baseStart_5932320 baseEnd_5932320 := by
    simpa [prefixWord, tailWord_5932320, baseEnd_5932320] using wordTrace_append hprefix tailTrace_5932320
  have hstable : (prefixWord ++ tailWord_5932320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932320).length < 2 ^ (prefixWord ++ tailWord_5932320).sum := by decide
  have hdescent : baseEnd_5932320 < baseStart_5932320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932323 : List Nat := [1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 4]
def baseStart_5932323 : Nat := 118140960795 + 5932323 * 2 ^ 59
def prefixEnd_5932323 : Nat := 4983230072969 + 3 ^ 40 * 5932323 * 2
def baseEnd_5932323 : Nat := 3046133096722298492680249

theorem tailTrace_5932323 : CollatzResearch.WordTrace tailWord_5932323 prefixEnd_5932323 3046133096722298492680249 := by
  unfold tailWord_5932323
  simp only [CollatzResearch.WordTrace]
  refine ⟨216369595287214405951713623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144246396858142937301142415 216369595287214405951713623)
  ·
    refine ⟨324554392930821608927570435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216369595287214405951713623 324554392930821608927570435)
    ·
      refine ⟨486831589396232413391355653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324554392930821608927570435 486831589396232413391355653)
      ·
        refine ⟨91280923011793577510879185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 486831589396232413391355653 91280923011793577510879185)
        ·
          refine ⟨68460692258845183133159389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91280923011793577510879185 68460692258845183133159389)
          ·
            refine ⟨25672759597066943674934771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68460692258845183133159389 25672759597066943674934771)
            ·
              refine ⟨38509139395600415512402157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25672759597066943674934771 38509139395600415512402157)
              ·
                refine ⟨14440927273350155817150809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38509139395600415512402157 14440927273350155817150809)
                ·
                  refine ⟨10830695455012616862863107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14440927273350155817150809 10830695455012616862863107)
                  ·
                    refine ⟨16246043182518925294294661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10830695455012616862863107 16246043182518925294294661)
                    ·
                      refine ⟨3046133096722298492680249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16246043182518925294294661 3046133096722298492680249)
                      ·
                        rfl

theorem cell23_5932323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_5932323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932323 prefixEnd_5932323 := by exact prefixLift 5932323
  have htrace : WordTrace (prefixWord ++ tailWord_5932323) baseStart_5932323 baseEnd_5932323 := by
    simpa [prefixWord, tailWord_5932323, baseEnd_5932323] using wordTrace_append hprefix tailTrace_5932323
  have hstable : (prefixWord ++ tailWord_5932323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932323).length < 2 ^ (prefixWord ++ tailWord_5932323).sum := by decide
  have hdescent : baseEnd_5932323 < baseStart_5932323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932336 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 6]
def baseStart_5932336 : Nat := 118140960795 + 5932336 * 2 ^ 59
def prefixEnd_5932336 : Nat := 4983230072969 + 3 ^ 40 * 5932336 * 2
def baseEnd_5932336 : Nat := 3046139771970806941817689

theorem tailTrace_5932336 : CollatzResearch.WordTrace tailWord_5932336 prefixEnd_5932336 3046139771970806941817689 := by
  unfold tailWord_5932336
  simp only [CollatzResearch.WordTrace]
  refine ⟨108185034718083654585968431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144246712957444872781291241 108185034718083654585968431)
  ·
    refine ⟨162277552077125481878952647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108185034718083654585968431 162277552077125481878952647)
    ·
      refine ⟨243416328115688222818428971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162277552077125481878952647 243416328115688222818428971)
      ·
        refine ⟨365124492173532334227643457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243416328115688222818428971 365124492173532334227643457)
        ·
          refine ⟨273843369130149250670732593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365124492173532334227643457 273843369130149250670732593)
          ·
            refine ⟨205382526847611938003049445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273843369130149250670732593 205382526847611938003049445)
            ·
              refine ⟨38509223783927238375571771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 205382526847611938003049445 38509223783927238375571771)
              ·
                refine ⟨57763835675890857563357657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38509223783927238375571771 57763835675890857563357657)
                ·
                  refine ⟨43322876756918143172518243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57763835675890857563357657 43322876756918143172518243)
                  ·
                    refine ⟨64984315135377214758777365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43322876756918143172518243 64984315135377214758777365)
                    ·
                      refine ⟨3046139771970806941817689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64984315135377214758777365 3046139771970806941817689)
                      ·
                        rfl

theorem cell23_5932336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 6].length) (baseStart_5932336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932336 prefixEnd_5932336 := by exact prefixLift 5932336
  have htrace : WordTrace (prefixWord ++ tailWord_5932336) baseStart_5932336 baseEnd_5932336 := by
    simpa [prefixWord, tailWord_5932336, baseEnd_5932336] using wordTrace_append hprefix tailTrace_5932336
  have hstable : (prefixWord ++ tailWord_5932336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932336).length < 2 ^ (prefixWord ++ tailWord_5932336).sum := by decide
  have hdescent : baseEnd_5932336 < baseStart_5932336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932340 : List Nat := [2, 5, 1, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_5932340 : Nat := 118140960795 + 5932340 * 2 ^ 59
def prefixEnd_5932340 : Nat := 4983230072969 + 3 ^ 40 * 5932340 * 2
def baseEnd_5932340 : Nat := 3046141825893424926167671

theorem tailTrace_5932340 : CollatzResearch.WordTrace tailWord_5932340 prefixEnd_5932340 3046141825893424926167671 := by
  unfold tailWord_5932340
  simp only [CollatzResearch.WordTrace]
  refine ⟨108185107664076408927541237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144246810218768545236721649 108185107664076408927541237)
  ·
    refine ⟨10142353843507163336956991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108185107664076408927541237 10142353843507163336956991)
    ·
      refine ⟨15213530765260745005435487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10142353843507163336956991 15213530765260745005435487)
      ·
        refine ⟨22820296147891117508153231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15213530765260745005435487 22820296147891117508153231)
        ·
          refine ⟨34230444221836676262229847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22820296147891117508153231 34230444221836676262229847)
          ·
            refine ⟨51345666332755014393344771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34230444221836676262229847 51345666332755014393344771)
            ·
              refine ⟨77018499499132521590017157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51345666332755014393344771 77018499499132521590017157)
              ·
                refine ⟨14440968656087347798128217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77018499499132521590017157 14440968656087347798128217)
                ·
                  refine ⟨10830726492065510848596163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14440968656087347798128217 10830726492065510848596163)
                  ·
                    refine ⟨16246089738098266272894245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10830726492065510848596163 16246089738098266272894245)
                    ·
                      refine ⟨3046141825893424926167671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16246089738098266272894245 3046141825893424926167671)
                      ·
                        rfl

theorem cell23_5932340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_5932340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932340 prefixEnd_5932340 := by exact prefixLift 5932340
  have htrace : WordTrace (prefixWord ++ tailWord_5932340) baseStart_5932340 baseEnd_5932340 := by
    simpa [prefixWord, tailWord_5932340, baseEnd_5932340] using wordTrace_append hprefix tailTrace_5932340
  have hstable : (prefixWord ++ tailWord_5932340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932340).length < 2 ^ (prefixWord ++ tailWord_5932340).sum := by decide
  have hdescent : baseEnd_5932340 < baseStart_5932340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932350 : List Nat := [4, 2, 1, 2, 1, 1, 2, 3, 3, 4]
def baseStart_5932350 : Nat := 118140960795 + 5932350 * 2 ^ 59
def prefixEnd_5932350 : Nat := 4983230072969 + 3 ^ 40 * 5932350 * 2
def baseEnd_5932350 : Nat := 1015382320233323295680875

theorem tailTrace_5932350 : CollatzResearch.WordTrace tailWord_5932350 prefixEnd_5932350 1015382320233323295680875 := by
  unfold tailWord_5932350
  simp only [CollatzResearch.WordTrace]
  refine ⟨27046322507264573695368313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144247053372077726375297669 27046322507264573695368313)
  ·
    refine ⟨20284741880448430271526235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27046322507264573695368313 20284741880448430271526235)
    ·
      refine ⟨30427112820672645407289353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20284741880448430271526235 30427112820672645407289353)
      ·
        refine ⟨22820334615504484055467015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30427112820672645407289353 22820334615504484055467015)
        ·
          refine ⟨34230501923256726083200523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22820334615504484055467015 34230501923256726083200523)
          ·
            refine ⟨51345752884885089124800785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34230501923256726083200523 51345752884885089124800785)
            ·
              refine ⟨38509314663663816843600589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51345752884885089124800785 38509314663663816843600589)
              ·
                refine ⟨14440992998873931316350221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38509314663663816843600589 14440992998873931316350221)
                ·
                  refine ⟨5415372374577724243631333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14440992998873931316350221 5415372374577724243631333)
                  ·
                    refine ⟨1015382320233323295680875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5415372374577724243631333 1015382320233323295680875)
                    ·
                      rfl

theorem cell23_5932350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_5932350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932350 prefixEnd_5932350 := by exact prefixLift 5932350
  have htrace : WordTrace (prefixWord ++ tailWord_5932350) baseStart_5932350 baseEnd_5932350 := by
    simpa [prefixWord, tailWord_5932350, baseEnd_5932350] using wordTrace_append hprefix tailTrace_5932350
  have hstable : (prefixWord ++ tailWord_5932350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932350).length < 2 ^ (prefixWord ++ tailWord_5932350).sum := by decide
  have hdescent : baseEnd_5932350 < baseStart_5932350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932400 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 4, 3, 2]
def baseStart_5932400 : Nat := 118140960795 + 5932400 * 2 ^ 59
def prefixEnd_5932400 : Nat := 4983230072969 + 3 ^ 40 * 5932400 * 2
def baseEnd_5932400 : Nat := 3046172634732694691417395

theorem tailTrace_5932400 : CollatzResearch.WordTrace tailWord_5932400 prefixEnd_5932400 3046172634732694691417395 := by
  unfold tailWord_5932400
  simp only [CollatzResearch.WordTrace]
  refine ⟨108186201853967724051133327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144248269138623632068177769 108186201853967724051133327)
  ·
    refine ⟨162279302780951586076699991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108186201853967724051133327 162279302780951586076699991)
    ·
      refine ⟨243418954171427379115049987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162279302780951586076699991 243418954171427379115049987)
      ·
        refine ⟨365128431257141068672574981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243418954171427379115049987 365128431257141068672574981)
        ·
          refine ⟨68461580860713950376107809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 365128431257141068672574981 68461580860713950376107809)
          ·
            refine ⟨51346185645535462782080857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68461580860713950376107809 51346185645535462782080857)
            ·
              refine ⟨38509639234151597086560643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51346185645535462782080857 38509639234151597086560643)
              ·
                refine ⟨57764458851227395629840965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38509639234151597086560643 57764458851227395629840965)
                ·
                  refine ⟨10830836034605136680595181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57764458851227395629840965 10830836034605136680595181)
                  ·
                    refine ⟨4061563512976926255223193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10830836034605136680595181 4061563512976926255223193)
                    ·
                      refine ⟨3046172634732694691417395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4061563512976926255223193 3046172634732694691417395)
                      ·
                        rfl

theorem cell23_5932400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 4, 3, 2].length) (baseStart_5932400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932400 prefixEnd_5932400 := by exact prefixLift 5932400
  have htrace : WordTrace (prefixWord ++ tailWord_5932400) baseStart_5932400 baseEnd_5932400 := by
    simpa [prefixWord, tailWord_5932400, baseEnd_5932400] using wordTrace_append hprefix tailTrace_5932400
  have hstable : (prefixWord ++ tailWord_5932400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932400).length < 2 ^ (prefixWord ++ tailWord_5932400).sum := by decide
  have hdescent : baseEnd_5932400 < baseStart_5932400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932407 : List Nat := [1, 1, 3, 1, 1, 2, 3, 6, 1, 1, 3]
def baseStart_5932407 : Nat := 118140960795 + 5932407 * 2 ^ 59
def prefixEnd_5932407 : Nat := 4983230072969 + 3 ^ 40 * 5932407 * 2
def baseEnd_5932407 : Nat := 3046176229097276164029863

theorem tailTrace_5932407 : CollatzResearch.WordTrace tailWord_5932407 prefixEnd_5932407 3046176229097276164029863 := by
  unfold tailWord_5932407
  simp only [CollatzResearch.WordTrace]
  refine ⟨216372659018910088297771475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144248439345940058865180983 216372659018910088297771475)
  ·
    refine ⟨324558988528365132446657213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216372659018910088297771475 324558988528365132446657213)
    ·
      refine ⟨121709620698136924667496455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324558988528365132446657213 121709620698136924667496455)
      ·
        refine ⟨182564431047205387001244683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121709620698136924667496455 182564431047205387001244683)
        ·
          refine ⟨273846646570808080501867025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182564431047205387001244683 273846646570808080501867025)
          ·
            refine ⟨205384984928106060376400269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273846646570808080501867025 205384984928106060376400269)
            ·
              refine ⟨77019369348039772641150101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 205384984928106060376400269 77019369348039772641150101)
              ·
                refine ⟨3610282938189364342553911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77019369348039772641150101 3610282938189364342553911)
                ·
                  refine ⟨5415424407284046513830867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3610282938189364342553911 5415424407284046513830867)
                  ·
                    refine ⟨8123136610926069770746301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5415424407284046513830867 8123136610926069770746301)
                    ·
                      refine ⟨3046176229097276164029863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8123136610926069770746301 3046176229097276164029863)
                      ·
                        rfl

theorem cell23_5932407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6, 1, 1, 3].length) (baseStart_5932407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932407 prefixEnd_5932407 := by exact prefixLift 5932407
  have htrace : WordTrace (prefixWord ++ tailWord_5932407) baseStart_5932407 baseEnd_5932407 := by
    simpa [prefixWord, tailWord_5932407, baseEnd_5932407] using wordTrace_append hprefix tailTrace_5932407
  have hstable : (prefixWord ++ tailWord_5932407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932407).length < 2 ^ (prefixWord ++ tailWord_5932407).sum := by decide
  have hdescent : baseEnd_5932407 < baseStart_5932407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932450 : List Nat := [3, 3, 1, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_5932450 : Nat := 118140960795 + 5932450 * 2 ^ 59
def prefixEnd_5932450 : Nat := 4983230072969 + 3 ^ 40 * 5932450 * 2
def baseEnd_5932450 : Nat := 3046198308765419495792165

theorem tailTrace_5932450 : CollatzResearch.WordTrace tailWord_5932450 prefixEnd_5932450 3046198308765419495792165 := by
  unfold tailWord_5932450
  simp only [CollatzResearch.WordTrace]
  refine ⟨54093556839438576660396701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144249484905169537761057869 54093556839438576660396701)
  ·
    refine ⟨20285083814789466247648763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54093556839438576660396701 20285083814789466247648763)
    ·
      refine ⟨30427625722184199371473145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20285083814789466247648763 30427625722184199371473145)
      ·
        refine ⟨22820719291638149528604859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30427625722184199371473145 22820719291638149528604859)
        ·
          refine ⟨34231078937457224292907289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22820719291638149528604859 34231078937457224292907289)
          ·
            refine ⟨25673309203092918219680467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34231078937457224292907289 25673309203092918219680467)
            ·
              refine ⟨38509963804639377329520701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25673309203092918219680467 38509963804639377329520701)
              ·
                refine ⟨14441236426739766498570263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38509963804639377329520701 14441236426739766498570263)
                ·
                  refine ⟨21661854640109649747855395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14441236426739766498570263 21661854640109649747855395)
                  ·
                    refine ⟨32492781960164474621783093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21661854640109649747855395 32492781960164474621783093)
                    ·
                      refine ⟨3046198308765419495792165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32492781960164474621783093 3046198308765419495792165)
                      ·
                        rfl

theorem cell23_5932450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_5932450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932450 prefixEnd_5932450 := by exact prefixLift 5932450
  have htrace : WordTrace (prefixWord ++ tailWord_5932450) baseStart_5932450 baseEnd_5932450 := by
    simpa [prefixWord, tailWord_5932450, baseEnd_5932450] using wordTrace_append hprefix tailTrace_5932450
  have hstable : (prefixWord ++ tailWord_5932450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932450).length < 2 ^ (prefixWord ++ tailWord_5932450).sum := by decide
  have hdescent : baseEnd_5932450 < baseStart_5932450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932484 : List Nat := [2, 3, 3, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_5932484 : Nat := 118140960795 + 5932484 * 2 ^ 59
def prefixEnd_5932484 : Nat := 4983230072969 + 3 ^ 40 * 5932484 * 2
def baseEnd_5932484 : Nat := 3046215767107672362767009

theorem tailTrace_5932484 : CollatzResearch.WordTrace tailWord_5932484 prefixEnd_5932484 3046215767107672362767009 := by
  unfold tailWord_5932484
  simp only [CollatzResearch.WordTrace]
  refine ⟨108187733719815565224162253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144250311626420753632216337 108187733719815565224162253)
  ·
    refine ⟨40570400144930836959060845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108187733719815565224162253 40570400144930836959060845)
    ·
      refine ⟨15213900054349063859647817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40570400144930836959060845 15213900054349063859647817)
      ·
        refine ⟨11410425040761797894735863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15213900054349063859647817 11410425040761797894735863)
        ·
          refine ⟨17115637561142696842103795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11410425040761797894735863 17115637561142696842103795)
          ·
            refine ⟨25673456341714045263155693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17115637561142696842103795 25673456341714045263155693)
            ·
              refine ⟨9627546128142766973683385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25673456341714045263155693 9627546128142766973683385)
              ·
                refine ⟨7220659596107075230262539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9627546128142766973683385 7220659596107075230262539)
                ·
                  refine ⟨10830989394160612845393809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7220659596107075230262539 10830989394160612845393809)
                  ·
                    refine ⟨8123242045620459634045357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10830989394160612845393809 8123242045620459634045357)
                    ·
                      refine ⟨3046215767107672362767009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8123242045620459634045357 3046215767107672362767009)
                      ·
                        rfl

theorem cell23_5932484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_5932484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932484 prefixEnd_5932484 := by exact prefixLift 5932484
  have htrace : WordTrace (prefixWord ++ tailWord_5932484) baseStart_5932484 baseEnd_5932484 := by
    simpa [prefixWord, tailWord_5932484, baseEnd_5932484] using wordTrace_append hprefix tailTrace_5932484
  have hstable : (prefixWord ++ tailWord_5932484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932484).length < 2 ^ (prefixWord ++ tailWord_5932484).sum := by decide
  have hdescent : baseEnd_5932484 < baseStart_5932484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932503 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 4]
def baseStart_5932503 : Nat := 118140960795 + 5932503 * 2 ^ 59
def prefixEnd_5932503 : Nat := 4983230072969 + 3 ^ 40 * 5932503 * 2
def baseEnd_5932503 : Nat := 3046225523240107788429421

theorem tailTrace_5932503 : CollatzResearch.WordTrace tailWord_5932503 prefixEnd_5932503 3046225523240107788429421 := by
  unfold tailWord_5932503
  simp only [CollatzResearch.WordTrace]
  refine ⟨216376160426562296693266163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144250773617708197795510775 216376160426562296693266163)
  ·
    refine ⟨324564240639843445039899245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216376160426562296693266163 324564240639843445039899245)
    ·
      refine ⟨121711590239941291889962217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324564240639843445039899245 121711590239941291889962217)
      ·
        refine ⟨91283692679955968917471663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121711590239941291889962217 91283692679955968917471663)
        ·
          refine ⟨136925539019933953376207495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91283692679955968917471663 136925539019933953376207495)
          ·
            refine ⟨205388308529900930064311243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136925539019933953376207495 205388308529900930064311243)
            ·
              refine ⟨308082462794851395096466865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205388308529900930064311243 308082462794851395096466865)
              ·
                refine ⟨231061847096138546322350149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308082462794851395096466865 231061847096138546322350149)
                ·
                  refine ⟨43324096330525977435440653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 231061847096138546322350149 43324096330525977435440653)
                  ·
                    refine ⟨16246536123947241538290245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43324096330525977435440653 16246536123947241538290245)
                    ·
                      refine ⟨3046225523240107788429421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16246536123947241538290245 3046225523240107788429421)
                      ·
                        rfl

theorem cell23_5932503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_5932503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932503 prefixEnd_5932503 := by exact prefixLift 5932503
  have htrace : WordTrace (prefixWord ++ tailWord_5932503) baseStart_5932503 baseEnd_5932503 := by
    simpa [prefixWord, tailWord_5932503, baseEnd_5932503] using wordTrace_append hprefix tailTrace_5932503
  have hstable : (prefixWord ++ tailWord_5932503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932503).length < 2 ^ (prefixWord ++ tailWord_5932503).sum := by decide
  have hdescent : baseEnd_5932503 < baseStart_5932503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932523 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 5]
def baseStart_5932523 : Nat := 118140960795 + 5932523 * 2 ^ 59
def prefixEnd_5932523 : Nat := 4983230072969 + 3 ^ 40 * 5932523 * 2
def baseEnd_5932523 : Nat := 3046235792853197710179329

theorem tailTrace_5932523 : CollatzResearch.WordTrace tailWord_5932523 prefixEnd_5932523 3046235792853197710179329 := by
  unfold tailWord_5932523
  simp only [CollatzResearch.WordTrace]
  refine ⟨216376889886489840108994223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144251259924326560072662815 216376889886489840108994223)
  ·
    refine ⟨324565334829734760163491335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216376889886489840108994223 324565334829734760163491335)
    ·
      refine ⟨486848002244602140245237003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324565334829734760163491335 486848002244602140245237003)
      ·
        refine ⟨730272003366903210367855505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486848002244602140245237003 730272003366903210367855505)
        ·
          refine ⟨547704002525177407775891629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 730272003366903210367855505 547704002525177407775891629)
          ·
            refine ⟨205389000946941527915959361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 547704002525177407775891629 205389000946941527915959361)
            ·
              refine ⟨154041750710206145936969521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205389000946941527915959361 154041750710206145936969521)
              ·
                refine ⟨115531313032654609452727141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154041750710206145936969521 115531313032654609452727141)
                ·
                  refine ⟨21662121193622739272386339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115531313032654609452727141 21662121193622739272386339)
                  ·
                    refine ⟨32493181790434108908579509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21662121193622739272386339 32493181790434108908579509)
                    ·
                      refine ⟨3046235792853197710179329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32493181790434108908579509 3046235792853197710179329)
                      ·
                        rfl

theorem cell23_5932523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 5].length) (baseStart_5932523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932523 prefixEnd_5932523 := by exact prefixLift 5932523
  have htrace : WordTrace (prefixWord ++ tailWord_5932523) baseStart_5932523 baseEnd_5932523 := by
    simpa [prefixWord, tailWord_5932523, baseEnd_5932523] using wordTrace_append hprefix tailTrace_5932523
  have hstable : (prefixWord ++ tailWord_5932523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932523).length < 2 ^ (prefixWord ++ tailWord_5932523).sum := by decide
  have hdescent : baseEnd_5932523 < baseStart_5932523 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932530 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 1, 8]
def baseStart_5932530 : Nat := 118140960795 + 5932530 * 2 ^ 59
def prefixEnd_5932530 : Nat := 4983230072969 + 3 ^ 40 * 5932530 * 2
def baseEnd_5932530 : Nat := 1015413129072593060930599

theorem tailTrace_5932530 : CollatzResearch.WordTrace tailWord_5932530 prefixEnd_5932530 1015413129072593060930599 := by
  unfold tailWord_5932530
  simp only [CollatzResearch.WordTrace]
  refine ⟨54094286299366120076124761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144251430131642986869666029 54094286299366120076124761)
  ·
    refine ⟨40570714724524590057093571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54094286299366120076124761 40570714724524590057093571)
    ·
      refine ⟨60856072086786885085640357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40570714724524590057093571 60856072086786885085640357)
      ·
        refine ⟨11410513516272540953557567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60856072086786885085640357 11410513516272540953557567)
        ·
          refine ⟨17115770274408811430336351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11410513516272540953557567 17115770274408811430336351)
          ·
            refine ⟨25673655411613217145504527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17115770274408811430336351 25673655411613217145504527)
            ·
              refine ⟨38510483117419825718256791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25673655411613217145504527 38510483117419825718256791)
              ·
                refine ⟨57765724676129738577385187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38510483117419825718256791 57765724676129738577385187)
                ·
                  refine ⟨86648587014194607866077781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57765724676129738577385187 86648587014194607866077781)
                  ·
                    refine ⟨1015413129072593060930599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 86648587014194607866077781 1015413129072593060930599)
                    ·
                      rfl

theorem cell23_5932530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_5932530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932530 prefixEnd_5932530 := by exact prefixLift 5932530
  have htrace : WordTrace (prefixWord ++ tailWord_5932530) baseStart_5932530 baseEnd_5932530 := by
    simpa [prefixWord, tailWord_5932530, baseEnd_5932530] using wordTrace_append hprefix tailTrace_5932530
  have hstable : (prefixWord ++ tailWord_5932530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932530).length < 2 ^ (prefixWord ++ tailWord_5932530).sum := by decide
  have hdescent : baseEnd_5932530 < baseStart_5932530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932537 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 6, 2, 2]
def baseStart_5932537 : Nat := 118140960795 + 5932537 * 2 ^ 59
def prefixEnd_5932537 : Nat := 4983230072969 + 3 ^ 40 * 5932537 * 2
def baseEnd_5932537 : Nat := 3046242981582360655404265

theorem tailTrace_5932537 : CollatzResearch.WordTrace tailWord_5932537 prefixEnd_5932537 3046242981582360655404265 := by
  unfold tailWord_5932537
  simp only [CollatzResearch.WordTrace]
  refine ⟨216377400508439120500003865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144251600338959413666669243 216377400508439120500003865)
  ·
    refine ⟨162283050381329340375002899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216377400508439120500003865 162283050381329340375002899)
    ·
      refine ⟨243424575571994010562504349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162283050381329340375002899 243424575571994010562504349)
      ·
        refine ⟨91284215839497753960939131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243424575571994010562504349 91284215839497753960939131)
        ·
          refine ⟨136926323759246630941408697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91284215839497753960939131 136926323759246630941408697)
          ·
            refine ⟨102694742819434973206056523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136926323759246630941408697 102694742819434973206056523)
            ·
              refine ⟨154042114229152459809084785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102694742819434973206056523 154042114229152459809084785)
              ·
                refine ⟨115531585671864344856813589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154042114229152459809084785 115531585671864344856813589)
                ·
                  refine ⟨5415543078368641165163137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 115531585671864344856813589 5415543078368641165163137)
                  ·
                    refine ⟨4061657308776480873872353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5415543078368641165163137 4061657308776480873872353)
                    ·
                      refine ⟨3046242981582360655404265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4061657308776480873872353 3046242981582360655404265)
                      ·
                        rfl

theorem cell23_5932537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6, 2, 2].length) (baseStart_5932537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932537 prefixEnd_5932537 := by exact prefixLift 5932537
  have htrace : WordTrace (prefixWord ++ tailWord_5932537) baseStart_5932537 baseEnd_5932537 := by
    simpa [prefixWord, tailWord_5932537, baseEnd_5932537] using wordTrace_append hprefix tailTrace_5932537
  have hstable : (prefixWord ++ tailWord_5932537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932537).length < 2 ^ (prefixWord ++ tailWord_5932537).sum := by decide
  have hdescent : baseEnd_5932537 < baseStart_5932537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932558 : List Nat := [4, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2]
def baseStart_5932558 : Nat := 118140960795 + 5932558 * 2 ^ 59
def prefixEnd_5932558 : Nat := 4983230072969 + 3 ^ 40 * 5932558 * 2
def baseEnd_5932558 : Nat := 3046253764676105073241669

theorem tailTrace_5932558 : CollatzResearch.WordTrace tailWord_5932558 prefixEnd_5932558 3046253764676105073241669 := by
  unfold tailWord_5932558
  simp only [CollatzResearch.WordTrace]
  refine ⟨27047270805170380135814791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144252110960908694057678885 27047270805170380135814791)
  ·
    refine ⟨40570906207755570203722187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27047270805170380135814791 40570906207755570203722187)
    ·
      refine ⟨60856359311633355305583281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40570906207755570203722187 60856359311633355305583281)
      ·
        refine ⟨45642269483725016479187461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60856359311633355305583281 45642269483725016479187461)
        ·
          refine ⟨8557925528198440589847649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45642269483725016479187461 8557925528198440589847649)
          ·
            refine ⟨6418444146148830442385737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8557925528198440589847649 6418444146148830442385737)
            ·
              refine ⟨4813833109611622831789303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6418444146148830442385737 4813833109611622831789303)
              ·
                refine ⟨7220749664417434247683955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4813833109611622831789303 7220749664417434247683955)
                ·
                  refine ⟨10831124496626151371525933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7220749664417434247683955 10831124496626151371525933)
                  ·
                    refine ⟨4061671686234806764322225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10831124496626151371525933 4061671686234806764322225)
                    ·
                      refine ⟨3046253764676105073241669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4061671686234806764322225 3046253764676105073241669)
                      ·
                        rfl

theorem cell23_5932558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_5932558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932558 prefixEnd_5932558 := by exact prefixLift 5932558
  have htrace : WordTrace (prefixWord ++ tailWord_5932558) baseStart_5932558 baseEnd_5932558 := by
    simpa [prefixWord, tailWord_5932558, baseEnd_5932558] using wordTrace_append hprefix tailTrace_5932558
  have hstable : (prefixWord ++ tailWord_5932558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932558).length < 2 ^ (prefixWord ++ tailWord_5932558).sum := by decide
  have hdescent : baseEnd_5932558 < baseStart_5932558 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932577 : List Nat := [1, 2, 3, 2, 2, 2, 2, 4, 5]
def baseStart_5932577 : Nat := 118140960795 + 5932577 * 2 ^ 59
def prefixEnd_5932577 : Nat := 4983230072969 + 3 ^ 40 * 5932577 * 2
def baseEnd_5932577 : Nat := 338473724534282277656009

theorem tailTrace_5932577 : CollatzResearch.WordTrace tailWord_5932577 prefixEnd_5932577 338473724534282277656009 := by
  unfold tailWord_5932577
  simp only [CollatzResearch.WordTrace]
  refine ⟨216378859428294207331459985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144252572952196138220973323 216378859428294207331459985)
  ·
    refine ⟨162284144571220655498594989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216378859428294207331459985 162284144571220655498594989)
    ·
      refine ⟨60856554214207745811973121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162284144571220655498594989 60856554214207745811973121)
      ·
        refine ⟨45642415660655809358979841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60856554214207745811973121 45642415660655809358979841)
        ·
          refine ⟨34231811745491857019234881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45642415660655809358979841 34231811745491857019234881)
          ·
            refine ⟨25673858809118892764426161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34231811745491857019234881 25673858809118892764426161)
            ·
              refine ⟨19255394106839169573319621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25673858809118892764426161 19255394106839169573319621)
              ·
                refine ⟨3610386395032344294997429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19255394106839169573319621 3610386395032344294997429)
                ·
                  refine ⟨338473724534282277656009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3610386395032344294997429 338473724534282277656009)
                  ·
                    rfl

theorem cell23_5932577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4, 5].length) (baseStart_5932577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932577 prefixEnd_5932577 := by exact prefixLift 5932577
  have htrace : WordTrace (prefixWord ++ tailWord_5932577) baseStart_5932577 baseEnd_5932577 := by
    simpa [prefixWord, tailWord_5932577, baseEnd_5932577] using wordTrace_append hprefix tailTrace_5932577
  have hstable : (prefixWord ++ tailWord_5932577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932577).length < 2 ^ (prefixWord ++ tailWord_5932577).sum := by decide
  have hdescent : baseEnd_5932577 < baseStart_5932577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932727 : List Nat := [1, 1, 3, 1, 5, 1, 2, 2, 1, 6]
def baseStart_5932727 : Nat := 118140960795 + 5932727 * 2 ^ 59
def prefixEnd_5932727 : Nat := 4983230072969 + 3 ^ 40 * 5932727 * 2
def baseEnd_5932727 : Nat := 1015446847635571637342797

theorem tailTrace_5932727 : CollatzResearch.WordTrace tailWord_5932727 prefixEnd_5932727 1015446847635571637342797 := by
  unfold tailWord_5932727
  simp only [CollatzResearch.WordTrace]
  refine ⟨216384330377750782949420435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144256220251833855299613623 216384330377750782949420435)
  ·
    refine ⟨324576495566626174424130653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216384330377750782949420435 324576495566626174424130653)
    ·
      refine ⟨121716185837484815409048995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324576495566626174424130653 121716185837484815409048995)
      ·
        refine ⟨182574278756227223113573493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121716185837484815409048995 182574278756227223113573493)
        ·
          refine ⟨17116338633396302166897515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 182574278756227223113573493 17116338633396302166897515)
          ·
            refine ⟨25674507950094453250346273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17116338633396302166897515 25674507950094453250346273)
            ·
              refine ⟨19255880962570839937759705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25674507950094453250346273 19255880962570839937759705)
              ·
                refine ⟨14441910721928129953319779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19255880962570839937759705 14441910721928129953319779)
                ·
                  refine ⟨21662866082892194929979669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14441910721928129953319779 21662866082892194929979669)
                  ·
                    refine ⟨1015446847635571637342797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21662866082892194929979669 1015446847635571637342797)
                    ·
                      rfl

theorem cell23_5932727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 6].length) (baseStart_5932727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932727 prefixEnd_5932727 := by exact prefixLift 5932727
  have htrace : WordTrace (prefixWord ++ tailWord_5932727) baseStart_5932727 baseEnd_5932727 := by
    simpa [prefixWord, tailWord_5932727, baseEnd_5932727] using wordTrace_append hprefix tailTrace_5932727
  have hstable : (prefixWord ++ tailWord_5932727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932727).length < 2 ^ (prefixWord ++ tailWord_5932727).sum := by decide
  have hdescent : baseEnd_5932727 < baseStart_5932727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932754 : List Nat := [3, 2, 2, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_5932754 : Nat := 118140960795 + 5932754 * 2 ^ 59
def prefixEnd_5932754 : Nat := 4983230072969 + 3 ^ 40 * 5932754 * 2
def baseEnd_5932754 : Nat := 3046354406884386306390767

theorem tailTrace_5932754 : CollatzResearch.WordTrace tailWord_5932754 prefixEnd_5932754 3046354406884386306390767 := by
  unfold tailWord_5932754
  simp only [CollatzResearch.WordTrace]
  refine ⟨54096328787163241640163329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144256876765768644373768877 54096328787163241640163329)
  ·
    refine ⟨40572246590372431230122497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54096328787163241640163329 40572246590372431230122497)
    ·
      refine ⟨30429184942779323422591873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40572246590372431230122497 30429184942779323422591873)
      ·
        refine ⟨22821888707084492566943905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30429184942779323422591873 22821888707084492566943905)
        ·
          refine ⟨17116416530313369425207929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22821888707084492566943905 17116416530313369425207929)
          ·
            refine ⟨12837312397735027068905947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17116416530313369425207929 12837312397735027068905947)
            ·
              refine ⟨19255968596602540603358921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12837312397735027068905947 19255968596602540603358921)
              ·
                refine ⟨14441976447451905452519191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19255968596602540603358921 14441976447451905452519191)
                ·
                  refine ⟨21662964671177858178778787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14441976447451905452519191 21662964671177858178778787)
                  ·
                    refine ⟨32494447006766787268168181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21662964671177858178778787 32494447006766787268168181)
                    ·
                      refine ⟨3046354406884386306390767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32494447006766787268168181 3046354406884386306390767)
                      ·
                        rfl

theorem cell23_5932754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_5932754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932754 prefixEnd_5932754 := by exact prefixLift 5932754
  have htrace : WordTrace (prefixWord ++ tailWord_5932754) baseStart_5932754 baseEnd_5932754 := by
    simpa [prefixWord, tailWord_5932754, baseEnd_5932754] using wordTrace_append hprefix tailTrace_5932754
  have hstable : (prefixWord ++ tailWord_5932754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932754).length < 2 ^ (prefixWord ++ tailWord_5932754).sum := by decide
  have hdescent : baseEnd_5932754 < baseStart_5932754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932761 : List Nat := [1, 2, 1, 2, 3, 4, 3, 1, 2, 4]
def baseStart_5932761 : Nat := 118140960795 + 5932761 * 2 ^ 59
def prefixEnd_5932761 : Nat := 4983230072969 + 3 ^ 40 * 5932761 * 2
def baseEnd_5932761 : Nat := 1015452667082989259667745

theorem tailTrace_5932761 : CollatzResearch.WordTrace tailWord_5932761 prefixEnd_5932761 1015452667082989259667745 := by
  unfold tailWord_5932761
  simp only [CollatzResearch.WordTrace]
  refine ⟨216385570459627606756158137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144257046973085071170772091 216385570459627606756158137)
  ·
    refine ⟨162289177844720705067118603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216385570459627606756158137 162289177844720705067118603)
    ·
      refine ⟨243433766767081057600677905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162289177844720705067118603 243433766767081057600677905)
      ·
        refine ⟨182575325075310793200508429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243433766767081057600677905 182575325075310793200508429)
        ·
          refine ⟨68465746903241547450190661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182575325075310793200508429 68465746903241547450190661)
          ·
            refine ⟨12837327544357790146910749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68465746903241547450190661 12837327544357790146910749)
            ·
              refine ⟨4813997829134171305091531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12837327544357790146910749 4813997829134171305091531)
              ·
                refine ⟨7220996743701256957637297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4813997829134171305091531 7220996743701256957637297)
                ·
                  refine ⟨5415747557775942718227973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7220996743701256957637297 5415747557775942718227973)
                  ·
                    refine ⟨1015452667082989259667745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5415747557775942718227973 1015452667082989259667745)
                    ·
                      rfl

theorem cell23_5932761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 2, 4].length) (baseStart_5932761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932761 prefixEnd_5932761 := by exact prefixLift 5932761
  have htrace : WordTrace (prefixWord ++ tailWord_5932761) baseStart_5932761 baseEnd_5932761 := by
    simpa [prefixWord, tailWord_5932761, baseEnd_5932761] using wordTrace_append hprefix tailTrace_5932761
  have hstable : (prefixWord ++ tailWord_5932761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932761).length < 2 ^ (prefixWord ++ tailWord_5932761).sum := by decide
  have hdescent : baseEnd_5932761 < baseStart_5932761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932785 : List Nat := [1, 2, 2, 2, 2, 5, 1, 3, 1, 2, 2]
def baseStart_5932785 : Nat := 118140960795 + 5932785 * 2 ^ 59
def prefixEnd_5932785 : Nat := 4983230072969 + 3 ^ 40 * 5932785 * 2
def baseEnd_5932785 : Nat := 3046370324784675685103125

theorem tailTrace_5932785 : CollatzResearch.WordTrace tailWord_5932785 prefixEnd_5932785 3046370324784675685103125 := by
  unfold tailWord_5932785
  simp only [CollatzResearch.WordTrace]
  refine ⟨216386445811540658855031809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144257630541027105903354539 216386445811540658855031809)
  ·
    refine ⟨162289834358655494141273857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216386445811540658855031809 162289834358655494141273857)
    ·
      refine ⟨121717375768991620605955393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162289834358655494141273857 121717375768991620605955393)
      ·
        refine ⟨91288031826743715454466545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121717375768991620605955393 91288031826743715454466545)
        ·
          refine ⟨68466023870057786590849909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91288031826743715454466545 68466023870057786590849909)
          ·
            refine ⟨6418689737817917492892179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68466023870057786590849909 6418689737817917492892179)
            ·
              refine ⟨9628034606726876239338269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6418689737817917492892179 9628034606726876239338269)
              ·
                refine ⟨3610512977522578589751851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9628034606726876239338269 3610512977522578589751851)
                ·
                  refine ⟨5415769466283867884627777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3610512977522578589751851 5415769466283867884627777)
                  ·
                    refine ⟨4061827099712900913470833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5415769466283867884627777 4061827099712900913470833)
                    ·
                      refine ⟨3046370324784675685103125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4061827099712900913470833 3046370324784675685103125)
                      ·
                        rfl

theorem cell23_5932785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3, 1, 2, 2].length) (baseStart_5932785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932785 prefixEnd_5932785 := by exact prefixLift 5932785
  have htrace : WordTrace (prefixWord ++ tailWord_5932785) baseStart_5932785 baseEnd_5932785 := by
    simpa [prefixWord, tailWord_5932785, baseEnd_5932785] using wordTrace_append hprefix tailTrace_5932785
  have hstable : (prefixWord ++ tailWord_5932785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932785).length < 2 ^ (prefixWord ++ tailWord_5932785).sum := by decide
  have hdescent : baseEnd_5932785 < baseStart_5932785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932788 : List Nat := [2, 6, 1, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_5932788 : Nat := 118140960795 + 5932788 * 2 ^ 59
def prefixEnd_5932788 : Nat := 4983230072969 + 3 ^ 40 * 5932788 * 2
def baseEnd_5932788 : Nat := 3046371865226639173365611

theorem tailTrace_5932788 : CollatzResearch.WordTrace tailWord_5932788 prefixEnd_5932788 3046371865226639173365611 := by
  unfold tailWord_5932788
  simp only [CollatzResearch.WordTrace]
  refine ⟨108193277615264895183695509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144257703487019860244927345 108193277615264895183695509)
  ·
    refine ⟨5071559888215541961735727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 108193277615264895183695509 5071559888215541961735727)
    ·
      refine ⟨7607339832323312942603591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5071559888215541961735727 7607339832323312942603591)
      ·
        refine ⟨11411009748484969413905387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7607339832323312942603591 11411009748484969413905387)
        ·
          refine ⟨17116514622727454120858081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11411009748484969413905387 17116514622727454120858081)
          ·
            refine ⟨12837385967045590590643561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17116514622727454120858081 12837385967045590590643561)
            ·
              refine ⟨9628039475284192942982671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12837385967045590590643561 9628039475284192942982671)
              ·
                refine ⟨14442059212926289414474007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9628039475284192942982671 14442059212926289414474007)
                ·
                  refine ⟨21663088819389434121711011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14442059212926289414474007 21663088819389434121711011)
                  ·
                    refine ⟨32494633229084151182566517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21663088819389434121711011 32494633229084151182566517)
                    ·
                      refine ⟨3046371865226639173365611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32494633229084151182566517 3046371865226639173365611)
                      ·
                        rfl

theorem cell23_5932788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_5932788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932788 prefixEnd_5932788 := by exact prefixLift 5932788
  have htrace : WordTrace (prefixWord ++ tailWord_5932788) baseStart_5932788 baseEnd_5932788 := by
    simpa [prefixWord, tailWord_5932788, baseEnd_5932788] using wordTrace_append hprefix tailTrace_5932788
  have hstable : (prefixWord ++ tailWord_5932788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932788).length < 2 ^ (prefixWord ++ tailWord_5932788).sum := by decide
  have hdescent : baseEnd_5932788 < baseStart_5932788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932794 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2]
def baseStart_5932794 : Nat := 118140960795 + 5932794 * 2 ^ 59
def prefixEnd_5932794 : Nat := 4983230072969 + 3 ^ 40 * 5932794 * 2
def baseEnd_5932794 : Nat := 3046374946110566149890583

theorem tailTrace_5932794 : CollatzResearch.WordTrace tailWord_5932794 prefixEnd_5932794 3046374946110566149890583 := by
  unfold tailWord_5932794
  simp only [CollatzResearch.WordTrace]
  refine ⟨54096693517127013348027359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144257849379005368928072957 54096693517127013348027359)
  ·
    refine ⟨81145040275690520022041039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54096693517127013348027359 81145040275690520022041039)
    ·
      refine ⟨121717560413535780033061559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81145040275690520022041039 121717560413535780033061559)
      ·
        refine ⟨182576340620303670049592339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121717560413535780033061559 182576340620303670049592339)
        ·
          refine ⟨273864510930455505074388509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182576340620303670049592339 273864510930455505074388509)
          ·
            refine ⟨102699191598920814402895691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273864510930455505074388509 102699191598920814402895691)
            ·
              refine ⟨154048787398381221604343537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102699191598920814402895691 154048787398381221604343537)
              ·
                refine ⟨115536590548785916203257653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154048787398381221604343537 115536590548785916203257653)
                ·
                  refine ⟨10831555363948679644055405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115536590548785916203257653 10831555363948679644055405)
                  ·
                    refine ⟨4061833261480754866520777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10831555363948679644055405 4061833261480754866520777)
                    ·
                      refine ⟨3046374946110566149890583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4061833261480754866520777 3046374946110566149890583)
                      ·
                        rfl

theorem cell23_5932794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2].length) (baseStart_5932794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932794 prefixEnd_5932794 := by exact prefixLift 5932794
  have htrace : WordTrace (prefixWord ++ tailWord_5932794) baseStart_5932794 baseEnd_5932794 := by
    simpa [prefixWord, tailWord_5932794, baseEnd_5932794] using wordTrace_append hprefix tailTrace_5932794
  have hstable : (prefixWord ++ tailWord_5932794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932794).length < 2 ^ (prefixWord ++ tailWord_5932794).sum := by decide
  have hdescent : baseEnd_5932794 < baseStart_5932794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932802 : List Nat := [3, 4, 1, 1, 1, 1, 5, 2, 1, 2, 2]
def baseStart_5932802 : Nat := 118140960795 + 5932802 * 2 ^ 59
def prefixEnd_5932802 : Nat := 4983230072969 + 3 ^ 40 * 5932802 * 2
def baseEnd_5932802 : Nat := 3046379053955802118590547

theorem tailTrace_5932802 : CollatzResearch.WordTrace tailWord_5932802 prefixEnd_5932802 3046379053955802118590547 := by
  unfold tailWord_5932802
  simp only [CollatzResearch.WordTrace]
  refine ⟨54096766463119767689600165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144258043901652713838933773 54096766463119767689600165)
  ·
    refine ⟨10143143711834956441800031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54096766463119767689600165 10143143711834956441800031)
    ·
      refine ⟨15214715567752434662700047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10143143711834956441800031 15214715567752434662700047)
      ·
        refine ⟨22822073351628651994050071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15214715567752434662700047 22822073351628651994050071)
        ·
          refine ⟨34233110027442977991075107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22822073351628651994050071 34233110027442977991075107)
          ·
            refine ⟨51349665041164466986612661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34233110027442977991075107 51349665041164466986612661)
            ·
              refine ⟨4814031097609168779994937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51349665041164466986612661 4814031097609168779994937)
              ·
                refine ⟨3610523323206876584996203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4814031097609168779994937 3610523323206876584996203)
                ·
                  refine ⟨5415784984810314877494305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3610523323206876584996203 5415784984810314877494305)
                  ·
                    refine ⟨4061838738607736158120729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5415784984810314877494305 4061838738607736158120729)
                    ·
                      refine ⟨3046379053955802118590547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4061838738607736158120729 3046379053955802118590547)
                      ·
                        rfl

theorem cell23_5932802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_5932802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932802 prefixEnd_5932802 := by exact prefixLift 5932802
  have htrace : WordTrace (prefixWord ++ tailWord_5932802) baseStart_5932802 baseEnd_5932802 := by
    simpa [prefixWord, tailWord_5932802, baseEnd_5932802] using wordTrace_append hprefix tailTrace_5932802
  have hstable : (prefixWord ++ tailWord_5932802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932802).length < 2 ^ (prefixWord ++ tailWord_5932802).sum := by decide
  have hdescent : baseEnd_5932802 < baseStart_5932802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932827 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 2, 4, 3]
def baseStart_5932827 : Nat := 118140960795 + 5932827 * 2 ^ 59
def prefixEnd_5932827 : Nat := 4983230072969 + 3 ^ 40 * 5932827 * 2
def baseEnd_5932827 : Nat := 3046391890972164520777931

theorem tailTrace_5932827 : CollatzResearch.WordTrace tailWord_5932827 prefixEnd_5932827 3046391890972164520777931 := by
  unfold tailWord_5932827
  simp only [CollatzResearch.WordTrace]
  refine ⟨216387977677388500028060735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144258651784925666685373823 216387977677388500028060735)
  ·
    refine ⟨324581966516082750042091103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216387977677388500028060735 324581966516082750042091103)
    ·
      refine ⟨486872949774124125063136655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324581966516082750042091103 486872949774124125063136655)
      ·
        refine ⟨730309424661186187594704983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486872949774124125063136655 730309424661186187594704983)
        ·
          refine ⟨1095464136991779281392057475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730309424661186187594704983 1095464136991779281392057475)
          ·
            refine ⟨1643196205487668922088086213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1095464136991779281392057475 1643196205487668922088086213)
            ·
              refine ⟨308099288528937922891516165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1643196205487668922088086213 308099288528937922891516165)
              ·
                refine ⟨57768616599175860542159281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 308099288528937922891516165 57768616599175860542159281)
                ·
                  refine ⟨43326462449381895406619461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57768616599175860542159281 43326462449381895406619461)
                  ·
                    refine ⟨8123711709259105388741149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43326462449381895406619461 8123711709259105388741149)
                    ·
                      refine ⟨3046391890972164520777931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8123711709259105388741149 3046391890972164520777931)
                      ·
                        rfl

theorem cell23_5932827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4, 3].length) (baseStart_5932827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932827 prefixEnd_5932827 := by exact prefixLift 5932827
  have htrace : WordTrace (prefixWord ++ tailWord_5932827) baseStart_5932827 baseEnd_5932827 := by
    simpa [prefixWord, tailWord_5932827, baseEnd_5932827] using wordTrace_append hprefix tailTrace_5932827
  have hstable : (prefixWord ++ tailWord_5932827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932827).length < 2 ^ (prefixWord ++ tailWord_5932827).sum := by decide
  have hdescent : baseEnd_5932827 < baseStart_5932827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932858 : List Nat := [3, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2]
def baseStart_5932858 : Nat := 118140960795 + 5932858 * 2 ^ 59
def prefixEnd_5932858 : Nat := 4983230072969 + 3 ^ 40 * 5932858 * 2
def baseEnd_5932858 : Nat := 3046407808872453899490289

theorem tailTrace_5932858 : CollatzResearch.WordTrace tailWord_5932858 prefixEnd_5932858 3046407808872453899490289 := by
  unfold tailWord_5932858
  simp only [CollatzResearch.WordTrace]
  refine ⟨54097277085069048080609807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144259405560184128214959485 54097277085069048080609807)
  ·
    refine ⟨81145915627603572120914711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54097277085069048080609807 81145915627603572120914711)
    ·
      refine ⟨121718873441405358181372067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81145915627603572120914711 121718873441405358181372067)
      ·
        refine ⟨182578310162108037272058101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121718873441405358181372067 182578310162108037272058101)
        ·
          refine ⟨17116716577697628494255447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 182578310162108037272058101 17116716577697628494255447)
          ·
            refine ⟨25675074866546442741383171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17116716577697628494255447 25675074866546442741383171)
            ·
              refine ⟨38512612299819664112074757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25675074866546442741383171 38512612299819664112074757)
              ·
                refine ⟨7221114806216187021014017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38512612299819664112074757 7221114806216187021014017)
                ·
                  refine ⟨5415836104662140265760513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7221114806216187021014017 5415836104662140265760513)
                  ·
                    refine ⟨4061877078496605199320385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5415836104662140265760513 4061877078496605199320385)
                    ·
                      refine ⟨3046407808872453899490289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4061877078496605199320385 3046407808872453899490289)
                      ·
                        rfl

theorem cell23_5932858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 2, 2, 2].length) (baseStart_5932858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932858 prefixEnd_5932858 := by exact prefixLift 5932858
  have htrace : WordTrace (prefixWord ++ tailWord_5932858) baseStart_5932858 baseEnd_5932858 := by
    simpa [prefixWord, tailWord_5932858, baseEnd_5932858] using wordTrace_append hprefix tailTrace_5932858
  have hstable : (prefixWord ++ tailWord_5932858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932858).length < 2 ^ (prefixWord ++ tailWord_5932858).sum := by decide
  have hdescent : baseEnd_5932858 < baseStart_5932858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932874 : List Nat := [3, 1, 2, 1, 1, 1, 5, 1, 2, 3, 3]
def baseStart_5932874 : Nat := 118140960795 + 5932874 * 2 ^ 59
def prefixEnd_5932874 : Nat := 4983230072969 + 3 ^ 40 * 5932874 * 2
def baseEnd_5932874 : Nat := 3046416024562925836890215

theorem tailTrace_5932874 : CollatzResearch.WordTrace tailWord_5932874 prefixEnd_5932874 3046416024562925836890215 := by
  unfold tailWord_5932874
  simp only [CollatzResearch.WordTrace]
  refine ⟨54097422977054556763755419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144259794605478818036681117 54097422977054556763755419)
  ·
    refine ⟨81146134465581835145633129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54097422977054556763755419 81146134465581835145633129)
    ·
      refine ⟨60859600849186376359224847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81146134465581835145633129 60859600849186376359224847)
      ·
        refine ⟨91289401273779564538837271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60859600849186376359224847 91289401273779564538837271)
        ·
          refine ⟨136934101910669346808255907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91289401273779564538837271 136934101910669346808255907)
          ·
            refine ⟨205401152866004020212383861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136934101910669346808255907 205401152866004020212383861)
            ·
              refine ⟨19256358081187876894910987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 205401152866004020212383861 19256358081187876894910987)
              ·
                refine ⟨28884537121781815342366481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19256358081187876894910987 28884537121781815342366481)
                ·
                  refine ⟨21663402841336361506774861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28884537121781815342366481 21663402841336361506774861)
                  ·
                    refine ⟨8123776065501135565040573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21663402841336361506774861 8123776065501135565040573)
                    ·
                      refine ⟨3046416024562925836890215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8123776065501135565040573 3046416024562925836890215)
                      ·
                        rfl

theorem cell23_5932874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_5932874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932874 prefixEnd_5932874 := by exact prefixLift 5932874
  have htrace : WordTrace (prefixWord ++ tailWord_5932874) baseStart_5932874 baseEnd_5932874 := by
    simpa [prefixWord, tailWord_5932874, baseEnd_5932874] using wordTrace_append hprefix tailTrace_5932874
  have hstable : (prefixWord ++ tailWord_5932874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932874).length < 2 ^ (prefixWord ++ tailWord_5932874).sum := by decide
  have hdescent : baseEnd_5932874 < baseStart_5932874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932898 : List Nat := [3, 3, 2, 1, 2, 2, 2, 3, 5]
def baseStart_5932898 : Nat := 118140960795 + 5932898 * 2 ^ 59
def prefixEnd_5932898 : Nat := 4983230072969 + 3 ^ 40 * 5932898 * 2
def baseEnd_5932898 : Nat := 338492038677625971443345

theorem tailTrace_5932898 : CollatzResearch.WordTrace tailWord_5932898 prefixEnd_5932898 338492038677625971443345 := by
  unfold tailWord_5932898
  simp only [CollatzResearch.WordTrace]
  refine ⟨54097641815032819788473837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144260378173420852769263565 54097641815032819788473837)
  ·
    refine ⟨20286615680637307420677689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54097641815032819788473837 20286615680637307420677689)
    ·
      refine ⟨15214961760477980565508267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20286615680637307420677689 15214961760477980565508267)
      ·
        refine ⟨22822442640716970848262401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15214961760477980565508267 22822442640716970848262401)
        ·
          refine ⟨17116831980537728136196801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22822442640716970848262401 17116831980537728136196801)
          ·
            refine ⟨12837623985403296102147601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17116831980537728136196801 12837623985403296102147601)
            ·
              refine ⟨9628217989052472076610701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12837623985403296102147601 9628217989052472076610701)
              ·
                refine ⟨3610581745894677028729013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9628217989052472076610701 3610581745894677028729013)
                ·
                  refine ⟨338492038677625971443345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3610581745894677028729013 338492038677625971443345)
                  ·
                    rfl

theorem cell23_5932898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_5932898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932898 prefixEnd_5932898 := by exact prefixLift 5932898
  have htrace : WordTrace (prefixWord ++ tailWord_5932898) baseStart_5932898 baseEnd_5932898 := by
    simpa [prefixWord, tailWord_5932898, baseEnd_5932898] using wordTrace_append hprefix tailTrace_5932898
  have hstable : (prefixWord ++ tailWord_5932898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932898).length < 2 ^ (prefixWord ++ tailWord_5932898).sum := by decide
  have hdescent : baseEnd_5932898 < baseStart_5932898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932914 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 4, 1, 4]
def baseStart_5932914 : Nat := 118140960795 + 5932914 * 2 ^ 59
def prefixEnd_5932914 : Nat := 4983230072969 + 3 ^ 40 * 5932914 * 2
def baseEnd_5932914 : Nat := 3046436563789105680390031

theorem tailTrace_5932914 : CollatzResearch.WordTrace tailWord_5932914 prefixEnd_5932914 3046436563789105680390031 := by
  unfold tailWord_5932914
  simp only [CollatzResearch.WordTrace]
  refine ⟨54097787707018328471619449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144260767218715542590985197 54097787707018328471619449)
  ·
    refine ⟨40573340780263746353714587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54097787707018328471619449 40573340780263746353714587)
    ·
      refine ⟨60860011170395619530571881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40573340780263746353714587 60860011170395619530571881)
      ·
        refine ⟨45645008377796714647928911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60860011170395619530571881 45645008377796714647928911)
        ·
          refine ⟨68467512566695071971893367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45645008377796714647928911 68467512566695071971893367)
          ·
            refine ⟨102701268850042607957840051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68467512566695071971893367 102701268850042607957840051)
            ·
              refine ⟨154051903275063911936760077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102701268850042607957840051 154051903275063911936760077)
              ·
                refine ⟨57769463728148966976285029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154051903275063911936760077 57769463728148966976285029)
                ·
                  refine ⟨10831774449027931308053443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57769463728148966976285029 10831774449027931308053443)
                  ·
                    refine ⟨16247661673541896962080165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10831774449027931308053443 16247661673541896962080165)
                    ·
                      refine ⟨3046436563789105680390031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16247661673541896962080165 3046436563789105680390031)
                      ·
                        rfl

theorem cell23_5932914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_5932914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932914 prefixEnd_5932914 := by exact prefixLift 5932914
  have htrace : WordTrace (prefixWord ++ tailWord_5932914) baseStart_5932914 baseEnd_5932914 := by
    simpa [prefixWord, tailWord_5932914, baseEnd_5932914] using wordTrace_append hprefix tailTrace_5932914
  have hstable : (prefixWord ++ tailWord_5932914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932914).length < 2 ^ (prefixWord ++ tailWord_5932914).sum := by decide
  have hdescent : baseEnd_5932914 < baseStart_5932914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932927 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 6]
def baseStart_5932927 : Nat := 118140960795 + 5932927 * 2 ^ 59
def prefixEnd_5932927 : Nat := 4983230072969 + 3 ^ 40 * 5932927 * 2
def baseEnd_5932927 : Nat := 3046443239037614129527471

theorem tailTrace_5932927 : CollatzResearch.WordTrace tailWord_5932927 prefixEnd_5932927 3046443239037614129527471 := by
  unfold tailWord_5932927
  simp only [CollatzResearch.WordTrace]
  refine ⟨216391624977026217106701035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144261083318017478071134023 216391624977026217106701035)
  ·
    refine ⟨324587437465539325660051553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216391624977026217106701035 324587437465539325660051553)
    ·
      refine ⟨243440578099154494245038665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324587437465539325660051553 243440578099154494245038665)
      ·
        refine ⟨182580433574365870683778999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243440578099154494245038665 182580433574365870683778999)
        ·
          refine ⟨273870650361548806025668499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182580433574365870683778999 273870650361548806025668499)
          ·
            refine ⟨410805975542323209038502749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273870650361548806025668499 410805975542323209038502749)
            ·
              refine ⟨154052240828371203389438531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 410805975542323209038502749 154052240828371203389438531)
              ·
                refine ⟨231078361242556805084157797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154052240828371203389438531 231078361242556805084157797)
                ·
                  refine ⟨43327192732979400953279587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 231078361242556805084157797 43327192732979400953279587)
                  ·
                    refine ⟨64990789099469101429919381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43327192732979400953279587 64990789099469101429919381)
                    ·
                      refine ⟨3046443239037614129527471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64990789099469101429919381 3046443239037614129527471)
                      ·
                        rfl

theorem cell23_5932927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_5932927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932927 prefixEnd_5932927 := by exact prefixLift 5932927
  have htrace : WordTrace (prefixWord ++ tailWord_5932927) baseStart_5932927 baseEnd_5932927 := by
    simpa [prefixWord, tailWord_5932927, baseEnd_5932927] using wordTrace_append hprefix tailTrace_5932927
  have hstable : (prefixWord ++ tailWord_5932927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932927).length < 2 ^ (prefixWord ++ tailWord_5932927).sum := by decide
  have hdescent : baseEnd_5932927 < baseStart_5932927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932931 : List Nat := [1, 1, 1, 3, 4, 2, 2, 1, 2, 4, 2]
def baseStart_5932931 : Nat := 118140960795 + 5932931 * 2 ^ 59
def prefixEnd_5932931 : Nat := 4983230072969 + 3 ^ 40 * 5932931 * 2
def baseEnd_5932931 : Nat := 3046445292960232113877453

theorem tailTrace_5932931 : CollatzResearch.WordTrace tailWord_5932931 prefixEnd_5932931 3046445292960232113877453 := by
  unfold tailWord_5932931
  simp only [CollatzResearch.WordTrace]
  refine ⟨216391770869011725789846647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144261180579341150526564431 216391770869011725789846647)
  ·
    refine ⟨324587656303517588684769971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216391770869011725789846647 324587656303517588684769971)
    ·
      refine ⟨486881484455276383027154957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324587656303517588684769971 486881484455276383027154957)
      ·
        refine ⟨182580556670728643635183109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 486881484455276383027154957 182580556670728643635183109)
        ·
          refine ⟨34233854375761620681596833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182580556670728643635183109 34233854375761620681596833)
          ·
            refine ⟨25675390781821215511197625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34233854375761620681596833 25675390781821215511197625)
            ·
              refine ⟨19256543086365911633398219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25675390781821215511197625 19256543086365911633398219)
              ·
                refine ⟨28884814629548867450097329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19256543086365911633398219 28884814629548867450097329)
                ·
                  refine ⟨21663610972161650587572997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28884814629548867450097329 21663610972161650587572997)
                  ·
                    refine ⟨4061927057280309485169937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21663610972161650587572997 4061927057280309485169937)
                    ·
                      refine ⟨3046445292960232113877453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4061927057280309485169937 3046445292960232113877453)
                      ·
                        rfl

theorem cell23_5932931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 4, 2].length) (baseStart_5932931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932931 prefixEnd_5932931 := by exact prefixLift 5932931
  have htrace : WordTrace (prefixWord ++ tailWord_5932931) baseStart_5932931 baseEnd_5932931 := by
    simpa [prefixWord, tailWord_5932931, baseEnd_5932931] using wordTrace_append hprefix tailTrace_5932931
  have hstable : (prefixWord ++ tailWord_5932931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932931).length < 2 ^ (prefixWord ++ tailWord_5932931).sum := by decide
  have hdescent : baseEnd_5932931 < baseStart_5932931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932954 : List Nat := [3, 1, 1, 4, 2, 1, 1, 2, 8]
def baseStart_5932954 : Nat := 118140960795 + 5932954 * 2 ^ 59
def prefixEnd_5932954 : Nat := 4983230072969 + 3 ^ 40 * 5932954 * 2
def baseEnd_5932954 : Nat := 338495233668365058209983

theorem tailTrace_5932954 : CollatzResearch.WordTrace tailWord_5932954 prefixEnd_5932954 338495233668365058209983 := by
  unfold tailWord_5932954
  simp only [CollatzResearch.WordTrace]
  refine ⟨54098152436982100179483479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144261739831952267145289277 54098152436982100179483479)
  ·
    refine ⟨81147228655473150269225219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54098152436982100179483479 81147228655473150269225219)
    ·
      refine ⟨121720842983209725403837829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81147228655473150269225219 121720842983209725403837829)
      ·
        refine ⟨22822658059351823513219593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121720842983209725403837829 22822658059351823513219593)
        ·
          refine ⟨17116993544513867634914695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22822658059351823513219593 17116993544513867634914695)
          ·
            refine ⟨25675490316770801452372043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17116993544513867634914695 25675490316770801452372043)
            ·
              refine ⟨38513235475156202178558065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25675490316770801452372043 38513235475156202178558065)
              ·
                refine ⟨28884926606367151633918549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38513235475156202178558065 28884926606367151633918549)
                ·
                  refine ⟨338495233668365058209983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28884926606367151633918549 338495233668365058209983)
                  ·
                    rfl

theorem cell23_5932954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 8].length) (baseStart_5932954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932954 prefixEnd_5932954 := by exact prefixLift 5932954
  have htrace : WordTrace (prefixWord ++ tailWord_5932954) baseStart_5932954 baseEnd_5932954 := by
    simpa [prefixWord, tailWord_5932954, baseEnd_5932954] using wordTrace_append hprefix tailTrace_5932954
  have hstable : (prefixWord ++ tailWord_5932954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932954).length < 2 ^ (prefixWord ++ tailWord_5932954).sum := by decide
  have hdescent : baseEnd_5932954 < baseStart_5932954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932984 : List Nat := [2, 1, 2, 1, 2, 3, 2, 2, 3, 5]
def baseStart_5932984 : Nat := 118140960795 + 5932984 * 2 ^ 59
def prefixEnd_5932984 : Nat := 4983230072969 + 3 ^ 40 * 5932984 * 2
def baseEnd_5932984 : Nat := 1015490835811640135504903

theorem tailTrace_5932984 : CollatzResearch.WordTrace tailWord_5932984 prefixEnd_5932984 1015490835811640135504903 := by
  unfold tailWord_5932984
  simp only [CollatzResearch.WordTrace]
  refine ⟨108196851968909857920763003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144262469291879810561017337 108196851968909857920763003)
  ·
    refine ⟨162295277953364786881144505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108196851968909857920763003 162295277953364786881144505)
    ·
      refine ⟨121721458465023590160858379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162295277953364786881144505 121721458465023590160858379)
      ·
        refine ⟨182582187697535385241287569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121721458465023590160858379 182582187697535385241287569)
        ·
          refine ⟨136936640773151538930965677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182582187697535385241287569 136936640773151538930965677)
          ·
            refine ⟨51351240289931827099112129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136936640773151538930965677 51351240289931827099112129)
            ·
              refine ⟨38513430217448870324334097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51351240289931827099112129 38513430217448870324334097)
              ·
                refine ⟨28885072663086652743250573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38513430217448870324334097 28885072663086652743250573)
                ·
                  refine ⟨10831902248657494778718965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28885072663086652743250573 10831902248657494778718965)
                  ·
                    refine ⟨1015490835811640135504903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10831902248657494778718965 1015490835811640135504903)
                    ·
                      rfl

theorem cell23_5932984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 3, 5].length) (baseStart_5932984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932984 prefixEnd_5932984 := by exact prefixLift 5932984
  have htrace : WordTrace (prefixWord ++ tailWord_5932984) baseStart_5932984 baseEnd_5932984 := by
    simpa [prefixWord, tailWord_5932984, baseEnd_5932984] using wordTrace_append hprefix tailTrace_5932984
  have hstable : (prefixWord ++ tailWord_5932984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932984).length < 2 ^ (prefixWord ++ tailWord_5932984).sum := by decide
  have hdescent : baseEnd_5932984 < baseStart_5932984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932988 : List Nat := [2, 2, 2, 5, 1, 1, 1, 3, 6]
def baseStart_5932988 : Nat := 118140960795 + 5932988 * 2 ^ 59
def prefixEnd_5932988 : Nat := 4983230072969 + 3 ^ 40 * 5932988 * 2
def baseEnd_5932988 : Nat := 338497173484170932318299

theorem tailTrace_5932988 : CollatzResearch.WordTrace tailWord_5932988 prefixEnd_5932988 338497173484170932318299 := by
  unfold tailWord_5932988
  simp only [CollatzResearch.WordTrace]
  refine ⟨108196924914902612262335809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144262566553203483016447745 108196924914902612262335809)
  ·
    refine ⟨81147693686176959196751857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108196924914902612262335809 81147693686176959196751857)
    ·
      refine ⟨60860770264632719397563893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81147693686176959196751857 60860770264632719397563893)
      ·
        refine ⟨5705697212309317443521615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60860770264632719397563893 5705697212309317443521615)
        ·
          refine ⟨8558545818463976165282423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5705697212309317443521615 8558545818463976165282423)
          ·
            refine ⟨12837818727695964247923635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8558545818463976165282423 12837818727695964247923635)
            ·
              refine ⟨19256728091543946371885453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12837818727695964247923635 19256728091543946371885453)
              ·
                refine ⟨7221273034328979889457045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19256728091543946371885453 7221273034328979889457045)
                ·
                  refine ⟨338497173484170932318299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7221273034328979889457045 338497173484170932318299)
                  ·
                    rfl

theorem cell23_5932988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 6].length) (baseStart_5932988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932988 prefixEnd_5932988 := by exact prefixLift 5932988
  have htrace : WordTrace (prefixWord ++ tailWord_5932988) baseStart_5932988 baseEnd_5932988 := by
    simpa [prefixWord, tailWord_5932988, baseEnd_5932988] using wordTrace_append hprefix tailTrace_5932988
  have hstable : (prefixWord ++ tailWord_5932988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932988).length < 2 ^ (prefixWord ++ tailWord_5932988).sum := by decide
  have hdescent : baseEnd_5932988 < baseStart_5932988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5932991 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 4, 3, 2]
def baseStart_5932991 : Nat := 118140960795 + 5932991 * 2 ^ 59
def prefixEnd_5932991 : Nat := 4983230072969 + 3 ^ 40 * 5932991 * 2
def baseEnd_5932991 : Nat := 3046476101799501879127177

theorem tailTrace_5932991 : CollatzResearch.WordTrace tailWord_5932991 prefixEnd_5932991 3046476101799501879127177 := by
  unfold tailWord_5932991
  simp only [CollatzResearch.WordTrace]
  refine ⟨216393959248794356037030827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144262639499196237358020551 216393959248794356037030827)
  ·
    refine ⟨324590938873191534055546241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216393959248794356037030827 324590938873191534055546241)
    ·
      refine ⟨243443204154893650541659681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324590938873191534055546241 243443204154893650541659681)
      ·
        refine ⟨182582403116170237906244761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243443204154893650541659681 182582403116170237906244761)
        ·
          refine ⟨136936802337127678429683571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182582403116170237906244761 136936802337127678429683571)
          ·
            refine ⟨205405203505691517644525357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136936802337127678429683571 205405203505691517644525357)
            ·
              refine ⟨77026951314634319116697009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 205405203505691517644525357 77026951314634319116697009)
              ·
                refine ⟨57770213485975739337522757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77026951314634319116697009 57770213485975739337522757)
                ·
                  refine ⟨10831915028620451125785517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57770213485975739337522757 10831915028620451125785517)
                  ·
                    refine ⟨4061968135732669172169569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10831915028620451125785517 4061968135732669172169569)
                    ·
                      refine ⟨3046476101799501879127177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4061968135732669172169569 3046476101799501879127177)
                      ·
                        rfl

theorem cell23_5932991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 3, 2].length) (baseStart_5932991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5932991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5932991 prefixEnd_5932991 := by exact prefixLift 5932991
  have htrace : WordTrace (prefixWord ++ tailWord_5932991) baseStart_5932991 baseEnd_5932991 := by
    simpa [prefixWord, tailWord_5932991, baseEnd_5932991] using wordTrace_append hprefix tailTrace_5932991
  have hstable : (prefixWord ++ tailWord_5932991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5932991).length < 2 ^ (prefixWord ++ tailWord_5932991).sum := by decide
  have hdescent : baseEnd_5932991 < baseStart_5932991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5932991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933026 : List Nat := [3, 3, 3, 1, 3, 1, 2, 2, 1, 4]
def baseStart_5933026 : Nat := 118140960795 + 5933026 * 2 ^ 59
def prefixEnd_5933026 : Nat := 4983230072969 + 3 ^ 40 * 5933026 * 2
def baseEnd_5933026 : Nat := 1015498024540803080729839

theorem tailTrace_5933026 : CollatzResearch.WordTrace tailWord_5933026 prefixEnd_5933026 1015498024540803080729839 := by
  unfold tailWord_5933026
  simp only [CollatzResearch.WordTrace]
  refine ⟨54098808950916889253638733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144263490535778371343036621 54098808950916889253638733)
  ·
    refine ⟨20287053356593833470114525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54098808950916889253638733 20287053356593833470114525)
    ·
      refine ⟨7607645008722687551292947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20287053356593833470114525 7607645008722687551292947)
      ·
        refine ⟨11411467513084031326939421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7607645008722687551292947 11411467513084031326939421)
        ·
          refine ⟨4279300317406511747602283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11411467513084031326939421 4279300317406511747602283)
          ·
            refine ⟨6418950476109767621403425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4279300317406511747602283 6418950476109767621403425)
            ·
              refine ⟨4814212857082325716052569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6418950476109767621403425 4814212857082325716052569)
              ·
                refine ⟨3610659642811744287039427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4814212857082325716052569 3610659642811744287039427)
                ·
                  refine ⟨5415989464217616430559141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3610659642811744287039427 5415989464217616430559141)
                  ·
                    refine ⟨1015498024540803080729839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5415989464217616430559141 1015498024540803080729839)
                    ·
                      rfl

theorem cell23_5933026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_5933026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933026 prefixEnd_5933026 := by exact prefixLift 5933026
  have htrace : WordTrace (prefixWord ++ tailWord_5933026) baseStart_5933026 baseEnd_5933026 := by
    simpa [prefixWord, tailWord_5933026, baseEnd_5933026] using wordTrace_append hprefix tailTrace_5933026
  have hstable : (prefixWord ++ tailWord_5933026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933026).length < 2 ^ (prefixWord ++ tailWord_5933026).sum := by decide
  have hdescent : baseEnd_5933026 < baseStart_5933026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933061 : List Nat := [1, 3, 1, 1, 2, 5, 3, 7]
def baseStart_5933061 : Nat := 118140960795 + 5933061 * 2 ^ 59
def prefixEnd_5933061 : Nat := 4983230072969 + 3 ^ 40 * 5933061 * 2
def baseEnd_5933061 : Nat := 112833779460937652046365

theorem tailTrace_5933061 : CollatzResearch.WordTrace tailWord_5933061 prefixEnd_5933061 112833779460937652046365 := by
  unfold tailWord_5933061
  simp only [CollatzResearch.WordTrace]
  refine ⟨216396512358540757992079037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144264341572360505328052691 216396512358540757992079037)
  ·
    refine ⟨81148692134452784247029639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216396512358540757992079037 81148692134452784247029639)
    ·
      refine ⟨121723038201679176370544459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81148692134452784247029639 121723038201679176370544459)
      ·
        refine ⟨182584557302518764555816689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121723038201679176370544459 182584557302518764555816689)
        ·
          refine ⟨136938417976889073416862517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182584557302518764555816689 136938417976889073416862517)
          ·
            refine ⟨12837976685333350632830861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136938417976889073416862517 12837976685333350632830861)
            ·
              refine ⟨4814241257000006487311573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12837976685333350632830861 4814241257000006487311573)
              ·
                refine ⟨112833779460937652046365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4814241257000006487311573 112833779460937652046365)
                ·
                  rfl

theorem cell23_5933061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 7].length) (baseStart_5933061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933061 prefixEnd_5933061 := by exact prefixLift 5933061
  have htrace : WordTrace (prefixWord ++ tailWord_5933061) baseStart_5933061 baseEnd_5933061 := by
    simpa [prefixWord, tailWord_5933061, baseEnd_5933061] using wordTrace_append hprefix tailTrace_5933061
  have hstable : (prefixWord ++ tailWord_5933061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933061).length < 2 ^ (prefixWord ++ tailWord_5933061).sum := by decide
  have hdescent : baseEnd_5933061 < baseStart_5933061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933145 : List Nat := [1, 2, 1, 2, 2, 1, 4, 4, 2, 2, 2]
def baseStart_5933145 : Nat := 118140960795 + 5933145 * 2 ^ 59
def prefixEnd_5933145 : Nat := 4983230072969 + 3 ^ 40 * 5933145 * 2
def baseEnd_5933145 : Nat := 3046555177820294276601469

theorem tailTrace_5933145 : CollatzResearch.WordTrace tailWord_5933145 prefixEnd_5933145 3046555177820294276601469 := by
  unfold tailWord_5933145
  simp only [CollatzResearch.WordTrace]
  refine ⟨216399576090236440338136889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144266384060157626892091259 216399576090236440338136889)
  ·
    refine ⟨162299682067677330253602667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216399576090236440338136889 162299682067677330253602667)
    ·
      refine ⟨243449523101515995380404001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162299682067677330253602667 243449523101515995380404001)
      ·
        refine ⟨182587142326136996535303001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243449523101515995380404001 182587142326136996535303001)
        ·
          refine ⟨136940356744602747401477251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182587142326136996535303001 136940356744602747401477251)
          ·
            refine ⟨205410535116904121102215877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136940356744602747401477251 205410535116904121102215877)
            ·
              refine ⟨38514475334419522706665477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 205410535116904121102215877 38514475334419522706665477)
              ·
                refine ⟨7221464125203660507499777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38514475334419522706665477 7221464125203660507499777)
                ·
                  refine ⟨5416098093902745380624833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7221464125203660507499777 5416098093902745380624833)
                  ·
                    refine ⟨4062073570427059035468625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5416098093902745380624833 4062073570427059035468625)
                    ·
                      refine ⟨3046555177820294276601469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4062073570427059035468625 3046555177820294276601469)
                      ·
                        rfl

theorem cell23_5933145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2, 2, 2].length) (baseStart_5933145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933145 prefixEnd_5933145 := by exact prefixLift 5933145
  have htrace : WordTrace (prefixWord ++ tailWord_5933145) baseStart_5933145 baseEnd_5933145 := by
    simpa [prefixWord, tailWord_5933145, baseEnd_5933145] using wordTrace_append hprefix tailTrace_5933145
  have hstable : (prefixWord ++ tailWord_5933145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933145).length < 2 ^ (prefixWord ++ tailWord_5933145).sum := by decide
  have hdescent : baseEnd_5933145 < baseStart_5933145 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933161 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 1, 5, 3]
def baseStart_5933161 : Nat := 118140960795 + 5933161 * 2 ^ 59
def prefixEnd_5933161 : Nat := 4983230072969 + 3 ^ 40 * 5933161 * 2
def baseEnd_5933161 : Nat := 3046563393510766214001395

theorem tailTrace_5933161 : CollatzResearch.WordTrace tailWord_5933161 prefixEnd_5933161 3046563393510766214001395 := by
  unfold tailWord_5933161
  simp only [CollatzResearch.WordTrace]
  refine ⟨216400159658178475070719337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144266773105452316713812891 216400159658178475070719337)
  ·
    refine ⟨162300119743633856303039503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216400159658178475070719337 162300119743633856303039503)
    ·
      refine ⟨243450179615450784454559255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162300119743633856303039503 243450179615450784454559255)
      ·
        refine ⟨365175269423176176681838883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243450179615450784454559255 365175269423176176681838883)
        ·
          refine ⟨547762904134764265022758325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365175269423176176681838883 547762904134764265022758325)
          ·
            refine ⟨51352772262634149845883593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 547762904134764265022758325 51352772262634149845883593)
            ·
              refine ⟨38514579196975612384412695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51352772262634149845883593 38514579196975612384412695)
              ·
                refine ⟨57771868795463418576619043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38514579196975612384412695 57771868795463418576619043)
                ·
                  refine ⟨86657803193195127864928565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57771868795463418576619043 86657803193195127864928565)
                  ·
                    refine ⟨8124169049362043237337053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86657803193195127864928565 8124169049362043237337053)
                    ·
                      refine ⟨3046563393510766214001395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8124169049362043237337053 3046563393510766214001395)
                      ·
                        rfl

theorem cell23_5933161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 5, 3].length) (baseStart_5933161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933161 prefixEnd_5933161 := by exact prefixLift 5933161
  have htrace : WordTrace (prefixWord ++ tailWord_5933161) baseStart_5933161 baseEnd_5933161 := by
    simpa [prefixWord, tailWord_5933161, baseEnd_5933161] using wordTrace_append hprefix tailTrace_5933161
  have hstable : (prefixWord ++ tailWord_5933161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933161).length < 2 ^ (prefixWord ++ tailWord_5933161).sum := by decide
  have hdescent : baseEnd_5933161 < baseStart_5933161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933191 : List Nat := [1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 5]
def baseStart_5933191 : Nat := 118140960795 + 5933191 * 2 ^ 59
def prefixEnd_5933191 : Nat := 4983230072969 + 3 ^ 40 * 5933191 * 2
def baseEnd_5933191 : Nat := 3046578797930401096626257

theorem tailTrace_5933191 : CollatzResearch.WordTrace tailWord_5933191 prefixEnd_5933191 3046578797930401096626257 := by
  unfold tailWord_5933191
  simp only [CollatzResearch.WordTrace]
  refine ⟨216401253848069790194311427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144267502565379860129540951 216401253848069790194311427)
  ·
    refine ⟨324601880772104685291467141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216401253848069790194311427 324601880772104685291467141)
    ·
      refine ⟨60862852644769628492150089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 324601880772104685291467141 60862852644769628492150089)
      ·
        refine ⟨45647139483577221369112567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60862852644769628492150089 45647139483577221369112567)
        ·
          refine ⟨68470709225365832053668851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45647139483577221369112567 68470709225365832053668851)
          ·
            refine ⟨102706063838048748080503277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68470709225365832053668851 102706063838048748080503277)
            ·
              refine ⟨38514773939268280530188729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102706063838048748080503277 38514773939268280530188729)
              ·
                refine ⟨28886080454451210397641547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38514773939268280530188729 28886080454451210397641547)
                ·
                  refine ⟨43329120681676815596462321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28886080454451210397641547 43329120681676815596462321)
                  ·
                    refine ⟨32496840511257611697346741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43329120681676815596462321 32496840511257611697346741)
                    ·
                      refine ⟨3046578797930401096626257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32496840511257611697346741 3046578797930401096626257)
                      ·
                        rfl

theorem cell23_5933191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_5933191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933191 prefixEnd_5933191 := by exact prefixLift 5933191
  have htrace : WordTrace (prefixWord ++ tailWord_5933191) baseStart_5933191 baseEnd_5933191 := by
    simpa [prefixWord, tailWord_5933191, baseEnd_5933191] using wordTrace_append hprefix tailTrace_5933191
  have hstable : (prefixWord ++ tailWord_5933191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933191).length < 2 ^ (prefixWord ++ tailWord_5933191).sum := by decide
  have hdescent : baseEnd_5933191 < baseStart_5933191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933236 : List Nat := [2, 5, 3, 1, 1, 1, 2, 3, 5]
def baseStart_5933236 : Nat := 118140960795 + 5933236 * 2 ^ 59
def prefixEnd_5933236 : Nat := 4983230072969 + 3 ^ 40 * 5933236 * 2
def baseEnd_5933236 : Nat := 338511322728872602284839

theorem tailTrace_5933236 : CollatzResearch.WordTrace tailWord_5933236 prefixEnd_5933236 338511322728872602284839 := by
  unfold tailWord_5933236
  simp only [CollatzResearch.WordTrace]
  refine ⟨108201447566453381439849781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144268596755271175253133041 108201447566453381439849781)
  ·
    refine ⟨10143885709355004509985917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108201447566453381439849781 10143885709355004509985917)
    ·
      refine ⟨3803957141008126691244719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10143885709355004509985917 3803957141008126691244719)
      ·
        refine ⟨5705935711512190036867079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3803957141008126691244719 5705935711512190036867079)
        ·
          refine ⟨8558903567268285055300619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5705935711512190036867079 8558903567268285055300619)
          ·
            refine ⟨12838355350902427582950929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8558903567268285055300619 12838355350902427582950929)
            ·
              refine ⟨9628766513176820687213197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12838355350902427582950929 9628766513176820687213197)
              ·
                refine ⟨3610787442441307757704949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9628766513176820687213197 3610787442441307757704949)
                ·
                  refine ⟨338511322728872602284839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3610787442441307757704949 338511322728872602284839)
                  ·
                    rfl

theorem cell23_5933236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_5933236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933236 prefixEnd_5933236 := by exact prefixLift 5933236
  have htrace : WordTrace (prefixWord ++ tailWord_5933236) baseStart_5933236 baseEnd_5933236 := by
    simpa [prefixWord, tailWord_5933236, baseEnd_5933236] using wordTrace_append hprefix tailTrace_5933236
  have hstable : (prefixWord ++ tailWord_5933236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933236).length < 2 ^ (prefixWord ++ tailWord_5933236).sum := by decide
  have hdescent : baseEnd_5933236 < baseStart_5933236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933241 : List Nat := [1, 2, 1, 4, 1, 2, 2, 2, 8]
def baseStart_5933241 : Nat := 118140960795 + 5933241 * 2 ^ 59
def prefixEnd_5933241 : Nat := 4983230072969 + 3 ^ 40 * 5933241 * 2
def baseEnd_5933241 : Nat := 338511607995902877889003

theorem tailTrace_5933241 : CollatzResearch.WordTrace tailWord_5933241 prefixEnd_5933241 338511607995902877889003 := by
  unfold tailWord_5933241
  simp only [CollatzResearch.WordTrace]
  refine ⟨216403077497888648733631577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144268718331925765822421051 216403077497888648733631577)
  ·
    refine ⟨162302308123416486550223683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216403077497888648733631577 162302308123416486550223683)
    ·
      refine ⟨243453462185124729825335525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162302308123416486550223683 243453462185124729825335525)
      ·
        refine ⟨45647524159710886842250411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 243453462185124729825335525 45647524159710886842250411)
        ·
          refine ⟨68471286239566330263375617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45647524159710886842250411 68471286239566330263375617)
          ·
            refine ⟨51353464679674747697531713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68471286239566330263375617 51353464679674747697531713)
            ·
              refine ⟨38515098509756060773148785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51353464679674747697531713 38515098509756060773148785)
              ·
                refine ⟨28886323882317045579861589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38515098509756060773148785 28886323882317045579861589)
                ·
                  refine ⟨338511607995902877889003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28886323882317045579861589 338511607995902877889003)
                  ·
                    rfl

theorem cell23_5933241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 8].length) (baseStart_5933241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933241 prefixEnd_5933241 := by exact prefixLift 5933241
  have htrace : WordTrace (prefixWord ++ tailWord_5933241) baseStart_5933241 baseEnd_5933241 := by
    simpa [prefixWord, tailWord_5933241, baseEnd_5933241] using wordTrace_append hprefix tailTrace_5933241
  have hstable : (prefixWord ++ tailWord_5933241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933241).length < 2 ^ (prefixWord ++ tailWord_5933241).sum := by decide
  have hdescent : baseEnd_5933241 < baseStart_5933241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933262 : List Nat := [4, 1, 1, 1, 4, 1, 2, 4, 1, 4]
def baseStart_5933262 : Nat := 118140960795 + 5933262 * 2 ^ 59
def prefixEnd_5933262 : Nat := 4983230072969 + 3 ^ 40 * 5933262 * 2
def baseEnd_5933262 : Nat := 1015538418352290106279477

theorem tailTrace_5933262 : CollatzResearch.WordTrace tailWord_5933262 prefixEnd_5933262 1015538418352290106279477 := by
  unfold tailWord_5933262
  simp only [CollatzResearch.WordTrace]
  refine ⟨27050480428851571165018255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 144269228953875046213430693 27050480428851571165018255)
  ·
    refine ⟨40575720643277356747527383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27050480428851571165018255 40575720643277356747527383)
    ·
      refine ⟨60863580964916035121291075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40575720643277356747527383 60863580964916035121291075)
      ·
        refine ⟨91295371447374052681936613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60863580964916035121291075 91295371447374052681936613)
        ·
          refine ⟨17117882146382634877863115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91295371447374052681936613 17117882146382634877863115)
          ·
            refine ⟨25676823219573952316794673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17117882146382634877863115 25676823219573952316794673)
            ·
              refine ⟨19257617414680464237596005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25676823219573952316794673 19257617414680464237596005)
              ·
                refine ⟨3610803265252587044549251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19257617414680464237596005 3610803265252587044549251)
                ·
                  refine ⟨5416204897878880566823877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3610803265252587044549251 5416204897878880566823877)
                  ·
                    refine ⟨1015538418352290106279477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5416204897878880566823877 1015538418352290106279477)
                    ·
                      rfl

theorem cell23_5933262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_5933262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933262 prefixEnd_5933262 := by exact prefixLift 5933262
  have htrace : WordTrace (prefixWord ++ tailWord_5933262) baseStart_5933262 baseEnd_5933262 := by
    simpa [prefixWord, tailWord_5933262, baseEnd_5933262] using wordTrace_append hprefix tailTrace_5933262
  have hstable : (prefixWord ++ tailWord_5933262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933262).length < 2 ^ (prefixWord ++ tailWord_5933262).sum := by decide
  have hdescent : baseEnd_5933262 < baseStart_5933262 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933295 : List Nat := [1, 1, 2, 1, 6, 1, 2, 1, 1, 5, 2]
def baseStart_5933295 : Nat := 118140960795 + 5933295 * 2 ^ 59
def prefixEnd_5933295 : Nat := 4983230072969 + 3 ^ 40 * 5933295 * 2
def baseEnd_5933295 : Nat := 3046632199918468689725779

theorem tailTrace_5933295 : CollatzResearch.WordTrace tailWord_5933295 prefixEnd_5933295 3046632199918468689725779 := by
  unfold tailWord_5933295
  simp only [CollatzResearch.WordTrace]
  refine ⟨216405047039693015956097339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144270031359795343970731559 216405047039693015956097339)
  ·
    refine ⟨324607570559539523934146009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216405047039693015956097339 324607570559539523934146009)
    ·
      refine ⟨243455677919654642950609507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 324607570559539523934146009 243455677919654642950609507)
      ·
        refine ⟨365183516879481964425914261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243455677919654642950609507 365183516879481964425914261)
        ·
          refine ⟨17117977353725717082464731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 365183516879481964425914261 17117977353725717082464731)
          ·
            refine ⟨25676966030588575623697097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17117977353725717082464731 25676966030588575623697097)
            ·
              refine ⟨19257724522941431717772823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25676966030588575623697097 19257724522941431717772823)
              ·
                refine ⟨28886586784412147576659235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19257724522941431717772823 28886586784412147576659235)
                ·
                  refine ⟨43329880176618221364988853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28886586784412147576659235 43329880176618221364988853)
                  ·
                    refine ⟨4062176266557958252967705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43329880176618221364988853 4062176266557958252967705)
                    ·
                      refine ⟨3046632199918468689725779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4062176266557958252967705 3046632199918468689725779)
                      ·
                        rfl

theorem cell23_5933295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 5, 2].length) (baseStart_5933295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933295 prefixEnd_5933295 := by exact prefixLift 5933295
  have htrace : WordTrace (prefixWord ++ tailWord_5933295) baseStart_5933295 baseEnd_5933295 := by
    simpa [prefixWord, tailWord_5933295, baseEnd_5933295] using wordTrace_append hprefix tailTrace_5933295
  have hstable : (prefixWord ++ tailWord_5933295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933295).length < 2 ^ (prefixWord ++ tailWord_5933295).sum := by decide
  have hdescent : baseEnd_5933295 < baseStart_5933295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933348 : List Nat := [2, 3, 1, 3, 1, 2, 2, 9]
def baseStart_5933348 : Nat := 118140960795 + 5933348 * 2 ^ 59
def prefixEnd_5933348 : Nat := 4983230072969 + 3 ^ 40 * 5933348 * 2
def baseEnd_5933348 : Nat := 112839237570116925272705

theorem tailTrace_5933348 : CollatzResearch.WordTrace tailWord_5933348 prefixEnd_5933348 112839237570116925272705 := by
  unfold tailWord_5933348
  simp only [CollatzResearch.WordTrace]
  refine ⟨108203490054250503003888349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144271320072334004005184465 108203490054250503003888349)
  ·
    refine ⟨40576308770343938626458131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108203490054250503003888349 40576308770343938626458131)
    ·
      refine ⟨60864463155515907939687197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40576308770343938626458131 60864463155515907939687197)
      ·
        refine ⟨22824173683318465477382699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60864463155515907939687197 22824173683318465477382699)
        ·
          refine ⟨34236260524977698216074049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22824173683318465477382699 34236260524977698216074049)
          ·
            refine ⟨25677195393733273662055537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34236260524977698216074049 25677195393733273662055537)
            ·
              refine ⟨19257896545299955246541653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25677195393733273662055537 19257896545299955246541653)
              ·
                refine ⟨112839237570116925272705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19257896545299955246541653 112839237570116925272705)
                ·
                  rfl

theorem cell23_5933348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 9].length) (baseStart_5933348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933348 prefixEnd_5933348 := by exact prefixLift 5933348
  have htrace : WordTrace (prefixWord ++ tailWord_5933348) baseStart_5933348 baseEnd_5933348 := by
    simpa [prefixWord, tailWord_5933348, baseEnd_5933348] using wordTrace_append hprefix tailTrace_5933348
  have hstable : (prefixWord ++ tailWord_5933348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933348).length < 2 ^ (prefixWord ++ tailWord_5933348).sum := by decide
  have hdescent : baseEnd_5933348 < baseStart_5933348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933362 : List Nat := [3, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5]
def baseStart_5933362 : Nat := 118140960795 + 5933362 * 2 ^ 59
def prefixEnd_5933362 : Nat := 4983230072969 + 3 ^ 40 * 5933362 * 2
def baseEnd_5933362 : Nat := 3046666603122319927587971

theorem tailTrace_5933362 : CollatzResearch.WordTrace tailWord_5933362 prefixEnd_5933362 3046666603122319927587971 := by
  unfold tailWord_5933362
  simp only [CollatzResearch.WordTrace]
  refine ⟨54101872682612571599696585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144271660486966857599190893 54101872682612571599696585)
  ·
    refine ⟨40576404511959428699772439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54101872682612571599696585 40576404511959428699772439)
    ·
      refine ⟨60864606767939143049658659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40576404511959428699772439 60864606767939143049658659)
      ·
        refine ⟨91296910151908714574487989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60864606767939143049658659 91296910151908714574487989)
        ·
          refine ⟨8559085326741441991358249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91296910151908714574487989 8559085326741441991358249)
          ·
            refine ⟨6419313995056081493518687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8559085326741441991358249 6419313995056081493518687)
            ·
              refine ⟨9628970992584122240278031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6419313995056081493518687 9628970992584122240278031)
              ·
                refine ⟨14443456488876183360417047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9628970992584122240278031 14443456488876183360417047)
                ·
                  refine ⟨21665184733314275040625571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14443456488876183360417047 21665184733314275040625571)
                  ·
                    refine ⟨32497777099971412560938357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21665184733314275040625571 32497777099971412560938357)
                    ·
                      refine ⟨3046666603122319927587971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32497777099971412560938357 3046666603122319927587971)
                      ·
                        rfl

theorem cell23_5933362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_5933362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933362 prefixEnd_5933362 := by exact prefixLift 5933362
  have htrace : WordTrace (prefixWord ++ tailWord_5933362) baseStart_5933362 baseEnd_5933362 := by
    simpa [prefixWord, tailWord_5933362, baseEnd_5933362] using wordTrace_append hprefix tailTrace_5933362
  have hstable : (prefixWord ++ tailWord_5933362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933362).length < 2 ^ (prefixWord ++ tailWord_5933362).sum := by decide
  have hdescent : baseEnd_5933362 < baseStart_5933362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933392 : List Nat := [2, 1, 1, 1, 1, 6, 2, 3, 2, 1, 3]
def baseStart_5933392 : Nat := 118140960795 + 5933392 * 2 ^ 59
def prefixEnd_5933392 : Nat := 4983230072969 + 3 ^ 40 * 5933392 * 2
def baseEnd_5933392 : Nat := 3046682007541954810212833

theorem tailTrace_5933392 : CollatzResearch.WordTrace tailWord_5933392 prefixEnd_5933392 3046682007541954810212833 := by
  unfold tailWord_5933392
  simp only [CollatzResearch.WordTrace]
  refine ⟨108204292460170800761189215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144272389946894401014918953 108204292460170800761189215)
  ·
    refine ⟨162306438690256201141783823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108204292460170800761189215 162306438690256201141783823)
    ·
      refine ⟨243459658035384301712675735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162306438690256201141783823 243459658035384301712675735)
      ·
        refine ⟨365189487053076452569013603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243459658035384301712675735 365189487053076452569013603)
        ·
          refine ⟨547784230579614678853520405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365189487053076452569013603 547784230579614678853520405)
          ·
            refine ⟨25677385808419438071258769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 547784230579614678853520405 25677385808419438071258769)
            ·
              refine ⟨19258039356314578553444077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25677385808419438071258769 19258039356314578553444077)
              ·
                refine ⟨7221764758617966957541529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19258039356314578553444077 7221764758617966957541529)
                ·
                  refine ⟨5416323568963475218156147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7221764758617966957541529 5416323568963475218156147)
                  ·
                    refine ⟨8124485353445212827234221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5416323568963475218156147 8124485353445212827234221)
                    ·
                      refine ⟨3046682007541954810212833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8124485353445212827234221 3046682007541954810212833)
                      ·
                        rfl

theorem cell23_5933392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 2, 1, 3].length) (baseStart_5933392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933392 prefixEnd_5933392 := by exact prefixLift 5933392
  have htrace : WordTrace (prefixWord ++ tailWord_5933392) baseStart_5933392 baseEnd_5933392 := by
    simpa [prefixWord, tailWord_5933392, baseEnd_5933392] using wordTrace_append hprefix tailTrace_5933392
  have hstable : (prefixWord ++ tailWord_5933392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933392).length < 2 ^ (prefixWord ++ tailWord_5933392).sum := by decide
  have hdescent : baseEnd_5933392 < baseStart_5933392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933402 : List Nat := [3, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2]
def baseStart_5933402 : Nat := 118140960795 + 5933402 * 2 ^ 59
def prefixEnd_5933402 : Nat := 4983230072969 + 3 ^ 40 * 5933402 * 2
def baseEnd_5933402 : Nat := 3046687142348499771087787

theorem tailTrace_5933402 : CollatzResearch.WordTrace tailWord_5933402 prefixEnd_5933402 3046687142348499771087787 := by
  unfold tailWord_5933402
  simp only [CollatzResearch.WordTrace]
  refine ⟨54102237412576343307560615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 144272633100203582153494973 54102237412576343307560615)
  ·
    refine ⟨81153356118864514961340923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54102237412576343307560615 81153356118864514961340923)
    ·
      refine ⟨121730034178296772442011385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81153356118864514961340923 121730034178296772442011385)
      ·
        refine ⟨91297525633722579331508539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121730034178296772442011385 91297525633722579331508539)
        ·
          refine ⟨136946288450583868997262809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91297525633722579331508539 136946288450583868997262809)
          ·
            refine ⟨102709716337937901747947107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136946288450583868997262809 102709716337937901747947107)
            ·
              refine ⟨154064574506906852621920661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102709716337937901747947107 154064574506906852621920661)
              ·
                refine ⟨7221776930011258716652531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 154064574506906852621920661 7221776930011258716652531)
                ·
                  refine ⟨10832665395016888074978797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7221776930011258716652531 10832665395016888074978797)
                  ·
                    refine ⟨4062249523131333028117049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10832665395016888074978797 4062249523131333028117049)
                    ·
                      refine ⟨3046687142348499771087787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4062249523131333028117049 3046687142348499771087787)
                      ·
                        rfl

theorem cell23_5933402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2].length) (baseStart_5933402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933402 prefixEnd_5933402 := by exact prefixLift 5933402
  have htrace : WordTrace (prefixWord ++ tailWord_5933402) baseStart_5933402 baseEnd_5933402 := by
    simpa [prefixWord, tailWord_5933402, baseEnd_5933402] using wordTrace_append hprefix tailTrace_5933402
  have hstable : (prefixWord ++ tailWord_5933402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933402).length < 2 ^ (prefixWord ++ tailWord_5933402).sum := by decide
  have hdescent : baseEnd_5933402 < baseStart_5933402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933449 : List Nat := [1, 2, 1, 1, 6, 3, 1, 1, 1, 4, 2]
def baseStart_5933449 : Nat := 118140960795 + 5933449 * 2 ^ 59
def prefixEnd_5933449 : Nat := 4983230072969 + 3 ^ 40 * 5933449 * 2
def baseEnd_5933449 : Nat := 3046711275939261087200071

theorem tailTrace_5933449 : CollatzResearch.WordTrace tailWord_5933449 prefixEnd_5933449 3046711275939261087200071 := by
  unfold tailWord_5933449
  simp only [CollatzResearch.WordTrace]
  refine ⟨216410663881135100257203401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144273775920756733504802267 216410663881135100257203401)
  ·
    refine ⟨162307997910851325192902551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216410663881135100257203401 162307997910851325192902551)
    ·
      refine ⟨243461996866276987789353827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162307997910851325192902551 243461996866276987789353827)
      ·
        refine ⟨365192995299415481684030741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243461996866276987789353827 365192995299415481684030741)
        ·
          refine ⟨17118421654660100703938941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 365192995299415481684030741 17118421654660100703938941)
          ·
            refine ⟨6419408120497537763977103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17118421654660100703938941 6419408120497537763977103)
            ·
              refine ⟨9629112180746306645965655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6419408120497537763977103 9629112180746306645965655)
              ·
                refine ⟨14443668271119459968948483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9629112180746306645965655 14443668271119459968948483)
                ·
                  refine ⟨21665502406679189953422725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14443668271119459968948483 21665502406679189953422725)
                  ·
                    refine ⟨4062281701252348116266761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21665502406679189953422725 4062281701252348116266761)
                    ·
                      refine ⟨3046711275939261087200071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4062281701252348116266761 3046711275939261087200071)
                      ·
                        rfl

theorem cell23_5933449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 4, 2].length) (baseStart_5933449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933449 prefixEnd_5933449 := by exact prefixLift 5933449
  have htrace : WordTrace (prefixWord ++ tailWord_5933449) baseStart_5933449 baseEnd_5933449 := by
    simpa [prefixWord, tailWord_5933449, baseEnd_5933449] using wordTrace_append hprefix tailTrace_5933449
  have hstable : (prefixWord ++ tailWord_5933449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933449).length < 2 ^ (prefixWord ++ tailWord_5933449).sum := by decide
  have hdescent : baseEnd_5933449 < baseStart_5933449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933472 : List Nat := [2, 1, 1, 4, 1, 3, 3, 3, 5]
def baseStart_5933472 : Nat := 118140960795 + 5933472 * 2 ^ 59
def prefixEnd_5933472 : Nat := 4983230072969 + 3 ^ 40 * 5933472 * 2
def baseEnd_5933472 : Nat := 338524787332701610801385

theorem tailTrace_5933472 : CollatzResearch.WordTrace tailWord_5933472 prefixEnd_5933472 338524787332701610801385 := by
  unfold tailWord_5933472
  simp only [CollatzResearch.WordTrace]
  refine ⟨108205751380025887592645335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 144274335173367850123527113 108205751380025887592645335)
  ·
    refine ⟨162308627070038831388968003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108205751380025887592645335 162308627070038831388968003)
    ·
      refine ⟨243462940605058247083452005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162308627070038831388968003 243462940605058247083452005)
      ·
        refine ⟨45649301363448421328147251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 243462940605058247083452005 45649301363448421328147251)
        ·
          refine ⟨68473952045172631992220877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45649301363448421328147251 68473952045172631992220877)
          ·
            refine ⟨25677732016939736997082829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68473952045172631992220877 25677732016939736997082829)
            ·
              refine ⟨9629149506352401373906061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25677732016939736997082829 9629149506352401373906061)
              ·
                refine ⟨3610931064882150515214773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9629149506352401373906061 3610931064882150515214773)
                ·
                  refine ⟨338524787332701610801385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3610931064882150515214773 338524787332701610801385)
                  ·
                    rfl

theorem cell23_5933472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3, 5].length) (baseStart_5933472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933472 prefixEnd_5933472 := by exact prefixLift 5933472
  have htrace : WordTrace (prefixWord ++ tailWord_5933472) baseStart_5933472 baseEnd_5933472 := by
    simpa [prefixWord, tailWord_5933472, baseEnd_5933472] using wordTrace_append hprefix tailTrace_5933472
  have hstable : (prefixWord ++ tailWord_5933472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933472).length < 2 ^ (prefixWord ++ tailWord_5933472).sum := by decide
  have hdescent : baseEnd_5933472 < baseStart_5933472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933489 : List Nat := [1, 2, 2, 4, 1, 3, 3, 2, 5]
def baseStart_5933489 : Nat := 118140960795 + 5933489 * 2 ^ 59
def prefixEnd_5933489 : Nat := 4983230072969 + 3 ^ 40 * 5933489 * 2
def baseEnd_5933489 : Nat := 338525757240604547855543

theorem tailTrace_5933489 : CollatzResearch.WordTrace tailWord_5933489 prefixEnd_5933489 338525757240604547855543 := by
  unfold tailWord_5933489
  simp only [CollatzResearch.WordTrace]
  refine ⟨216412122800990187088659521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144274748533993458059106347 216412122800990187088659521)
  ·
    refine ⟨162309092100742640316494641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 216412122800990187088659521 162309092100742640316494641)
    ·
      refine ⟨121731819075556980237370981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162309092100742640316494641 121731819075556980237370981)
      ·
        refine ⟨22824716076666933794507059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121731819075556980237370981 22824716076666933794507059)
        ·
          refine ⟨34237074115000400691760589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22824716076666933794507059 34237074115000400691760589)
          ·
            refine ⟨12838902793125150259410221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34237074115000400691760589 12838902793125150259410221)
            ·
              refine ⟨4814588547421931347278833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12838902793125150259410221 4814588547421931347278833)
              ·
                refine ⟨3610941410566448510459125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4814588547421931347278833 3610941410566448510459125)
                ·
                  refine ⟨338525757240604547855543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3610941410566448510459125 338525757240604547855543)
                  ·
                    rfl

theorem cell23_5933489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2, 5].length) (baseStart_5933489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933489 prefixEnd_5933489 := by exact prefixLift 5933489
  have htrace : WordTrace (prefixWord ++ tailWord_5933489) baseStart_5933489 baseEnd_5933489 := by
    simpa [prefixWord, tailWord_5933489, baseEnd_5933489] using wordTrace_append hprefix tailTrace_5933489
  have hstable : (prefixWord ++ tailWord_5933489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933489).length < 2 ^ (prefixWord ++ tailWord_5933489).sum := by decide
  have hdescent : baseEnd_5933489 < baseStart_5933489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933495 : List Nat := [1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 5]
def baseStart_5933495 : Nat := 118140960795 + 5933495 * 2 ^ 59
def prefixEnd_5933495 : Nat := 4983230072969 + 3 ^ 40 * 5933495 * 2
def baseEnd_5933495 : Nat := 3046734896049367907224859

theorem tailTrace_5933495 : CollatzResearch.WordTrace tailWord_5933495 prefixEnd_5933495 3046734896049367907224859 := by
  unfold tailWord_5933495
  simp only [CollatzResearch.WordTrace]
  refine ⟨216412341638968450113377939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144274894425978966742251959 216412341638968450113377939)
  ·
    refine ⟨324618512458452675170066909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216412341638968450113377939 324618512458452675170066909)
    ·
      refine ⟨121731942171919753188775091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 324618512458452675170066909 121731942171919753188775091)
      ·
        refine ⟨182597913257879629783162637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121731942171919753188775091 182597913257879629783162637)
        ·
          refine ⟨68474217471704861168685989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182597913257879629783162637 68474217471704861168685989)
          ·
            refine ⟨12838915775944661469128623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68474217471704861168685989 12838915775944661469128623)
            ·
              refine ⟨19258373663916992203692935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12838915775944661469128623 19258373663916992203692935)
              ·
                refine ⟨28887560495875488305539403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19258373663916992203692935 28887560495875488305539403)
                ·
                  refine ⟨43331340743813232458309105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28887560495875488305539403 43331340743813232458309105)
                  ·
                    refine ⟨32498505557859924343731829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43331340743813232458309105 32498505557859924343731829)
                    ·
                      refine ⟨3046734896049367907224859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32498505557859924343731829 3046734896049367907224859)
                      ·
                        rfl

theorem cell23_5933495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_5933495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933495 prefixEnd_5933495 := by exact prefixLift 5933495
  have htrace : WordTrace (prefixWord ++ tailWord_5933495) baseStart_5933495 baseEnd_5933495 := by
    simpa [prefixWord, tailWord_5933495, baseEnd_5933495] using wordTrace_append hprefix tailTrace_5933495
  have hstable : (prefixWord ++ tailWord_5933495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933495).length < 2 ^ (prefixWord ++ tailWord_5933495).sum := by decide
  have hdescent : baseEnd_5933495 < baseStart_5933495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933515 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 5, 4]
def baseStart_5933515 : Nat := 118140960795 + 5933515 * 2 ^ 59
def prefixEnd_5933515 : Nat := 4983230072969 + 3 ^ 40 * 5933515 * 2
def baseEnd_5933515 : Nat := 1015581721887485942991589

theorem tailTrace_5933515 : CollatzResearch.WordTrace tailWord_5933515 prefixEnd_5933515 1015581721887485942991589 := by
  unfold tailWord_5933515
  simp only [CollatzResearch.WordTrace]
  refine ⟨216413071098895993529105999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144275380732597329019403999 216413071098895993529105999)
  ·
    refine ⟨324619606648343990293658999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 216413071098895993529105999 324619606648343990293658999)
    ·
      refine ⟨486929409972515985440488499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324619606648343990293658999 486929409972515985440488499)
      ·
        refine ⟨730394114958773978160732749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 486929409972515985440488499 730394114958773978160732749)
        ·
          refine ⟨273897793109540241810274781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 730394114958773978160732749 273897793109540241810274781)
          ·
            refine ⟨102711672416077590678853043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273897793109540241810274781 102711672416077590678853043)
            ·
              refine ⟨154067508624116386018279565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102711672416077590678853043 154067508624116386018279565)
              ·
                refine ⟨57775315734043644756854837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 154067508624116386018279565 57775315734043644756854837)
                ·
                  refine ⟨5416435850066591695955141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57775315734043644756854837 5416435850066591695955141)
                  ·
                    refine ⟨1015581721887485942991589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5416435850066591695955141 1015581721887485942991589)
                    ·
                      rfl

theorem cell23_5933515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5, 4].length) (baseStart_5933515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933515 prefixEnd_5933515 := by exact prefixLift 5933515
  have htrace : WordTrace (prefixWord ++ tailWord_5933515) baseStart_5933515 baseEnd_5933515 := by
    simpa [prefixWord, tailWord_5933515, baseEnd_5933515] using wordTrace_append hprefix tailTrace_5933515
  have hstable : (prefixWord ++ tailWord_5933515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933515).length < 2 ^ (prefixWord ++ tailWord_5933515).sum := by decide
  have hdescent : baseEnd_5933515 < baseStart_5933515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5933605 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 3, 6]
def baseStart_5933605 : Nat := 118140960795 + 5933605 * 2 ^ 59
def prefixEnd_5933605 : Nat := 4983230072969 + 3 ^ 40 * 5933605 * 2
def baseEnd_5933605 : Nat := 1015597126307120825616451

theorem tailTrace_5933605 : CollatzResearch.WordTrace tailWord_5933605 prefixEnd_5933605 1015597126307120825616451 := by
  unfold tailWord_5933605
  simp only [CollatzResearch.WordTrace]
  refine ⟨216416353668569938899882269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 144277569112379959266588179 216416353668569938899882269)
  ·
    refine ⟨81156132625713727087455851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 216416353668569938899882269 81156132625713727087455851)
    ·
      refine ⟨121734198938570590631183777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81156132625713727087455851 121734198938570590631183777)
      ·
        refine ⟨91300649203927942973387833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121734198938570590631183777 91300649203927942973387833)
        ·
          refine ⟨68475486902945957230040875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91300649203927942973387833 68475486902945957230040875)
          ·
            refine ⟨102713230354418935845061313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68475486902945957230040875 102713230354418935845061313)
            ·
              refine ⟨77034922765814201883795985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102713230354418935845061313 77034922765814201883795985)
              ·
                refine ⟨57776192074360651412846989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77034922765814201883795985 57776192074360651412846989)
                ·
                  refine ⟨21666072027885244279817621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57776192074360651412846989 21666072027885244279817621)
                  ·
                    refine ⟨1015597126307120825616451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21666072027885244279817621 1015597126307120825616451)
                    ·
                      rfl

theorem cell23_5933605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 6].length) (baseStart_5933605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5933605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5933605 prefixEnd_5933605 := by exact prefixLift 5933605
  have htrace : WordTrace (prefixWord ++ tailWord_5933605) baseStart_5933605 baseEnd_5933605 := by
    simpa [prefixWord, tailWord_5933605, baseEnd_5933605] using wordTrace_append hprefix tailTrace_5933605
  have hstable : (prefixWord ++ tailWord_5933605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5933605).length < 2 ^ (prefixWord ++ tailWord_5933605).sum := by decide
  have hdescent : baseEnd_5933605 < baseStart_5933605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5933605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
