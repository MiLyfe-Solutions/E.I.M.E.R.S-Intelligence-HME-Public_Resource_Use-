import V185TrunkScan23Chunk1177

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6978978 : List Nat := [3, 3, 1, 2, 1, 3, 3, 2, 1, 1, 3]
def baseStart_6978978 : Nat := 118140960795 + 6978978 * 2 ^ 59
def prefixEnd_6978978 : Nat := 4983230072969 + 3 ^ 40 * 6978978 * 2
def baseEnd_6978978 : Nat := 3583570191153900950179271

theorem tailTrace_6978978 : CollatzResearch.WordTrace tailWord_6978978 prefixEnd_6978978 3583570191153900950179271 := by
  unfold tailWord_6978978
  simp only [CollatzResearch.WordTrace]
  refine ⟨63636059827590523848586397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169696159540241396929563725 63636059827590523848586397)
  ·
    refine ⟨23863522435346446443219899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63636059827590523848586397 23863522435346446443219899)
    ·
      refine ⟨35795283653019669664829849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23863522435346446443219899 35795283653019669664829849)
      ·
        refine ⟨26846462739764752248622387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35795283653019669664829849 26846462739764752248622387)
        ·
          refine ⟨40269694109647128372933581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26846462739764752248622387 40269694109647128372933581)
          ·
            refine ⟨15101135291117673139850093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40269694109647128372933581 15101135291117673139850093)
            ·
              refine ⟨5662925734169127427443785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15101135291117673139850093 5662925734169127427443785)
              ·
                refine ⟨4247194300626845570582839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5662925734169127427443785 4247194300626845570582839)
                ·
                  refine ⟨6370791450940268355874259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4247194300626845570582839 6370791450940268355874259)
                  ·
                    refine ⟨9556187176410402533811389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6370791450940268355874259 9556187176410402533811389)
                    ·
                      refine ⟨3583570191153900950179271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9556187176410402533811389 3583570191153900950179271)
                      ·
                        rfl

theorem cell23_6978978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_6978978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6978978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6978978 prefixEnd_6978978 := by exact prefixLift 6978978
  have htrace : WordTrace (prefixWord ++ tailWord_6978978) baseStart_6978978 baseEnd_6978978 := by
    simpa [prefixWord, tailWord_6978978, baseEnd_6978978] using wordTrace_append hprefix tailTrace_6978978
  have hstable : (prefixWord ++ tailWord_6978978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6978978).length < 2 ^ (prefixWord ++ tailWord_6978978).sum := by decide
  have hdescent : baseEnd_6978978 < baseStart_6978978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6978978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979001 : List Nat := [1, 2, 1, 4, 5, 1, 1, 2, 1, 1, 4]
def baseStart_6979001 : Nat := 118140960795 + 6979001 * 2 ^ 59
def prefixEnd_6979001 : Nat := 4983230072969 + 3 ^ 40 * 6979001 * 2
def baseEnd_6979001 : Nat := 3583582001208954360191665

theorem tailTrace_6979001 : CollatzResearch.WordTrace tailWord_6979001 prefixEnd_6979001 3583582001208954360191665 := by
  unfold tailWord_6979001
  simp only [CollatzResearch.WordTrace]
  refine ⟨254545078189278770322432857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169696718792852513548288571 254545078189278770322432857)
  ·
    refine ⟨190908808641959077741824643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254545078189278770322432857 190908808641959077741824643)
    ·
      refine ⟨286363212962938616612736965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190908808641959077741824643 286363212962938616612736965)
      ·
        refine ⟨53693102430550990614888181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286363212962938616612736965 53693102430550990614888181)
        ·
          refine ⟨5033728352864155370145767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53693102430550990614888181 5033728352864155370145767)
          ·
            refine ⟨7550592529296233055218651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5033728352864155370145767 7550592529296233055218651)
            ·
              refine ⟨11325888793944349582827977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7550592529296233055218651 11325888793944349582827977)
              ·
                refine ⟨8494416595458262187120983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11325888793944349582827977 8494416595458262187120983)
                ·
                  refine ⟨12741624893187393280681475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8494416595458262187120983 12741624893187393280681475)
                  ·
                    refine ⟨19112437339781089921022213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12741624893187393280681475 19112437339781089921022213)
                    ·
                      refine ⟨3583582001208954360191665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19112437339781089921022213 3583582001208954360191665)
                      ·
                        rfl

theorem cell23_6979001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_6979001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979001 prefixEnd_6979001 := by exact prefixLift 6979001
  have htrace : WordTrace (prefixWord ++ tailWord_6979001) baseStart_6979001 baseEnd_6979001 := by
    simpa [prefixWord, tailWord_6979001, baseEnd_6979001] using wordTrace_append hprefix tailTrace_6979001
  have hstable : (prefixWord ++ tailWord_6979001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979001).length < 2 ^ (prefixWord ++ tailWord_6979001).sum := by decide
  have hdescent : baseEnd_6979001 < baseStart_6979001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979004 : List Nat := [2, 2, 2, 4, 2, 1, 1, 1, 3, 2, 3]
def baseStart_6979004 : Nat := 118140960795 + 6979004 * 2 ^ 59
def prefixEnd_6979004 : Nat := 4983230072969 + 3 ^ 40 * 6979004 * 2
def baseEnd_6979004 : Nat := 3583583541650917848454151

theorem tailTrace_6979004 : CollatzResearch.WordTrace tailWord_6979004 prefixEnd_6979004 3583583541650917848454151 := by
  unfold tailWord_6979004
  simp only [CollatzResearch.WordTrace]
  refine ⟨127272593804133950917396033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169696791738845267889861377 127272593804133950917396033)
  ·
    refine ⟨95454445353100463188047025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127272593804133950917396033 95454445353100463188047025)
    ·
      refine ⟨71590834014825347391035269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95454445353100463188047025 71590834014825347391035269)
      ·
        refine ⟨13423281377779752635819113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71590834014825347391035269 13423281377779752635819113)
        ·
          refine ⟨10067461033334814476864335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13423281377779752635819113 10067461033334814476864335)
          ·
            refine ⟨15101191550002221715296503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10067461033334814476864335 15101191550002221715296503)
            ·
              refine ⟨22651787325003332572944755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15101191550002221715296503 22651787325003332572944755)
              ·
                refine ⟨33977680987504998859417133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22651787325003332572944755 33977680987504998859417133)
                ·
                  refine ⟨12741630370314374572281425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33977680987504998859417133 12741630370314374572281425)
                  ·
                    refine ⟨9556222777735780929211069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12741630370314374572281425 9556222777735780929211069)
                    ·
                      refine ⟨3583583541650917848454151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9556222777735780929211069 3583583541650917848454151)
                      ·
                        rfl

theorem cell23_6979004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_6979004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979004 prefixEnd_6979004 := by exact prefixLift 6979004
  have htrace : WordTrace (prefixWord ++ tailWord_6979004) baseStart_6979004 baseEnd_6979004 := by
    simpa [prefixWord, tailWord_6979004, baseEnd_6979004] using wordTrace_append hprefix tailTrace_6979004
  have hstable : (prefixWord ++ tailWord_6979004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979004).length < 2 ^ (prefixWord ++ tailWord_6979004).sum := by decide
  have hdescent : baseEnd_6979004 < baseStart_6979004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979034 : List Nat := [3, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3]
def baseStart_6979034 : Nat := 118140960795 + 6979034 * 2 ^ 59
def prefixEnd_6979034 : Nat := 4983230072969 + 3 ^ 40 * 6979034 * 2
def baseEnd_6979034 : Nat := 3583598946070552731079013

theorem tailTrace_6979034 : CollatzResearch.WordTrace tailWord_6979034 prefixEnd_6979034 3583598946070552731079013 := by
  unfold tailWord_6979034
  simp only [CollatzResearch.WordTrace]
  refine ⟨63636570449539804239596039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169697521198772811305589437 63636570449539804239596039)
  ·
    refine ⟨95454855674309706359394059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63636570449539804239596039 95454855674309706359394059)
    ·
      refine ⟨143182283511464559539091089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95454855674309706359394059 143182283511464559539091089)
      ·
        refine ⟨107386712633598419654318317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143182283511464559539091089 107386712633598419654318317)
        ·
          refine ⟨40270017237599407370369369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107386712633598419654318317 40270017237599407370369369)
          ·
            refine ⟨30202512928199555527777027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40270017237599407370369369 30202512928199555527777027)
            ·
              refine ⟨45303769392299333291665541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30202512928199555527777027 45303769392299333291665541)
              ·
                refine ⟨8494456761056124992187289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45303769392299333291665541 8494456761056124992187289)
                ·
                  refine ⟨6370842570792093744140467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8494456761056124992187289 6370842570792093744140467)
                  ·
                    refine ⟨9556263856188140616210701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6370842570792093744140467 9556263856188140616210701)
                    ·
                      refine ⟨3583598946070552731079013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9556263856188140616210701 3583598946070552731079013)
                      ·
                        rfl

theorem cell23_6979034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_6979034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979034 prefixEnd_6979034 := by exact prefixLift 6979034
  have htrace : WordTrace (prefixWord ++ tailWord_6979034) baseStart_6979034 baseEnd_6979034 := by
    simpa [prefixWord, tailWord_6979034, baseEnd_6979034] using wordTrace_append hprefix tailTrace_6979034
  have hstable : (prefixWord ++ tailWord_6979034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979034).length < 2 ^ (prefixWord ++ tailWord_6979034).sum := by decide
  have hdescent : baseEnd_6979034 < baseStart_6979034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979061 : List Nat := [1, 3, 5, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_6979061 : Nat := 118140960795 + 6979061 * 2 ^ 59
def prefixEnd_6979061 : Nat := 4983230072969 + 3 ^ 40 * 6979061 * 2
def baseEnd_6979061 : Nat := 3583612810048224125441389

theorem tailTrace_6979061 : CollatzResearch.WordTrace tailWord_6979061 prefixEnd_6979061 3583612810048224125441389 := by
  unfold tailWord_6979061
  simp only [CollatzResearch.WordTrace]
  refine ⟨254547266569061400569617037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169698177712707600379744691 254547266569061400569617037)
  ·
    refine ⟨95455224963398025213606389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254547266569061400569617037 95455224963398025213606389)
    ·
      refine ⟨8948927340318564863775599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95455224963398025213606389 8948927340318564863775599)
      ·
        refine ⟨13423391010477847295663399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8948927340318564863775599 13423391010477847295663399)
        ·
          refine ⟨20135086515716770943495099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13423391010477847295663399 20135086515716770943495099)
          ·
            refine ⟨30202629773575156415242649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20135086515716770943495099 30202629773575156415242649)
            ·
              refine ⟨22651972330181367311431987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30202629773575156415242649 22651972330181367311431987)
              ·
                refine ⟨33977958495272050967147981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22651972330181367311431987 33977958495272050967147981)
                ·
                  refine ⟨12741734435727019112680493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33977958495272050967147981 12741734435727019112680493)
                  ·
                    refine ⟨4778150413397632167255185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12741734435727019112680493 4778150413397632167255185)
                    ·
                      refine ⟨3583612810048224125441389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4778150413397632167255185 3583612810048224125441389)
                      ·
                        rfl

theorem cell23_6979061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_6979061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979061 prefixEnd_6979061 := by exact prefixLift 6979061
  have htrace : WordTrace (prefixWord ++ tailWord_6979061) baseStart_6979061 baseEnd_6979061 := by
    simpa [prefixWord, tailWord_6979061, baseEnd_6979061] using wordTrace_append hprefix tailTrace_6979061
  have hstable : (prefixWord ++ tailWord_6979061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979061).length < 2 ^ (prefixWord ++ tailWord_6979061).sum := by decide
  have hdescent : baseEnd_6979061 < baseStart_6979061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979091 : List Nat := [1, 1, 1, 2, 1, 6, 3, 2, 2, 2, 2]
def baseStart_6979091 : Nat := 118140960795 + 6979091 * 2 ^ 59
def prefixEnd_6979091 : Nat := 4983230072969 + 3 ^ 40 * 6979091 * 2
def baseEnd_6979091 : Nat := 3583628214467859008066251

theorem tailTrace_6979091 : CollatzResearch.WordTrace tailWord_6979091 prefixEnd_6979091 3583628214467859008066251 := by
  unfold tailWord_6979091
  simp only [CollatzResearch.WordTrace]
  refine ⟨254548360758952715693209127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169698907172635143795472751 254548360758952715693209127)
  ·
    refine ⟨381822541138429073539813691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254548360758952715693209127 381822541138429073539813691)
    ·
      refine ⟨572733811707643610309720537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381822541138429073539813691 572733811707643610309720537)
      ·
        refine ⟨429550358780732707732290403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 572733811707643610309720537 429550358780732707732290403)
        ·
          refine ⟨644325538171099061598435605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429550358780732707732290403 644325538171099061598435605)
          ·
            refine ⟨30202759601770268512426669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 644325538171099061598435605 30202759601770268512426669)
            ·
              refine ⟨11326034850663850692160001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30202759601770268512426669 11326034850663850692160001)
              ·
                refine ⟨8494526137997888019120001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11326034850663850692160001 8494526137997888019120001)
                ·
                  refine ⟨6370894603498416014340001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8494526137997888019120001 6370894603498416014340001)
                  ·
                    refine ⟨4778170952623812010755001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6370894603498416014340001 4778170952623812010755001)
                    ·
                      refine ⟨3583628214467859008066251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4778170952623812010755001 3583628214467859008066251)
                      ·
                        rfl

theorem cell23_6979091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2, 2, 2].length) (baseStart_6979091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979091 prefixEnd_6979091 := by exact prefixLift 6979091
  have htrace : WordTrace (prefixWord ++ tailWord_6979091) baseStart_6979091 baseEnd_6979091 := by
    simpa [prefixWord, tailWord_6979091, baseEnd_6979091] using wordTrace_append hprefix tailTrace_6979091
  have hstable : (prefixWord ++ tailWord_6979091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979091).length < 2 ^ (prefixWord ++ tailWord_6979091).sum := by decide
  have hdescent : baseEnd_6979091 < baseStart_6979091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979102 : List Nat := [4, 3, 3, 1, 2, 1, 1, 1, 1, 3, 3]
def baseStart_6979102 : Nat := 118140960795 + 6979102 * 2 ^ 59
def prefixEnd_6979102 : Nat := 4983230072969 + 3 ^ 40 * 6979102 * 2
def baseEnd_6979102 : Nat := 3583633862755058465028701

theorem tailTrace_6979102 : CollatzResearch.WordTrace tailWord_6979102 prefixEnd_6979102 3583633862755058465028701 := by
  unfold tailWord_6979102
  simp only [CollatzResearch.WordTrace]
  refine ⟨31818595245239108071482445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169699174641275243047906373 31818595245239108071482445)
  ·
    refine ⟨11931973216964665526805917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31818595245239108071482445 11931973216964665526805917)
    ·
      refine ⟨4474489956361749572552219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11931973216964665526805917 4474489956361749572552219)
      ·
        refine ⟨6711734934542624358828329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4474489956361749572552219 6711734934542624358828329)
        ·
          refine ⟨5033801200906968269121247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6711734934542624358828329 5033801200906968269121247)
          ·
            refine ⟨7550701801360452403681871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5033801200906968269121247 7550701801360452403681871)
            ·
              refine ⟨11326052702040678605522807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7550701801360452403681871 11326052702040678605522807)
              ·
                refine ⟨16989079053061017908284211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11326052702040678605522807 16989079053061017908284211)
                ·
                  refine ⟨25483618579591526862426317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16989079053061017908284211 25483618579591526862426317)
                  ·
                    refine ⟨9556356967346822573409869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25483618579591526862426317 9556356967346822573409869)
                    ·
                      refine ⟨3583633862755058465028701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9556356967346822573409869 3583633862755058465028701)
                      ·
                        rfl

theorem cell23_6979102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_6979102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979102 prefixEnd_6979102 := by exact prefixLift 6979102
  have htrace : WordTrace (prefixWord ++ tailWord_6979102) baseStart_6979102 baseEnd_6979102 := by
    simpa [prefixWord, tailWord_6979102, baseEnd_6979102] using wordTrace_append hprefix tailTrace_6979102
  have hstable : (prefixWord ++ tailWord_6979102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979102).length < 2 ^ (prefixWord ++ tailWord_6979102).sum := by decide
  have hdescent : baseEnd_6979102 < baseStart_6979102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979120 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 5]
def baseStart_6979120 : Nat := 118140960795 + 6979120 * 2 ^ 59
def prefixEnd_6979120 : Nat := 4983230072969 + 3 ^ 40 * 6979120 * 2
def baseEnd_6979120 : Nat := 3583643105406839394603617

theorem tailTrace_6979120 : CollatzResearch.WordTrace tailWord_6979120 prefixEnd_6979120 3583643105406839394603617 := by
  unfold tailWord_6979120
  simp only [CollatzResearch.WordTrace]
  refine ⟨127274709237923826823007407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169699612317231769097343209 127274709237923826823007407)
  ·
    refine ⟨190912063856885740234511111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127274709237923826823007407 190912063856885740234511111)
    ·
      refine ⟨286368095785328610351766667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190912063856885740234511111 286368095785328610351766667)
      ·
        refine ⟨429552143677992915527650001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286368095785328610351766667 429552143677992915527650001)
        ·
          refine ⟨322164107758494686645737501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429552143677992915527650001 322164107758494686645737501)
          ·
            refine ⟨120811540409435507492151563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322164107758494686645737501 120811540409435507492151563)
            ·
              refine ⟨181217310614153261238227345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120811540409435507492151563 181217310614153261238227345)
              ·
                refine ⟨135912982960614945928670509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181217310614153261238227345 135912982960614945928670509)
                ·
                  refine ⟨50967368610230604723251441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135912982960614945928670509 50967368610230604723251441)
                  ·
                    refine ⟨38225526457672953542438581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50967368610230604723251441 38225526457672953542438581)
                    ·
                      refine ⟨3583643105406839394603617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38225526457672953542438581 3583643105406839394603617)
                      ·
                        rfl

theorem cell23_6979120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 5].length) (baseStart_6979120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979120 prefixEnd_6979120 := by exact prefixLift 6979120
  have htrace : WordTrace (prefixWord ++ tailWord_6979120) baseStart_6979120 baseEnd_6979120 := by
    simpa [prefixWord, tailWord_6979120, baseEnd_6979120] using wordTrace_append hprefix tailTrace_6979120
  have hstable : (prefixWord ++ tailWord_6979120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979120).length < 2 ^ (prefixWord ++ tailWord_6979120).sum := by decide
  have hdescent : baseEnd_6979120 < baseStart_6979120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979137 : List Nat := [1, 2, 5, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_6979137 : Nat := 118140960795 + 6979137 * 2 ^ 59
def prefixEnd_6979137 : Nat := 4983230072969 + 3 ^ 40 * 6979137 * 2
def baseEnd_6979137 : Nat := 3583651834577965828091039

theorem tailTrace_6979137 : CollatzResearch.WordTrace tailWord_6979137 prefixEnd_6979137 3583651834577965828091039 := by
  unfold tailWord_6979137
  simp only [CollatzResearch.WordTrace]
  refine ⟨254550038516786065549383665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169700025677857377032922443 254550038516786065549383665)
  ·
    refine ⟨190912528887589549162037749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254550038516786065549383665 190912528887589549162037749)
    ·
      refine ⟨17898049583211520233941039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 190912528887589549162037749 17898049583211520233941039)
      ·
        refine ⟨26847074374817280350911559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17898049583211520233941039 26847074374817280350911559)
        ·
          refine ⟨40270611562225920526367339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26847074374817280350911559 40270611562225920526367339)
          ·
            refine ⟨60405917343338880789551009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40270611562225920526367339 60405917343338880789551009)
            ·
              refine ⟨45304438007504160592163257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60405917343338880789551009 45304438007504160592163257)
              ·
                refine ⟨33978328505628120444122443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45304438007504160592163257 33978328505628120444122443)
                ·
                  refine ⟨50967492758442180666183665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33978328505628120444122443 50967492758442180666183665)
                  ·
                    refine ⟨38225619568831635499637749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50967492758442180666183665 38225619568831635499637749)
                    ·
                      refine ⟨3583651834577965828091039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38225619568831635499637749 3583651834577965828091039)
                      ·
                        rfl

theorem cell23_6979137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_6979137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979137 prefixEnd_6979137 := by exact prefixLift 6979137
  have htrace : WordTrace (prefixWord ++ tailWord_6979137) baseStart_6979137 baseEnd_6979137 := by
    simpa [prefixWord, tailWord_6979137, baseEnd_6979137] using wordTrace_append hprefix tailTrace_6979137
  have hstable : (prefixWord ++ tailWord_6979137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979137).length < 2 ^ (prefixWord ++ tailWord_6979137).sum := by decide
  have hdescent : baseEnd_6979137 < baseStart_6979137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979181 : List Nat := [1, 5, 1, 1, 4, 1, 2, 1, 2, 1, 4]
def baseStart_6979181 : Nat := 118140960795 + 6979181 * 2 ^ 59
def prefixEnd_6979181 : Nat := 4983230072969 + 3 ^ 40 * 6979181 * 2
def baseEnd_6979181 : Nat := 3583674427726763655940837

theorem tailTrace_6979181 : CollatzResearch.WordTrace tailWord_6979181 prefixEnd_6979181 3583674427726763655940837 := by
  unfold tailWord_6979181
  simp only [CollatzResearch.WordTrace]
  refine ⟨254551643328626661063985397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169701095552417774042656931 254551643328626661063985397)
  ·
    refine ⟨23864216562058749474748631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 254551643328626661063985397 23864216562058749474748631)
    ·
      refine ⟨35796324843088124212122947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23864216562058749474748631 35796324843088124212122947)
      ·
        refine ⟨53694487264632186318184421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35796324843088124212122947 53694487264632186318184421)
        ·
          refine ⟨10067716362118534934659579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53694487264632186318184421 10067716362118534934659579)
          ·
            refine ⟨15101574543177802401989369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10067716362118534934659579 15101574543177802401989369)
            ·
              refine ⟨11326180907383351801492027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15101574543177802401989369 11326180907383351801492027)
              ·
                refine ⟨16989271361075027702238041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11326180907383351801492027 16989271361075027702238041)
                ·
                  refine ⟨12741953520806270776678531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16989271361075027702238041 12741953520806270776678531)
                  ·
                    refine ⟨19112930281209406165017797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12741953520806270776678531 19112930281209406165017797)
                    ·
                      refine ⟨3583674427726763655940837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19112930281209406165017797 3583674427726763655940837)
                      ·
                        rfl

theorem cell23_6979181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_6979181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979181 prefixEnd_6979181 := by exact prefixLift 6979181
  have htrace : WordTrace (prefixWord ++ tailWord_6979181) baseStart_6979181 baseEnd_6979181 := by
    simpa [prefixWord, tailWord_6979181, baseEnd_6979181] using wordTrace_append hprefix tailTrace_6979181
  have hstable : (prefixWord ++ tailWord_6979181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979181).length < 2 ^ (prefixWord ++ tailWord_6979181).sum := by decide
  have hdescent : baseEnd_6979181 < baseStart_6979181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979184 : List Nat := [2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 3]
def baseStart_6979184 : Nat := 118140960795 + 6979184 * 2 ^ 59
def prefixEnd_6979184 : Nat := 4983230072969 + 3 ^ 40 * 6979184 * 2
def baseEnd_6979184 : Nat := 3583675968168727144203323

theorem tailTrace_6979184 : CollatzResearch.WordTrace tailWord_6979184 prefixEnd_6979184 3583675968168727144203323 := by
  unfold tailWord_6979184
  simp only [CollatzResearch.WordTrace]
  refine ⟨127275876373807896288172303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169701168498410528384229737 127275876373807896288172303)
  ·
    refine ⟨190913814560711844432258455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127275876373807896288172303 190913814560711844432258455)
    ·
      refine ⟨286370721841067766648387683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190913814560711844432258455 286370721841067766648387683)
      ·
        refine ⟨429556082761601649972581525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286370721841067766648387683 429556082761601649972581525)
        ·
          refine ⟨20135441379450077342464759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 429556082761601649972581525 20135441379450077342464759)
          ·
            refine ⟨30203162069175116013697139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20135441379450077342464759 30203162069175116013697139)
            ·
              refine ⟨45304743103762674020545709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30203162069175116013697139 45304743103762674020545709)
              ·
                refine ⟨16989278663911002757704641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45304743103762674020545709 16989278663911002757704641)
                ·
                  refine ⟨12741958997933252068278481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16989278663911002757704641 12741958997933252068278481)
                  ·
                    refine ⟨9556469248449939051208861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12741958997933252068278481 9556469248449939051208861)
                    ·
                      refine ⟨3583675968168727144203323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9556469248449939051208861 3583675968168727144203323)
                      ·
                        rfl

theorem cell23_6979184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 3].length) (baseStart_6979184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979184 prefixEnd_6979184 := by exact prefixLift 6979184
  have htrace : WordTrace (prefixWord ++ tailWord_6979184) baseStart_6979184 baseEnd_6979184 := by
    simpa [prefixWord, tailWord_6979184, baseEnd_6979184] using wordTrace_append hprefix tailTrace_6979184
  have hstable : (prefixWord ++ tailWord_6979184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979184).length < 2 ^ (prefixWord ++ tailWord_6979184).sum := by decide
  have hdescent : baseEnd_6979184 < baseStart_6979184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979247 : List Nat := [1, 1, 2, 1, 2, 4, 1, 4, 1, 6]
def baseStart_6979247 : Nat := 118140960795 + 6979247 * 2 ^ 59
def prefixEnd_6979247 : Nat := 4983230072969 + 3 ^ 40 * 6979247 * 2
def baseEnd_6979247 : Nat := 1194569439149986799238511

theorem tailTrace_6979247 : CollatzResearch.WordTrace tailWord_6979247 prefixEnd_6979247 1194569439149986799238511 := by
  unfold tailWord_6979247
  simp only [CollatzResearch.WordTrace]
  refine ⟨254554050546387554335887995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169702700364258369557258663 254554050546387554335887995)
  ·
    refine ⟨381831075819581331503831993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254554050546387554335887995 381831075819581331503831993)
    ·
      refine ⟨286373306864685998627873995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381831075819581331503831993 286373306864685998627873995)
      ·
        refine ⟨429559960297028997941810993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286373306864685998627873995 429559960297028997941810993)
        ·
          refine ⟨322169970222771748456358245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429559960297028997941810993 322169970222771748456358245)
          ·
            refine ⟨60406869416769702835567171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 322169970222771748456358245 60406869416769702835567171)
            ·
              refine ⟨90610304125154554253350757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60406869416769702835567171 90610304125154554253350757)
              ·
                refine ⟨16989432023466478922503267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90610304125154554253350757 16989432023466478922503267)
                ·
                  refine ⟨25484148035199718383754901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16989432023466478922503267 25484148035199718383754901)
                  ·
                    refine ⟨1194569439149986799238511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25484148035199718383754901 1194569439149986799238511)
                    ·
                      rfl

theorem cell23_6979247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 6].length) (baseStart_6979247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979247 prefixEnd_6979247 := by exact prefixLift 6979247
  have htrace : WordTrace (prefixWord ++ tailWord_6979247) baseStart_6979247 baseEnd_6979247 := by
    simpa [prefixWord, tailWord_6979247, baseEnd_6979247] using wordTrace_append hprefix tailTrace_6979247
  have hstable : (prefixWord ++ tailWord_6979247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979247).length < 2 ^ (prefixWord ++ tailWord_6979247).sum := by decide
  have hdescent : baseEnd_6979247 < baseStart_6979247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979264 : List Nat := [2, 1, 1, 2, 4, 1, 3, 1, 4, 4]
def baseStart_6979264 : Nat := 118140960795 + 6979264 * 2 ^ 59
def prefixEnd_6979264 : Nat := 4983230072969 + 3 ^ 40 * 6979264 * 2
def baseEnd_6979264 : Nat := 1194572348873695610400985

theorem tailTrace_6979264 : CollatzResearch.WordTrace tailWord_6979264 prefixEnd_6979264 1194572348873695610400985 := by
  unfold tailWord_6979264
  simp only [CollatzResearch.WordTrace]
  refine ⟨127277335293662983119628423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169703113724883977492837897 127277335293662983119628423)
  ·
    refine ⟨190916002940494474679442635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127277335293662983119628423 190916002940494474679442635)
    ·
      refine ⟨286374004410741712019163953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190916002940494474679442635 286374004410741712019163953)
      ·
        refine ⟨214780503308056284014372965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286374004410741712019163953 214780503308056284014372965)
        ·
          refine ⟨40271344370260553252694931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214780503308056284014372965 40271344370260553252694931)
          ·
            refine ⟨60407016555390829879042397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40271344370260553252694931 60407016555390829879042397)
            ·
              refine ⟨22652631208271561204640899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60407016555390829879042397 22652631208271561204640899)
              ·
                refine ⟨33978946812407341806961349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22652631208271561204640899 33978946812407341806961349)
                ·
                  refine ⟨6371052527326376588805253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33978946812407341806961349 6371052527326376588805253)
                  ·
                    refine ⟨1194572348873695610400985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6371052527326376588805253 1194572348873695610400985)
                    ·
                      rfl

theorem cell23_6979264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 4, 4].length) (baseStart_6979264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979264 prefixEnd_6979264 := by exact prefixLift 6979264
  have htrace : WordTrace (prefixWord ++ tailWord_6979264) baseStart_6979264 baseEnd_6979264 := by
    simpa [prefixWord, tailWord_6979264, baseEnd_6979264] using wordTrace_append hprefix tailTrace_6979264
  have hstable : (prefixWord ++ tailWord_6979264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979264).length < 2 ^ (prefixWord ++ tailWord_6979264).sum := by decide
  have hdescent : baseEnd_6979264 < baseStart_6979264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979337 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 1, 8]
def baseStart_6979337 : Nat := 118140960795 + 6979337 * 2 ^ 59
def prefixEnd_6979337 : Nat := 4983230072969 + 3 ^ 40 * 6979337 * 2
def baseEnd_6979337 : Nat := 1194584843569621681863373

theorem tailTrace_6979337 : CollatzResearch.WordTrace tailWord_6979337 prefixEnd_6979337 1194584843569621681863373 := by
  unfold tailWord_6979337
  simp only [CollatzResearch.WordTrace]
  refine ⟨254557333116061499706664265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169704888744040999804442843 254557333116061499706664265)
  ·
    refine ⟨190917999837046124779998199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254557333116061499706664265 190917999837046124779998199)
    ·
      refine ⟨286376999755569187169997299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190917999837046124779998199 286376999755569187169997299)
      ·
        refine ⟨429565499633353780754995949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286376999755569187169997299 429565499633353780754995949)
        ·
          refine ⟨161087062362507667783123481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 429565499633353780754995949 161087062362507667783123481)
          ·
            refine ⟨120815296771880750837342611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161087062362507667783123481 120815296771880750837342611)
            ·
              refine ⟨181222945157821126256013917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120815296771880750837342611 181222945157821126256013917)
              ·
                refine ⟨67958604434182922346005219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181222945157821126256013917 67958604434182922346005219)
                ·
                  refine ⟨101937906651274383519007829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67958604434182922346005219 101937906651274383519007829)
                  ·
                    refine ⟨1194584843569621681863373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101937906651274383519007829 1194584843569621681863373)
                    ·
                      rfl

theorem cell23_6979337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 8].length) (baseStart_6979337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979337 prefixEnd_6979337 := by exact prefixLift 6979337
  have htrace : WordTrace (prefixWord ++ tailWord_6979337) baseStart_6979337 baseEnd_6979337 := by
    simpa [prefixWord, tailWord_6979337, baseEnd_6979337] using wordTrace_append hprefix tailTrace_6979337
  have hstable : (prefixWord ++ tailWord_6979337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979337).length < 2 ^ (prefixWord ++ tailWord_6979337).sum := by decide
  have hdescent : baseEnd_6979337 < baseStart_6979337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979338 : List Nat := [3, 1, 2, 2, 1, 4, 1, 3, 2, 1, 3]
def baseStart_6979338 : Nat := 118140960795 + 6979338 * 2 ^ 59
def prefixEnd_6979338 : Nat := 4983230072969 + 3 ^ 40 * 6979338 * 2
def baseEnd_6979338 : Nat := 3583755044189519541677615

theorem tailTrace_6979338 : CollatzResearch.WordTrace tailWord_6979338 prefixEnd_6979338 3583755044189519541677615 := by
  unfold tailWord_6979338
  simp only [CollatzResearch.WordTrace]
  refine ⟨63639342397264469219362667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169704913059371917918300445 63639342397264469219362667)
  ·
    refine ⟨95459013595896703829044001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63639342397264469219362667 95459013595896703829044001)
    ·
      refine ⟨71594260196922527871783001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95459013595896703829044001 71594260196922527871783001)
      ·
        refine ⟨53695695147691895903837251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71594260196922527871783001 53695695147691895903837251)
        ·
          refine ⟨80543542721537843855755877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53695695147691895903837251 80543542721537843855755877)
          ·
            refine ⟨15101914260288345722954227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80543542721537843855755877 15101914260288345722954227)
            ·
              refine ⟨22652871390432518584431341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15101914260288345722954227 22652871390432518584431341)
              ·
                refine ⟨8494826771412194469161753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22652871390432518584431341 8494826771412194469161753)
                ·
                  refine ⟨6371120078559145851871315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8494826771412194469161753 6371120078559145851871315)
                  ·
                    refine ⟨9556680117838718777806973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6371120078559145851871315 9556680117838718777806973)
                    ·
                      refine ⟨3583755044189519541677615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9556680117838718777806973 3583755044189519541677615)
                      ·
                        rfl

theorem cell23_6979338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_6979338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979338 prefixEnd_6979338 := by exact prefixLift 6979338
  have htrace : WordTrace (prefixWord ++ tailWord_6979338) baseStart_6979338 baseEnd_6979338 := by
    simpa [prefixWord, tailWord_6979338, baseEnd_6979338] using wordTrace_append hprefix tailTrace_6979338
  have hstable : (prefixWord ++ tailWord_6979338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979338).length < 2 ^ (prefixWord ++ tailWord_6979338).sum := by decide
  have hdescent : baseEnd_6979338 < baseStart_6979338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979361 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 3, 4, 2]
def baseStart_6979361 : Nat := 118140960795 + 6979361 * 2 ^ 59
def prefixEnd_6979361 : Nat := 4983230072969 + 3 ^ 40 * 6979361 * 2
def baseEnd_6979361 : Nat := 3583766854244572951690009

theorem tailTrace_6979361 : CollatzResearch.WordTrace tailWord_6979361 prefixEnd_6979361 3583766854244572951690009 := by
  unfold tailWord_6979361
  simp only [CollatzResearch.WordTrace]
  refine ⟨254558208467974551805537937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169705472311983034537025291 254558208467974551805537937)
  ·
    refine ⟨190918656350980913854153453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254558208467974551805537937 190918656350980913854153453)
    ·
      refine ⟨71594496131617842695307545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190918656350980913854153453 71594496131617842695307545)
      ·
        refine ⟨53695872098713382021480659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71594496131617842695307545 53695872098713382021480659)
        ·
          refine ⟨80543808148070073032220989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53695872098713382021480659 80543808148070073032220989)
          ·
            refine ⟨30203928055526277387082871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80543808148070073032220989 30203928055526277387082871)
            ·
              refine ⟨45305892083289416080624307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30203928055526277387082871 45305892083289416080624307)
              ·
                refine ⟨67958838124934124120936461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45305892083289416080624307 67958838124934124120936461)
                ·
                  refine ⟨25484564296850296545351173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67958838124934124120936461 25484564296850296545351173)
                  ·
                    refine ⟨4778355805659430602253345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25484564296850296545351173 4778355805659430602253345)
                    ·
                      refine ⟨3583766854244572951690009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4778355805659430602253345 3583766854244572951690009)
                      ·
                        rfl

theorem cell23_6979361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_6979361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979361 prefixEnd_6979361 := by exact prefixLift 6979361
  have htrace : WordTrace (prefixWord ++ tailWord_6979361) baseStart_6979361 baseEnd_6979361 := by
    simpa [prefixWord, tailWord_6979361, baseEnd_6979361] using wordTrace_append hprefix tailTrace_6979361
  have hstable : (prefixWord ++ tailWord_6979361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979361).length < 2 ^ (prefixWord ++ tailWord_6979361).sum := by decide
  have hdescent : baseEnd_6979361 < baseStart_6979361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979365 : List Nat := [1, 3, 1, 2, 3, 3, 3, 1, 1, 3, 2]
def baseStart_6979365 : Nat := 118140960795 + 6979365 * 2 ^ 59
def prefixEnd_6979365 : Nat := 4983230072969 + 3 ^ 40 * 6979365 * 2
def baseEnd_6979365 : Nat := 3583768908167190936039991

theorem tailTrace_6979365 : CollatzResearch.WordTrace tailWord_6979365 prefixEnd_6979365 3583768908167190936039991 := by
  unfold tailWord_6979365
  simp only [CollatzResearch.WordTrace]
  refine ⟨254558354359960060488683549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169705569573306706992455699 254558354359960060488683549)
  ·
    refine ⟨95459382884985022683256331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254558354359960060488683549 95459382884985022683256331)
    ·
      refine ⟨143189074327477534024884497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95459382884985022683256331 143189074327477534024884497)
      ·
        refine ⟨107391805745608150518663373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143189074327477534024884497 107391805745608150518663373)
        ·
          refine ⟨40271927154603056444498765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107391805745608150518663373 40271927154603056444498765)
          ·
            refine ⟨15101972682976146166687037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40271927154603056444498765 15101972682976146166687037)
            ·
              refine ⟨5663239756116054812507639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15101972682976146166687037 5663239756116054812507639)
              ·
                refine ⟨8494859634174082218761459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5663239756116054812507639 8494859634174082218761459)
                ·
                  refine ⟨12742289451261123328142189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8494859634174082218761459 12742289451261123328142189)
                  ·
                    refine ⟨4778358544222921248053321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12742289451261123328142189 4778358544222921248053321)
                    ·
                      refine ⟨3583768908167190936039991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4778358544222921248053321 3583768908167190936039991)
                      ·
                        rfl

theorem cell23_6979365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 1, 3, 2].length) (baseStart_6979365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979365 prefixEnd_6979365 := by exact prefixLift 6979365
  have htrace : WordTrace (prefixWord ++ tailWord_6979365) baseStart_6979365 baseEnd_6979365 := by
    simpa [prefixWord, tailWord_6979365, baseEnd_6979365] using wordTrace_append hprefix tailTrace_6979365
  have hstable : (prefixWord ++ tailWord_6979365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979365).length < 2 ^ (prefixWord ++ tailWord_6979365).sum := by decide
  have hdescent : baseEnd_6979365 < baseStart_6979365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979391 : List Nat := [1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 4]
def baseStart_6979391 : Nat := 118140960795 + 6979391 * 2 ^ 59
def prefixEnd_6979391 : Nat := 4983230072969 + 3 ^ 40 * 6979391 * 2
def baseEnd_6979391 : Nat := 3583782258664207834314871

theorem tailTrace_6979391 : CollatzResearch.WordTrace tailWord_6979391 prefixEnd_6979391 3583782258664207834314871 := by
  unfold tailWord_6979391
  simp only [CollatzResearch.WordTrace]
  refine ⟨254559302657865866929130027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169706201771910577952753351 254559302657865866929130027)
  ·
    refine ⟨381838953986798800393695041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254559302657865866929130027 381838953986798800393695041)
    ·
      refine ⟨286379215490099100295271281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381838953986798800393695041 286379215490099100295271281)
      ·
        refine ⟨214784411617574325221453461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286379215490099100295271281 214784411617574325221453461)
        ·
          refine ⟨10068019294573796494755631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 214784411617574325221453461 10068019294573796494755631)
          ·
            refine ⟨15102028941860694742133447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10068019294573796494755631 15102028941860694742133447)
            ·
              refine ⟨22653043412791042113200171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15102028941860694742133447 22653043412791042113200171)
              ·
                refine ⟨33979565119186563169800257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22653043412791042113200171 33979565119186563169800257)
                ·
                  refine ⟨25484673839389922377350193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33979565119186563169800257 25484673839389922377350193)
                  ·
                    refine ⟨19113505379542441783012645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25484673839389922377350193 19113505379542441783012645)
                    ·
                      refine ⟨3583782258664207834314871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19113505379542441783012645 3583782258664207834314871)
                      ·
                        rfl

theorem cell23_6979391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 4].length) (baseStart_6979391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979391 prefixEnd_6979391 := by exact prefixLift 6979391
  have htrace : WordTrace (prefixWord ++ tailWord_6979391) baseStart_6979391 baseEnd_6979391 := by
    simpa [prefixWord, tailWord_6979391, baseEnd_6979391] using wordTrace_append hprefix tailTrace_6979391
  have hstable : (prefixWord ++ tailWord_6979391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979391).length < 2 ^ (prefixWord ++ tailWord_6979391).sum := by decide
  have hdescent : baseEnd_6979391 < baseStart_6979391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979461 : List Nat := [1, 3, 1, 1, 3, 2, 1, 4, 3, 4]
def baseStart_6979461 : Nat := 118140960795 + 6979461 * 2 ^ 59
def prefixEnd_6979461 : Nat := 4983230072969 + 3 ^ 40 * 6979461 * 2
def baseEnd_6979461 : Nat := 1194606067436674186813183

theorem tailTrace_6979461 : CollatzResearch.WordTrace tailWord_6979461 prefixEnd_6979461 1194606067436674186813183 := by
  unfold tailWord_6979461
  simp only [CollatzResearch.WordTrace]
  refine ⟨254561855767612268884178237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169707903845074845922785491 254561855767612268884178237)
  ·
    refine ⟨95460695912854600831566839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254561855767612268884178237 95460695912854600831566839)
    ·
      refine ⟨143191043869281901247350259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95460695912854600831566839 143191043869281901247350259)
      ·
        refine ⟨214786565803922851871025389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143191043869281901247350259 214786565803922851871025389)
        ·
          refine ⟨80544962176471069451634521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214786565803922851871025389 80544962176471069451634521)
          ·
            refine ⟨60408721632353302088725891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80544962176471069451634521 60408721632353302088725891)
            ·
              refine ⟨90613082448529953133088837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60408721632353302088725891 90613082448529953133088837)
              ·
                refine ⟨16989952959099366212454157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90613082448529953133088837 16989952959099366212454157)
                ·
                  refine ⟨6371232359662262329670309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16989952959099366212454157 6371232359662262329670309)
                  ·
                    refine ⟨1194606067436674186813183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6371232359662262329670309 1194606067436674186813183)
                    ·
                      rfl

theorem cell23_6979461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3, 4].length) (baseStart_6979461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979461 prefixEnd_6979461 := by exact prefixLift 6979461
  have htrace : WordTrace (prefixWord ++ tailWord_6979461) baseStart_6979461 baseEnd_6979461 := by
    simpa [prefixWord, tailWord_6979461, baseEnd_6979461] using wordTrace_append hprefix tailTrace_6979461
  have hstable : (prefixWord ++ tailWord_6979461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979461).length < 2 ^ (prefixWord ++ tailWord_6979461).sum := by decide
  have hdescent : baseEnd_6979461 < baseStart_6979461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979495 : List Nat := [1, 1, 6, 1, 2, 3, 1, 1, 3, 4]
def baseStart_6979495 : Nat := 118140960795 + 6979495 * 2 ^ 59
def prefixEnd_6979495 : Nat := 4983230072969 + 3 ^ 40 * 6979495 * 2
def baseEnd_6979495 : Nat := 1194611886884091809138131

theorem tailTrace_6979495 : CollatzResearch.WordTrace tailWord_6979495 prefixEnd_6979495 1194611886884091809138131 := by
  unfold tailWord_6979495
  simp only [CollatzResearch.WordTrace]
  refine ⟨254563095849489092690915939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169708730566326061793943959 254563095849489092690915939)
  ·
    refine ⟨381844643774233639036373909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254563095849489092690915939 381844643774233639036373909)
    ·
      refine ⟨17898967676917201829830027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 381844643774233639036373909 17898967676917201829830027)
      ·
        refine ⟨26848451515375802744745041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17898967676917201829830027 26848451515375802744745041)
        ·
          refine ⟨20136338636531852058558781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26848451515375802744745041 20136338636531852058558781)
          ·
            refine ⟨7551126988699444521959543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20136338636531852058558781 7551126988699444521959543)
            ·
              refine ⟨11326690483049166782939315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7551126988699444521959543 11326690483049166782939315)
              ·
                refine ⟨16990035724573750174408973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11326690483049166782939315 16990035724573750174408973)
                ·
                  refine ⟨6371263396715156315403365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16990035724573750174408973 6371263396715156315403365)
                  ·
                    refine ⟨1194611886884091809138131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6371263396715156315403365 1194611886884091809138131)
                    ·
                      rfl

theorem cell23_6979495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_6979495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979495 prefixEnd_6979495 := by exact prefixLift 6979495
  have htrace : WordTrace (prefixWord ++ tailWord_6979495) baseStart_6979495 baseEnd_6979495 := by
    simpa [prefixWord, tailWord_6979495, baseEnd_6979495] using wordTrace_append hprefix tailTrace_6979495
  have hstable : (prefixWord ++ tailWord_6979495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979495).length < 2 ^ (prefixWord ++ tailWord_6979495).sum := by decide
  have hdescent : baseEnd_6979495 < baseStart_6979495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979514 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7]
def baseStart_6979514 : Nat := 118140960795 + 6979514 * 2 ^ 59
def prefixEnd_6979514 : Nat := 4983230072969 + 3 ^ 40 * 6979514 * 2
def baseEnd_6979514 : Nat := 3583845416784710853076805

theorem tailTrace_6979514 : CollatzResearch.WordTrace tailWord_6979514 prefixEnd_6979514 3583845416784710853076805 := by
  unfold tailWord_6979514
  simp only [CollatzResearch.WordTrace]
  refine ⟨63640947209105064733964399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169709192557613505957238397 63640947209105064733964399)
  ·
    refine ⟨95461420813657597100946599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63640947209105064733964399 95461420813657597100946599)
    ·
      refine ⟨143192131220486395651419899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95461420813657597100946599 143192131220486395651419899)
      ·
        refine ⟨214788196830729593477129849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143192131220486395651419899 214788196830729593477129849)
        ·
          refine ⟨161091147623047195107847387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214788196830729593477129849 161091147623047195107847387)
          ·
            refine ⟨241636721434570792661771081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161091147623047195107847387 241636721434570792661771081)
            ·
              refine ⟨181227541075928094496328311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241636721434570792661771081 181227541075928094496328311)
              ·
                refine ⟨271841311613892141744492467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181227541075928094496328311 271841311613892141744492467)
                ·
                  refine ⟨407761967420838212616738701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 271841311613892141744492467 407761967420838212616738701)
                  ·
                    refine ⟨152910737782814329731277013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 407761967420838212616738701 152910737782814329731277013)
                    ·
                      refine ⟨3583845416784710853076805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152910737782814329731277013 3583845416784710853076805)
                      ·
                        rfl

theorem cell23_6979514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_6979514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979514 prefixEnd_6979514 := by exact prefixLift 6979514
  have htrace : WordTrace (prefixWord ++ tailWord_6979514) baseStart_6979514 baseEnd_6979514 := by
    simpa [prefixWord, tailWord_6979514, baseEnd_6979514] using wordTrace_append hprefix tailTrace_6979514
  have hstable : (prefixWord ++ tailWord_6979514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979514).length < 2 ^ (prefixWord ++ tailWord_6979514).sum := by decide
  have hdescent : baseEnd_6979514 < baseStart_6979514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979535 : List Nat := [1, 1, 2, 1, 1, 5, 2, 5, 1, 1, 3]
def baseStart_6979535 : Nat := 118140960795 + 6979535 * 2 ^ 59
def prefixEnd_6979535 : Nat := 4983230072969 + 3 ^ 40 * 6979535 * 2
def baseEnd_6979535 : Nat := 3583856199878455270914209

theorem tailTrace_6979535 : CollatzResearch.WordTrace tailWord_6979535 prefixEnd_6979535 3583856199878455270914209 := by
  unfold tailWord_6979535
  simp only [CollatzResearch.WordTrace]
  refine ⟨254564554769344179522372059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169709703179562786348248039 254564554769344179522372059)
  ·
    refine ⟨381846832154016269283558089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254564554769344179522372059 381846832154016269283558089)
    ·
      refine ⟨286385124115512201962668567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381846832154016269283558089 286385124115512201962668567)
      ·
        refine ⟨429577686173268302944002851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286385124115512201962668567 429577686173268302944002851)
        ·
          refine ⟨644366529259902454416004277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429577686173268302944002851 644366529259902454416004277)
          ·
            refine ⟨60409362118115855101500401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 644366529259902454416004277 60409362118115855101500401)
            ·
              refine ⟨45307021588586891326125301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60409362118115855101500401 45307021588586891326125301)
              ·
                refine ⟨4247533273930021061824247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45307021588586891326125301 4247533273930021061824247)
                ·
                  refine ⟨6371299910895031592736371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4247533273930021061824247 6371299910895031592736371)
                  ·
                    refine ⟨9556949866342547389104557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6371299910895031592736371 9556949866342547389104557)
                    ·
                      refine ⟨3583856199878455270914209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9556949866342547389104557 3583856199878455270914209)
                      ·
                        rfl

theorem cell23_6979535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 5, 1, 1, 3].length) (baseStart_6979535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979535 prefixEnd_6979535 := by exact prefixLift 6979535
  have htrace : WordTrace (prefixWord ++ tailWord_6979535) baseStart_6979535 baseEnd_6979535 := by
    simpa [prefixWord, tailWord_6979535, baseEnd_6979535] using wordTrace_append hprefix tailTrace_6979535
  have hstable : (prefixWord ++ tailWord_6979535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979535).length < 2 ^ (prefixWord ++ tailWord_6979535).sum := by decide
  have hdescent : baseEnd_6979535 < baseStart_6979535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979568 : List Nat := [2, 1, 1, 1, 3, 2, 4, 3, 2, 4]
def baseStart_6979568 : Nat := 118140960795 + 6979568 * 2 ^ 59
def prefixEnd_6979568 : Nat := 4983230072969 + 3 ^ 40 * 6979568 * 2
def baseEnd_6979568 : Nat := 1194624381580017880600519

theorem tailTrace_6979568 : CollatzResearch.WordTrace tailWord_6979568 prefixEnd_6979568 1194624381580017880600519 := by
  unfold tailWord_6979568
  simp only [CollatzResearch.WordTrace]
  refine ⟨127282879189112313079161679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169710505585483084105548905 127282879189112313079161679)
  ·
    refine ⟨190924318783668469618742519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127282879189112313079161679 190924318783668469618742519)
    ·
      refine ⟨286386478175502704428113779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190924318783668469618742519 286386478175502704428113779)
      ·
        refine ⟨429579717263254056642170669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286386478175502704428113779 429579717263254056642170669)
        ·
          refine ⟨161092393973720271240814001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 429579717263254056642170669 161092393973720271240814001)
          ·
            refine ⟨120819295480290203430610501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161092393973720271240814001 120819295480290203430610501)
            ·
              refine ⟨22653617902554413143239469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120819295480290203430610501 22653617902554413143239469)
              ·
                refine ⟨8495106713457904928714801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22653617902554413143239469 8495106713457904928714801)
                ·
                  refine ⟨6371330035093428696536101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8495106713457904928714801 6371330035093428696536101)
                  ·
                    refine ⟨1194624381580017880600519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6371330035093428696536101 1194624381580017880600519)
                    ·
                      rfl

theorem cell23_6979568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 3, 2, 4].length) (baseStart_6979568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979568 prefixEnd_6979568 := by exact prefixLift 6979568
  have htrace : WordTrace (prefixWord ++ tailWord_6979568) baseStart_6979568 baseEnd_6979568 := by
    simpa [prefixWord, tailWord_6979568, baseEnd_6979568] using wordTrace_append hprefix tailTrace_6979568
  have hstable : (prefixWord ++ tailWord_6979568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979568).length < 2 ^ (prefixWord ++ tailWord_6979568).sum := by decide
  have hdescent : baseEnd_6979568 < baseStart_6979568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979635 : List Nat := [1, 1, 1, 2, 4, 1, 3, 4, 1, 3, 2]
def baseStart_6979635 : Nat := 118140960795 + 6979635 * 2 ^ 59
def prefixEnd_6979635 : Nat := 4983230072969 + 3 ^ 40 * 6979635 * 2
def baseEnd_6979635 : Nat := 3583907547943904879663749

theorem tailTrace_6979635 : CollatzResearch.WordTrace tailWord_6979635 prefixEnd_6979635 3583907547943904879663749 := by
  unfold tailWord_6979635
  simp only [CollatzResearch.WordTrace]
  refine ⟨254568202068981896601012359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169712134712654597734008239 254568202068981896601012359)
  ·
    refine ⟨381852303103472844901518539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254568202068981896601012359 381852303103472844901518539)
    ·
      refine ⟨572778454655209267352277809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381852303103472844901518539 572778454655209267352277809)
      ·
        refine ⟨429583840991406950514208357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 572778454655209267352277809 429583840991406950514208357)
        ·
          refine ⟨80546970185888803221414067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 429583840991406950514208357 80546970185888803221414067)
          ·
            refine ⟨120820455278833204832121101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80546970185888803221414067 120820455278833204832121101)
            ·
              refine ⟨45307670729562451812045413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120820455278833204832121101 45307670729562451812045413)
              ·
                refine ⟨8495188261792959714758515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45307670729562451812045413 8495188261792959714758515)
                ·
                  refine ⟨12742782392689439572137773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8495188261792959714758515 12742782392689439572137773)
                  ·
                    refine ⟨4778543397258539839551665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12742782392689439572137773 4778543397258539839551665)
                    ·
                      refine ⟨3583907547943904879663749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4778543397258539839551665 3583907547943904879663749)
                      ·
                        rfl

theorem cell23_6979635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 3, 2].length) (baseStart_6979635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979635 prefixEnd_6979635 := by exact prefixLift 6979635
  have htrace : WordTrace (prefixWord ++ tailWord_6979635) baseStart_6979635 baseEnd_6979635 := by
    simpa [prefixWord, tailWord_6979635, baseEnd_6979635] using wordTrace_append hprefix tailTrace_6979635
  have hstable : (prefixWord ++ tailWord_6979635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979635).length < 2 ^ (prefixWord ++ tailWord_6979635).sum := by decide
  have hdescent : baseEnd_6979635 < baseStart_6979635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979638 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_6979638 : Nat := 118140960795 + 6979638 * 2 ^ 59
def prefixEnd_6979638 : Nat := 4983230072969 + 3 ^ 40 * 6979638 * 2
def baseEnd_6979638 : Nat := 3583909088385868367926235

theorem tailTrace_6979638 : CollatzResearch.WordTrace tailWord_6979638 prefixEnd_6979638 3583909088385868367926235 := by
  unfold tailWord_6979638
  simp only [CollatzResearch.WordTrace]
  refine ⟨15910519467998189257085723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169712207658647352075581045 15910519467998189257085723)
  ·
    refine ⟨23865779201997283885628585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15910519467998189257085723 23865779201997283885628585)
    ·
      refine ⟨17899334401497962914221439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23865779201997283885628585 17899334401497962914221439)
      ·
        refine ⟨26849001602246944371332159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17899334401497962914221439 26849001602246944371332159)
        ·
          refine ⟨40273502403370416556998239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26849001602246944371332159 40273502403370416556998239)
          ·
            refine ⟨60410253605055624835497359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40273502403370416556998239 60410253605055624835497359)
            ·
              refine ⟨90615380407583437253246039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60410253605055624835497359 90615380407583437253246039)
              ·
                refine ⟨135923070611375155879869059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90615380407583437253246039 135923070611375155879869059)
                ·
                  refine ⟨203884605917062733819803589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135923070611375155879869059 203884605917062733819803589)
                  ·
                    refine ⟨38228363609449262591213173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 203884605917062733819803589 38228363609449262591213173)
                    ·
                      refine ⟨3583909088385868367926235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38228363609449262591213173 3583909088385868367926235)
                      ·
                        rfl

theorem cell23_6979638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_6979638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979638 prefixEnd_6979638 := by exact prefixLift 6979638
  have htrace : WordTrace (prefixWord ++ tailWord_6979638) baseStart_6979638 baseEnd_6979638 := by
    simpa [prefixWord, tailWord_6979638, baseEnd_6979638] using wordTrace_append hprefix tailTrace_6979638
  have hstable : (prefixWord ++ tailWord_6979638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979638).length < 2 ^ (prefixWord ++ tailWord_6979638).sum := by decide
  have hdescent : baseEnd_6979638 < baseStart_6979638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979668 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 2, 4, 3]
def baseStart_6979668 : Nat := 118140960795 + 6979668 * 2 ^ 59
def prefixEnd_6979668 : Nat := 4983230072969 + 3 ^ 40 * 6979668 * 2
def baseEnd_6979668 : Nat := 3583924492805503250551097

theorem tailTrace_6979668 : CollatzResearch.WordTrace tailWord_6979668 prefixEnd_6979668 3583924492805503250551097 := by
  unfold tailWord_6979668
  simp only [CollatzResearch.WordTrace]
  refine ⟨127284702838931171618481829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169712937118574895491309105 127284702838931171618481829)
  ·
    refine ⟨23865881782299594678465343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127284702838931171618481829 23865881782299594678465343)
    ·
      refine ⟨35798822673449392017698015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23865881782299594678465343 35798822673449392017698015)
      ·
        refine ⟨53698234010174088026547023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35798822673449392017698015 53698234010174088026547023)
        ·
          refine ⟨80547351015261132039820535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53698234010174088026547023 80547351015261132039820535)
          ·
            refine ⟨120821026522891698059730803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80547351015261132039820535 120821026522891698059730803)
            ·
              refine ⟨181231539784337547089596205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120821026522891698059730803 181231539784337547089596205)
              ·
                refine ⟨67961827419126580158598577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181231539784337547089596205 67961827419126580158598577)
                ·
                  refine ⟨50971370564344935118948933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67961827419126580158598577 50971370564344935118948933)
                  ·
                    refine ⟨9557131980814675334802925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50971370564344935118948933 9557131980814675334802925)
                    ·
                      refine ⟨3583924492805503250551097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9557131980814675334802925 3583924492805503250551097)
                      ·
                        rfl

theorem cell23_6979668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_6979668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979668 prefixEnd_6979668 := by exact prefixLift 6979668
  have htrace : WordTrace (prefixWord ++ tailWord_6979668) baseStart_6979668 baseEnd_6979668 := by
    simpa [prefixWord, tailWord_6979668, baseEnd_6979668] using wordTrace_append hprefix tailTrace_6979668
  have hstable : (prefixWord ++ tailWord_6979668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979668).length < 2 ^ (prefixWord ++ tailWord_6979668).sum := by decide
  have hdescent : baseEnd_6979668 < baseStart_6979668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979722 : List Nat := [3, 1, 2, 3, 1, 2, 4, 2, 5]
def baseStart_6979722 : Nat := 118140960795 + 6979722 * 2 ^ 59
def prefixEnd_6979722 : Nat := 4983230072969 + 3 ^ 40 * 6979722 * 2
def baseEnd_6979722 : Nat := 398216913417871782141761

theorem tailTrace_6979722 : CollatzResearch.WordTrace tailWord_6979722 prefixEnd_6979722 398216913417871782141761 := by
  unfold tailWord_6979722
  simp only [CollatzResearch.WordTrace]
  refine ⟨63642843804916677614857355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169714250146444473639619613 63642843804916677614857355)
  ·
    refine ⟨95464265707375016422286033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63642843804916677614857355 95464265707375016422286033)
    ·
      refine ⟨71598199280531262316714525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95464265707375016422286033 71598199280531262316714525)
      ·
        refine ⟨26849324730199223368767947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71598199280531262316714525 26849324730199223368767947)
        ·
          refine ⟨40273987095298835053151921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26849324730199223368767947 40273987095298835053151921)
          ·
            refine ⟨30205490321474126289863941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40273987095298835053151921 30205490321474126289863941)
            ·
              refine ⟨5663529435276398679349489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30205490321474126289863941 5663529435276398679349489)
              ·
                refine ⟨4247647076457299009512117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5663529435276398679349489 4247647076457299009512117)
                ·
                  refine ⟨398216913417871782141761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4247647076457299009512117 398216913417871782141761)
                  ·
                    rfl

theorem cell23_6979722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2, 5].length) (baseStart_6979722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979722 prefixEnd_6979722 := by exact prefixLift 6979722
  have htrace : WordTrace (prefixWord ++ tailWord_6979722) baseStart_6979722 baseEnd_6979722 := by
    simpa [prefixWord, tailWord_6979722, baseEnd_6979722] using wordTrace_append hprefix tailTrace_6979722
  have hstable : (prefixWord ++ tailWord_6979722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979722).length < 2 ^ (prefixWord ++ tailWord_6979722).sum := by decide
  have hdescent : baseEnd_6979722 < baseStart_6979722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979731 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 2, 8]
def baseStart_6979731 : Nat := 118140960795 + 6979731 * 2 ^ 59
def prefixEnd_6979731 : Nat := 4983230072969 + 3 ^ 40 * 6979731 * 2
def baseEnd_6979731 : Nat := 1194652280695578834687769

theorem tailTrace_6979731 : CollatzResearch.WordTrace tailWord_6979731 prefixEnd_6979731 1194652280695578834687769 := by
  unfold tailWord_6979731
  simp only [CollatzResearch.WordTrace]
  refine ⟨254571703476634104996507047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169714468984422736664338031 254571703476634104996507047)
  ·
    refine ⟨381857555214951157494760571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254571703476634104996507047 381857555214951157494760571)
    ·
      refine ⟨572786332822426736242140857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381857555214951157494760571 572786332822426736242140857)
      ·
        refine ⟨429589749616820052181605643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 572786332822426736242140857 429589749616820052181605643)
        ·
          refine ⟨644384624425230078272408465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429589749616820052181605643 644384624425230078272408465)
          ·
            refine ⟨483288468318922558704306349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 644384624425230078272408465 483288468318922558704306349)
            ·
              refine ⟨181233175619595959514114881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 483288468318922558704306349 181233175619595959514114881)
              ·
                refine ⟨135924881714696969635586161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181233175619595959514114881 135924881714696969635586161)
                ·
                  refine ⟨101943661286022727226689621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135924881714696969635586161 101943661286022727226689621)
                  ·
                    refine ⟨1194652280695578834687769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101943661286022727226689621 1194652280695578834687769)
                    ·
                      rfl

theorem cell23_6979731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 8].length) (baseStart_6979731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979731 prefixEnd_6979731 := by exact prefixLift 6979731
  have htrace : WordTrace (prefixWord ++ tailWord_6979731) baseStart_6979731 baseEnd_6979731 := by
    simpa [prefixWord, tailWord_6979731, baseEnd_6979731] using wordTrace_append hprefix tailTrace_6979731
  have hstable : (prefixWord ++ tailWord_6979731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979731).length < 2 ^ (prefixWord ++ tailWord_6979731).sum := by decide
  have hdescent : baseEnd_6979731 < baseStart_6979731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979825 : List Nat := [1, 2, 2, 2, 2, 1, 4, 3, 1, 5]
def baseStart_6979825 : Nat := 118140960795 + 6979825 * 2 ^ 59
def prefixEnd_6979825 : Nat := 4983230072969 + 3 ^ 40 * 6979825 * 2
def baseEnd_6979825 : Nat := 1194668369756086378762625

theorem tailTrace_6979825 : CollatzResearch.WordTrace tailWord_6979825 prefixEnd_6979825 1194668369756086378762625 := by
  unfold tailWord_6979825
  simp only [CollatzResearch.WordTrace]
  refine ⟨254575131938293559050428929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169716754625529039366952619 254575131938293559050428929)
  ·
    refine ⟨190931348953720169287821697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254575131938293559050428929 190931348953720169287821697)
    ·
      refine ⟨143198511715290126965866273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190931348953720169287821697 143198511715290126965866273)
      ·
        refine ⟨107398883786467595224399705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143198511715290126965866273 107398883786467595224399705)
        ·
          refine ⟨80549162839850696418299779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107398883786467595224399705 80549162839850696418299779)
          ·
            refine ⟨120823744259776044627449669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80549162839850696418299779 120823744259776044627449669)
            ·
              refine ⟨22654452048708008367646813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120823744259776044627449669 22654452048708008367646813)
              ·
                refine ⟨8495419518265503137867555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22654452048708008367646813 8495419518265503137867555)
                ·
                  refine ⟨12743129277398254706801333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8495419518265503137867555 12743129277398254706801333)
                  ·
                    refine ⟨1194668369756086378762625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12743129277398254706801333 1194668369756086378762625)
                    ·
                      rfl

theorem cell23_6979825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 1, 5].length) (baseStart_6979825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979825 prefixEnd_6979825 := by exact prefixLift 6979825
  have htrace : WordTrace (prefixWord ++ tailWord_6979825) baseStart_6979825 baseEnd_6979825 := by
    simpa [prefixWord, tailWord_6979825, baseEnd_6979825] using wordTrace_append hprefix tailTrace_6979825
  have hstable : (prefixWord ++ tailWord_6979825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979825).length < 2 ^ (prefixWord ++ tailWord_6979825).sum := by decide
  have hdescent : baseEnd_6979825 < baseStart_6979825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979845 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 2, 6, 2]
def baseStart_6979845 : Nat := 118140960795 + 6979845 * 2 ^ 59
def prefixEnd_6979845 : Nat := 4983230072969 + 3 ^ 40 * 6979845 * 2
def baseEnd_6979845 : Nat := 3584015378881349058037783

theorem tailTrace_6979845 : CollatzResearch.WordTrace tailWord_6979845 prefixEnd_6979845 3584015378881349058037783 := by
  unfold tailWord_6979845
  simp only [CollatzResearch.WordTrace]
  refine ⟨254575861398221102466156989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169717240932147401644104659 254575861398221102466156989)
  ·
    refine ⟨95465948024332913424808871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254575861398221102466156989 95465948024332913424808871)
    ·
      refine ⟨143198922036499370137213307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95465948024332913424808871 143198922036499370137213307)
      ·
        refine ⟨214798383054749055205819961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143198922036499370137213307 214798383054749055205819961)
        ·
          refine ⟨161098787291061791404364971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214798383054749055205819961 161098787291061791404364971)
          ·
            refine ⟨241648180936592687106547457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161098787291061791404364971 241648180936592687106547457)
            ·
              refine ⟨181236135702444515329910593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241648180936592687106547457 181236135702444515329910593)
              ·
                refine ⟨135927101776833386497432945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181236135702444515329910593 135927101776833386497432945)
                ·
                  refine ⟨101945326332625039873074709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135927101776833386497432945 101945326332625039873074709)
                  ·
                    refine ⟨4778687171841798744050377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101945326332625039873074709 4778687171841798744050377)
                    ·
                      refine ⟨3584015378881349058037783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4778687171841798744050377 3584015378881349058037783)
                      ·
                        rfl

theorem cell23_6979845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 6, 2].length) (baseStart_6979845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979845 prefixEnd_6979845 := by exact prefixLift 6979845
  have htrace : WordTrace (prefixWord ++ tailWord_6979845) baseStart_6979845 baseEnd_6979845 := by
    simpa [prefixWord, tailWord_6979845, baseEnd_6979845] using wordTrace_append hprefix tailTrace_6979845
  have hstable : (prefixWord ++ tailWord_6979845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979845).length < 2 ^ (prefixWord ++ tailWord_6979845).sum := by decide
  have hdescent : baseEnd_6979845 < baseStart_6979845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979875 : List Nat := [1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 4]
def baseStart_6979875 : Nat := 118140960795 + 6979875 * 2 ^ 59
def prefixEnd_6979875 : Nat := 4983230072969 + 3 ^ 40 * 6979875 * 2
def baseEnd_6979875 : Nat := 3584030783300983940662645

theorem tailTrace_6979875 : CollatzResearch.WordTrace tailWord_6979875 prefixEnd_6979875 3584030783300983940662645 := by
  unfold tailWord_6979875
  simp only [CollatzResearch.WordTrace]
  refine ⟨254576955588112417589749079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169717970392074945059832719 254576955588112417589749079)
  ·
    refine ⟨381865433382168626384623619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254576955588112417589749079 381865433382168626384623619)
    ·
      refine ⟨572798150073252939576935429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381865433382168626384623619 572798150073252939576935429)
      ·
        refine ⟨107399653138734926170675393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 572798150073252939576935429 107399653138734926170675393)
        ·
          refine ⟨80549739854051194628006545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107399653138734926170675393 80549739854051194628006545)
          ·
            refine ⟨60412304890538395971004909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80549739854051194628006545 60412304890538395971004909)
            ·
              refine ⟨22654614333951898489126841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60412304890538395971004909 22654614333951898489126841)
              ·
                refine ⟨16990960750463923866845131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22654614333951898489126841 16990960750463923866845131)
                ·
                  refine ⟨25486441125695885800267697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16990960750463923866845131 25486441125695885800267697)
                  ·
                    refine ⟨19114830844271914350200773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25486441125695885800267697 19114830844271914350200773)
                    ·
                      refine ⟨3584030783300983940662645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19114830844271914350200773 3584030783300983940662645)
                      ·
                        rfl

theorem cell23_6979875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_6979875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979875 prefixEnd_6979875 := by exact prefixLift 6979875
  have htrace : WordTrace (prefixWord ++ tailWord_6979875) baseStart_6979875 baseEnd_6979875 := by
    simpa [prefixWord, tailWord_6979875, baseEnd_6979875] using wordTrace_append hprefix tailTrace_6979875
  have hstable : (prefixWord ++ tailWord_6979875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979875).length < 2 ^ (prefixWord ++ tailWord_6979875).sum := by decide
  have hdescent : baseEnd_6979875 < baseStart_6979875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979885 : List Nat := [1, 5, 3, 1, 13]
def baseStart_6979885 : Nat := 118140960795 + 6979885 * 2 ^ 59
def prefixEnd_6979885 : Nat := 4983230072969 + 3 ^ 40 * 6979885 * 2
def baseEnd_6979885 : Nat := 4916373001519244035031

theorem tailTrace_6979885 : CollatzResearch.WordTrace tailWord_6979885 prefixEnd_6979885 4916373001519244035031 := by
  unfold tailWord_6979885
  simp only [CollatzResearch.WordTrace]
  refine ⟨254577320318076189297613109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169718213545384126198408739 254577320318076189297613109)
  ·
    refine ⟨23866623779819642746651229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 254577320318076189297613109 23866623779819642746651229)
    ·
      refine ⟨8949983917432366029994211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23866623779819642746651229 8949983917432366029994211)
      ·
        refine ⟨13424975876148549044991317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8949983917432366029994211 13424975876148549044991317)
        ·
          refine ⟨4916373001519244035031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 13424975876148549044991317 4916373001519244035031)
          ·
            rfl

theorem cell23_6979885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 13].length) (baseStart_6979885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979885 prefixEnd_6979885 := by exact prefixLift 6979885
  have htrace : WordTrace (prefixWord ++ tailWord_6979885) baseStart_6979885 baseEnd_6979885 := by
    simpa [prefixWord, tailWord_6979885, baseEnd_6979885] using wordTrace_append hprefix tailTrace_6979885
  have hstable : (prefixWord ++ tailWord_6979885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979885).length < 2 ^ (prefixWord ++ tailWord_6979885).sum := by decide
  have hdescent : baseEnd_6979885 < baseStart_6979885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979888 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 6]
def baseStart_6979888 : Nat := 118140960795 + 6979888 * 2 ^ 59
def prefixEnd_6979888 : Nat := 4983230072969 + 3 ^ 40 * 6979888 * 2
def baseEnd_6979888 : Nat := 3584037458549492389800085

theorem tailTrace_6979888 : CollatzResearch.WordTrace tailWord_6979888 prefixEnd_6979888 3584037458549492389800085 := by
  unfold tailWord_6979888
  simp only [CollatzResearch.WordTrace]
  refine ⟨127288714868532660404986159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169718286491376880539981545 127288714868532660404986159)
  ·
    refine ⟨190933072302798990607479239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127288714868532660404986159 190933072302798990607479239)
    ·
      refine ⟨286399608454198485911218859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190933072302798990607479239 286399608454198485911218859)
      ·
        refine ⟨429599412681297728866828289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286399608454198485911218859 429599412681297728866828289)
        ·
          refine ⟨322199559510973296650121217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429599412681297728866828289 322199559510973296650121217)
          ·
            refine ⟨241649669633229972487590913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322199559510973296650121217 241649669633229972487590913)
            ·
              refine ⟨181237252224922479365693185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241649669633229972487590913 181237252224922479365693185)
              ·
                refine ⟨135927939168691859524269889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181237252224922479365693185 135927939168691859524269889)
                ·
                  refine ⟨101945954376518894643202417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135927939168691859524269889 101945954376518894643202417)
                  ·
                    refine ⟨76459465782389170982401813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101945954376518894643202417 76459465782389170982401813)
                    ·
                      refine ⟨3584037458549492389800085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76459465782389170982401813 3584037458549492389800085)
                      ·
                        rfl

theorem cell23_6979888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 6].length) (baseStart_6979888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979888 prefixEnd_6979888 := by exact prefixLift 6979888
  have htrace : WordTrace (prefixWord ++ tailWord_6979888) baseStart_6979888 baseEnd_6979888 := by
    simpa [prefixWord, tailWord_6979888, baseEnd_6979888] using wordTrace_append hprefix tailTrace_6979888
  have hstable : (prefixWord ++ tailWord_6979888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979888).length < 2 ^ (prefixWord ++ tailWord_6979888).sum := by decide
  have hdescent : baseEnd_6979888 < baseStart_6979888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979889 : List Nat := [1, 2, 2, 3, 4, 1, 2, 2, 2, 4]
def baseStart_6979889 : Nat := 118140960795 + 6979889 * 2 ^ 59
def prefixEnd_6979889 : Nat := 4983230072969 + 3 ^ 40 * 6979889 * 2
def baseEnd_6979889 : Nat := 1194679324010048961962527

theorem tailTrace_6979889 : CollatzResearch.WordTrace tailWord_6979889 prefixEnd_6979889 1194679324010048961962527 := by
  unfold tailWord_6979889
  simp only [CollatzResearch.WordTrace]
  refine ⟨254577466210061697980758721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169718310806707798653839147 254577466210061697980758721)
  ·
    refine ⟨190933099657546273485569041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254577466210061697980758721 190933099657546273485569041)
    ·
      refine ⟨143199824743159705114176781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190933099657546273485569041 143199824743159705114176781)
      ·
        refine ⟨53699934278684889417816293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143199824743159705114176781 53699934278684889417816293)
        ·
          refine ⟨10068737677253416765840555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53699934278684889417816293 10068737677253416765840555)
          ·
            refine ⟨15103106515880125148760833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10068737677253416765840555 15103106515880125148760833)
            ·
              refine ⟨11327329886910093861570625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15103106515880125148760833 11327329886910093861570625)
              ·
                refine ⟨8495497415182570396177969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11327329886910093861570625 8495497415182570396177969)
                ·
                  refine ⟨6371623061386927797133477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8495497415182570396177969 6371623061386927797133477)
                  ·
                    refine ⟨1194679324010048961962527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6371623061386927797133477 1194679324010048961962527)
                    ·
                      rfl

theorem cell23_6979889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 4].length) (baseStart_6979889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979889 prefixEnd_6979889 := by exact prefixLift 6979889
  have htrace : WordTrace (prefixWord ++ tailWord_6979889) baseStart_6979889 baseEnd_6979889 := by
    simpa [prefixWord, tailWord_6979889, baseEnd_6979889] using wordTrace_append hprefix tailTrace_6979889
  have hstable : (prefixWord ++ tailWord_6979889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979889).length < 2 ^ (prefixWord ++ tailWord_6979889).sum := by decide
  have hdescent : baseEnd_6979889 < baseStart_6979889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979890 : List Nat := [3, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3]
def baseStart_6979890 : Nat := 118140960795 + 6979890 * 2 ^ 59
def prefixEnd_6979890 : Nat := 4983230072969 + 3 ^ 40 * 6979890 * 2
def baseEnd_6979890 : Nat := 3584038485510801381975077

theorem tailTrace_6979890 : CollatzResearch.WordTrace tailWord_6979890 prefixEnd_6979890 3584038485510801381975077 := by
  unfold tailWord_6979890
  simp only [CollatzResearch.WordTrace]
  refine ⟨63644375670764518787886281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169718335122038716767696749 63644375670764518787886281)
  ·
    refine ⟨47733281753073389090914711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63644375670764518787886281 47733281753073389090914711)
    ·
      refine ⟨71599922629610083636372067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47733281753073389090914711 71599922629610083636372067)
      ·
        refine ⟨107399883944415125454558101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71599922629610083636372067 107399883944415125454558101)
        ·
          refine ⟨5034369559894459005682411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 107399883944415125454558101 5034369559894459005682411)
          ·
            refine ⟨7551554339841688508523617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5034369559894459005682411 7551554339841688508523617)
            ·
              refine ⟨5663665754881266381392713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7551554339841688508523617 5663665754881266381392713)
              ·
                refine ⟨4247749316160949786044535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5663665754881266381392713 4247749316160949786044535)
                ·
                  refine ⟨6371623974241424679066803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4247749316160949786044535 6371623974241424679066803)
                  ·
                    refine ⟨9557435961362137018600205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6371623974241424679066803 9557435961362137018600205)
                    ·
                      refine ⟨3584038485510801381975077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9557435961362137018600205 3584038485510801381975077)
                      ·
                        rfl

theorem cell23_6979890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3].length) (baseStart_6979890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979890 prefixEnd_6979890 := by exact prefixLift 6979890
  have htrace : WordTrace (prefixWord ++ tailWord_6979890) baseStart_6979890 baseEnd_6979890 := by
    simpa [prefixWord, tailWord_6979890, baseEnd_6979890] using wordTrace_append hprefix tailTrace_6979890
  have hstable : (prefixWord ++ tailWord_6979890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979890).length < 2 ^ (prefixWord ++ tailWord_6979890).sum := by decide
  have hdescent : baseEnd_6979890 < baseStart_6979890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979902 : List Nat := [4, 2, 1, 2, 1, 4, 1, 8]
def baseStart_6979902 : Nat := 118140960795 + 6979902 * 2 ^ 59
def prefixEnd_6979902 : Nat := 4983230072969 + 3 ^ 40 * 6979902 * 2
def baseEnd_6979902 : Nat := 132742394343653901297223

theorem tailTrace_6979902 : CollatzResearch.WordTrace tailWord_6979902 prefixEnd_6979902 132742394343653901297223 := by
  unfold tailWord_6979902
  simp only [CollatzResearch.WordTrace]
  refine ⟨31822242544876825150122745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169718626906009734133987973 31822242544876825150122745)
  ·
    refine ⟨23866681908657618862592059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31822242544876825150122745 23866681908657618862592059)
    ·
      refine ⟨35800022862986428293888089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23866681908657618862592059 35800022862986428293888089)
      ·
        refine ⟨26850017147239821220416067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35800022862986428293888089 26850017147239821220416067)
        ·
          refine ⟨40275025720859731830624101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26850017147239821220416067 40275025720859731830624101)
          ·
            refine ⟨7551567322661199718242019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40275025720859731830624101 7551567322661199718242019)
            ·
              refine ⟨11327350983991799577363029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7551567322661199718242019 11327350983991799577363029)
              ·
                refine ⟨132742394343653901297223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11327350983991799577363029 132742394343653901297223)
                ·
                  rfl

theorem cell23_6979902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 8].length) (baseStart_6979902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979902 prefixEnd_6979902 := by exact prefixLift 6979902
  have htrace : WordTrace (prefixWord ++ tailWord_6979902) baseStart_6979902 baseEnd_6979902 := by
    simpa [prefixWord, tailWord_6979902, baseEnd_6979902] using wordTrace_append hprefix tailTrace_6979902
  have hstable : (prefixWord ++ tailWord_6979902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979902).length < 2 ^ (prefixWord ++ tailWord_6979902).sum := by decide
  have hdescent : baseEnd_6979902 < baseStart_6979902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979939 : List Nat := [1, 1, 1, 5, 2, 1, 3, 3, 1, 3, 2]
def baseStart_6979939 : Nat := 118140960795 + 6979939 * 2 ^ 59
def prefixEnd_6979939 : Nat := 4983230072969 + 3 ^ 40 * 6979939 * 2
def baseEnd_6979939 : Nat := 3584063646062871690262351

theorem tailTrace_6979939 : CollatzResearch.WordTrace tailWord_6979939 prefixEnd_6979939 3584063646062871690262351 := by
  unfold tailWord_6979939
  simp only [CollatzResearch.WordTrace]
  refine ⟨254579289859880556520078871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169719526573253704346719247 254579289859880556520078871)
  ·
    refine ⟨381868934789820834780118307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254579289859880556520078871 381868934789820834780118307)
    ·
      refine ⟨572803402184731252170177461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381868934789820834780118307 572803402184731252170177461)
      ·
        refine ⟨53700318954818554890954137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 572803402184731252170177461 53700318954818554890954137)
        ·
          refine ⟨40275239216113916168215603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53700318954818554890954137 40275239216113916168215603)
          ·
            refine ⟨60412858824170874252323405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40275239216113916168215603 60412858824170874252323405)
            ·
              refine ⟨22654822059064077844621277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60412858824170874252323405 22654822059064077844621277)
              ·
                refine ⟨8495558272149029191732979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22654822059064077844621277 8495558272149029191732979)
                ·
                  refine ⟨12743337408223543787599469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8495558272149029191732979 12743337408223543787599469)
                  ·
                    refine ⟨4778751528083828920349801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12743337408223543787599469 4778751528083828920349801)
                    ·
                      refine ⟨3584063646062871690262351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4778751528083828920349801 3584063646062871690262351)
                      ·
                        rfl

theorem cell23_6979939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_6979939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979939 prefixEnd_6979939 := by exact prefixLift 6979939
  have htrace : WordTrace (prefixWord ++ tailWord_6979939) baseStart_6979939 baseEnd_6979939 := by
    simpa [prefixWord, tailWord_6979939, baseEnd_6979939] using wordTrace_append hprefix tailTrace_6979939
  have hstable : (prefixWord ++ tailWord_6979939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979939).length < 2 ^ (prefixWord ++ tailWord_6979939).sum := by decide
  have hdescent : baseEnd_6979939 < baseStart_6979939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979946 : List Nat := [3, 1, 3, 3, 1, 1, 3, 2, 2, 1, 3]
def baseStart_6979946 : Nat := 118140960795 + 6979946 * 2 ^ 59
def prefixEnd_6979946 : Nat := 4983230072969 + 3 ^ 40 * 6979946 * 2
def baseEnd_6979946 : Nat := 3584067240427453162874819

theorem tailTrace_6979946 : CollatzResearch.WordTrace tailWord_6979946 prefixEnd_6979946 3584067240427453162874819 := by
  unfold tailWord_6979946
  simp only [CollatzResearch.WordTrace]
  refine ⟨63644886292713799178895923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169719696780570131143722461 63644886292713799178895923)
  ·
    refine ⟨95467329439070698768343885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63644886292713799178895923 95467329439070698768343885)
    ·
      refine ⟨35800248539651512038128957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95467329439070698768343885 35800248539651512038128957)
      ·
        refine ⟨13425093202369317014298359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35800248539651512038128957 13425093202369317014298359)
        ·
          refine ⟨20137639803553975521447539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13425093202369317014298359 20137639803553975521447539)
          ·
            refine ⟨30206459705330963282171309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20137639803553975521447539 30206459705330963282171309)
            ·
              refine ⟨11327422389499111230814241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30206459705330963282171309 11327422389499111230814241)
              ·
                refine ⟨8495566792124333423110681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11327422389499111230814241 8495566792124333423110681)
                ·
                  refine ⟨6371675094093250067333011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8495566792124333423110681 6371675094093250067333011)
                  ·
                    refine ⟨9557512641139875100999517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6371675094093250067333011 9557512641139875100999517)
                    ·
                      refine ⟨3584067240427453162874819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9557512641139875100999517 3584067240427453162874819)
                      ·
                        rfl

theorem cell23_6979946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_6979946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979946 prefixEnd_6979946 := by exact prefixLift 6979946
  have htrace : WordTrace (prefixWord ++ tailWord_6979946) baseStart_6979946 baseEnd_6979946 := by
    simpa [prefixWord, tailWord_6979946, baseEnd_6979946] using wordTrace_append hprefix tailTrace_6979946
  have hstable : (prefixWord ++ tailWord_6979946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979946).length < 2 ^ (prefixWord ++ tailWord_6979946).sum := by decide
  have hdescent : baseEnd_6979946 < baseStart_6979946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6979975 : List Nat := [1, 1, 4, 2, 2, 1, 1, 4, 7]
def baseStart_6979975 : Nat := 118140960795 + 6979975 * 2 ^ 59
def prefixEnd_6979975 : Nat := 4983230072969 + 3 ^ 40 * 6979975 * 2
def baseEnd_6979975 : Nat := 398231347929603727712465

theorem tailTrace_6979975 : CollatzResearch.WordTrace tailWord_6979975 prefixEnd_6979975 398231347929603727712465 := by
  unfold tailWord_6979975
  simp only [CollatzResearch.WordTrace]
  refine ⟨254580602887750134668389379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169720401925166756445592919 254580602887750134668389379)
  ·
    refine ⟨381870904331625202002584069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254580602887750134668389379 381870904331625202002584069)
    ·
      refine ⟨71600794562179725375484513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 381870904331625202002584069 71600794562179725375484513)
      ·
        refine ⟨53700595921634794031613385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71600794562179725375484513 53700595921634794031613385)
        ·
          refine ⟨40275446941226095523710039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53700595921634794031613385 40275446941226095523710039)
          ·
            refine ⟨60413170411839143285565059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40275446941226095523710039 60413170411839143285565059)
            ·
              refine ⟨90619755617758714928347589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60413170411839143285565059 90619755617758714928347589)
              ·
                refine ⟨16991204178329759049065173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90619755617758714928347589 16991204178329759049065173)
                ·
                  refine ⟨398231347929603727712465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16991204178329759049065173 398231347929603727712465)
                  ·
                    rfl

theorem cell23_6979975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 7].length) (baseStart_6979975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6979975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6979975 prefixEnd_6979975 := by exact prefixLift 6979975
  have htrace : WordTrace (prefixWord ++ tailWord_6979975) baseStart_6979975 baseEnd_6979975 := by
    simpa [prefixWord, tailWord_6979975, baseEnd_6979975] using wordTrace_append hprefix tailTrace_6979975
  have hstable : (prefixWord ++ tailWord_6979975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6979975).length < 2 ^ (prefixWord ++ tailWord_6979975).sum := by decide
  have hdescent : baseEnd_6979975 < baseStart_6979975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6979975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980012 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 2, 5, 2]
def baseStart_6980012 : Nat := 118140960795 + 6980012 * 2 ^ 59
def prefixEnd_6980012 : Nat := 4983230072969 + 3 ^ 40 * 6980012 * 2
def baseEnd_6980012 : Nat := 3584101130150649904649515

theorem tailTrace_6980012 : CollatzResearch.WordTrace tailWord_6980012 prefixEnd_6980012 3584101130150649904649515 := by
  unfold tailWord_6980012
  simp only [CollatzResearch.WordTrace]
  refine ⟨127290976194308044993743145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169721301592410726658324193 127290976194308044993743145)
  ·
    refine ⟨95468232145731033745307359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127290976194308044993743145 95468232145731033745307359)
    ·
      refine ⟨143202348218596550617961039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95468232145731033745307359 143202348218596550617961039)
      ·
        refine ⟨214803522327894825926941559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143202348218596550617961039 214803522327894825926941559)
        ·
          refine ⟨322205283491842238890412339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214803522327894825926941559 322205283491842238890412339)
          ·
            refine ⟨483307925237763358335618509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322205283491842238890412339 483307925237763358335618509)
            ·
              refine ⟨181240471964161259375856941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 483307925237763358335618509 181240471964161259375856941)
              ·
                refine ⟨67965176986560472265946353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181240471964161259375856941 67965176986560472265946353)
                ·
                  refine ⟨50973882739920354199459765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67965176986560472265946353 50973882739920354199459765)
                  ·
                    refine ⟨4778801506867533206199353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50973882739920354199459765 4778801506867533206199353)
                    ·
                      refine ⟨3584101130150649904649515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4778801506867533206199353 3584101130150649904649515)
                      ·
                        rfl

theorem cell23_6980012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 5, 2].length) (baseStart_6980012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980012 prefixEnd_6980012 := by exact prefixLift 6980012
  have htrace : WordTrace (prefixWord ++ tailWord_6980012) baseStart_6980012 baseEnd_6980012 := by
    simpa [prefixWord, tailWord_6980012, baseEnd_6980012] using wordTrace_append hprefix tailTrace_6980012
  have hstable : (prefixWord ++ tailWord_6980012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980012).length < 2 ^ (prefixWord ++ tailWord_6980012).sum := by decide
  have hdescent : baseEnd_6980012 < baseStart_6980012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980103 : List Nat := [1, 1, 4, 3, 3, 1, 2, 3, 1, 4]
def baseStart_6980103 : Nat := 118140960795 + 6980103 * 2 ^ 59
def prefixEnd_6980103 : Nat := 4983230072969 + 3 ^ 40 * 6980103 * 2
def baseEnd_6980103 : Nat := 1194715952296736349537199

theorem tailTrace_6980103 : CollatzResearch.WordTrace tailWord_6980103 prefixEnd_6980103 1194715952296736349537199 := by
  unfold tailWord_6980103
  simp only [CollatzResearch.WordTrace]
  refine ⟨254585271431286412529048963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169723514287524275019365975 254585271431286412529048963)
  ·
    refine ⟨381877907146929618793573445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254585271431286412529048963 381877907146929618793573445)
    ·
      refine ⟨71602107590049303523795021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 381877907146929618793573445 71602107590049303523795021)
      ·
        refine ⟨26850790346268488821423133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71602107590049303523795021 26850790346268488821423133)
        ·
          refine ⟨10069046379850683308033675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26850790346268488821423133 10069046379850683308033675)
          ·
            refine ⟨15103569569776024962050513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10069046379850683308033675 15103569569776024962050513)
            ·
              refine ⟨11327677177332018721537885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15103569569776024962050513 11327677177332018721537885)
              ·
                refine ⟨4247878941499507020576707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11327677177332018721537885 4247878941499507020576707)
                ·
                  refine ⟨6371818412249260530865061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4247878941499507020576707 6371818412249260530865061)
                  ·
                    refine ⟨1194715952296736349537199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6371818412249260530865061 1194715952296736349537199)
                    ·
                      rfl

theorem cell23_6980103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_6980103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980103 prefixEnd_6980103 := by exact prefixLift 6980103
  have htrace : WordTrace (prefixWord ++ tailWord_6980103) baseStart_6980103 baseEnd_6980103 := by
    simpa [prefixWord, tailWord_6980103, baseEnd_6980103] using wordTrace_append hprefix tailTrace_6980103
  have hstable : (prefixWord ++ tailWord_6980103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980103).length < 2 ^ (prefixWord ++ tailWord_6980103).sum := by decide
  have hdescent : baseEnd_6980103 < baseStart_6980103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980116 : List Nat := [2, 4, 3, 1, 1, 1, 3, 2, 6]
def baseStart_6980116 : Nat := 118140960795 + 6980116 * 2 ^ 59
def prefixEnd_6980116 : Nat := 4983230072969 + 3 ^ 40 * 6980116 * 2
def baseEnd_6980116 : Nat := 398239392459857499749893

theorem tailTrace_6980116 : CollatzResearch.WordTrace tailWord_6980116 prefixEnd_6980116 398239392459857499749893 := by
  unfold tailWord_6980116
  simp only [CollatzResearch.WordTrace]
  refine ⟨127292872790119657874636101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169723830386826210499514801 127292872790119657874636101)
  ·
    refine ⟨23867413648147435851494269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127292872790119657874636101 23867413648147435851494269)
    ·
      refine ⟨8950280118055288444310351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23867413648147435851494269 8950280118055288444310351)
      ·
        refine ⟨13425420177082932666465527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8950280118055288444310351 13425420177082932666465527)
        ·
          refine ⟨20138130265624398999698291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13425420177082932666465527 20138130265624398999698291)
          ·
            refine ⟨30207195398436598499547437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20138130265624398999698291 30207195398436598499547437)
            ·
              refine ⟨11327698274413724437330289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30207195398436598499547437 11327698274413724437330289)
              ·
                refine ⟨8495773705810293327997717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11327698274413724437330289 8495773705810293327997717)
                ·
                  refine ⟨398239392459857499749893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8495773705810293327997717 398239392459857499749893)
                  ·
                    rfl

theorem cell23_6980116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_6980116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980116 prefixEnd_6980116 := by exact prefixLift 6980116
  have htrace : WordTrace (prefixWord ++ tailWord_6980116) baseStart_6980116 baseEnd_6980116 := by
    simpa [prefixWord, tailWord_6980116, baseEnd_6980116] using wordTrace_append hprefix tailTrace_6980116
  have hstable : (prefixWord ++ tailWord_6980116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980116).length < 2 ^ (prefixWord ++ tailWord_6980116).sum := by decide
  have hdescent : baseEnd_6980116 < baseStart_6980116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980136 : List Nat := [2, 1, 5, 2, 1, 1, 1, 2, 1, 5, 2]
def baseStart_6980136 : Nat := 118140960795 + 6980136 * 2 ^ 59
def prefixEnd_6980136 : Nat := 4983230072969 + 3 ^ 40 * 6980136 * 2
def baseEnd_6980136 : Nat := 3584164801751807419498945

theorem tailTrace_6980136 : CollatzResearch.WordTrace tailWord_6980136 prefixEnd_6980136 3584164801751807419498945 := by
  unfold tailWord_6980136
  simp only [CollatzResearch.WordTrace]
  refine ⟨127293237520083429582500131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169724316693444572776666841 127293237520083429582500131)
  ·
    refine ⟨190939856280125144373750197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127293237520083429582500131 190939856280125144373750197)
    ·
      refine ⟨17900611526261732285039081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 190939856280125144373750197 17900611526261732285039081)
      ·
        refine ⟨13425458644696299213779311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17900611526261732285039081 13425458644696299213779311)
        ·
          refine ⟨20138187967044448820668967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13425458644696299213779311 20138187967044448820668967)
          ·
            refine ⟨30207281950566673231003451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20138187967044448820668967 30207281950566673231003451)
            ·
              refine ⟨45310922925850009846505177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30207281950566673231003451 45310922925850009846505177)
              ·
                refine ⟨33983192194387507384878883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45310922925850009846505177 33983192194387507384878883)
                ·
                  refine ⟨50974788291581261077318325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33983192194387507384878883 50974788291581261077318325)
                  ·
                    refine ⟨4778886402335743225998593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50974788291581261077318325 4778886402335743225998593)
                    ·
                      refine ⟨3584164801751807419498945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4778886402335743225998593 3584164801751807419498945)
                      ·
                        rfl

theorem cell23_6980136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_6980136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980136 prefixEnd_6980136 := by exact prefixLift 6980136
  have htrace : WordTrace (prefixWord ++ tailWord_6980136) baseStart_6980136 baseEnd_6980136 := by
    simpa [prefixWord, tailWord_6980136, baseEnd_6980136] using wordTrace_append hprefix tailTrace_6980136
  have hstable : (prefixWord ++ tailWord_6980136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980136).length < 2 ^ (prefixWord ++ tailWord_6980136).sum := by decide
  have hdescent : baseEnd_6980136 < baseStart_6980136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980149 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 2, 6, 2]
def baseStart_6980149 : Nat := 118140960795 + 6980149 * 2 ^ 59
def prefixEnd_6980149 : Nat := 4983230072969 + 3 ^ 40 * 6980149 * 2
def baseEnd_6980149 : Nat := 3584171477000315868636385

theorem tailTrace_6980149 : CollatzResearch.WordTrace tailWord_6980149 prefixEnd_6980149 3584171477000315868636385 := by
  unfold tailWord_6980149
  simp only [CollatzResearch.WordTrace]
  refine ⟨254586949189119762385223501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169724632792746508256815667 254586949189119762385223501)
  ·
    refine ⟨95470105945919910894458813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254586949189119762385223501 95470105945919910894458813)
    ·
      refine ⟨35801289729719966585422055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95470105945919910894458813 35801289729719966585422055)
      ·
        refine ⟨53701934594579949878133083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35801289729719966585422055 53701934594579949878133083)
        ·
          refine ⟨80552901891869924817199625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53701934594579949878133083 80552901891869924817199625)
          ·
            refine ⟨60414676418902443612899719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80552901891869924817199625 60414676418902443612899719)
            ·
              refine ⟨90622014628353665419349579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60414676418902443612899719 90622014628353665419349579)
              ·
                refine ⟨135933021942530498129024369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90622014628353665419349579 135933021942530498129024369)
                ·
                  refine ⟨101949766456897873596768277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135933021942530498129024369 101949766456897873596768277)
                  ·
                    refine ⟨4778895302667087824848513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101949766456897873596768277 4778895302667087824848513)
                    ·
                      refine ⟨3584171477000315868636385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4778895302667087824848513 3584171477000315868636385)
                      ·
                        rfl

theorem cell23_6980149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 6, 2].length) (baseStart_6980149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980149 prefixEnd_6980149 := by exact prefixLift 6980149
  have htrace : WordTrace (prefixWord ++ tailWord_6980149) baseStart_6980149 baseEnd_6980149 := by
    simpa [prefixWord, tailWord_6980149, baseEnd_6980149] using wordTrace_append hprefix tailTrace_6980149
  have hstable : (prefixWord ++ tailWord_6980149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980149).length < 2 ^ (prefixWord ++ tailWord_6980149).sum := by decide
  have hdescent : baseEnd_6980149 < baseStart_6980149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980152 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 3, 1, 5]
def baseStart_6980152 : Nat := 118140960795 + 6980152 * 2 ^ 59
def prefixEnd_6980152 : Nat := 4983230072969 + 3 ^ 40 * 6980152 * 2
def baseEnd_6980152 : Nat := 3584173017442279356898871

theorem tailTrace_6980152 : CollatzResearch.WordTrace tailWord_6980152 prefixEnd_6980152 3584173017442279356898871 := by
  unfold tailWord_6980152
  simp only [CollatzResearch.WordTrace]
  refine ⟨127293529304054446948791355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169724705738739262598388473 127293529304054446948791355)
  ·
    refine ⟨190940293956081670423187033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127293529304054446948791355 190940293956081670423187033)
    ·
      refine ⟨143205220467061252817390275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190940293956081670423187033 143205220467061252817390275)
      ·
        refine ⟨214807830700591879226085413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143205220467061252817390275 214807830700591879226085413)
        ·
          refine ⟨40276468256360977354891015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214807830700591879226085413 40276468256360977354891015)
          ·
            refine ⟨60414702384541466032336523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40276468256360977354891015 60414702384541466032336523)
            ·
              refine ⟨90622053576812199048504785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60414702384541466032336523 90622053576812199048504785)
              ·
                refine ⟨67966540182609149286378589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90622053576812199048504785 67966540182609149286378589)
                ·
                  refine ⟨25487452568478430982391971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67966540182609149286378589 25487452568478430982391971)
                  ·
                    refine ⟨38231178852717646473587957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25487452568478430982391971 38231178852717646473587957)
                    ·
                      refine ⟨3584173017442279356898871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38231178852717646473587957 3584173017442279356898871)
                      ·
                        rfl

theorem cell23_6980152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_6980152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980152 prefixEnd_6980152 := by exact prefixLift 6980152
  have htrace : WordTrace (prefixWord ++ tailWord_6980152) baseStart_6980152 baseEnd_6980152 := by
    simpa [prefixWord, tailWord_6980152, baseEnd_6980152] using wordTrace_append hprefix tailTrace_6980152
  have hstable : (prefixWord ++ tailWord_6980152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980152).length < 2 ^ (prefixWord ++ tailWord_6980152).sum := by decide
  have hdescent : baseEnd_6980152 < baseStart_6980152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980193 : List Nat := [1, 2, 3, 1, 1, 6, 2, 1, 2, 4]
def baseStart_6980193 : Nat := 118140960795 + 6980193 * 2 ^ 59
def prefixEnd_6980193 : Nat := 4983230072969 + 3 ^ 40 * 6980193 * 2
def baseEnd_6980193 : Nat := 1194731356716371232162061

theorem tailTrace_6980193 : CollatzResearch.WordTrace tailWord_6980193 prefixEnd_6980193 1194731356716371232162061 := by
  unfold tailWord_6980193
  simp only [CollatzResearch.WordTrace]
  refine ⟨254588554000960357899825233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169725702667306905266550155 254588554000960357899825233)
  ·
    refine ⟨190941415500720268424868925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254588554000960357899825233 190941415500720268424868925)
    ·
      refine ⟨71603030812770100659325847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190941415500720268424868925 71603030812770100659325847)
      ·
        refine ⟨107404546219155150988988771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71603030812770100659325847 107404546219155150988988771)
        ·
          refine ⟨161106819328732726483483157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107404546219155150988988771 161106819328732726483483157)
          ·
            refine ⟨7551882156034346553913273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 161106819328732726483483157 7551882156034346553913273)
            ·
              refine ⟨5663911617025759915434955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7551882156034346553913273 5663911617025759915434955)
              ·
                refine ⟨8495867425538639873152433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5663911617025759915434955 8495867425538639873152433)
                ·
                  refine ⟨6371900569153979904864325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8495867425538639873152433 6371900569153979904864325)
                  ·
                    refine ⟨1194731356716371232162061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6371900569153979904864325 1194731356716371232162061)
                    ·
                      rfl

theorem cell23_6980193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 2, 4].length) (baseStart_6980193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980193 prefixEnd_6980193 := by exact prefixLift 6980193
  have htrace : WordTrace (prefixWord ++ tailWord_6980193) baseStart_6980193 baseEnd_6980193 := by
    simpa [prefixWord, tailWord_6980193, baseEnd_6980193] using wordTrace_append hprefix tailTrace_6980193
  have hstable : (prefixWord ++ tailWord_6980193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980193).length < 2 ^ (prefixWord ++ tailWord_6980193).sum := by decide
  have hdescent : baseEnd_6980193 < baseStart_6980193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980199 : List Nat := [1, 1, 5, 1, 1, 1, 1, 5, 1, 3, 3]
def baseStart_6980199 : Nat := 118140960795 + 6980199 * 2 ^ 59
def prefixEnd_6980199 : Nat := 4983230072969 + 3 ^ 40 * 6980199 * 2
def baseEnd_6980199 : Nat := 3584197151033040673011155

theorem tailTrace_6980199 : CollatzResearch.WordTrace tailWord_6980199 prefixEnd_6980199 3584197151033040673011155 := by
  unfold tailWord_6980199
  simp only [CollatzResearch.WordTrace]
  refine ⟨254588772838938620924543651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169725848559292413949695767 254588772838938620924543651)
  ·
    refine ⟨381883159258407931386815477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254588772838938620924543651 381883159258407931386815477)
    ·
      refine ⟨35801546180475743567513951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 381883159258407931386815477 35801546180475743567513951)
      ·
        refine ⟨53702319270713615351270927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35801546180475743567513951 53702319270713615351270927)
        ·
          refine ⟨80553478906070423026906391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53702319270713615351270927 80553478906070423026906391)
          ·
            refine ⟨120830218359105634540359587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80553478906070423026906391 120830218359105634540359587)
            ·
              refine ⟨181245327538658451810539381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120830218359105634540359587 181245327538658451810539381)
              ·
                refine ⟨16991749456749229857238067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 181245327538658451810539381 16991749456749229857238067)
                ·
                  refine ⟨25487624185123844785857101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16991749456749229857238067 25487624185123844785857101)
                  ·
                    refine ⟨9557859069421441794696413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25487624185123844785857101 9557859069421441794696413)
                    ·
                      refine ⟨3584197151033040673011155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9557859069421441794696413 3584197151033040673011155)
                      ·
                        rfl

theorem cell23_6980199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_6980199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980199 prefixEnd_6980199 := by exact prefixLift 6980199
  have htrace : WordTrace (prefixWord ++ tailWord_6980199) baseStart_6980199 baseEnd_6980199 := by
    simpa [prefixWord, tailWord_6980199, baseEnd_6980199] using wordTrace_append hprefix tailTrace_6980199
  have hstable : (prefixWord ++ tailWord_6980199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980199).length < 2 ^ (prefixWord ++ tailWord_6980199).sum := by decide
  have hdescent : baseEnd_6980199 < baseStart_6980199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980200 : List Nat := [2, 1, 4, 3, 3, 1, 1, 2, 1, 1, 4]
def baseStart_6980200 : Nat := 118140960795 + 6980200 * 2 ^ 59
def prefixEnd_6980200 : Nat := 4983230072969 + 3 ^ 40 * 6980200 * 2
def baseEnd_6980200 : Nat := 3584197664513695169098651

theorem tailTrace_6980200 : CollatzResearch.WordTrace tailWord_6980200 prefixEnd_6980200 3584197664513695169098651 := by
  unfold tailWord_6980200
  simp only [CollatzResearch.WordTrace]
  refine ⟨127294404655967499047665027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169725872874623332063553369 127294404655967499047665027)
  ·
    refine ⟨190941606983951248571497541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127294404655967499047665027 190941606983951248571497541)
    ·
      refine ⟨35801551309490859107155789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190941606983951248571497541 35801551309490859107155789)
      ·
        refine ⟨13425581741059072165183421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35801551309490859107155789 13425581741059072165183421)
        ·
          refine ⟨5034593152897152061943783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13425581741059072165183421 5034593152897152061943783)
          ·
            refine ⟨7551889729345728092915675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5034593152897152061943783 7551889729345728092915675)
            ·
              refine ⟨11327834594018592139373513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7551889729345728092915675 11327834594018592139373513)
              ·
                refine ⟨8495875945513944104530135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11327834594018592139373513 8495875945513944104530135)
                ·
                  refine ⟨12743813918270916156795203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8495875945513944104530135 12743813918270916156795203)
                  ·
                    refine ⟨19115720877406374235192805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12743813918270916156795203 19115720877406374235192805)
                    ·
                      refine ⟨3584197664513695169098651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19115720877406374235192805 3584197664513695169098651)
                      ·
                        rfl

theorem cell23_6980200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_6980200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980200 prefixEnd_6980200 := by exact prefixLift 6980200
  have htrace : WordTrace (prefixWord ++ tailWord_6980200) baseStart_6980200 baseEnd_6980200 := by
    simpa [prefixWord, tailWord_6980200, baseEnd_6980200] using wordTrace_append hprefix tailTrace_6980200
  have hstable : (prefixWord ++ tailWord_6980200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980200).length < 2 ^ (prefixWord ++ tailWord_6980200).sum := by decide
  have hdescent : baseEnd_6980200 < baseStart_6980200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980234 : List Nat := [3, 1, 2, 3, 3, 2, 2, 2, 1, 2, 2]
def baseStart_6980234 : Nat := 118140960795 + 6980234 * 2 ^ 59
def prefixEnd_6980234 : Nat := 4983230072969 + 3 ^ 40 * 6980234 * 2
def baseEnd_6980234 : Nat := 3584215122855948036073495

theorem tailTrace_6980234 : CollatzResearch.WordTrace tailWord_6980234 prefixEnd_6980234 3584215122855948036073495 := by
  unfold tailWord_6980234
  simp only [CollatzResearch.WordTrace]
  refine ⟨63647512348452955475516939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169726699595874547934711837 63647512348452955475516939)
  ·
    refine ⟨95471268522679433213275409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63647512348452955475516939 95471268522679433213275409)
    ·
      refine ⟨71603451392009574909956557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95471268522679433213275409 71603451392009574909956557)
      ·
        refine ⟨26851294272003590591233709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71603451392009574909956557 26851294272003590591233709)
        ·
          refine ⟨10069235352001346471712641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26851294272003590591233709 10069235352001346471712641)
          ·
            refine ⟨7551926514001009853784481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10069235352001346471712641 7551926514001009853784481)
            ·
              refine ⟨5663944885500757390338361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7551926514001009853784481 5663944885500757390338361)
              ·
                refine ⟨4247958664125568042753771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5663944885500757390338361 4247958664125568042753771)
                ·
                  refine ⟨6371937996188352064130657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4247958664125568042753771 6371937996188352064130657)
                  ·
                    refine ⟨4778953497141264048097993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6371937996188352064130657 4778953497141264048097993)
                    ·
                      refine ⟨3584215122855948036073495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4778953497141264048097993 3584215122855948036073495)
                      ·
                        rfl

theorem cell23_6980234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_6980234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980234 prefixEnd_6980234 := by exact prefixLift 6980234
  have htrace : WordTrace (prefixWord ++ tailWord_6980234) baseStart_6980234 baseEnd_6980234 := by
    simpa [prefixWord, tailWord_6980234, baseEnd_6980234] using wordTrace_append hprefix tailTrace_6980234
  have hstable : (prefixWord ++ tailWord_6980234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980234).length < 2 ^ (prefixWord ++ tailWord_6980234).sum := by decide
  have hdescent : baseEnd_6980234 < baseStart_6980234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980272 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 7]
def baseStart_6980272 : Nat := 118140960795 + 6980272 * 2 ^ 59
def prefixEnd_6980272 : Nat := 4983230072969 + 3 ^ 40 * 6980272 * 2
def baseEnd_6980272 : Nat := 3584234635120818887398319

theorem tailTrace_6980272 : CollatzResearch.WordTrace tailWord_6980272 prefixEnd_6980272 3584234635120818887398319 := by
  unfold tailWord_6980272
  simp only [CollatzResearch.WordTrace]
  refine ⟨127295717683837077195975535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169727623578449436261300713 127295717683837077195975535)
  ·
    refine ⟨190943576525755615793963303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127295717683837077195975535 190943576525755615793963303)
    ·
      refine ⟨286415364788633423690944955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190943576525755615793963303 286415364788633423690944955)
      ·
        refine ⟨429623047182950135536417433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286415364788633423690944955 429623047182950135536417433)
        ·
          refine ⟨322217285387212601652313075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429623047182950135536417433 322217285387212601652313075)
          ·
            refine ⟨483325928080818902478469613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322217285387212601652313075 483325928080818902478469613)
            ·
              refine ⟨181247223030307088429426105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 483325928080818902478469613 181247223030307088429426105)
              ·
                refine ⟨135935417272730316322069579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181247223030307088429426105 135935417272730316322069579)
                ·
                  refine ⟨203903125909095474483104369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135935417272730316322069579 203903125909095474483104369)
                  ·
                    refine ⟨152927344431821605862328277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 203903125909095474483104369 152927344431821605862328277)
                    ·
                      refine ⟨3584234635120818887398319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152927344431821605862328277 3584234635120818887398319)
                      ·
                        rfl

theorem cell23_6980272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_6980272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980272 prefixEnd_6980272 := by exact prefixLift 6980272
  have htrace : WordTrace (prefixWord ++ tailWord_6980272) baseStart_6980272 baseEnd_6980272 := by
    simpa [prefixWord, tailWord_6980272, baseEnd_6980272] using wordTrace_append hprefix tailTrace_6980272
  have hstable : (prefixWord ++ tailWord_6980272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980272).length < 2 ^ (prefixWord ++ tailWord_6980272).sum := by decide
  have hdescent : baseEnd_6980272 < baseStart_6980272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980277 : List Nat := [1, 3, 3, 3, 1, 3, 2, 1, 1, 3, 2]
def baseStart_6980277 : Nat := 118140960795 + 6980277 * 2 ^ 59
def prefixEnd_6980277 : Nat := 4983230072969 + 3 ^ 40 * 6980277 * 2
def baseEnd_6980277 : Nat := 3584237202524091367835797

theorem tailTrace_6980277 : CollatzResearch.WordTrace tailWord_6980277 prefixEnd_6980277 3584237202524091367835797 := by
  unfold tailWord_6980277
  simp only [CollatzResearch.WordTrace]
  refine ⟨254591617732656040245883085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169727745155104026830588723 254591617732656040245883085)
  ·
    refine ⟨95471856649746015092206157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254591617732656040245883085 95471856649746015092206157)
    ·
      refine ⟨35801946243654755659577309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95471856649746015092206157 35801946243654755659577309)
      ·
        refine ⟨13425729841370533372341491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35801946243654755659577309 13425729841370533372341491)
        ·
          refine ⟨20138594762055800058512237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13425729841370533372341491 20138594762055800058512237)
          ·
            refine ⟨7551973035770925021942089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20138594762055800058512237 7551973035770925021942089)
            ·
              refine ⟨5663979776828193766456567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7551973035770925021942089 5663979776828193766456567)
              ·
                refine ⟨8495969665242290649684851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5663979776828193766456567 8495969665242290649684851)
                ·
                  refine ⟨12743954497863435974527277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8495969665242290649684851 12743954497863435974527277)
                  ·
                    refine ⟨4778982936698788490447729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12743954497863435974527277 4778982936698788490447729)
                    ·
                      refine ⟨3584237202524091367835797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4778982936698788490447729 3584237202524091367835797)
                      ·
                        rfl

theorem cell23_6980277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_6980277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980277 prefixEnd_6980277 := by exact prefixLift 6980277
  have htrace : WordTrace (prefixWord ++ tailWord_6980277) baseStart_6980277 baseEnd_6980277 := by
    simpa [prefixWord, tailWord_6980277, baseEnd_6980277] using wordTrace_append hprefix tailTrace_6980277
  have hstable : (prefixWord ++ tailWord_6980277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980277).length < 2 ^ (prefixWord ++ tailWord_6980277).sum := by decide
  have hdescent : baseEnd_6980277 < baseStart_6980277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980296 : List Nat := [2, 1, 3, 1, 2, 3, 2, 4, 5]
def baseStart_6980296 : Nat := 118140960795 + 6980296 * 2 ^ 59
def prefixEnd_6980296 : Nat := 4983230072969 + 3 ^ 40 * 6980296 * 2
def baseEnd_6980296 : Nat := 398249662072947421499801

theorem tailTrace_6980296 : CollatzResearch.WordTrace tailWord_6980296 prefixEnd_6980296 398249662072947421499801 := by
  unfold tailWord_6980296
  simp only [CollatzResearch.WordTrace]
  refine ⟨127296155359793603245412371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169728207146391470993883161 127296155359793603245412371)
  ·
    refine ⟨190944233039690404868118557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127296155359793603245412371 190944233039690404868118557)
    ·
      refine ⟨71604087389883901825544459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190944233039690404868118557 71604087389883901825544459)
      ·
        refine ⟨107406131084825852738316689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71604087389883901825544459 107406131084825852738316689)
        ·
          refine ⟨80554598313619389553737517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107406131084825852738316689 80554598313619389553737517)
          ·
            refine ⟨30207974367607271082651569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80554598313619389553737517 30207974367607271082651569)
            ·
              refine ⟨22655980775705453311988677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30207974367607271082651569 22655980775705453311988677)
              ·
                refine ⟨4247996395444772495997877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22655980775705453311988677 4247996395444772495997877)
                ·
                  refine ⟨398249662072947421499801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4247996395444772495997877 398249662072947421499801)
                  ·
                    rfl

theorem cell23_6980296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4, 5].length) (baseStart_6980296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980296 prefixEnd_6980296 := by exact prefixLift 6980296
  have htrace : WordTrace (prefixWord ++ tailWord_6980296) baseStart_6980296 baseEnd_6980296 := by
    simpa [prefixWord, tailWord_6980296, baseEnd_6980296] using wordTrace_append hprefix tailTrace_6980296
  have hstable : (prefixWord ++ tailWord_6980296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980296).length < 2 ^ (prefixWord ++ tailWord_6980296).sum := by decide
  have hdescent : baseEnd_6980296 < baseStart_6980296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980329 : List Nat := [1, 2, 1, 1, 1, 2, 6, 1, 1, 3, 4]
def baseStart_6980329 : Nat := 118140960795 + 6980329 * 2 ^ 59
def prefixEnd_6980329 : Nat := 4983230072969 + 3 ^ 40 * 6980329 * 2
def baseEnd_6980329 : Nat := 3584263903518125164385557

theorem tailTrace_6980329 : CollatzResearch.WordTrace tailWord_6980329 prefixEnd_6980329 3584263903518125164385557 := by
  unfold tailWord_6980329
  simp only [CollatzResearch.WordTrace]
  refine ⟨254593514328467653126776041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169729009552311768751184027 254593514328467653126776041)
  ·
    refine ⟨190945135746350739845082031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254593514328467653126776041 190945135746350739845082031)
    ·
      refine ⟨286417703619526109767623047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190945135746350739845082031 286417703619526109767623047)
      ·
        refine ⟨429626555429289164651434571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286417703619526109767623047 429626555429289164651434571)
        ·
          refine ⟨644439833143933746977151857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429626555429289164651434571 644439833143933746977151857)
          ·
            refine ⟨483329874857950310232863893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 644439833143933746977151857 483329874857950310232863893)
            ·
              refine ⟨22656087883966420792165495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 483329874857950310232863893 22656087883966420792165495)
              ·
                refine ⟨33984131825949631188248243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22656087883966420792165495 33984131825949631188248243)
                ·
                  refine ⟨50976197738924446782372365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33984131825949631188248243 50976197738924446782372365)
                  ·
                    refine ⟨19116074152096667543389637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50976197738924446782372365 19116074152096667543389637)
                    ·
                      refine ⟨3584263903518125164385557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19116074152096667543389637 3584263903518125164385557)
                      ·
                        rfl

theorem cell23_6980329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 3, 4].length) (baseStart_6980329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980329 prefixEnd_6980329 := by exact prefixLift 6980329
  have htrace : WordTrace (prefixWord ++ tailWord_6980329) baseStart_6980329 baseEnd_6980329 := by
    simpa [prefixWord, tailWord_6980329, baseEnd_6980329] using wordTrace_append hprefix tailTrace_6980329
  have hstable : (prefixWord ++ tailWord_6980329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980329).length < 2 ^ (prefixWord ++ tailWord_6980329).sum := by decide
  have hdescent : baseEnd_6980329 < baseStart_6980329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980346 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2]
def baseStart_6980346 : Nat := 118140960795 + 6980346 * 2 ^ 59
def prefixEnd_6980346 : Nat := 4983230072969 + 3 ^ 40 * 6980346 * 2
def baseEnd_6980346 : Nat := 3584272632689251597872979

theorem tailTrace_6980346 : CollatzResearch.WordTrace tailWord_6980346 prefixEnd_6980346 3584272632689251597872979 := by
  unfold tailWord_6980346
  simp only [CollatzResearch.WordTrace]
  refine ⟨63648533592351516257536223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169729422912937376686763261 63648533592351516257536223)
  ·
    refine ⟨95472800388527274386304335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63648533592351516257536223 95472800388527274386304335)
    ·
      refine ⟨143209200582790911579456503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95472800388527274386304335 143209200582790911579456503)
      ·
        refine ⟨214813800874186367369184755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143209200582790911579456503 214813800874186367369184755)
        ·
          refine ⟨322220701311279551053777133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214813800874186367369184755 322220701311279551053777133)
          ·
            refine ⟨120832762991729831645166425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322220701311279551053777133 120832762991729831645166425)
            ·
              refine ⟨90624572243797373733874819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120832762991729831645166425 90624572243797373733874819)
              ·
                refine ⟨135936858365696060600812229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90624572243797373733874819 135936858365696060600812229)
                ·
                  refine ⟨25488160943568011362652293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135936858365696060600812229 25488160943568011362652293)
                  ·
                    refine ⟨4779030176919002130497305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25488160943568011362652293 4779030176919002130497305)
                    ·
                      refine ⟨3584272632689251597872979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4779030176919002130497305 3584272632689251597872979)
                      ·
                        rfl

theorem cell23_6980346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2].length) (baseStart_6980346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980346 prefixEnd_6980346 := by exact prefixLift 6980346
  have htrace : WordTrace (prefixWord ++ tailWord_6980346) baseStart_6980346 baseEnd_6980346 := by
    simpa [prefixWord, tailWord_6980346, baseEnd_6980346] using wordTrace_append hprefix tailTrace_6980346
  have hstable : (prefixWord ++ tailWord_6980346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980346).length < 2 ^ (prefixWord ++ tailWord_6980346).sum := by decide
  have hdescent : baseEnd_6980346 < baseStart_6980346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980366 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3]
def baseStart_6980366 : Nat := 118140960795 + 6980366 * 2 ^ 59
def prefixEnd_6980366 : Nat := 4983230072969 + 3 ^ 40 * 6980366 * 2
def baseEnd_6980366 : Nat := 3584282902302341519622887

theorem tailTrace_6980366 : CollatzResearch.WordTrace tailWord_6980366 prefixEnd_6980366 3584282902302341519622887 := by
  unfold tailWord_6980366
  simp only [CollatzResearch.WordTrace]
  refine ⟨31824357978666701055734119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169729909219555738963915301 31824357978666701055734119)
  ·
    refine ⟨47736536968000051583601179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31824357978666701055734119 47736536968000051583601179)
    ·
      refine ⟨71604805452000077375401769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47736536968000051583601179 71604805452000077375401769)
      ·
        refine ⟨53703604089000058031551327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71604805452000077375401769 53703604089000058031551327)
        ·
          refine ⟨80555406133500087047326991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53703604089000058031551327 80555406133500087047326991)
          ·
            refine ⟨120833109200250130570990487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80555406133500087047326991 120833109200250130570990487)
            ·
              refine ⟨181249663800375195856485731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120833109200250130570990487 181249663800375195856485731)
              ·
                refine ⟨271874495700562793784728597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181249663800375195856485731 271874495700562793784728597)
                ·
                  refine ⟨12744116985963880958659153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 271874495700562793784728597 12744116985963880958659153)
                  ·
                    refine ⟨9558087739472910718994365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12744116985963880958659153 9558087739472910718994365)
                    ·
                      refine ⟨3584282902302341519622887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9558087739472910718994365 3584282902302341519622887)
                      ·
                        rfl

theorem cell23_6980366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_6980366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980366 prefixEnd_6980366 := by exact prefixLift 6980366
  have htrace : WordTrace (prefixWord ++ tailWord_6980366) baseStart_6980366 baseEnd_6980366 := by
    simpa [prefixWord, tailWord_6980366, baseEnd_6980366] using wordTrace_append hprefix tailTrace_6980366
  have hstable : (prefixWord ++ tailWord_6980366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980366).length < 2 ^ (prefixWord ++ tailWord_6980366).sum := by decide
  have hdescent : baseEnd_6980366 < baseStart_6980366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980383 : List Nat := [1, 1, 2, 4, 2, 3, 2, 1, 2, 2, 3]
def baseStart_6980383 : Nat := 118140960795 + 6980383 * 2 ^ 59
def prefixEnd_6980383 : Nat := 4983230072969 + 3 ^ 40 * 6980383 * 2
def baseEnd_6980383 : Nat := 3584291631473467953110309

theorem tailTrace_6980383 : CollatzResearch.WordTrace tailWord_6980383 prefixEnd_6980383 3584291631473467953110309 := by
  unfold tailWord_6980383
  simp only [CollatzResearch.WordTrace]
  refine ⟨254595483870272020349241803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169730322580181346899494535 254595483870272020349241803)
  ·
    refine ⟨381893225805408030523862705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254595483870272020349241803 381893225805408030523862705)
    ·
      refine ⟨286419919354056022892897029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381893225805408030523862705 286419919354056022892897029)
      ·
        refine ⟨53703734878885504292418193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286419919354056022892897029 53703734878885504292418193)
        ·
          refine ⟨40277801159164128219313645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53703734878885504292418193 40277801159164128219313645)
          ·
            refine ⟨15104175434686548082242617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40277801159164128219313645 15104175434686548082242617)
            ·
              refine ⟨11328131576014911061681963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15104175434686548082242617 11328131576014911061681963)
              ·
                refine ⟨16992197364022366592522945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11328131576014911061681963 16992197364022366592522945)
                ·
                  refine ⟨12744148023016774944392209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16992197364022366592522945 12744148023016774944392209)
                  ·
                    refine ⟨9558111017262581208294157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12744148023016774944392209 9558111017262581208294157)
                    ·
                      refine ⟨3584291631473467953110309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9558111017262581208294157 3584291631473467953110309)
                      ·
                        rfl

theorem cell23_6980383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_6980383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980383 prefixEnd_6980383 := by exact prefixLift 6980383
  have htrace : WordTrace (prefixWord ++ tailWord_6980383) baseStart_6980383 baseEnd_6980383 := by
    simpa [prefixWord, tailWord_6980383, baseEnd_6980383] using wordTrace_append hprefix tailTrace_6980383
  have hstable : (prefixWord ++ tailWord_6980383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980383).length < 2 ^ (prefixWord ++ tailWord_6980383).sum := by decide
  have hdescent : baseEnd_6980383 < baseStart_6980383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980399 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 7, 5]
def baseStart_6980399 : Nat := 118140960795 + 6980399 * 2 ^ 59
def prefixEnd_6980399 : Nat := 4983230072969 + 3 ^ 40 * 6980399 * 2
def baseEnd_6980399 : Nat := 1194766615721313296836745

theorem tailTrace_6980399 : CollatzResearch.WordTrace tailWord_6980399 prefixEnd_6980399 1194766615721313296836745 := by
  unfold tailWord_6980399
  simp only [CollatzResearch.WordTrace]
  refine ⟨254596067438214055081824251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169730711625476036721216167 254596067438214055081824251)
  ·
    refine ⟨381894101157321082622736377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254596067438214055081824251 381894101157321082622736377)
    ·
      refine ⟨286420575867990811967052283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381894101157321082622736377 286420575867990811967052283)
      ·
        refine ⟨429630863801986217950578425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286420575867990811967052283 429630863801986217950578425)
        ·
          refine ⟨322223147851489663462933819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429630863801986217950578425 322223147851489663462933819)
          ·
            refine ⟨483334721777234495194400729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322223147851489663462933819 483334721777234495194400729)
            ·
              refine ⟨362501041332925871395800547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483334721777234495194400729 362501041332925871395800547)
              ·
                refine ⟨543751561999388807093700821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362501041332925871395800547 543751561999388807093700821)
                ·
                  refine ⟨12744177234360675166258613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 543751561999388807093700821 12744177234360675166258613)
                  ·
                    refine ⟨1194766615721313296836745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12744177234360675166258613 1194766615721313296836745)
                    ·
                      rfl

theorem cell23_6980399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 7, 5].length) (baseStart_6980399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980399 prefixEnd_6980399 := by exact prefixLift 6980399
  have htrace : WordTrace (prefixWord ++ tailWord_6980399) baseStart_6980399 baseEnd_6980399 := by
    simpa [prefixWord, tailWord_6980399, baseEnd_6980399] using wordTrace_append hprefix tailTrace_6980399
  have hstable : (prefixWord ++ tailWord_6980399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980399).length < 2 ^ (prefixWord ++ tailWord_6980399).sum := by decide
  have hdescent : baseEnd_6980399 < baseStart_6980399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980450 : List Nat := [3, 3, 2, 1, 3, 1, 1, 3, 1, 5]
def baseStart_6980450 : Nat := 118140960795 + 6980450 * 2 ^ 59
def prefixEnd_6980450 : Nat := 4983230072969 + 3 ^ 40 * 6980450 * 2
def baseEnd_6980450 : Nat := 1194775344892439730324167

theorem tailTrace_6980450 : CollatzResearch.WordTrace tailWord_6980450 prefixEnd_6980450 1194775344892439730324167 := by
  unfold tailWord_6980450
  simp only [CollatzResearch.WordTrace]
  refine ⟨63649481890257322697982701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169731951707352860527953869 63649481890257322697982701)
  ·
    refine ⟨23868555708846496011743513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63649481890257322697982701 23868555708846496011743513)
    ·
      refine ⟨17901416781634872008807635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23868555708846496011743513 17901416781634872008807635)
      ·
        refine ⟨26852125172452308013211453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17901416781634872008807635 26852125172452308013211453)
        ·
          refine ⟨10069546939669615504954295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26852125172452308013211453 10069546939669615504954295)
          ·
            refine ⟨15104320409504423257431443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10069546939669615504954295 15104320409504423257431443)
            ·
              refine ⟨22656480614256634886147165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15104320409504423257431443 22656480614256634886147165)
              ·
                refine ⟨8496180230346238082305187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22656480614256634886147165 8496180230346238082305187)
                ·
                  refine ⟨12744270345519357123457781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8496180230346238082305187 12744270345519357123457781)
                  ·
                    refine ⟨1194775344892439730324167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12744270345519357123457781 1194775344892439730324167)
                    ·
                      rfl

theorem cell23_6980450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_6980450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980450 prefixEnd_6980450 := by exact prefixLift 6980450
  have htrace : WordTrace (prefixWord ++ tailWord_6980450) baseStart_6980450 baseEnd_6980450 := by
    simpa [prefixWord, tailWord_6980450, baseEnd_6980450] using wordTrace_append hprefix tailTrace_6980450
  have hstable : (prefixWord ++ tailWord_6980450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980450).length < 2 ^ (prefixWord ++ tailWord_6980450).sum := by decide
  have hdescent : baseEnd_6980450 < baseStart_6980450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980466 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 3, 2, 4]
def baseStart_6980466 : Nat := 118140960795 + 6980466 * 2 ^ 59
def prefixEnd_6980466 : Nat := 4983230072969 + 3 ^ 40 * 6980466 * 2
def baseEnd_6980466 : Nat := 3584334250367791128372427

theorem tailTrace_6980466 : CollatzResearch.WordTrace tailWord_6980466 prefixEnd_6980466 3584334250367791128372427 := by
  unfold tailWord_6980466
  simp only [CollatzResearch.WordTrace]
  refine ⟨63649627782242831381128313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169732340752647550349675501 63649627782242831381128313)
  ·
    refine ⟨47737220836682123535846235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63649627782242831381128313 47737220836682123535846235)
    ·
      refine ⟨71605831255023185303769353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47737220836682123535846235 71605831255023185303769353)
      ·
        refine ⟨53704373441267388977827015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71605831255023185303769353 53704373441267388977827015)
        ·
          refine ⟨80556560161901083466740523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53704373441267388977827015 80556560161901083466740523)
          ·
            refine ⟨120834840242851625200110785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80556560161901083466740523 120834840242851625200110785)
            ·
              refine ⟨90626130182138718900083089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120834840242851625200110785 90626130182138718900083089)
              ·
                refine ⟨67969597636604039175062317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90626130182138718900083089 67969597636604039175062317)
                ·
                  refine ⟨25488599113726514690648369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67969597636604039175062317 25488599113726514690648369)
                  ·
                    refine ⟨19116449335294886017986277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25488599113726514690648369 19116449335294886017986277)
                    ·
                      refine ⟨3584334250367791128372427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19116449335294886017986277 3584334250367791128372427)
                      ·
                        rfl

theorem cell23_6980466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_6980466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980466 prefixEnd_6980466 := by exact prefixLift 6980466
  have htrace : WordTrace (prefixWord ++ tailWord_6980466) baseStart_6980466 baseEnd_6980466 := by
    simpa [prefixWord, tailWord_6980466, baseEnd_6980466] using wordTrace_append hprefix tailTrace_6980466
  have hstable : (prefixWord ++ tailWord_6980466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980466).length < 2 ^ (prefixWord ++ tailWord_6980466).sum := by decide
  have hdescent : baseEnd_6980466 < baseStart_6980466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980490 : List Nat := [3, 1, 2, 4, 1, 1, 1, 4, 1, 2, 3]
def baseStart_6980490 : Nat := 118140960795 + 6980490 * 2 ^ 59
def prefixEnd_6980490 : Nat := 4983230072969 + 3 ^ 40 * 6980490 * 2
def baseEnd_6980490 : Nat := 3584346573903499034472317

theorem tailTrace_6980490 : CollatzResearch.WordTrace tailWord_6980490 prefixEnd_6980490 3584346573903499034472317 := by
  unfold tailWord_6980490
  simp only [CollatzResearch.WordTrace]
  refine ⟨63649846620221094405846731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169732924320589585082257949 63649846620221094405846731)
  ·
    refine ⟨95474769930331641608770097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63649846620221094405846731 95474769930331641608770097)
    ·
      refine ⟨71606077447748731206577573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95474769930331641608770097 71606077447748731206577573)
      ·
        refine ⟨13426139521452887101233295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71606077447748731206577573 13426139521452887101233295)
        ·
          refine ⟨20139209282179330651849943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13426139521452887101233295 20139209282179330651849943)
          ·
            refine ⟨30208813923268995977774915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20139209282179330651849943 30208813923268995977774915)
            ·
              refine ⟨45313220884903493966662373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30208813923268995977774915 45313220884903493966662373)
              ·
                refine ⟨8496228915919405118749195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45313220884903493966662373 8496228915919405118749195)
                ·
                  refine ⟨12744343373879107678123793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8496228915919405118749195 12744343373879107678123793)
                  ·
                    refine ⟨9558257530409330758592845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12744343373879107678123793 9558257530409330758592845)
                    ·
                      refine ⟨3584346573903499034472317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9558257530409330758592845 3584346573903499034472317)
                      ·
                        rfl

theorem cell23_6980490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_6980490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980490 prefixEnd_6980490 := by exact prefixLift 6980490
  have htrace : WordTrace (prefixWord ++ tailWord_6980490) baseStart_6980490 baseEnd_6980490 := by
    simpa [prefixWord, tailWord_6980490, baseEnd_6980490] using wordTrace_append hprefix tailTrace_6980490
  have hstable : (prefixWord ++ tailWord_6980490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980490).length < 2 ^ (prefixWord ++ tailWord_6980490).sum := by decide
  have hdescent : baseEnd_6980490 < baseStart_6980490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980503 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 6, 1, 3]
def baseStart_6980503 : Nat := 118140960795 + 6980503 * 2 ^ 59
def prefixEnd_6980503 : Nat := 4983230072969 + 3 ^ 40 * 6980503 * 2
def baseEnd_6980503 : Nat := 3584353249152007483609757

theorem tailTrace_6980503 : CollatzResearch.WordTrace tailWord_6980503 prefixEnd_6980503 3584353249152007483609757 := by
  unfold tailWord_6980503
  simp only [CollatzResearch.WordTrace]
  refine ⟨254599860629837280843610163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169733240419891520562406775 254599860629837280843610163)
  ·
    refine ⟨381899790944755921265415245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254599860629837280843610163 381899790944755921265415245)
    ·
      refine ⟨143212421604283470474530717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381899790944755921265415245 143212421604283470474530717)
      ·
        refine ⟨53704658101606301427949019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143212421604283470474530717 53704658101606301427949019)
        ·
          refine ⟨80556987152409452141923529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53704658101606301427949019 80556987152409452141923529)
          ·
            refine ⟨60417740364307089106442647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80556987152409452141923529 60417740364307089106442647)
            ·
              refine ⟨90626610546460633659663971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60417740364307089106442647 90626610546460633659663971)
              ·
                refine ⟨135939915819690950489495957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90626610546460633659663971 135939915819690950489495957)
                ·
                  refine ⟨6372183554048013304195123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135939915819690950489495957 6372183554048013304195123)
                  ·
                    refine ⟨9558275331072019956292685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6372183554048013304195123 9558275331072019956292685)
                    ·
                      refine ⟨3584353249152007483609757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9558275331072019956292685 3584353249152007483609757)
                      ·
                        rfl

theorem cell23_6980503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_6980503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980503 prefixEnd_6980503 := by exact prefixLift 6980503
  have htrace : WordTrace (prefixWord ++ tailWord_6980503) baseStart_6980503 baseEnd_6980503 := by
    simpa [prefixWord, tailWord_6980503, baseEnd_6980503] using wordTrace_append hprefix tailTrace_6980503
  have hstable : (prefixWord ++ tailWord_6980503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980503).length < 2 ^ (prefixWord ++ tailWord_6980503).sum := by decide
  have hdescent : baseEnd_6980503 < baseStart_6980503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980516 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 2, 2, 5]
def baseStart_6980516 : Nat := 118140960795 + 6980516 * 2 ^ 59
def prefixEnd_6980516 : Nat := 4983230072969 + 3 ^ 40 * 6980516 * 2
def baseEnd_6980516 : Nat := 3584359924400515932747197

theorem tailTrace_6980516 : CollatzResearch.WordTrace tailWord_6980516 prefixEnd_6980516 3584359924400515932747197 := by
  unfold tailWord_6980516
  simp only [CollatzResearch.WordTrace]
  refine ⟨127300167389395092031916701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169733556519193456042555601 127300167389395092031916701)
  ·
    refine ⟨47737562771023159511968763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127300167389395092031916701 47737562771023159511968763)
    ·
      refine ⟨71606344156534739267953145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47737562771023159511968763 71606344156534739267953145)
      ·
        refine ⟨53704758117401054450964859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71606344156534739267953145 53704758117401054450964859)
        ·
          refine ⟨80557137176101581676447289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53704758117401054450964859 80557137176101581676447289)
          ·
            refine ⟨60417852882076186257335467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80557137176101581676447289 60417852882076186257335467)
            ·
              refine ⟨90626779323114279386003201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60417852882076186257335467 90626779323114279386003201)
              ·
                refine ⟨67970084492335709539502401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90626779323114279386003201 67970084492335709539502401)
                ·
                  refine ⟨50977563369251782154626801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67970084492335709539502401 50977563369251782154626801)
                  ·
                    refine ⟨38233172526938836615970101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50977563369251782154626801 38233172526938836615970101)
                    ·
                      refine ⟨3584359924400515932747197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38233172526938836615970101 3584359924400515932747197)
                      ·
                        rfl

theorem cell23_6980516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_6980516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980516 prefixEnd_6980516 := by exact prefixLift 6980516
  have htrace : WordTrace (prefixWord ++ tailWord_6980516) baseStart_6980516 baseEnd_6980516 := by
    simpa [prefixWord, tailWord_6980516, baseEnd_6980516] using wordTrace_append hprefix tailTrace_6980516
  have hstable : (prefixWord ++ tailWord_6980516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980516).length < 2 ^ (prefixWord ++ tailWord_6980516).sum := by decide
  have hdescent : baseEnd_6980516 < baseStart_6980516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980537 : List Nat := [1, 2, 1, 4, 2, 2, 4, 1, 2, 1, 3]
def baseStart_6980537 : Nat := 118140960795 + 6980537 * 2 ^ 59
def prefixEnd_6980537 : Nat := 4983230072969 + 3 ^ 40 * 6980537 * 2
def baseEnd_6980537 : Nat := 3584370707494260350584601

theorem tailTrace_6980537 : CollatzResearch.WordTrace tailWord_6980537 prefixEnd_6980537 3584370707494260350584601 := by
  unfold tailWord_6980537
  simp only [CollatzResearch.WordTrace]
  refine ⟨254601100711714104650347865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169734067141142736433565243 254601100711714104650347865)
  ·
    refine ⟨190950825533785578487760899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254601100711714104650347865 190950825533785578487760899)
    ·
      refine ⟨286426238300678367731641349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190950825533785578487760899 286426238300678367731641349)
      ·
        refine ⟨53704919681377193949682753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286426238300678367731641349 53704919681377193949682753)
        ·
          refine ⟨40278689761032895462262065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53704919681377193949682753 40278689761032895462262065)
          ·
            refine ⟨30209017320774671596696549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40278689761032895462262065 30209017320774671596696549)
            ·
              refine ⟨5664190747645250924380603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30209017320774671596696549 5664190747645250924380603)
              ·
                refine ⟨8496286121467876386570905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5664190747645250924380603 8496286121467876386570905)
                ·
                  refine ⟨6372214591100907289928179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8496286121467876386570905 6372214591100907289928179)
                  ·
                    refine ⟨9558321886651360934892269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6372214591100907289928179 9558321886651360934892269)
                    ·
                      refine ⟨3584370707494260350584601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9558321886651360934892269 3584370707494260350584601)
                      ·
                        rfl

theorem cell23_6980537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_6980537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980537 prefixEnd_6980537 := by exact prefixLift 6980537
  have htrace : WordTrace (prefixWord ++ tailWord_6980537) baseStart_6980537 baseEnd_6980537 := by
    simpa [prefixWord, tailWord_6980537, baseEnd_6980537] using wordTrace_append hprefix tailTrace_6980537
  have hstable : (prefixWord ++ tailWord_6980537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980537).length < 2 ^ (prefixWord ++ tailWord_6980537).sum := by decide
  have hdescent : baseEnd_6980537 < baseStart_6980537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980564 : List Nat := [2, 4, 1, 2, 1, 3, 3, 1, 1, 3, 2]
def baseStart_6980564 : Nat := 118140960795 + 6980564 * 2 ^ 59
def prefixEnd_6980564 : Nat := 4983230072969 + 3 ^ 40 * 6980564 * 2
def baseEnd_6980564 : Nat := 3584384571471931744946977

theorem tailTrace_6980564 : CollatzResearch.WordTrace tailWord_6980564 prefixEnd_6980564 3584384571471931744946977 := by
  unfold tailWord_6980564
  simp only [CollatzResearch.WordTrace]
  refine ⟨127301042741308144130790373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169734723655077525507720497 127301042741308144130790373)
  ·
    refine ⟨23868945513995277024523195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127301042741308144130790373 23868945513995277024523195)
    ·
      refine ⟨35803418270992915536784793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23868945513995277024523195 35803418270992915536784793)
      ·
        refine ⟨26852563703244686652588595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35803418270992915536784793 26852563703244686652588595)
        ·
          refine ⟨40278845554867029978882893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26852563703244686652588595 40278845554867029978882893)
          ·
            refine ⟨15104567083075136242081085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40278845554867029978882893 15104567083075136242081085)
            ·
              refine ⟨5664212656153176090780407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15104567083075136242081085 5664212656153176090780407)
              ·
                refine ⟨8496318984229764136170611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5664212656153176090780407 8496318984229764136170611)
                ·
                  refine ⟨12744478476344646204255917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8496318984229764136170611 12744478476344646204255917)
                  ·
                    refine ⟨4779179428629242326595969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12744478476344646204255917 4779179428629242326595969)
                    ·
                      refine ⟨3584384571471931744946977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4779179428629242326595969 3584384571471931744946977)
                      ·
                        rfl

theorem cell23_6980564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_6980564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980564 prefixEnd_6980564 := by exact prefixLift 6980564
  have htrace : WordTrace (prefixWord ++ tailWord_6980564) baseStart_6980564 baseEnd_6980564 := by
    simpa [prefixWord, tailWord_6980564, baseEnd_6980564] using wordTrace_append hprefix tailTrace_6980564
  have hstable : (prefixWord ++ tailWord_6980564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980564).length < 2 ^ (prefixWord ++ tailWord_6980564).sum := by decide
  have hdescent : baseEnd_6980564 < baseStart_6980564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980590 : List Nat := [4, 1, 2, 1, 4, 1, 1, 1, 2, 2, 4]
def baseStart_6980590 : Nat := 118140960795 + 6980590 * 2 ^ 59
def prefixEnd_6980590 : Nat := 4983230072969 + 3 ^ 40 * 6980590 * 2
def baseEnd_6980590 : Nat := 3584397921968948643221857

theorem tailTrace_6980590 : CollatzResearch.WordTrace tailWord_6980590 prefixEnd_6980590 3584397921968948643221857 := by
  unfold tailWord_6980590
  simp only [CollatzResearch.WordTrace]
  refine ⟨31825379222565261837753403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169735355853681396468018149 31825379222565261837753403)
  ·
    refine ⟨47738068833847892756630105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31825379222565261837753403 47738068833847892756630105)
    ·
      refine ⟨35803551625385919567472579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47738068833847892756630105 35803551625385919567472579)
      ·
        refine ⟨53705327438078879351208869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35803551625385919567472579 53705327438078879351208869)
        ·
          refine ⟨10069748894639789878351663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53705327438078879351208869 10069748894639789878351663)
          ·
            refine ⟨15104623341959684817527495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10069748894639789878351663 15104623341959684817527495)
            ·
              refine ⟨22656935012939527226291243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15104623341959684817527495 22656935012939527226291243)
              ·
                refine ⟨33985402519409290839436865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22656935012939527226291243 33985402519409290839436865)
                ·
                  refine ⟨25489051889556968129577649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33985402519409290839436865 25489051889556968129577649)
                  ·
                    refine ⟨19116788917167726097183237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25489051889556968129577649 19116788917167726097183237)
                    ·
                      refine ⟨3584397921968948643221857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19116788917167726097183237 3584397921968948643221857)
                      ·
                        rfl

theorem cell23_6980590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_6980590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980590 prefixEnd_6980590 := by exact prefixLift 6980590
  have htrace : WordTrace (prefixWord ++ tailWord_6980590) baseStart_6980590 baseEnd_6980590 := by
    simpa [prefixWord, tailWord_6980590, baseEnd_6980590] using wordTrace_append hprefix tailTrace_6980590
  have hstable : (prefixWord ++ tailWord_6980590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980590).length < 2 ^ (prefixWord ++ tailWord_6980590).sum := by decide
  have hdescent : baseEnd_6980590 < baseStart_6980590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980593 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 1, 5, 3]
def baseStart_6980593 : Nat := 118140960795 + 6980593 * 2 ^ 59
def prefixEnd_6980593 : Nat := 4983230072969 + 3 ^ 40 * 6980593 * 2
def baseEnd_6980593 : Nat := 3584399462410912131484343

theorem tailTrace_6980593 : CollatzResearch.WordTrace tailWord_6980593 prefixEnd_6980593 3584399462410912131484343 := by
  unfold tailWord_6980593
  simp only [CollatzResearch.WordTrace]
  refine ⟨254603143199511226214386433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169735428799674150809590955 254603143199511226214386433)
  ·
    refine ⟨190952357399633419660789825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254603143199511226214386433 190952357399633419660789825)
    ·
      refine ⟨143214268049725064745592369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190952357399633419660789825 143214268049725064745592369)
      ·
        refine ⟨107410701037293798559194277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143214268049725064745592369 107410701037293798559194277)
        ·
          refine ⟨20139506444492587229848927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107410701037293798559194277 20139506444492587229848927)
          ·
            refine ⟨30209259666738880844773391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20139506444492587229848927 30209259666738880844773391)
            ·
              refine ⟨45313889500108321267160087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30209259666738880844773391 45313889500108321267160087)
              ·
                refine ⟨67970834250162481900740131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45313889500108321267160087 67970834250162481900740131)
                ·
                  refine ⟨101956251375243722851110197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67970834250162481900740131 101956251375243722851110197)
                  ·
                    refine ⟨9558398566429099017291581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101956251375243722851110197 9558398566429099017291581)
                    ·
                      refine ⟨3584399462410912131484343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9558398566429099017291581 3584399462410912131484343)
                      ·
                        rfl

theorem cell23_6980593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_6980593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980593 prefixEnd_6980593 := by exact prefixLift 6980593
  have htrace : WordTrace (prefixWord ++ tailWord_6980593) baseStart_6980593 baseEnd_6980593 := by
    simpa [prefixWord, tailWord_6980593, baseEnd_6980593] using wordTrace_append hprefix tailTrace_6980593
  have hstable : (prefixWord ++ tailWord_6980593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980593).length < 2 ^ (prefixWord ++ tailWord_6980593).sum := by decide
  have hdescent : baseEnd_6980593 < baseStart_6980593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980594 : List Nat := [3, 2, 1, 5, 1, 1, 2, 1, 1, 4, 2]
def baseStart_6980594 : Nat := 118140960795 + 6980594 * 2 ^ 59
def prefixEnd_6980594 : Nat := 4983230072969 + 3 ^ 40 * 6980594 * 2
def baseEnd_6980594 : Nat := 3584399975891566627571839

theorem tailTrace_6980594 : CollatzResearch.WordTrace tailWord_6980594 prefixEnd_6980594 3584399975891566627571839 := by
  unfold tailWord_6980594
  simp only [CollatzResearch.WordTrace]
  refine ⟨63650794918126900846293209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169735453115005068923448557 63650794918126900846293209)
  ·
    refine ⟨47738096188595175634719907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63650794918126900846293209 47738096188595175634719907)
    ·
      refine ⟨71607144282892763452079861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47738096188595175634719907 71607144282892763452079861)
      ·
        refine ⟨6713169776521196573632487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71607144282892763452079861 6713169776521196573632487)
        ·
          refine ⟨10069754664781794860448731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6713169776521196573632487 10069754664781794860448731)
          ·
            refine ⟨15104631997172692290673097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10069754664781794860448731 15104631997172692290673097)
            ·
              refine ⟨11328473997879519218004823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15104631997172692290673097 11328473997879519218004823)
              ·
                refine ⟨16992710996819278827007235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11328473997879519218004823 16992710996819278827007235)
                ·
                  refine ⟨25489066495228918240510853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16992710996819278827007235 25489066495228918240510853)
                  ·
                    refine ⟨4779199967855422170095785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25489066495228918240510853 4779199967855422170095785)
                    ·
                      refine ⟨3584399975891566627571839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4779199967855422170095785 3584399975891566627571839)
                      ·
                        rfl

theorem cell23_6980594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_6980594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980594 prefixEnd_6980594 := by exact prefixLift 6980594
  have htrace : WordTrace (prefixWord ++ tailWord_6980594) baseStart_6980594 baseEnd_6980594 := by
    simpa [prefixWord, tailWord_6980594, baseEnd_6980594] using wordTrace_append hprefix tailTrace_6980594
  have hstable : (prefixWord ++ tailWord_6980594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980594).length < 2 ^ (prefixWord ++ tailWord_6980594).sum := by decide
  have hdescent : baseEnd_6980594 < baseStart_6980594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980603 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 4, 5, 2]
def baseStart_6980603 : Nat := 118140960795 + 6980603 * 2 ^ 59
def prefixEnd_6980603 : Nat := 4983230072969 + 3 ^ 40 * 6980603 * 2
def baseEnd_6980603 : Nat := 3584404597217457092359297

theorem tailTrace_6980603 : CollatzResearch.WordTrace tailWord_6980603 prefixEnd_6980603 3584404597217457092359297 := by
  unfold tailWord_6980603
  simp only [CollatzResearch.WordTrace]
  refine ⟨254603507929474997922250463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169735671952983331948166975 254603507929474997922250463)
  ·
    refine ⟨381905261894212496883375695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254603507929474997922250463 381905261894212496883375695)
    ·
      refine ⟨572857892841318745325063543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381905261894212496883375695 572857892841318745325063543)
      ·
        refine ⟨859286839261978117987595315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572857892841318745325063543 859286839261978117987595315)
        ·
          refine ⟨1288930258892967176981392973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859286839261978117987595315 1288930258892967176981392973)
          ·
            refine ⟨483348847084862691368022365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1288930258892967176981392973 483348847084862691368022365)
            ·
              refine ⟨181255817656823509263008387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 483348847084862691368022365 181255817656823509263008387)
              ·
                refine ⟨271883726485235263894512581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181255817656823509263008387 271883726485235263894512581)
                ·
                  refine ⟨50978198715981611980221109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 271883726485235263894512581 50978198715981611980221109)
                  ·
                    refine ⟨4779206129623276123145729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50978198715981611980221109 4779206129623276123145729)
                    ·
                      refine ⟨3584404597217457092359297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4779206129623276123145729 3584404597217457092359297)
                      ·
                        rfl

theorem cell23_6980603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 5, 2].length) (baseStart_6980603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980603 prefixEnd_6980603 := by exact prefixLift 6980603
  have htrace : WordTrace (prefixWord ++ tailWord_6980603) baseStart_6980603 baseEnd_6980603 := by
    simpa [prefixWord, tailWord_6980603, baseEnd_6980603] using wordTrace_append hprefix tailTrace_6980603
  have hstable : (prefixWord ++ tailWord_6980603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980603).length < 2 ^ (prefixWord ++ tailWord_6980603).sum := by decide
  have hdescent : baseEnd_6980603 < baseStart_6980603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980633 : List Nat := [1, 2, 1, 2, 1, 1, 4, 4, 2, 1, 4]
def baseStart_6980633 : Nat := 118140960795 + 6980633 * 2 ^ 59
def prefixEnd_6980633 : Nat := 4983230072969 + 3 ^ 40 * 6980633 * 2
def baseEnd_6980633 : Nat := 3584420001637091974984159

theorem tailTrace_6980633 : CollatzResearch.WordTrace tailWord_6980633 prefixEnd_6980633 3584420001637091974984159 := by
  unfold tailWord_6980633
  simp only [CollatzResearch.WordTrace]
  refine ⟨254604602119366313045842553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169736401412910875363895035 254604602119366313045842553)
  ·
    refine ⟨190953451589524734784381915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254604602119366313045842553 190953451589524734784381915)
    ·
      refine ⟨286430177384287102176572873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190953451589524734784381915 286430177384287102176572873)
      ·
        refine ⟨214822633038215326632429655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286430177384287102176572873 214822633038215326632429655)
        ·
          refine ⟨322233949557322989948644483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214822633038215326632429655 322233949557322989948644483)
          ·
            refine ⟨483350924335984484922966725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322233949557322989948644483 483350924335984484922966725)
            ·
              refine ⟨90628298312997090923056261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 483350924335984484922966725 90628298312997090923056261)
              ·
                refine ⟨16992805933686954548073049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90628298312997090923056261 16992805933686954548073049)
                ·
                  refine ⟨12744604450265215911054787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16992805933686954548073049 12744604450265215911054787)
                  ·
                    refine ⟨19116906675397823866582181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12744604450265215911054787 19116906675397823866582181)
                    ·
                      refine ⟨3584420001637091974984159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19116906675397823866582181 3584420001637091974984159)
                      ·
                        rfl

theorem cell23_6980633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_6980633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980633 prefixEnd_6980633 := by exact prefixLift 6980633
  have htrace : WordTrace (prefixWord ++ tailWord_6980633) baseStart_6980633 baseEnd_6980633 := by
    simpa [prefixWord, tailWord_6980633, baseEnd_6980633] using wordTrace_append hprefix tailTrace_6980633
  have hstable : (prefixWord ++ tailWord_6980633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980633).length < 2 ^ (prefixWord ++ tailWord_6980633).sum := by decide
  have hdescent : baseEnd_6980633 < baseStart_6980633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980677 : List Nat := [1, 3, 1, 1, 1, 3, 5, 3, 1, 4]
def baseStart_6980677 : Nat := 118140960795 + 6980677 * 2 ^ 59
def prefixEnd_6980677 : Nat := 4983230072969 + 3 ^ 40 * 6980677 * 2
def baseEnd_6980677 : Nat := 1194814198261963267611319

theorem tailTrace_6980677 : CollatzResearch.WordTrace tailWord_6980677 prefixEnd_6980677 1194814198261963267611319 := by
  unfold tailWord_6980677
  simp only [CollatzResearch.WordTrace]
  refine ⟨254606206931206908560444285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169737471287471272373629523 254606206931206908560444285)
  ·
    refine ⟨95477327599202590710166607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254606206931206908560444285 95477327599202590710166607)
    ·
      refine ⟨143215991398803886065249911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95477327599202590710166607 143215991398803886065249911)
      ·
        refine ⟨214823987098205829097874867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143215991398803886065249911 214823987098205829097874867)
        ·
          refine ⟨322235980647308743646812301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214823987098205829097874867 322235980647308743646812301)
          ·
            refine ⟨120838492742740778867554613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322235980647308743646812301 120838492742740778867554613)
            ·
              refine ⟨11328608694631948018833245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120838492742740778867554613 11328608694631948018833245)
              ·
                refine ⟨4248228260486980507062467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11328608694631948018833245 4248228260486980507062467)
                ·
                  refine ⟨6372342390730470760593701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4248228260486980507062467 6372342390730470760593701)
                  ·
                    refine ⟨1194814198261963267611319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6372342390730470760593701 1194814198261963267611319)
                    ·
                      rfl

theorem cell23_6980677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 3, 1, 4].length) (baseStart_6980677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980677 prefixEnd_6980677 := by exact prefixLift 6980677
  have htrace : WordTrace (prefixWord ++ tailWord_6980677) baseStart_6980677 baseEnd_6980677 := by
    simpa [prefixWord, tailWord_6980677, baseEnd_6980677] using wordTrace_append hprefix tailTrace_6980677
  have hstable : (prefixWord ++ tailWord_6980677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980677).length < 2 ^ (prefixWord ++ tailWord_6980677).sum := by decide
  have hdescent : baseEnd_6980677 < baseStart_6980677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980703 : List Nat := [1, 1, 2, 3, 1, 1, 4, 2, 3, 5]
def baseStart_6980703 : Nat := 118140960795 + 6980703 * 2 ^ 59
def prefixEnd_6980703 : Nat := 4983230072969 + 3 ^ 40 * 6980703 * 2
def baseEnd_6980703 : Nat := 1194818648427635567036279

theorem tailTrace_6980703 : CollatzResearch.WordTrace tailWord_6980703 prefixEnd_6980703 1194818648427635567036279 := by
  unfold tailWord_6980703
  simp only [CollatzResearch.WordTrace]
  refine ⟨254607155229112715000890763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169738103486075143333927175 254607155229112715000890763)
  ·
    refine ⟨381910732843669072501336145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254607155229112715000890763 381910732843669072501336145)
    ·
      refine ⟨286433049632751804376002109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381910732843669072501336145 286433049632751804376002109)
      ·
        refine ⟨107412393612281926641000791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286433049632751804376002109 107412393612281926641000791)
        ·
          refine ⟨161118590418422889961501187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107412393612281926641000791 161118590418422889961501187)
          ·
            refine ⟨241677885627634334942251781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161118590418422889961501187 241677885627634334942251781)
            ·
              refine ⟨45314603555181437801672209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 241677885627634334942251781 45314603555181437801672209)
              ·
                refine ⟨33985952666386078351254157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45314603555181437801672209 33985952666386078351254157)
                ·
                  refine ⟨12744732249894779381720309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33985952666386078351254157 12744732249894779381720309)
                  ·
                    refine ⟨1194818648427635567036279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12744732249894779381720309 1194818648427635567036279)
                    ·
                      rfl

theorem cell23_6980703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 5].length) (baseStart_6980703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980703 prefixEnd_6980703 := by exact prefixLift 6980703
  have htrace : WordTrace (prefixWord ++ tailWord_6980703) baseStart_6980703 baseEnd_6980703 := by
    simpa [prefixWord, tailWord_6980703, baseEnd_6980703] using wordTrace_append hprefix tailTrace_6980703
  have hstable : (prefixWord ++ tailWord_6980703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980703).length < 2 ^ (prefixWord ++ tailWord_6980703).sum := by decide
  have hdescent : baseEnd_6980703 < baseStart_6980703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980727 : List Nat := [1, 1, 3, 1, 1, 4, 4, 1, 2, 3, 2]
def baseStart_6980727 : Nat := 118140960795 + 6980727 * 2 ^ 59
def prefixEnd_6980727 : Nat := 4983230072969 + 3 ^ 40 * 6980727 * 2
def baseEnd_6980727 : Nat := 3584468268818614607208727

theorem tailTrace_6980727 : CollatzResearch.WordTrace tailWord_6980727 prefixEnd_6980727 3584468268818614607208727 := by
  unfold tailWord_6980727
  simp only [CollatzResearch.WordTrace]
  refine ⟨254608030581025767099764435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169738687054017178066509623 254608030581025767099764435)
  ·
    refine ⟨381912045871538650649646653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254608030581025767099764435 381912045871538650649646653)
    ·
      refine ⟨143217017201826993993617495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381912045871538650649646653 143217017201826993993617495)
      ·
        refine ⟨214825525802740490990426243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143217017201826993993617495 214825525802740490990426243)
        ·
          refine ⟨322238288704110736485639365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214825525802740490990426243 322238288704110736485639365)
          ·
            refine ⟨60419679132020763091057381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 322238288704110736485639365 60419679132020763091057381)
            ·
              refine ⟨11328689837253893079573259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60419679132020763091057381 11328689837253893079573259)
              ·
                refine ⟨16993034755880839619359889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11328689837253893079573259 16993034755880839619359889)
                ·
                  refine ⟨12744776066910629714519917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16993034755880839619359889 12744776066910629714519917)
                  ·
                    refine ⟨4779291025091486142944969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12744776066910629714519917 4779291025091486142944969)
                    ·
                      refine ⟨3584468268818614607208727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4779291025091486142944969 3584468268818614607208727)
                      ·
                        rfl

theorem cell23_6980727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 3, 2].length) (baseStart_6980727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980727 prefixEnd_6980727 := by exact prefixLift 6980727
  have htrace : WordTrace (prefixWord ++ tailWord_6980727) baseStart_6980727 baseEnd_6980727 := by
    simpa [prefixWord, tailWord_6980727, baseEnd_6980727] using wordTrace_append hprefix tailTrace_6980727
  have hstable : (prefixWord ++ tailWord_6980727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980727).length < 2 ^ (prefixWord ++ tailWord_6980727).sum := by decide
  have hdescent : baseEnd_6980727 < baseStart_6980727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980767 : List Nat := [1, 1, 2, 6, 2, 1, 2, 1, 1, 6]
def baseStart_6980767 : Nat := 118140960795 + 6980767 * 2 ^ 59
def prefixEnd_6980767 : Nat := 4983230072969 + 3 ^ 40 * 6980767 * 2
def baseEnd_6980767 : Nat := 1194829602681598150236181

theorem tailTrace_6980767 : CollatzResearch.WordTrace tailWord_6980767 prefixEnd_6980767 1194829602681598150236181 := by
  unfold tailWord_6980767
  simp only [CollatzResearch.WordTrace]
  refine ⟨254609489500880853931220555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169739659667253902620813703 254609489500880853931220555)
  ·
    refine ⟨381914234251321280896830833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254609489500880853931220555 381914234251321280896830833)
    ·
      refine ⟨286435675688490960672623125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381914234251321280896830833 286435675688490960672623125)
      ·
        refine ⟨13426672297898013781529209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 286435675688490960672623125 13426672297898013781529209)
        ·
          refine ⟨10070004223423510336146907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13426672297898013781529209 10070004223423510336146907)
          ·
            refine ⟨15105006335135265504220361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10070004223423510336146907 15105006335135265504220361)
            ·
              refine ⟨11328754751351449128165271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15105006335135265504220361 11328754751351449128165271)
              ·
                refine ⟨16993132127027173692247907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11328754751351449128165271 16993132127027173692247907)
                ·
                  refine ⟨25489698190540760538371861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16993132127027173692247907 25489698190540760538371861)
                  ·
                    refine ⟨1194829602681598150236181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25489698190540760538371861 1194829602681598150236181)
                    ·
                      rfl

theorem cell23_6980767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 1, 6].length) (baseStart_6980767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980767 prefixEnd_6980767 := by exact prefixLift 6980767
  have htrace : WordTrace (prefixWord ++ tailWord_6980767) baseStart_6980767 baseEnd_6980767 := by
    simpa [prefixWord, tailWord_6980767, baseEnd_6980767] using wordTrace_append hprefix tailTrace_6980767
  have hstable : (prefixWord ++ tailWord_6980767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980767).length < 2 ^ (prefixWord ++ tailWord_6980767).sum := by decide
  have hdescent : baseEnd_6980767 < baseStart_6980767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980791 : List Nat := [1, 1, 3, 1, 4, 1, 4, 3, 1, 2, 2]
def baseStart_6980791 : Nat := 118140960795 + 6980791 * 2 ^ 59
def prefixEnd_6980791 : Nat := 4983230072969 + 3 ^ 40 * 6980791 * 2
def baseEnd_6980791 : Nat := 3584501131580502356808433

theorem tailTrace_6980791 : CollatzResearch.WordTrace tailWord_6980791 prefixEnd_6980791 3584501131580502356808433 := by
  unfold tailWord_6980791
  simp only [CollatzResearch.WordTrace]
  refine ⟨254610364852793906030094227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169740243235195937353396151 254610364852793906030094227)
  ·
    refine ⟨381915547279190859045141341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254610364852793906030094227 381915547279190859045141341)
    ·
      refine ⟨143218330229696572141928003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381915547279190859045141341 143218330229696572141928003)
      ·
        refine ⟨214827495344544858212892005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143218330229696572141928003 214827495344544858212892005)
        ·
          refine ⟨40280155377102160914917251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214827495344544858212892005 40280155377102160914917251)
          ·
            refine ⟨60420233065653241372375877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40280155377102160914917251 60420233065653241372375877)
            ·
              refine ⟨11328793699809982757320477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60420233065653241372375877 11328793699809982757320477)
              ·
                refine ⟨4248297637428743533995179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11328793699809982757320477 4248297637428743533995179)
                ·
                  refine ⟨6372446456143115300992769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4248297637428743533995179 6372446456143115300992769)
                  ·
                    refine ⟨4779334842107336475744577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6372446456143115300992769 4779334842107336475744577)
                    ·
                      refine ⟨3584501131580502356808433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4779334842107336475744577 3584501131580502356808433)
                      ·
                        rfl

theorem cell23_6980791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3, 1, 2, 2].length) (baseStart_6980791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980791 prefixEnd_6980791 := by exact prefixLift 6980791
  have htrace : WordTrace (prefixWord ++ tailWord_6980791) baseStart_6980791 baseEnd_6980791 := by
    simpa [prefixWord, tailWord_6980791, baseEnd_6980791] using wordTrace_append hprefix tailTrace_6980791
  have hstable : (prefixWord ++ tailWord_6980791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980791).length < 2 ^ (prefixWord ++ tailWord_6980791).sum := by decide
  have hdescent : baseEnd_6980791 < baseStart_6980791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980801 : List Nat := [1, 2, 6, 1, 1, 3, 1, 2, 2, 4]
def baseStart_6980801 : Nat := 118140960795 + 6980801 * 2 ^ 59
def prefixEnd_6980801 : Nat := 4983230072969 + 3 ^ 40 * 6980801 * 2
def baseEnd_6980801 : Nat := 1194835422129015772561129

theorem tailTrace_6980801 : CollatzResearch.WordTrace tailWord_6980801 prefixEnd_6980801 1194835422129015772561129 := by
  unfold tailWord_6980801
  simp only [CollatzResearch.WordTrace]
  refine ⟨254610729582757677737958257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169740486388505118491972171 254610729582757677737958257)
  ·
    refine ⟨190958047187068258303468693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254610729582757677737958257 190958047187068258303468693)
    ·
      refine ⟨8951158461893824607975095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 190958047187068258303468693 8951158461893824607975095)
      ·
        refine ⟨13426737692840736911962643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8951158461893824607975095 13426737692840736911962643)
        ·
          refine ⟨20140106539261105367943965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13426737692840736911962643 20140106539261105367943965)
          ·
            refine ⟨7552539952222914512978987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20140106539261105367943965 7552539952222914512978987)
            ·
              refine ⟨11328809928334371769468481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7552539952222914512978987 11328809928334371769468481)
              ·
                refine ⟨8496607446250778827101361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11328809928334371769468481 8496607446250778827101361)
                ·
                  refine ⟨6372455584688084120326021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8496607446250778827101361 6372455584688084120326021)
                  ·
                    refine ⟨1194835422129015772561129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6372455584688084120326021 1194835422129015772561129)
                    ·
                      rfl

theorem cell23_6980801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_6980801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980801 prefixEnd_6980801 := by exact prefixLift 6980801
  have htrace : WordTrace (prefixWord ++ tailWord_6980801) baseStart_6980801 baseEnd_6980801 := by
    simpa [prefixWord, tailWord_6980801, baseEnd_6980801] using wordTrace_append hprefix tailTrace_6980801
  have hstable : (prefixWord ++ tailWord_6980801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980801).length < 2 ^ (prefixWord ++ tailWord_6980801).sum := by decide
  have hdescent : baseEnd_6980801 < baseStart_6980801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980803 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 5]
def baseStart_6980803 : Nat := 118140960795 + 6980803 * 2 ^ 59
def prefixEnd_6980803 : Nat := 4983230072969 + 3 ^ 40 * 6980803 * 2
def baseEnd_6980803 : Nat := 3584507293348356309858377

theorem tailTrace_6980803 : CollatzResearch.WordTrace tailWord_6980803 prefixEnd_6980803 3584507293348356309858377 := by
  unfold tailWord_6980803
  simp only [CollatzResearch.WordTrace]
  refine ⟨254610802528750432079531063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169740535019166954719687375 254610802528750432079531063)
  ·
    refine ⟨381916203793125648119296595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254610802528750432079531063 381916203793125648119296595)
    ·
      refine ⟨572874305689688472178944893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381916203793125648119296595 572874305689688472178944893)
      ·
        refine ⟨214827864633633177067104335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 572874305689688472178944893 214827864633633177067104335)
        ·
          refine ⟨322241796950449765600656503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214827864633633177067104335 322241796950449765600656503)
          ·
            refine ⟨483362695425674648400984755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322241796950449765600656503 483362695425674648400984755)
            ·
              refine ⟨725044043138511972601477133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483362695425674648400984755 725044043138511972601477133)
              ·
                refine ⟨271891516176941989725553925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 725044043138511972601477133 271891516176941989725553925)
                ·
                  refine ⟨50979659283176623073541361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 271891516176941989725553925 50979659283176623073541361)
                  ·
                    refine ⟨38234744462382467305156021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50979659283176623073541361 38234744462382467305156021)
                    ·
                      refine ⟨3584507293348356309858377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38234744462382467305156021 3584507293348356309858377)
                      ·
                        rfl

theorem cell23_6980803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_6980803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980803 prefixEnd_6980803 := by exact prefixLift 6980803
  have htrace : WordTrace (prefixWord ++ tailWord_6980803) baseStart_6980803 baseEnd_6980803 := by
    simpa [prefixWord, tailWord_6980803, baseEnd_6980803] using wordTrace_append hprefix tailTrace_6980803
  have hstable : (prefixWord ++ tailWord_6980803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980803).length < 2 ^ (prefixWord ++ tailWord_6980803).sum := by decide
  have hdescent : baseEnd_6980803 < baseStart_6980803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980824 : List Nat := [2, 1, 2, 2, 5, 2, 1, 1, 1, 3, 3]
def baseStart_6980824 : Nat := 118140960795 + 6980824 * 2 ^ 59
def prefixEnd_6980824 : Nat := 4983230072969 + 3 ^ 40 * 6980824 * 2
def baseEnd_6980824 : Nat := 3584518076442100727695781

theorem tailTrace_6980824 : CollatzResearch.WordTrace tailWord_6980824 prefixEnd_6980824 3584518076442100727695781 := by
  unfold tailWord_6980824
  simp only [CollatzResearch.WordTrace]
  refine ⟨127305784230837176333022763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169741045641116235110697017 127305784230837176333022763)
  ·
    refine ⟨190958676346255764499534145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127305784230837176333022763 190958676346255764499534145)
    ·
      refine ⟨143219007259691823374650609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190958676346255764499534145 143219007259691823374650609)
      ·
        refine ⟨107414255444768867530987957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143219007259691823374650609 107414255444768867530987957)
        ·
          refine ⟨10070086447947081331030121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107414255444768867530987957 10070086447947081331030121)
          ·
            refine ⟨7552564835960310998272591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10070086447947081331030121 7552564835960310998272591)
            ·
              refine ⟨11328847253940466497408887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7552564835960310998272591 11328847253940466497408887)
              ·
                refine ⟨16993270880910699746113331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11328847253940466497408887 16993270880910699746113331)
                ·
                  refine ⟨25489906321366049619169997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16993270880910699746113331 25489906321366049619169997)
                  ·
                    refine ⟨9558714870512268607188749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25489906321366049619169997 9558714870512268607188749)
                    ·
                      refine ⟨3584518076442100727695781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9558714870512268607188749 3584518076442100727695781)
                      ·
                        rfl

theorem cell23_6980824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_6980824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980824 prefixEnd_6980824 := by exact prefixLift 6980824
  have htrace : WordTrace (prefixWord ++ tailWord_6980824) baseStart_6980824 baseEnd_6980824 := by
    simpa [prefixWord, tailWord_6980824, baseEnd_6980824] using wordTrace_append hprefix tailTrace_6980824
  have hstable : (prefixWord ++ tailWord_6980824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980824).length < 2 ^ (prefixWord ++ tailWord_6980824).sum := by decide
  have hdescent : baseEnd_6980824 < baseStart_6980824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980864 : List Nat := [2, 1, 1, 2, 1, 1, 3, 6, 2, 2, 2]
def baseStart_6980864 : Nat := 118140960795 + 6980864 * 2 ^ 59
def prefixEnd_6980864 : Nat := 4983230072969 + 3 ^ 40 * 6980864 * 2
def baseEnd_6980864 : Nat := 3584538615668280571195597

theorem tailTrace_6980864 : CollatzResearch.WordTrace tailWord_6980864 prefixEnd_6980864 3584538615668280571195597 := by
  unfold tailWord_6980864
  simp only [CollatzResearch.WordTrace]
  refine ⟨127306513690764719748750823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169742018254352959665001097 127306513690764719748750823)
  ·
    refine ⟨190959770536147079623126235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127306513690764719748750823 190959770536147079623126235)
    ·
      refine ⟨286439655804220619434689353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190959770536147079623126235 286439655804220619434689353)
      ·
        refine ⟨214829741853165464576017015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286439655804220619434689353 214829741853165464576017015)
        ·
          refine ⟨322244612779748196864025523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214829741853165464576017015 322244612779748196864025523)
          ·
            refine ⟨483366919169622295296038285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322244612779748196864025523 483366919169622295296038285)
            ·
              refine ⟨181262594688608360736014357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 483366919169622295296038285 181262594688608360736014357)
              ·
                refine ⟨8496684126028516909500673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 181262594688608360736014357 8496684126028516909500673)
                ·
                  refine ⟨6372513094521387682125505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8496684126028516909500673 6372513094521387682125505)
                  ·
                    refine ⟨4779384820891040761594129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6372513094521387682125505 4779384820891040761594129)
                    ·
                      refine ⟨3584538615668280571195597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4779384820891040761594129 3584538615668280571195597)
                      ·
                        rfl

theorem cell23_6980864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 2, 2, 2].length) (baseStart_6980864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980864 prefixEnd_6980864 := by exact prefixLift 6980864
  have htrace : WordTrace (prefixWord ++ tailWord_6980864) baseStart_6980864 baseEnd_6980864 := by
    simpa [prefixWord, tailWord_6980864, baseEnd_6980864] using wordTrace_append hprefix tailTrace_6980864
  have hstable : (prefixWord ++ tailWord_6980864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980864).length < 2 ^ (prefixWord ++ tailWord_6980864).sum := by decide
  have hdescent : baseEnd_6980864 < baseStart_6980864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980880 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 3]
def baseStart_6980880 : Nat := 118140960795 + 6980880 * 2 ^ 59
def prefixEnd_6980880 : Nat := 4983230072969 + 3 ^ 40 * 6980880 * 2
def baseEnd_6980880 : Nat := 3584546831358752508595523

theorem tailTrace_6980880 : CollatzResearch.WordTrace tailWord_6980880 prefixEnd_6980880 3584546831358752508595523 := by
  unfold tailWord_6980880
  simp only [CollatzResearch.WordTrace]
  refine ⟨127306805474735737115042047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169742407299647649486722729 127306805474735737115042047)
  ·
    refine ⟨190960208212103605672563071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127306805474735737115042047 190960208212103605672563071)
    ·
      refine ⟨286440312318155408508844607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190960208212103605672563071 286440312318155408508844607)
      ·
        refine ⟨429660468477233112763266911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286440312318155408508844607 429660468477233112763266911)
        ·
          refine ⟨644490702715849669144900367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429660468477233112763266911 644490702715849669144900367)
          ·
            refine ⟨966736054073774503717350551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644490702715849669144900367 966736054073774503717350551)
            ·
              refine ⟨1450104081110661755576025827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 966736054073774503717350551 1450104081110661755576025827)
              ·
                refine ⟨2175156121665992633364038741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1450104081110661755576025827 2175156121665992633364038741)
                ·
                  refine ⟨25490110800773351172234829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2175156121665992633364038741 25490110800773351172234829)
                  ·
                    refine ⟨9558791550290006689588061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25490110800773351172234829 9558791550290006689588061)
                    ·
                      refine ⟨3584546831358752508595523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9558791550290006689588061 3584546831358752508595523)
                      ·
                        rfl

theorem cell23_6980880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 3].length) (baseStart_6980880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980880 prefixEnd_6980880 := by exact prefixLift 6980880
  have htrace : WordTrace (prefixWord ++ tailWord_6980880) baseStart_6980880 baseEnd_6980880 := by
    simpa [prefixWord, tailWord_6980880, baseEnd_6980880] using wordTrace_append hprefix tailTrace_6980880
  have hstable : (prefixWord ++ tailWord_6980880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980880).length < 2 ^ (prefixWord ++ tailWord_6980880).sum := by decide
  have hdescent : baseEnd_6980880 < baseStart_6980880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980917 : List Nat := [1, 3, 3, 1, 2, 2, 2, 2, 2, 5]
def baseStart_6980917 : Nat := 118140960795 + 6980917 * 2 ^ 59
def prefixEnd_6980917 : Nat := 4983230072969 + 3 ^ 40 * 6980917 * 2
def baseEnd_6980917 : Nat := 1194855276714322954610951

theorem tailTrace_6980917 : CollatzResearch.WordTrace tailWord_6980917 prefixEnd_6980917 1194855276714322954610951 := by
  unfold tailWord_6980917
  simp only [CollatzResearch.WordTrace]
  refine ⟨254614960450337429549181005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169743306966891619699454003 254614960450337429549181005)
  ·
    refine ⟨95480610168876536080942877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254614960450337429549181005 95480610168876536080942877)
    ·
      refine ⟨35805228813328701030353579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95480610168876536080942877 35805228813328701030353579)
      ·
        refine ⟨53707843219993051545530369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35805228813328701030353579 53707843219993051545530369)
        ·
          refine ⟨40280882414994788659147777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53707843219993051545530369 40280882414994788659147777)
          ·
            refine ⟨30210661811246091494360833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40280882414994788659147777 30210661811246091494360833)
            ·
              refine ⟨22657996358434568620770625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30210661811246091494360833 22657996358434568620770625)
              ·
                refine ⟨16993497268825926465577969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22657996358434568620770625 16993497268825926465577969)
                ·
                  refine ⟨12745122951619444849183477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16993497268825926465577969 12745122951619444849183477)
                  ·
                    refine ⟨1194855276714322954610951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12745122951619444849183477 1194855276714322954610951)
                    ·
                      rfl

theorem cell23_6980917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_6980917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980917 prefixEnd_6980917 := by exact prefixLift 6980917
  have htrace : WordTrace (prefixWord ++ tailWord_6980917) baseStart_6980917 baseEnd_6980917 := by
    simpa [prefixWord, tailWord_6980917, baseEnd_6980917] using wordTrace_append hprefix tailTrace_6980917
  have hstable : (prefixWord ++ tailWord_6980917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980917).length < 2 ^ (prefixWord ++ tailWord_6980917).sum := by decide
  have hdescent : baseEnd_6980917 < baseStart_6980917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980920 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 3, 3, 4]
def baseStart_6980920 : Nat := 118140960795 + 6980920 * 2 ^ 59
def prefixEnd_6980920 : Nat := 4983230072969 + 3 ^ 40 * 6980920 * 2
def baseEnd_6980920 : Nat := 3584567370584932352095339

theorem tailTrace_6980920 : CollatzResearch.WordTrace tailWord_6980920 prefixEnd_6980920 3584567370584932352095339 := by
  unfold tailWord_6980920
  simp only [CollatzResearch.WordTrace]
  refine ⟨127307534934663280530770107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169743379912884374041026809 127307534934663280530770107)
  ·
    refine ⟨190961302401994920796155161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127307534934663280530770107 190961302401994920796155161)
    ·
      refine ⟨143220976801496190597116371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190961302401994920796155161 143220976801496190597116371)
      ·
        refine ⟨214831465202244285895674557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143220976801496190597116371 214831465202244285895674557)
        ·
          refine ⟨80561799450841607210877959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214831465202244285895674557 80561799450841607210877959)
          ·
            refine ⟨120842699176262410816316939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80561799450841607210877959 120842699176262410816316939)
            ·
              refine ⟨181264048764393616224475409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120842699176262410816316939 181264048764393616224475409)
              ·
                refine ⟨135948036573295212168356557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181264048764393616224475409 135948036573295212168356557)
                ·
                  refine ⟨50980513714985704563133709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135948036573295212168356557 50980513714985704563133709)
                  ·
                    refine ⟨19117692643119639211175141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50980513714985704563133709 19117692643119639211175141)
                    ·
                      refine ⟨3584567370584932352095339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19117692643119639211175141 3584567370584932352095339)
                      ·
                        rfl

theorem cell23_6980920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_6980920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980920 prefixEnd_6980920 := by exact prefixLift 6980920
  have htrace : WordTrace (prefixWord ++ tailWord_6980920) baseStart_6980920 baseEnd_6980920 := by
    simpa [prefixWord, tailWord_6980920, baseEnd_6980920] using wordTrace_append hprefix tailTrace_6980920
  have hstable : (prefixWord ++ tailWord_6980920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980920).length < 2 ^ (prefixWord ++ tailWord_6980920).sum := by decide
  have hdescent : baseEnd_6980920 < baseStart_6980920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980937 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 1, 6, 2]
def baseStart_6980937 : Nat := 118140960795 + 6980937 * 2 ^ 59
def prefixEnd_6980937 : Nat := 4983230072969 + 3 ^ 40 * 6980937 * 2
def baseEnd_6980937 : Nat := 3584576099756058785582761

theorem tailTrace_6980937 : CollatzResearch.WordTrace tailWord_6980937 prefixEnd_6980937 3584576099756058785582761 := by
  unfold tailWord_6980937
  simp only [CollatzResearch.WordTrace]
  refine ⟨254615689910264972964909065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169743793273509981976606043 254615689910264972964909065)
  ·
    refine ⟨190961767432698729723681799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254615689910264972964909065 190961767432698729723681799)
    ·
      refine ⟨286442651149048094585522699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190961767432698729723681799 286442651149048094585522699)
      ·
        refine ⟨429663976723572141878284049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286442651149048094585522699 429663976723572141878284049)
        ·
          refine ⟨322247982542679106408713037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429663976723572141878284049 322247982542679106408713037)
          ·
            refine ⟨120842993453504664903267389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322247982542679106408713037 120842993453504664903267389)
            ·
              refine ⟨45316122545064249338725271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120842993453504664903267389 45316122545064249338725271)
              ·
                refine ⟨67974183817596374008087907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45316122545064249338725271 67974183817596374008087907)
                ·
                  refine ⟨101961275726394561012131861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67974183817596374008087907 101961275726394561012131861)
                  ·
                    refine ⟨4779434799674745047443681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101961275726394561012131861 4779434799674745047443681)
                    ·
                      refine ⟨3584576099756058785582761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4779434799674745047443681 3584576099756058785582761)
                      ·
                        rfl

theorem cell23_6980937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 6, 2].length) (baseStart_6980937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980937 prefixEnd_6980937 := by exact prefixLift 6980937
  have htrace : WordTrace (prefixWord ++ tailWord_6980937) baseStart_6980937 baseEnd_6980937 := by
    simpa [prefixWord, tailWord_6980937, baseEnd_6980937] using wordTrace_append hprefix tailTrace_6980937
  have hstable : (prefixWord ++ tailWord_6980937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980937).length < 2 ^ (prefixWord ++ tailWord_6980937).sum := by decide
  have hdescent : baseEnd_6980937 < baseStart_6980937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980947 : List Nat := [1, 1, 1, 2, 1, 1, 7, 2, 3, 4]
def baseStart_6980947 : Nat := 118140960795 + 6980947 * 2 ^ 59
def prefixEnd_6980947 : Nat := 4983230072969 + 3 ^ 40 * 6980947 * 2
def baseEnd_6980947 : Nat := 1194860411520867915485905

theorem tailTrace_6980947 : CollatzResearch.WordTrace tailWord_6980947 prefixEnd_6980947 1194860411520867915485905 := by
  unfold tailWord_6980947
  simp only [CollatzResearch.WordTrace]
  refine ⟨254616054640228744672773095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169744036426819163115182063 254616054640228744672773095)
  ·
    refine ⟨381924081960343117009159643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254616054640228744672773095 381924081960343117009159643)
    ·
      refine ⟨572886122940514675513739465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381924081960343117009159643 572886122940514675513739465)
      ·
        refine ⟨429664592205386006635304599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 572886122940514675513739465 429664592205386006635304599)
        ·
          refine ⟨644496888308079009952956899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429664592205386006635304599 644496888308079009952956899)
          ·
            refine ⟨966745332462118514929435349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644496888308079009952956899 966745332462118514929435349)
            ·
              refine ⟨22658093729580902693658641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 966745332462118514929435349 22658093729580902693658641)
              ·
                refine ⟨16993570297185677020243981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22658093729580902693658641 16993570297185677020243981)
                ·
                  refine ⟨6372588861444628882591493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16993570297185677020243981 6372588861444628882591493)
                  ·
                    refine ⟨1194860411520867915485905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6372588861444628882591493 1194860411520867915485905)
                    ·
                      rfl

theorem cell23_6980947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 3, 4].length) (baseStart_6980947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980947 prefixEnd_6980947 := by exact prefixLift 6980947
  have htrace : WordTrace (prefixWord ++ tailWord_6980947) baseStart_6980947 baseEnd_6980947 := by
    simpa [prefixWord, tailWord_6980947, baseEnd_6980947] using wordTrace_append hprefix tailTrace_6980947
  have hstable : (prefixWord ++ tailWord_6980947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980947).length < 2 ^ (prefixWord ++ tailWord_6980947).sum := by decide
  have hdescent : baseEnd_6980947 < baseStart_6980947 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980977 : List Nat := [1, 2, 2, 2, 1, 2, 5, 2, 6]
def baseStart_6980977 : Nat := 118140960795 + 6980977 * 2 ^ 59
def prefixEnd_6980977 : Nat := 4983230072969 + 3 ^ 40 * 6980977 * 2
def baseEnd_6980977 : Nat := 398288515442470958786953

theorem tailTrace_6980977 : CollatzResearch.WordTrace tailWord_6980977 prefixEnd_6980977 398288515442470958786953 := by
  unfold tailWord_6980977
  simp only [CollatzResearch.WordTrace]
  refine ⟨254617148830120059796365185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169744765886746706530910123 254617148830120059796365185)
  ·
    refine ⟨190962861622590044847273889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254617148830120059796365185 190962861622590044847273889)
    ·
      refine ⟨143222146216942533635455417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190962861622590044847273889 143222146216942533635455417)
      ·
        refine ⟨107416609662706900226591563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143222146216942533635455417 107416609662706900226591563)
        ·
          refine ⟨161124914494060350339887345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107416609662706900226591563 161124914494060350339887345)
          ·
            refine ⟨120843685870545262754915509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161124914494060350339887345 120843685870545262754915509)
            ·
              refine ⟨11329095550363618383273329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120843685870545262754915509 11329095550363618383273329)
              ·
                refine ⟨8496821662772713787454997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11329095550363618383273329 8496821662772713787454997)
                ·
                  refine ⟨398288515442470958786953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8496821662772713787454997 398288515442470958786953)
                  ·
                    rfl

theorem cell23_6980977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 6].length) (baseStart_6980977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980977 prefixEnd_6980977 := by exact prefixLift 6980977
  have htrace : WordTrace (prefixWord ++ tailWord_6980977) baseStart_6980977 baseEnd_6980977 := by
    simpa [prefixWord, tailWord_6980977, baseEnd_6980977] using wordTrace_append hprefix tailTrace_6980977
  have hstable : (prefixWord ++ tailWord_6980977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980977).length < 2 ^ (prefixWord ++ tailWord_6980977).sum := by decide
  have hdescent : baseEnd_6980977 < baseStart_6980977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6980981 : List Nat := [1, 3, 4, 1, 3, 1, 2, 1, 3, 4]
def baseStart_6980981 : Nat := 118140960795 + 6980981 * 2 ^ 59
def prefixEnd_6980981 : Nat := 4983230072969 + 3 ^ 40 * 6980981 * 2
def baseEnd_6980981 : Nat := 1194866230968285537810853

theorem tailTrace_6980981 : CollatzResearch.WordTrace tailWord_6980981 prefixEnd_6980981 1194866230968285537810853 := by
  unfold tailWord_6980981
  simp only [CollatzResearch.WordTrace]
  refine ⟨254617294722105568479510797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169744863148070378986340531 254617294722105568479510797)
  ·
    refine ⟨95481485520789588179816549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254617294722105568479510797 95481485520789588179816549)
    ·
      refine ⟨17902778535148047783715603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95481485520789588179816549 17902778535148047783715603)
      ·
        refine ⟨26854167802722071675573405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17902778535148047783715603 26854167802722071675573405)
        ·
          refine ⟨10070312926020776878340027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26854167802722071675573405 10070312926020776878340027)
          ·
            refine ⟨15105469389031165317510041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10070312926020776878340027 15105469389031165317510041)
            ·
              refine ⟨11329102041773373988132531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15105469389031165317510041 11329102041773373988132531)
              ·
                refine ⟨16993653062660060982198797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11329102041773373988132531 16993653062660060982198797)
                ·
                  refine ⟨6372619898497522868324549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16993653062660060982198797 6372619898497522868324549)
                  ·
                    refine ⟨1194866230968285537810853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6372619898497522868324549 1194866230968285537810853)
                    ·
                      rfl

theorem cell23_6980981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_6980981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6980981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6980981 prefixEnd_6980981 := by exact prefixLift 6980981
  have htrace : WordTrace (prefixWord ++ tailWord_6980981) baseStart_6980981 baseEnd_6980981 := by
    simpa [prefixWord, tailWord_6980981, baseEnd_6980981] using wordTrace_append hprefix tailTrace_6980981
  have hstable : (prefixWord ++ tailWord_6980981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6980981).length < 2 ^ (prefixWord ++ tailWord_6980981).sum := by decide
  have hdescent : baseEnd_6980981 < baseStart_6980981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6980981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981004 : List Nat := [2, 2, 1, 2, 1, 3, 1, 4, 3, 1, 3]
def baseStart_6981004 : Nat := 118140960795 + 6981004 * 2 ^ 59
def prefixEnd_6981004 : Nat := 4983230072969 + 3 ^ 40 * 6981004 * 2
def baseEnd_6981004 : Nat := 3584610502959910023444953

theorem tailTrace_6981004 : CollatzResearch.WordTrace tailWord_6981004 prefixEnd_6981004 3584610502959910023444953 := by
  unfold tailWord_6981004
  simp only [CollatzResearch.WordTrace]
  refine ⟨127309066800511121703799033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169745422400681495605065377 127309066800511121703799033)
  ·
    refine ⟨95481800100383341277849275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127309066800511121703799033 95481800100383341277849275)
    ·
      refine ⟨143222700150575011916773913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95481800100383341277849275 143222700150575011916773913)
      ·
        refine ⟨107417025112931258937580435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143222700150575011916773913 107417025112931258937580435)
        ·
          refine ⟨161125537669396888406370653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107417025112931258937580435 161125537669396888406370653)
          ·
            refine ⟨60422076626023833152388995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161125537669396888406370653 60422076626023833152388995)
            ·
              refine ⟨90633114939035749728583493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60422076626023833152388995 90633114939035749728583493)
              ·
                refine ⟨16993709051069203074109405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90633114939035749728583493 16993709051069203074109405)
                ·
                  refine ⟨6372640894150951152791027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16993709051069203074109405 6372640894150951152791027)
                  ·
                    refine ⟨9558961341226426729186541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6372640894150951152791027 9558961341226426729186541)
                    ·
                      refine ⟨3584610502959910023444953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9558961341226426729186541 3584610502959910023444953)
                      ·
                        rfl

theorem cell23_6981004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_6981004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981004 prefixEnd_6981004 := by exact prefixLift 6981004
  have htrace : WordTrace (prefixWord ++ tailWord_6981004) baseStart_6981004 baseEnd_6981004 := by
    simpa [prefixWord, tailWord_6981004, baseEnd_6981004] using wordTrace_append hprefix tailTrace_6981004
  have hstable : (prefixWord ++ tailWord_6981004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981004).length < 2 ^ (prefixWord ++ tailWord_6981004).sum := by decide
  have hdescent : baseEnd_6981004 < baseStart_6981004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981031 : List Nat := [1, 1, 6, 1, 1, 1, 3, 2, 2, 3, 2]
def baseStart_6981031 : Nat := 118140960795 + 6981031 * 2 ^ 59
def prefixEnd_6981031 : Nat := 4983230072969 + 3 ^ 40 * 6981031 * 2
def baseEnd_6981031 : Nat := 3584624366937581417807329

theorem tailTrace_6981031 : CollatzResearch.WordTrace tailWord_6981031 prefixEnd_6981031 3584624366937581417807329 := by
  unfold tailWord_6981031
  simp only [CollatzResearch.WordTrace]
  refine ⟨254619118371924427018830947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169746078914616284679220631 254619118371924427018830947)
  ·
    refine ⟨381928677557886640528246421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254619118371924427018830947 381928677557886640528246421)
    ·
      refine ⟨17902906760525936274761551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 381928677557886640528246421 17902906760525936274761551)
      ·
        refine ⟨26854360140788904412142327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17902906760525936274761551 26854360140788904412142327)
        ·
          refine ⟨40281540211183356618213491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26854360140788904412142327 40281540211183356618213491)
          ·
            refine ⟨60422310316775034927320237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40281540211183356618213491 60422310316775034927320237)
            ·
              refine ⟨22658366368790638097745089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60422310316775034927320237 22658366368790638097745089)
              ·
                refine ⟨16993774776592978573308817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22658366368790638097745089 16993774776592978573308817)
                ·
                  refine ⟨12745331082444733929981613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16993774776592978573308817 12745331082444733929981613)
                  ·
                    refine ⟨4779499155916775223743105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12745331082444733929981613 4779499155916775223743105)
                    ·
                      refine ⟨3584624366937581417807329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4779499155916775223743105 3584624366937581417807329)
                      ·
                        rfl

theorem cell23_6981031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_6981031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981031 prefixEnd_6981031 := by exact prefixLift 6981031
  have htrace : WordTrace (prefixWord ++ tailWord_6981031) baseStart_6981031 baseEnd_6981031 := by
    simpa [prefixWord, tailWord_6981031, baseEnd_6981031] using wordTrace_append hprefix tailTrace_6981031
  have hstable : (prefixWord ++ tailWord_6981031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981031).length < 2 ^ (prefixWord ++ tailWord_6981031).sum := by decide
  have hdescent : baseEnd_6981031 < baseStart_6981031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981047 : List Nat := [1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 5]
def baseStart_6981047 : Nat := 118140960795 + 6981047 * 2 ^ 59
def prefixEnd_6981047 : Nat := 4983230072969 + 3 ^ 40 * 6981047 * 2
def baseEnd_6981047 : Nat := 3584632582628053355207255

theorem tailTrace_6981047 : CollatzResearch.WordTrace tailWord_6981047 prefixEnd_6981047 3584632582628053355207255 := by
  unfold tailWord_6981047
  simp only [CollatzResearch.WordTrace]
  refine ⟨254619701939866461751413395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169746467959910974500942263 254619701939866461751413395)
  ·
    refine ⟨381929552909799692627120093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254619701939866461751413395 381929552909799692627120093)
    ·
      refine ⟨143223582341174884735170035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381929552909799692627120093 143223582341174884735170035)
      ·
        refine ⟨214835373511762327102755053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143223582341174884735170035 214835373511762327102755053)
        ·
          refine ⟨80563265066910872663533145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214835373511762327102755053 80563265066910872663533145)
          ·
            refine ⟨60422448800183154497649859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80563265066910872663533145 60422448800183154497649859)
            ·
              refine ⟨90633673200274731746474789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60422448800183154497649859 90633673200274731746474789)
              ·
                refine ⟨16993813725051512202464023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90633673200274731746474789 16993813725051512202464023)
                ·
                  refine ⟨25490720587577268303696035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16993813725051512202464023 25490720587577268303696035)
                  ·
                    refine ⟨38236080881365902455544053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25490720587577268303696035 38236080881365902455544053)
                    ·
                      refine ⟨3584632582628053355207255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38236080881365902455544053 3584632582628053355207255)
                      ·
                        rfl

theorem cell23_6981047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_6981047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981047 prefixEnd_6981047 := by exact prefixLift 6981047
  have htrace : WordTrace (prefixWord ++ tailWord_6981047) baseStart_6981047 baseEnd_6981047 := by
    simpa [prefixWord, tailWord_6981047, baseEnd_6981047] using wordTrace_append hprefix tailTrace_6981047
  have hstable : (prefixWord ++ tailWord_6981047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981047).length < 2 ^ (prefixWord ++ tailWord_6981047).sum := by decide
  have hdescent : baseEnd_6981047 < baseStart_6981047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981064 : List Nat := [2, 1, 3, 1, 3, 1, 3, 1, 3, 2, 3]
def baseStart_6981064 : Nat := 118140960795 + 6981064 * 2 ^ 59
def prefixEnd_6981064 : Nat := 4983230072969 + 3 ^ 40 * 6981064 * 2
def baseEnd_6981064 : Nat := 3584641311799179788694677

theorem tailTrace_6981064 : CollatzResearch.WordTrace tailWord_6981064 prefixEnd_6981064 3584641311799179788694677 := by
  unfold tailWord_6981064
  simp only [CollatzResearch.WordTrace]
  refine ⟨127310160990402436827391123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169746881320536582436521497 127310160990402436827391123)
  ·
    refine ⟨190965241485603655241086685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127310160990402436827391123 190965241485603655241086685)
    ·
      refine ⟨71611965557101370715407507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190965241485603655241086685 71611965557101370715407507)
      ·
        refine ⟨107417948335652056073111261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71611965557101370715407507 107417948335652056073111261)
        ·
          refine ⟨40281730625869521027416723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107417948335652056073111261 40281730625869521027416723)
          ·
            refine ⟨60422595938804281541125085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40281730625869521027416723 60422595938804281541125085)
            ·
              refine ⟨22658473477051605577921907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60422595938804281541125085 22658473477051605577921907)
              ·
                refine ⟨33987710215577408366882861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22658473477051605577921907 33987710215577408366882861)
                ·
                  refine ⟨12745391330841528137581073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33987710215577408366882861 12745391330841528137581073)
                  ·
                    refine ⟨9559043498131146103185805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12745391330841528137581073 9559043498131146103185805)
                    ·
                      refine ⟨3584641311799179788694677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9559043498131146103185805 3584641311799179788694677)
                      ·
                        rfl

theorem cell23_6981064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_6981064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981064 prefixEnd_6981064 := by exact prefixLift 6981064
  have htrace : WordTrace (prefixWord ++ tailWord_6981064) baseStart_6981064 baseEnd_6981064 := by
    simpa [prefixWord, tailWord_6981064, baseEnd_6981064] using wordTrace_append hprefix tailTrace_6981064
  have hstable : (prefixWord ++ tailWord_6981064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981064).length < 2 ^ (prefixWord ++ tailWord_6981064).sum := by decide
  have hdescent : baseEnd_6981064 < baseStart_6981064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981095 : List Nat := [1, 1, 5, 2, 1, 3, 1, 4, 1, 2, 2]
def baseStart_6981095 : Nat := 118140960795 + 6981095 * 2 ^ 59
def prefixEnd_6981095 : Nat := 4983230072969 + 3 ^ 40 * 6981095 * 2
def baseEnd_6981095 : Nat := 3584657229699469167407035

theorem tailTrace_6981095 : CollatzResearch.WordTrace tailWord_6981095 prefixEnd_6981095 3584657229699469167407035 := by
  unfold tailWord_6981095
  simp only [CollatzResearch.WordTrace]
  refine ⟨254621452643692565949160739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169747635095795043966107159 254621452643692565949160739)
  ·
    refine ⟨381932178965538848923741109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254621452643692565949160739 381932178965538848923741109)
    ·
      refine ⟨35806141778019267086600729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 381932178965538848923741109 35806141778019267086600729)
      ·
        refine ⟨26854606333514450314950547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35806141778019267086600729 26854606333514450314950547)
        ·
          refine ⟨40281909500271675472425821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26854606333514450314950547 40281909500271675472425821)
          ·
            refine ⟨15105716062601878302159683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40281909500271675472425821 15105716062601878302159683)
            ·
              refine ⟨22658574093902817453239525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15105716062601878302159683 22658574093902817453239525)
              ·
                refine ⟨4248482642606778272482411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22658574093902817453239525 4248482642606778272482411)
                ·
                  refine ⟨6372723963910167408723617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4248482642606778272482411 6372723963910167408723617)
                  ·
                    refine ⟨4779542972932625556542713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6372723963910167408723617 4779542972932625556542713)
                    ·
                      refine ⟨3584657229699469167407035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4779542972932625556542713 3584657229699469167407035)
                      ·
                        rfl

theorem cell23_6981095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_6981095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981095 prefixEnd_6981095 := by exact prefixLift 6981095
  have htrace : WordTrace (prefixWord ++ tailWord_6981095) baseStart_6981095 baseEnd_6981095 := by
    simpa [prefixWord, tailWord_6981095, baseEnd_6981095] using wordTrace_append hprefix tailTrace_6981095
  have hstable : (prefixWord ++ tailWord_6981095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981095).length < 2 ^ (prefixWord ++ tailWord_6981095).sum := by decide
  have hdescent : baseEnd_6981095 < baseStart_6981095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981101 : List Nat := [1, 5, 1, 3, 2, 2, 1, 8]
def baseStart_6981101 : Nat := 118140960795 + 6981101 * 2 ^ 59
def prefixEnd_6981101 : Nat := 4983230072969 + 3 ^ 40 * 6981101 * 2
def baseEnd_6981101 : Nat := 132765196688273931256741

theorem tailTrace_6981101 : CollatzResearch.WordTrace tailWord_6981101 prefixEnd_6981101 132765196688273931256741 := by
  unfold tailWord_6981101
  simp only [CollatzResearch.WordTrace]
  refine ⟨254621671481670828973879157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169747780987780552649252771 254621671481670828973879157)
  ·
    refine ⟨23870781701406640216301171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 254621671481670828973879157 23870781701406640216301171)
    ·
      refine ⟨35806172552109960324451757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23870781701406640216301171 35806172552109960324451757)
      ·
        refine ⟨13427314707041235121669409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35806172552109960324451757 13427314707041235121669409)
        ·
          refine ⟨10070486030280926341252057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13427314707041235121669409 10070486030280926341252057)
          ·
            refine ⟨7552864522710694755939043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10070486030280926341252057 7552864522710694755939043)
            ·
              refine ⟨11329296784066042133908565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7552864522710694755939043 11329296784066042133908565)
              ·
                refine ⟨132765196688273931256741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11329296784066042133908565 132765196688273931256741)
                ·
                  rfl

theorem cell23_6981101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 8].length) (baseStart_6981101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981101 prefixEnd_6981101 := by exact prefixLift 6981101
  have htrace : WordTrace (prefixWord ++ tailWord_6981101) baseStart_6981101 baseEnd_6981101 := by
    simpa [prefixWord, tailWord_6981101, baseEnd_6981101] using wordTrace_append hprefix tailTrace_6981101
  have hstable : (prefixWord ++ tailWord_6981101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981101).length < 2 ^ (prefixWord ++ tailWord_6981101).sum := by decide
  have hdescent : baseEnd_6981101 < baseStart_6981101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981118 : List Nat := [4, 2, 2, 3, 1, 1, 3, 7]
def baseStart_6981118 : Nat := 118140960795 + 6981118 * 2 ^ 59
def prefixEnd_6981118 : Nat := 4983230072969 + 3 ^ 40 * 6981118 * 2
def baseEnd_6981118 : Nat := 132765519990908243608127

theorem tailTrace_6981118 : CollatzResearch.WordTrace tailWord_6981118 prefixEnd_6981118 132765519990908243608127 := by
  unfold tailWord_6981118
  simp only [CollatzResearch.WordTrace]
  refine ⟨31827786440326155109656001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169748194348406160584832005 31827786440326155109656001)
  ·
    refine ⟨23870839830244616332242001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31827786440326155109656001 23870839830244616332242001)
    ·
      refine ⟨17903129872683462249181501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23870839830244616332242001 17903129872683462249181501)
      ·
        refine ⟨6713673702256298343443063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17903129872683462249181501 6713673702256298343443063)
        ·
          refine ⟨10070510553384447515164595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6713673702256298343443063 10070510553384447515164595)
          ·
            refine ⟨15105765830076671272746893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10070510553384447515164595 15105765830076671272746893)
            ·
              refine ⟨5664662186278751727280085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15105765830076671272746893 5664662186278751727280085)
              ·
                refine ⟨132765519990908243608127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5664662186278751727280085 132765519990908243608127)
                ·
                  rfl

theorem cell23_6981118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 7].length) (baseStart_6981118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981118 prefixEnd_6981118 := by exact prefixLift 6981118
  have htrace : WordTrace (prefixWord ++ tailWord_6981118) baseStart_6981118 baseEnd_6981118 := by
    simpa [prefixWord, tailWord_6981118, baseEnd_6981118] using wordTrace_append hprefix tailTrace_6981118
  have hstable : (prefixWord ++ tailWord_6981118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981118).length < 2 ^ (prefixWord ++ tailWord_6981118).sum := by decide
  have hdescent : baseEnd_6981118 < baseStart_6981118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981137 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 5]
def baseStart_6981137 : Nat := 118140960795 + 6981137 * 2 ^ 59
def prefixEnd_6981137 : Nat := 4983230072969 + 3 ^ 40 * 6981137 * 2
def baseEnd_6981137 : Nat := 3584678795886958003081841

theorem tailTrace_6981137 : CollatzResearch.WordTrace tailWord_6981137 prefixEnd_6981137 3584678795886958003081841 := by
  unfold tailWord_6981137
  simp only [CollatzResearch.WordTrace]
  refine ⟨254622984509540407122189665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169748656339693604748126443 254622984509540407122189665)
  ·
    refine ⟨190967238382155305341642249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254622984509540407122189665 190967238382155305341642249)
    ·
      refine ⟨143225428786616479006231687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190967238382155305341642249 143225428786616479006231687)
      ·
        refine ⟨214838143179924718509347531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143225428786616479006231687 214838143179924718509347531)
        ·
          refine ⟨322257214769887077764021297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214838143179924718509347531 322257214769887077764021297)
          ·
            refine ⟨241692911077415308323015973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322257214769887077764021297 241692911077415308323015973)
            ·
              refine ⟨45317420827015370310565495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 241692911077415308323015973 45317420827015370310565495)
              ·
                refine ⟨67976131240523055465848243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45317420827015370310565495 67976131240523055465848243)
                ·
                  refine ⟨101964196860784583198772365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67976131240523055465848243 101964196860784583198772365)
                  ·
                    refine ⟨38236573822794218699539637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101964196860784583198772365 38236573822794218699539637)
                    ·
                      refine ⟨3584678795886958003081841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38236573822794218699539637 3584678795886958003081841)
                      ·
                        rfl

theorem cell23_6981137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_6981137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981137 prefixEnd_6981137 := by exact prefixLift 6981137
  have htrace : WordTrace (prefixWord ++ tailWord_6981137) baseStart_6981137 baseEnd_6981137 := by
    simpa [prefixWord, tailWord_6981137, baseEnd_6981137] using wordTrace_append hprefix tailTrace_6981137
  have hstable : (prefixWord ++ tailWord_6981137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981137).length < 2 ^ (prefixWord ++ tailWord_6981137).sum := by decide
  have hdescent : baseEnd_6981137 < baseStart_6981137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981154 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 1, 6, 3]
def baseStart_6981154 : Nat := 118140960795 + 6981154 * 2 ^ 59
def prefixEnd_6981154 : Nat := 4983230072969 + 3 ^ 40 * 6981154 * 2
def baseEnd_6981154 : Nat := 3584687525058084436569263

theorem tailTrace_6981154 : CollatzResearch.WordTrace tailWord_6981154 prefixEnd_6981154 3584687525058084436569263 := by
  unfold tailWord_6981154
  simp only [CollatzResearch.WordTrace]
  refine ⟨63655901137619704756389629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169749069700319212683705677 63655901137619704756389629)
  ·
    refine ⟨23870962926607389283646111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63655901137619704756389629 23870962926607389283646111)
    ·
      refine ⟨35806444389911083925469167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23870962926607389283646111 35806444389911083925469167)
      ·
        refine ⟨53709666584866625888203751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35806444389911083925469167 53709666584866625888203751)
        ·
          refine ⟨80564499877299938832305627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53709666584866625888203751 80564499877299938832305627)
          ·
            refine ⟨120846749815949908248458441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80564499877299938832305627 120846749815949908248458441)
            ·
              refine ⟨90635062361962431186343831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120846749815949908248458441 90635062361962431186343831)
              ·
                refine ⟨135952593542943646779515747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90635062361962431186343831 135952593542943646779515747)
                ·
                  refine ⟨203928890314415470169273621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135952593542943646779515747 203928890314415470169273621)
                  ·
                    refine ⟨9559166733488225164184701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 203928890314415470169273621 9559166733488225164184701)
                    ·
                      refine ⟨3584687525058084436569263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9559166733488225164184701 3584687525058084436569263)
                      ·
                        rfl

theorem cell23_6981154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_6981154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981154 prefixEnd_6981154 := by exact prefixLift 6981154
  have htrace : WordTrace (prefixWord ++ tailWord_6981154) baseStart_6981154 baseEnd_6981154 := by
    simpa [prefixWord, tailWord_6981154, baseEnd_6981154] using wordTrace_append hprefix tailTrace_6981154
  have hstable : (prefixWord ++ tailWord_6981154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981154).length < 2 ^ (prefixWord ++ tailWord_6981154).sum := by decide
  have hdescent : baseEnd_6981154 < baseStart_6981154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981227 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 9]
def baseStart_6981227 : Nat := 118140960795 + 6981227 * 2 ^ 59
def prefixEnd_6981227 : Nat := 4983230072969 + 3 ^ 40 * 6981227 * 2
def baseEnd_6981227 : Nat := 3584725009145862650956427

theorem tailTrace_6981227 : CollatzResearch.WordTrace tailWord_6981227 prefixEnd_6981227 3584725009145862650956427 := by
  unfold tailWord_6981227
  simp only [CollatzResearch.WordTrace]
  refine ⟨254626267079214352492965935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169750844719476234995310623 254626267079214352492965935)
  ·
    refine ⟨381939400618821528739448903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254626267079214352492965935 381939400618821528739448903)
    ·
      refine ⟨572909100928232293109173355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381939400618821528739448903 572909100928232293109173355)
      ·
        refine ⟨859363651392348439663760033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572909100928232293109173355 859363651392348439663760033)
        ·
          refine ⟨644522738544261329747820025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 859363651392348439663760033 644522738544261329747820025)
          ·
            refine ⟨483392053908195997310865019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 644522738544261329747820025 483392053908195997310865019)
            ·
              refine ⟨725088080862293995966297529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483392053908195997310865019 725088080862293995966297529)
              ·
                refine ⟨543816060646720496974723147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 725088080862293995966297529 543816060646720496974723147)
                ·
                  refine ⟨815724090970080745462084721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 543816060646720496974723147 815724090970080745462084721)
                  ·
                    refine ⟨611793068227560559096563541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 815724090970080745462084721 611793068227560559096563541)
                    ·
                      refine ⟨3584725009145862650956427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 611793068227560559096563541 3584725009145862650956427)
                      ·
                        rfl

theorem cell23_6981227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 9].length) (baseStart_6981227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981227 prefixEnd_6981227 := by exact prefixLift 6981227
  have htrace : WordTrace (prefixWord ++ tailWord_6981227) baseStart_6981227 baseEnd_6981227 := by
    simpa [prefixWord, tailWord_6981227, baseEnd_6981227] using wordTrace_append hprefix tailTrace_6981227
  have hstable : (prefixWord ++ tailWord_6981227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981227).length < 2 ^ (prefixWord ++ tailWord_6981227).sum := by decide
  have hdescent : baseEnd_6981227 < baseStart_6981227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981238 : List Nat := [5, 1, 1, 2, 2, 2, 2, 1, 2, 5]
def baseStart_6981238 : Nat := 118140960795 + 6981238 * 2 ^ 59
def prefixEnd_6981238 : Nat := 4983230072969 + 3 ^ 40 * 6981238 * 2
def baseEnd_6981238 : Nat := 1194910219144354035972959

theorem tailTrace_6981238 : CollatzResearch.WordTrace tailWord_6981238 prefixEnd_6981238 1194910219144354035972959 := by
  unfold tailWord_6981238
  simp only [CollatzResearch.WordTrace]
  refine ⟨15914166767635906335726023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169751112188116334247744245 15914166767635906335726023)
  ·
    refine ⟨23871250151453859503589035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15914166767635906335726023 23871250151453859503589035)
    ·
      refine ⟨35806875227180789255383553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23871250151453859503589035 35806875227180789255383553)
      ·
        refine ⟨26855156420385591941537665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35806875227180789255383553 26855156420385591941537665)
        ·
          refine ⟨20141367315289193956153249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26855156420385591941537665 20141367315289193956153249)
          ·
            refine ⟨15106025486466895467114937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20141367315289193956153249 15106025486466895467114937)
            ·
              refine ⟨11329519114850171600336203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15106025486466895467114937 11329519114850171600336203)
              ·
                refine ⟨16994278672275257400504305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11329519114850171600336203 16994278672275257400504305)
                ·
                  refine ⟨12745709004206443050378229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16994278672275257400504305 12745709004206443050378229)
                  ·
                    refine ⟨1194910219144354035972959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12745709004206443050378229 1194910219144354035972959)
                    ·
                      rfl

theorem cell23_6981238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_6981238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981238 prefixEnd_6981238 := by exact prefixLift 6981238
  have htrace : WordTrace (prefixWord ++ tailWord_6981238) baseStart_6981238 baseEnd_6981238 := by
    simpa [prefixWord, tailWord_6981238, baseEnd_6981238] using wordTrace_append hprefix tailTrace_6981238
  have hstable : (prefixWord ++ tailWord_6981238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981238).length < 2 ^ (prefixWord ++ tailWord_6981238).sum := by decide
  have hdescent : baseEnd_6981238 < baseStart_6981238 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981241 : List Nat := [1, 2, 1, 3, 3, 1, 4, 1, 2, 1, 4]
def baseStart_6981241 : Nat := 118140960795 + 6981241 * 2 ^ 59
def prefixEnd_6981241 : Nat := 4983230072969 + 3 ^ 40 * 6981241 * 2
def baseEnd_6981241 : Nat := 3584732197875025596181363

theorem tailTrace_6981241 : CollatzResearch.WordTrace tailWord_6981241 prefixEnd_6981241 3584732197875025596181363 := by
  unfold tailWord_6981241
  simp only [CollatzResearch.WordTrace]
  refine ⟨254626777701163632883975577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169751185134109088589317051 254626777701163632883975577)
  ·
    refine ⟨190970083275872724662981683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254626777701163632883975577 190970083275872724662981683)
    ·
      refine ⟨286455124913809086994472525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190970083275872724662981683 286455124913809086994472525)
      ·
        refine ⟨107420671842678407622927197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286455124913809086994472525 107420671842678407622927197)
        ·
          refine ⟨40282751941004402858597699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107420671842678407622927197 40282751941004402858597699)
          ·
            refine ⟨60424127911506604287896549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40282751941004402858597699 60424127911506604287896549)
            ·
              refine ⟨11329523983407488303980603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60424127911506604287896549 11329523983407488303980603)
              ·
                refine ⟨16994285975111232455970905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11329523983407488303980603 16994285975111232455970905)
                ·
                  refine ⟨12745714481333424341978179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16994285975111232455970905 12745714481333424341978179)
                  ·
                    refine ⟨19118571722000136512967269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12745714481333424341978179 19118571722000136512967269)
                    ·
                      refine ⟨3584732197875025596181363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19118571722000136512967269 3584732197875025596181363)
                      ·
                        rfl

theorem cell23_6981241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_6981241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981241 prefixEnd_6981241 := by exact prefixLift 6981241
  have htrace : WordTrace (prefixWord ++ tailWord_6981241) baseStart_6981241 baseEnd_6981241 := by
    simpa [prefixWord, tailWord_6981241, baseEnd_6981241] using wordTrace_append hprefix tailTrace_6981241
  have hstable : (prefixWord ++ tailWord_6981241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981241).length < 2 ^ (prefixWord ++ tailWord_6981241).sum := by decide
  have hdescent : baseEnd_6981241 < baseStart_6981241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981281 : List Nat := [1, 2, 3, 3, 2, 1, 2, 3, 6]
def baseStart_6981281 : Nat := 118140960795 + 6981281 * 2 ^ 59
def prefixEnd_6981281 : Nat := 4983230072969 + 3 ^ 40 * 6981281 * 2
def baseEnd_6981281 : Nat := 398305859677911715520131

theorem tailTrace_6981281 : CollatzResearch.WordTrace tailWord_6981281 prefixEnd_6981281 398305859677911715520131 := by
  unfold tailWord_6981281
  simp only [CollatzResearch.WordTrace]
  refine ⟨254628236621018719715431697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169752157747345813143621131 254628236621018719715431697)
  ·
    refine ⟨190971177465764039786573773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254628236621018719715431697 190971177465764039786573773)
    ·
      refine ⟨71614191549661514919965165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190971177465764039786573773 71614191549661514919965165)
      ·
        refine ⟨26855321831123068094986937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71614191549661514919965165 26855321831123068094986937)
        ·
          refine ⟨20141491373342301071240203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26855321831123068094986937 20141491373342301071240203)
          ·
            refine ⟨30212237060013451606860305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20141491373342301071240203 30212237060013451606860305)
            ·
              refine ⟨22659177795010088705145229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30212237060013451606860305 22659177795010088705145229)
              ·
                refine ⟨8497191673128783264429461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22659177795010088705145229 8497191673128783264429461)
                ·
                  refine ⟨398305859677911715520131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8497191673128783264429461 398305859677911715520131)
                  ·
                    rfl

theorem cell23_6981281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 6].length) (baseStart_6981281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981281 prefixEnd_6981281 := by exact prefixLift 6981281
  have htrace : WordTrace (prefixWord ++ tailWord_6981281) baseStart_6981281 baseEnd_6981281 := by
    simpa [prefixWord, tailWord_6981281, baseEnd_6981281] using wordTrace_append hprefix tailTrace_6981281
  have hstable : (prefixWord ++ tailWord_6981281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981281).length < 2 ^ (prefixWord ++ tailWord_6981281).sum := by decide
  have hdescent : baseEnd_6981281 < baseStart_6981281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981302 : List Nat := [5, 1, 3, 1, 1, 1, 1, 5, 1, 4]
def baseStart_6981302 : Nat := 118140960795 + 6981302 * 2 ^ 59
def prefixEnd_6981302 : Nat := 4983230072969 + 3 ^ 40 * 6981302 * 2
def baseEnd_6981302 : Nat := 1194921173398316619172861

theorem tailTrace_6981302 : CollatzResearch.WordTrace tailWord_6981302 prefixEnd_6981302 1194921173398316619172861 := by
  unfold tailWord_6981302
  simp only [CollatzResearch.WordTrace]
  refine ⟨15914312659621415018871635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169752668369295093534630773 15914312659621415018871635)
  ·
    refine ⟨23871468989432122528307453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15914312659621415018871635 23871468989432122528307453)
    ·
      refine ⟨8951800871037045948115295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23871468989432122528307453 8951800871037045948115295)
      ·
        refine ⟨13427701306555568922172943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8951800871037045948115295 13427701306555568922172943)
        ·
          refine ⟨20141551959833353383259415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13427701306555568922172943 20141551959833353383259415)
          ·
            refine ⟨30212327939750030074889123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20141551959833353383259415 30212327939750030074889123)
            ·
              refine ⟨45318491909625045112333685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30212327939750030074889123 45318491909625045112333685)
              ·
                refine ⟨4248608616527347979281283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45318491909625045112333685 4248608616527347979281283)
                ·
                  refine ⟨6372912924791021968921925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4248608616527347979281283 6372912924791021968921925)
                  ·
                    refine ⟨1194921173398316619172861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6372912924791021968921925 1194921173398316619172861)
                    ·
                      rfl

theorem cell23_6981302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_6981302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981302 prefixEnd_6981302 := by exact prefixLift 6981302
  have htrace : WordTrace (prefixWord ++ tailWord_6981302) baseStart_6981302 baseEnd_6981302 := by
    simpa [prefixWord, tailWord_6981302, baseEnd_6981302] using wordTrace_append hprefix tailTrace_6981302
  have hstable : (prefixWord ++ tailWord_6981302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981302).length < 2 ^ (prefixWord ++ tailWord_6981302).sum := by decide
  have hdescent : baseEnd_6981302 < baseStart_6981302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981311 : List Nat := [1, 1, 2, 2, 2, 3, 3, 3, 1, 5]
def baseStart_6981311 : Nat := 118140960795 + 6981311 * 2 ^ 59
def prefixEnd_6981311 : Nat := 4983230072969 + 3 ^ 40 * 6981311 * 2
def baseEnd_6981311 : Nat := 1194922713840280107435347

theorem tailTrace_6981311 : CollatzResearch.WordTrace tailWord_6981311 prefixEnd_6981311 1194922713840280107435347 := by
  unfold tailWord_6981311
  simp only [CollatzResearch.WordTrace]
  refine ⟨254629330810910034839023787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169752887207273356559349191 254629330810910034839023787)
  ·
    refine ⟨381943996216365052258535681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254629330810910034839023787 381943996216365052258535681)
    ·
      refine ⟨286457997162273789193901761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381943996216365052258535681 286457997162273789193901761)
      ·
        refine ⟨214843497871705341895426321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286457997162273789193901761 214843497871705341895426321)
        ·
          refine ⟨161132623403779006421569741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214843497871705341895426321 161132623403779006421569741)
          ·
            refine ⟨60424733776417127408088653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161132623403779006421569741 60424733776417127408088653)
            ·
              refine ⟨22659275166156422778033245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60424733776417127408088653 22659275166156422778033245)
              ·
                refine ⟨8497228187308658541762467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22659275166156422778033245 8497228187308658541762467)
                ·
                  refine ⟨12745842280962987812643701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8497228187308658541762467 12745842280962987812643701)
                  ·
                    refine ⟨1194922713840280107435347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12745842280962987812643701 1194922713840280107435347)
                    ·
                      rfl

theorem cell23_6981311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 5].length) (baseStart_6981311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981311 prefixEnd_6981311 := by exact prefixLift 6981311
  have htrace : WordTrace (prefixWord ++ tailWord_6981311) baseStart_6981311 baseEnd_6981311 := by
    simpa [prefixWord, tailWord_6981311, baseEnd_6981311] using wordTrace_append hprefix tailTrace_6981311
  have hstable : (prefixWord ++ tailWord_6981311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981311).length < 2 ^ (prefixWord ++ tailWord_6981311).sum := by decide
  have hdescent : baseEnd_6981311 < baseStart_6981311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981348 : List Nat := [2, 3, 1, 1, 1, 3, 4, 2, 1, 1, 4]
def baseStart_6981348 : Nat := 118140960795 + 6981348 * 2 ^ 59
def prefixEnd_6981348 : Nat := 4983230072969 + 3 ^ 40 * 6981348 * 2
def baseEnd_6981348 : Nat := 3584787140305056677543371

theorem tailTrace_6981348 : CollatzResearch.WordTrace tailWord_6981348 prefixEnd_6981348 3584787140305056677543371 := by
  unfold tailWord_6981348
  simp only [CollatzResearch.WordTrace]
  refine ⟨127315340155887995079060349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169753786874517326772080465 127315340155887995079060349)
  ·
    refine ⟨47743252558457998154647631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127315340155887995079060349 47743252558457998154647631)
    ·
      refine ⟨71614878837686997231971447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47743252558457998154647631 71614878837686997231971447)
      ·
        refine ⟨107422318256530495847957171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71614878837686997231971447 107422318256530495847957171)
        ·
          refine ⟨161133477384795743771935757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107422318256530495847957171 161133477384795743771935757)
          ·
            refine ⟨60425054019298403914475909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161133477384795743771935757 60425054019298403914475909)
            ·
              refine ⟨11329697628618450733964233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60425054019298403914475909 11329697628618450733964233)
              ·
                refine ⟨8497273221463838050473175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11329697628618450733964233 8497273221463838050473175)
                ·
                  refine ⟨12745909832195757075709763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8497273221463838050473175 12745909832195757075709763)
                  ·
                    refine ⟨19118864748293635613564645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12745909832195757075709763 19118864748293635613564645)
                    ·
                      refine ⟨3584787140305056677543371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19118864748293635613564645 3584787140305056677543371)
                      ·
                        rfl

theorem cell23_6981348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2, 1, 1, 4].length) (baseStart_6981348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981348 prefixEnd_6981348 := by exact prefixLift 6981348
  have htrace : WordTrace (prefixWord ++ tailWord_6981348) baseStart_6981348 baseEnd_6981348 := by
    simpa [prefixWord, tailWord_6981348, baseEnd_6981348] using wordTrace_append hprefix tailTrace_6981348
  have hstable : (prefixWord ++ tailWord_6981348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981348).length < 2 ^ (prefixWord ++ tailWord_6981348).sum := by decide
  have hdescent : baseEnd_6981348 < baseStart_6981348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981396 : List Nat := [2, 4, 4, 1, 2, 1, 1, 2, 1, 5]
def baseStart_6981396 : Nat := 118140960795 + 6981396 * 2 ^ 59
def prefixEnd_6981396 : Nat := 4983230072969 + 3 ^ 40 * 6981396 * 2
def baseEnd_6981396 : Nat := 1194937262458824163247717

theorem tailTrace_6981396 : CollatzResearch.WordTrace tailWord_6981396 prefixEnd_6981396 1194937262458824163247717 := by
  unfold tailWord_6981396
  simp only [CollatzResearch.WordTrace]
  refine ⟨127316215507801047177934021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169754954010401396237245361 127316215507801047177934021)
  ·
    refine ⟨23871790407712696345862629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127316215507801047177934021 23871790407712696345862629)
    ·
      refine ⟨4475960701446130564849243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23871790407712696345862629 4475960701446130564849243)
      ·
        refine ⟨6713941052169195847273865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4475960701446130564849243 6713941052169195847273865)
        ·
          refine ⟨5035455789126896885455399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6713941052169195847273865 5035455789126896885455399)
          ·
            refine ⟨7553183683690345328183099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5035455789126896885455399 7553183683690345328183099)
            ·
              refine ⟨11329775525535517992274649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7553183683690345328183099 11329775525535517992274649)
              ·
                refine ⟨8497331644151638494205987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11329775525535517992274649 8497331644151638494205987)
                ·
                  refine ⟨12745997466227457741308981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8497331644151638494205987 12745997466227457741308981)
                  ·
                    refine ⟨1194937262458824163247717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12745997466227457741308981 1194937262458824163247717)
                    ·
                      rfl

theorem cell23_6981396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_6981396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981396 prefixEnd_6981396 := by exact prefixLift 6981396
  have htrace : WordTrace (prefixWord ++ tailWord_6981396) baseStart_6981396 baseEnd_6981396 := by
    simpa [prefixWord, tailWord_6981396, baseEnd_6981396] using wordTrace_append hprefix tailTrace_6981396
  have hstable : (prefixWord ++ tailWord_6981396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981396).length < 2 ^ (prefixWord ++ tailWord_6981396).sum := by decide
  have hdescent : baseEnd_6981396 < baseStart_6981396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981433 : List Nat := [1, 2, 1, 7, 1, 2, 2, 2, 1, 2, 2]
def baseStart_6981433 : Nat := 118140960795 + 6981433 * 2 ^ 59
def prefixEnd_6981433 : Nat := 4983230072969 + 3 ^ 40 * 6981433 * 2
def baseEnd_6981433 : Nat := 3584830786160688844980481

theorem tailTrace_6981433 : CollatzResearch.WordTrace tailWord_6981433 prefixEnd_6981433 3584830786160688844980481 := by
  unfold tailWord_6981433
  simp only [CollatzResearch.WordTrace]
  refine ⟨254633780516468049674964953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169755853677645366449976635 254633780516468049674964953)
  ·
    refine ⟨190975335387351037256223715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254633780516468049674964953 190975335387351037256223715)
    ·
      refine ⟨286463003081026555884335573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190975335387351037256223715 286463003081026555884335573)
      ·
        refine ⟨6713976634711559903539115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 286463003081026555884335573 6713976634711559903539115)
        ·
          refine ⟨10070964952067339855308673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6713976634711559903539115 10070964952067339855308673)
          ·
            refine ⟨7553223714050504891481505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10070964952067339855308673 7553223714050504891481505)
            ·
              refine ⟨5664917785537878668611129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7553223714050504891481505 5664917785537878668611129)
              ·
                refine ⟨4248688339153409001458347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5664917785537878668611129 4248688339153409001458347)
                ·
                  refine ⟨6373032508730113502187521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4248688339153409001458347 6373032508730113502187521)
                  ·
                    refine ⟨4779774381547585126640641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6373032508730113502187521 4779774381547585126640641)
                    ·
                      refine ⟨3584830786160688844980481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4779774381547585126640641 3584830786160688844980481)
                      ·
                        rfl

theorem cell23_6981433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_6981433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981433 prefixEnd_6981433 := by exact prefixLift 6981433
  have htrace : WordTrace (prefixWord ++ tailWord_6981433) baseStart_6981433 baseEnd_6981433 := by
    simpa [prefixWord, tailWord_6981433, baseEnd_6981433] using wordTrace_append hprefix tailTrace_6981433
  have hstable : (prefixWord ++ tailWord_6981433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981433).length < 2 ^ (prefixWord ++ tailWord_6981433).sum := by decide
  have hdescent : baseEnd_6981433 < baseStart_6981433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981438 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_6981438 : Nat := 118140960795 + 6981438 * 2 ^ 59
def prefixEnd_6981438 : Nat := 4983230072969 + 3 ^ 40 * 6981438 * 2
def baseEnd_6981438 : Nat := 3584833353563961325417957

theorem tailTrace_6981438 : CollatzResearch.WordTrace tailWord_6981438 prefixEnd_6981438 3584833353563961325417957 := by
  unfold tailWord_6981438
  simp only [CollatzResearch.WordTrace]
  refine ⟨31829245360181241941112121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169755975254299957019264645 31829245360181241941112121)
  ·
    refine ⟨23871934020135931455834091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31829245360181241941112121 23871934020135931455834091)
    ·
      refine ⟨35807901030203897183751137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23871934020135931455834091 35807901030203897183751137)
      ·
        refine ⟨26855925772652922887813353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35807901030203897183751137 26855925772652922887813353)
        ·
          refine ⟨20141944329489692165860015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26855925772652922887813353 20141944329489692165860015)
          ·
            refine ⟨30212916494234538248790023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20141944329489692165860015 30212916494234538248790023)
            ·
              refine ⟨45319374741351807373185035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30212916494234538248790023 45319374741351807373185035)
              ·
                refine ⟨67979062112027711059777553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45319374741351807373185035 67979062112027711059777553)
                ·
                  refine ⟨50984296584020783294833165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67979062112027711059777553 50984296584020783294833165)
                  ·
                    refine ⟨19119111219007793735562437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50984296584020783294833165 19119111219007793735562437)
                    ·
                      refine ⟨3584833353563961325417957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19119111219007793735562437 3584833353563961325417957)
                      ·
                        rfl

theorem cell23_6981438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_6981438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981438 prefixEnd_6981438 := by exact prefixLift 6981438
  have htrace : WordTrace (prefixWord ++ tailWord_6981438) baseStart_6981438 baseEnd_6981438 := by
    simpa [prefixWord, tailWord_6981438, baseEnd_6981438] using wordTrace_append hprefix tailTrace_6981438
  have hstable : (prefixWord ++ tailWord_6981438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981438).length < 2 ^ (prefixWord ++ tailWord_6981438).sum := by decide
  have hdescent : baseEnd_6981438 < baseStart_6981438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981461 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 9]
def baseStart_6981461 : Nat := 118140960795 + 6981461 * 2 ^ 59
def prefixEnd_6981461 : Nat := 4983230072969 + 3 ^ 40 * 6981461 * 2
def baseEnd_6981461 : Nat := 398316129291001637270039

theorem tailTrace_6981461 : CollatzResearch.WordTrace tailWord_6981461 prefixEnd_6981461 398316129291001637270039 := by
  unfold tailWord_6981461
  simp only [CollatzResearch.WordTrace]
  refine ⟨254634801760366610456984237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169756534506911073637989491 254634801760366610456984237)
  ·
    refine ⟨95488050660137478921369089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254634801760366610456984237 95488050660137478921369089)
    ·
      refine ⟨71616037995103109191026817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95488050660137478921369089 71616037995103109191026817)
      ·
        refine ⟨53712028496327331893270113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71616037995103109191026817 53712028496327331893270113)
        ·
          refine ⟨40284021372245498919952585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53712028496327331893270113 40284021372245498919952585)
          ·
            refine ⟨30213016029184124189964439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40284021372245498919952585 30213016029184124189964439)
            ·
              refine ⟨45319524043776186284946659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30213016029184124189964439 45319524043776186284946659)
              ·
                refine ⟨67979286065664279427419989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45319524043776186284946659 67979286065664279427419989)
                ·
                  refine ⟨398316129291001637270039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67979286065664279427419989 398316129291001637270039)
                  ·
                    rfl

theorem cell23_6981461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 9].length) (baseStart_6981461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981461 prefixEnd_6981461 := by exact prefixLift 6981461
  have htrace : WordTrace (prefixWord ++ tailWord_6981461) baseStart_6981461 baseEnd_6981461 := by
    simpa [prefixWord, tailWord_6981461, baseEnd_6981461] using wordTrace_append hprefix tailTrace_6981461
  have hstable : (prefixWord ++ tailWord_6981461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981461).length < 2 ^ (prefixWord ++ tailWord_6981461).sum := by decide
  have hdescent : baseEnd_6981461 < baseStart_6981461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981476 : List Nat := [2, 3, 1, 1, 6, 1, 2, 1, 1, 3, 2]
def baseStart_6981476 : Nat := 118140960795 + 6981476 * 2 ^ 59
def prefixEnd_6981476 : Nat := 4983230072969 + 3 ^ 40 * 6981476 * 2
def baseEnd_6981476 : Nat := 3584852865828832176742783

theorem tailTrace_6981476 : CollatzResearch.WordTrace tailWord_6981476 prefixEnd_6981476 3584852865828832176742783 := by
  unfold tailWord_6981476
  simp only [CollatzResearch.WordTrace]
  refine ⟨127317674427656134009390141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169756899236874845345853521 127317674427656134009390141)
  ·
    refine ⟨47744127910371050253521303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127317674427656134009390141 47744127910371050253521303)
    ·
      refine ⟨71616191865556575380281955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47744127910371050253521303 71616191865556575380281955)
      ·
        refine ⟨107424287798334863070422933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71616191865556575380281955 107424287798334863070422933)
        ·
          refine ⟨5035513490546946706426075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 107424287798334863070422933 5035513490546946706426075)
          ·
            refine ⟨7553270235820420059639113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5035513490546946706426075 7553270235820420059639113)
            ·
              refine ⟨5664952676865315044729335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7553270235820420059639113 5664952676865315044729335)
              ·
                refine ⟨8497429015297972567094003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5664952676865315044729335 8497429015297972567094003)
                ·
                  refine ⟨12746143522946958850641005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8497429015297972567094003 12746143522946958850641005)
                  ·
                    refine ⟨4779803821105109568990377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12746143522946958850641005 4779803821105109568990377)
                    ·
                      refine ⟨3584852865828832176742783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4779803821105109568990377 3584852865828832176742783)
                      ·
                        rfl

theorem cell23_6981476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 1, 3, 2].length) (baseStart_6981476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981476 prefixEnd_6981476 := by exact prefixLift 6981476
  have htrace : WordTrace (prefixWord ++ tailWord_6981476) baseStart_6981476 baseEnd_6981476 := by
    simpa [prefixWord, tailWord_6981476, baseEnd_6981476] using wordTrace_append hprefix tailTrace_6981476
  have hstable : (prefixWord ++ tailWord_6981476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981476).length < 2 ^ (prefixWord ++ tailWord_6981476).sum := by decide
  have hdescent : baseEnd_6981476 < baseStart_6981476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981491 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 4, 5]
def baseStart_6981491 : Nat := 118140960795 + 6981491 * 2 ^ 59
def prefixEnd_6981491 : Nat := 4983230072969 + 3 ^ 40 * 6981491 * 2
def baseEnd_6981491 : Nat := 1194953522679549872685071

theorem tailTrace_6981491 : CollatzResearch.WordTrace tailWord_6981491 prefixEnd_6981491 1194953522679549872685071 := by
  unfold tailWord_6981491
  simp only [CollatzResearch.WordTrace]
  refine ⟨254635895950257925580576327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169757263966838617053717551 254635895950257925580576327)
  ·
    refine ⟨381953843925386888370864491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254635895950257925580576327 381953843925386888370864491)
    ·
      refine ⟨572930765888080332556296737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381953843925386888370864491 572930765888080332556296737)
      ·
        refine ⟨429698074416060249417222553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 572930765888080332556296737 429698074416060249417222553)
        ·
          refine ⟨322273555812045187062916915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429698074416060249417222553 322273555812045187062916915)
          ·
            refine ⟨483410333718067780594375373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322273555812045187062916915 483410333718067780594375373)
            ·
              refine ⟨181278875144275417722890765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 483410333718067780594375373 181278875144275417722890765)
              ·
                refine ⟨67979578179103281646084037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181278875144275417722890765 67979578179103281646084037)
                ·
                  refine ⟨12746170908581865308640757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67979578179103281646084037 12746170908581865308640757)
                  ·
                    refine ⟨1194953522679549872685071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12746170908581865308640757 1194953522679549872685071)
                    ·
                      rfl

theorem cell23_6981491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 5].length) (baseStart_6981491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981491 prefixEnd_6981491 := by exact prefixLift 6981491
  have htrace : WordTrace (prefixWord ++ tailWord_6981491) baseStart_6981491 baseEnd_6981491 := by
    simpa [prefixWord, tailWord_6981491, baseEnd_6981491] using wordTrace_append hprefix tailTrace_6981491
  have hstable : (prefixWord ++ tailWord_6981491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981491).length < 2 ^ (prefixWord ++ tailWord_6981491).sum := by decide
  have hdescent : baseEnd_6981491 < baseStart_6981491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981498 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2]
def baseStart_6981498 : Nat := 118140960795 + 6981498 * 2 ^ 59
def prefixEnd_6981498 : Nat := 4983230072969 + 3 ^ 40 * 6981498 * 2
def baseEnd_6981498 : Nat := 3584864162403231090667681

theorem tailTrace_6981498 : CollatzResearch.WordTrace tailWord_6981498 prefixEnd_6981498 3584864162403231090667681 := by
  unfold tailWord_6981498
  simp only [CollatzResearch.WordTrace]
  refine ⟨63659037815308141444020287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169757434174155043850720765 63659037815308141444020287)
  ·
    refine ⟨95488556722962212166030431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63659037815308141444020287 95488556722962212166030431)
    ·
      refine ⟨143232835084443318249045647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95488556722962212166030431 143232835084443318249045647)
      ·
        refine ⟨214849252626664977373568471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143232835084443318249045647 214849252626664977373568471)
        ·
          refine ⟨322273878939997466060352707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214849252626664977373568471 322273878939997466060352707)
          ·
            refine ⟨483410818409996199090529061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322273878939997466060352707 483410818409996199090529061)
            ·
              refine ⟨90639528451874287329474199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 483410818409996199090529061 90639528451874287329474199)
              ·
                refine ⟨135959292677811430994211299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90639528451874287329474199 135959292677811430994211299)
                ·
                  refine ⟨203938939016717146491316949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135959292677811430994211299 203938939016717146491316949)
                  ·
                    refine ⟨4779818883204308120890241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 203938939016717146491316949 4779818883204308120890241)
                    ·
                      refine ⟨3584864162403231090667681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4779818883204308120890241 3584864162403231090667681)
                      ·
                        rfl

theorem cell23_6981498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 1, 7, 2].length) (baseStart_6981498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981498 prefixEnd_6981498 := by exact prefixLift 6981498
  have htrace : WordTrace (prefixWord ++ tailWord_6981498) baseStart_6981498 baseEnd_6981498 := by
    simpa [prefixWord, tailWord_6981498, baseEnd_6981498] using wordTrace_append hprefix tailTrace_6981498
  have hstable : (prefixWord ++ tailWord_6981498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981498).length < 2 ^ (prefixWord ++ tailWord_6981498).sum := by decide
  have hdescent : baseEnd_6981498 < baseStart_6981498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981501 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 1, 1, 7]
def baseStart_6981501 : Nat := 118140960795 + 6981501 * 2 ^ 59
def prefixEnd_6981501 : Nat := 4983230072969 + 3 ^ 40 * 6981501 * 2
def baseEnd_6981501 : Nat := 3584865702845194578930167

theorem tailTrace_6981501 : CollatzResearch.WordTrace tailWord_6981501 prefixEnd_6981501 3584865702845194578930167 := by
  unfold tailWord_6981501
  simp only [CollatzResearch.WordTrace]
  refine ⟨254636260680221697288440357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169757507120147798192293571 254636260680221697288440357)
  ·
    refine ⟨47744298877541568241582567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254636260680221697288440357 47744298877541568241582567)
    ·
      refine ⟨71616448316312352362373851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47744298877541568241582567 71616448316312352362373851)
      ·
        refine ⟨107424672474468528543560777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71616448316312352362373851 107424672474468528543560777)
        ·
          refine ⟨80568504355851396407670583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107424672474468528543560777 80568504355851396407670583)
          ·
            refine ⟨120852756533777094611505875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80568504355851396407670583 120852756533777094611505875)
            ·
              refine ⟨181279134800665641917258813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120852756533777094611505875 181279134800665641917258813)
              ·
                refine ⟨67979675550249615718972055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181279134800665641917258813 67979675550249615718972055)
                ·
                  refine ⟨101969513325374423578458083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67979675550249615718972055 101969513325374423578458083)
                  ·
                    refine ⟨152954269988061635367687125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101969513325374423578458083 152954269988061635367687125)
                    ·
                      refine ⟨3584865702845194578930167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152954269988061635367687125 3584865702845194578930167)
                      ·
                        rfl

theorem cell23_6981501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_6981501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981501 prefixEnd_6981501 := by exact prefixLift 6981501
  have htrace : WordTrace (prefixWord ++ tailWord_6981501) baseStart_6981501 baseEnd_6981501 := by
    simpa [prefixWord, tailWord_6981501, baseEnd_6981501] using wordTrace_append hprefix tailTrace_6981501
  have hstable : (prefixWord ++ tailWord_6981501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981501).length < 2 ^ (prefixWord ++ tailWord_6981501).sum := by decide
  have hdescent : baseEnd_6981501 < baseStart_6981501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981541 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 1, 3, 6]
def baseStart_6981541 : Nat := 118140960795 + 6981541 * 2 ^ 59
def prefixEnd_6981541 : Nat := 4983230072969 + 3 ^ 40 * 6981541 * 2
def baseEnd_6981541 : Nat := 3584886242071374422429983

theorem tailTrace_6981541 : CollatzResearch.WordTrace tailWord_6981541 prefixEnd_6981541 3584886242071374422429983 := by
  unfold tailWord_6981541
  simp only [CollatzResearch.WordTrace]
  refine ⟨254637719600076784119896477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169758479733384522746597651 254637719600076784119896477)
  ·
    refine ⟨95489144850028794044961179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254637719600076784119896477 95489144850028794044961179)
    ·
      refine ⟨143233717275043191067441769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95489144850028794044961179 143233717275043191067441769)
      ·
        refine ⟨107425287956282393300581327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143233717275043191067441769 107425287956282393300581327)
        ·
          refine ⟨161137931934423589950871991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107425287956282393300581327 161137931934423589950871991)
          ·
            refine ⟨241706897901635384926307987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161137931934423589950871991 241706897901635384926307987)
            ·
              refine ⟨362560346852453077389461981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241706897901635384926307987 362560346852453077389461981)
              ·
                refine ⟨135960130069669904021048243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 362560346852453077389461981 135960130069669904021048243)
                ·
                  refine ⟨203940195104504856031572365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135960130069669904021048243 203940195104504856031572365)
                  ·
                    refine ⟨76477573164189321011839637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 203940195104504856031572365 76477573164189321011839637)
                    ·
                      refine ⟨3584886242071374422429983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76477573164189321011839637 3584886242071374422429983)
                      ·
                        rfl

theorem cell23_6981541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_6981541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981541 prefixEnd_6981541 := by exact prefixLift 6981541
  have htrace : WordTrace (prefixWord ++ tailWord_6981541) baseStart_6981541 baseEnd_6981541 := by
    simpa [prefixWord, tailWord_6981541, baseEnd_6981541] using wordTrace_append hprefix tailTrace_6981541
  have hstable : (prefixWord ++ tailWord_6981541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981541).length < 2 ^ (prefixWord ++ tailWord_6981541).sum := by decide
  have hdescent : baseEnd_6981541 < baseStart_6981541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981551 : List Nat := [1, 1, 2, 1, 2, 2, 3, 3, 8]
def baseStart_6981551 : Nat := 118140960795 + 6981551 * 2 ^ 59
def prefixEnd_6981551 : Nat := 4983230072969 + 3 ^ 40 * 6981551 * 2
def baseEnd_6981551 : Nat := 398321264097546598144993

theorem tailTrace_6981551 : CollatzResearch.WordTrace tailWord_6981551 prefixEnd_6981551 398321264097546598144993 := by
  unfold tailWord_6981551
  simp only [CollatzResearch.WordTrace]
  refine ⟨254638084330040555827760507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169758722886693703885173671 254638084330040555827760507)
  ·
    refine ⟨381957126495060833741640761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254638084330040555827760507 381957126495060833741640761)
    ·
      refine ⟨286467844871295625306230571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381957126495060833741640761 286467844871295625306230571)
      ·
        refine ⟨429701767306943437959345857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286467844871295625306230571 429701767306943437959345857)
        ·
          refine ⟨322276325480207578469509393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429701767306943437959345857 322276325480207578469509393)
          ·
            refine ⟨241707244110155683852132045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322276325480207578469509393 241707244110155683852132045)
            ·
              refine ⟨90640216541308381444549517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241707244110155683852132045 90640216541308381444549517)
              ·
                refine ⟨33990081202990643041706069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90640216541308381444549517 33990081202990643041706069)
                ·
                  refine ⟨398321264097546598144993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33990081202990643041706069 398321264097546598144993)
                  ·
                    rfl

theorem cell23_6981551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 8].length) (baseStart_6981551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981551 prefixEnd_6981551 := by exact prefixLift 6981551
  have htrace : WordTrace (prefixWord ++ tailWord_6981551) baseStart_6981551 baseEnd_6981551 := by
    simpa [prefixWord, tailWord_6981551, baseEnd_6981551] using wordTrace_append hprefix tailTrace_6981551
  have hstable : (prefixWord ++ tailWord_6981551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981551).length < 2 ^ (prefixWord ++ tailWord_6981551).sum := by decide
  have hdescent : baseEnd_6981551 < baseStart_6981551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981568 : List Nat := [2, 1, 1, 2, 3, 2, 3, 3, 6]
def baseStart_6981568 : Nat := 118140960795 + 6981568 * 2 ^ 59
def prefixEnd_6981568 : Nat := 4983230072969 + 3 ^ 40 * 6981568 * 2
def baseEnd_6981568 : Nat := 398322234005449535199151

theorem tailTrace_6981568 : CollatzResearch.WordTrace tailWord_6981568 prefixEnd_6981568 398322234005449535199151 := by
  unfold tailWord_6981568
  simp only [CollatzResearch.WordTrace]
  refine ⟨127319352185489483865564679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169759136247319311820752905 127319352185489483865564679)
  ·
    refine ⟨190979028278234225798347019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127319352185489483865564679 190979028278234225798347019)
    ·
      refine ⟨286468542417351338697520529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190979028278234225798347019 286468542417351338697520529)
      ·
        refine ⟨214851406813013504023140397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286468542417351338697520529 214851406813013504023140397)
        ·
          refine ⟨80569277554880064008677649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214851406813013504023140397 80569277554880064008677649)
          ·
            refine ⟨60426958166160048006508237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80569277554880064008677649 60426958166160048006508237)
            ·
              refine ⟨22660109312310018002440589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60426958166160048006508237 22660109312310018002440589)
              ·
                refine ⟨8497540992116256750915221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22660109312310018002440589 8497540992116256750915221)
                ·
                  refine ⟨398322234005449535199151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8497540992116256750915221 398322234005449535199151)
                  ·
                    rfl

theorem cell23_6981568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 6].length) (baseStart_6981568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981568 prefixEnd_6981568 := by exact prefixLift 6981568
  have htrace : WordTrace (prefixWord ++ tailWord_6981568) baseStart_6981568 baseEnd_6981568 := by
    simpa [prefixWord, tailWord_6981568, baseEnd_6981568] using wordTrace_append hprefix tailTrace_6981568
  have hstable : (prefixWord ++ tailWord_6981568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981568).length < 2 ^ (prefixWord ++ tailWord_6981568).sum := by decide
  have hdescent : baseEnd_6981568 < baseStart_6981568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981578 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 2, 5, 3]
def baseStart_6981578 : Nat := 118140960795 + 6981578 * 2 ^ 59
def prefixEnd_6981578 : Nat := 4983230072969 + 3 ^ 40 * 6981578 * 2
def baseEnd_6981578 : Nat := 3584905240855590777667313

theorem tailTrace_6981578 : CollatzResearch.WordTrace tailWord_6981578 prefixEnd_6981578 3584905240855590777667313 := by
  unfold tailWord_6981578
  simp only [CollatzResearch.WordTrace]
  refine ⟨63659767275235684859748347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169759379400628492959328925 63659767275235684859748347)
  ·
    refine ⟨95489650912853527289622521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63659767275235684859748347 95489650912853527289622521)
    ·
      refine ⟨71617238184640145467216891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95489650912853527289622521 71617238184640145467216891)
      ·
        refine ⟨107425857276960218200825337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71617238184640145467216891 107425857276960218200825337)
        ·
          refine ⟨80569392957720163650619003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107425857276960218200825337 80569392957720163650619003)
          ·
            refine ⟨120854089436580245475928505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80569392957720163650619003 120854089436580245475928505)
            ·
              refine ⟨90640567077435184106946379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120854089436580245475928505 90640567077435184106946379)
              ·
                refine ⟨135960850616152776160419569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90640567077435184106946379 135960850616152776160419569)
                ·
                  refine ⟨101970637962114582120314677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135960850616152776160419569 101970637962114582120314677)
                  ·
                    refine ⟨9559747308948242073779501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101970637962114582120314677 9559747308948242073779501)
                    ·
                      refine ⟨3584905240855590777667313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9559747308948242073779501 3584905240855590777667313)
                      ·
                        rfl

theorem cell23_6981578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_6981578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981578 prefixEnd_6981578 := by exact prefixLift 6981578
  have htrace : WordTrace (prefixWord ++ tailWord_6981578) baseStart_6981578 baseEnd_6981578 := by
    simpa [prefixWord, tailWord_6981578, baseEnd_6981578] using wordTrace_append hprefix tailTrace_6981578
  have hstable : (prefixWord ++ tailWord_6981578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981578).length < 2 ^ (prefixWord ++ tailWord_6981578).sum := by decide
  have hdescent : baseEnd_6981578 < baseStart_6981578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981639 : List Nat := [1, 1, 4, 3, 1, 4, 1, 1, 2, 3, 2]
def baseStart_6981639 : Nat := 118140960795 + 6981639 * 2 ^ 59
def prefixEnd_6981639 : Nat := 4983230072969 + 3 ^ 40 * 6981639 * 2
def baseEnd_6981639 : Nat := 3584936563175515039004533

theorem tailTrace_6981639 : CollatzResearch.WordTrace tailWord_6981639 prefixEnd_6981639 3584936563175515039004533 := by
  unfold tailWord_6981639
  simp only [CollatzResearch.WordTrace]
  refine ⟨254641293953721746856963971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169760862635814497904642647 254641293953721746856963971)
  ·
    refine ⟨381961940930582620285445957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254641293953721746856963971 381961940930582620285445957)
    ·
      refine ⟨71617863924484241303521117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 381961940930582620285445957 71617863924484241303521117)
      ·
        refine ⟨26856698971681590488820419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71617863924484241303521117 26856698971681590488820419)
        ·
          refine ⟨40285048457522385733230629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26856698971681590488820419 40285048457522385733230629)
          ·
            refine ⟨7553446585785447324980743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40285048457522385733230629 7553446585785447324980743)
            ·
              refine ⟨11330169878678170987471115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7553446585785447324980743 11330169878678170987471115)
              ·
                refine ⟨16995254818017256481206673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11330169878678170987471115 16995254818017256481206673)
                ·
                  refine ⟨12746441113512942360905005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16995254818017256481206673 12746441113512942360905005)
                  ·
                    refine ⟨4779915417567353385339377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12746441113512942360905005 4779915417567353385339377)
                    ·
                      refine ⟨3584936563175515039004533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4779915417567353385339377 3584936563175515039004533)
                      ·
                        rfl

theorem cell23_6981639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_6981639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981639 prefixEnd_6981639 := by exact prefixLift 6981639
  have htrace : WordTrace (prefixWord ++ tailWord_6981639) baseStart_6981639 baseEnd_6981639 := by
    simpa [prefixWord, tailWord_6981639, baseEnd_6981639] using wordTrace_append hprefix tailTrace_6981639
  have hstable : (prefixWord ++ tailWord_6981639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981639).length < 2 ^ (prefixWord ++ tailWord_6981639).sum := by decide
  have hdescent : baseEnd_6981639 < baseStart_6981639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981658 : List Nat := [3, 1, 1, 3, 1, 4, 10]
def baseStart_6981658 : Nat := 118140960795 + 6981658 * 2 ^ 59
def prefixEnd_6981658 : Nat := 4983230072969 + 3 ^ 40 * 6981658 * 2
def baseEnd_6981658 : Nat := 44258596534666055119345

theorem tailTrace_6981658 : CollatzResearch.WordTrace tailWord_6981658 prefixEnd_6981658 44258596534666055119345 := by
  unfold tailWord_6981658
  simp only [CollatzResearch.WordTrace]
  refine ⟨63660496735163228275476407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169761324627101942067937085 63660496735163228275476407)
  ·
    refine ⟨95490745102744842413214611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63660496735163228275476407 95490745102744842413214611)
    ·
      refine ⟨143236117654117263619821917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95490745102744842413214611 143236117654117263619821917)
      ·
        refine ⟨53713544120293973857433219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143236117654117263619821917 53713544120293973857433219)
        ·
          refine ⟨80570316180440960786149829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53713544120293973857433219 80570316180440960786149829)
          ·
            refine ⟨15106934283832680147403093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80570316180440960786149829 15106934283832680147403093)
            ·
              refine ⟨44258596534666055119345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15106934283832680147403093 44258596534666055119345)
              ·
                rfl

theorem cell23_6981658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 10].length) (baseStart_6981658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981658 prefixEnd_6981658 := by exact prefixLift 6981658
  have htrace : WordTrace (prefixWord ++ tailWord_6981658) baseStart_6981658 baseEnd_6981658 := by
    simpa [prefixWord, tailWord_6981658, baseEnd_6981658] using wordTrace_append hprefix tailTrace_6981658
  have hstable : (prefixWord ++ tailWord_6981658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981658).length < 2 ^ (prefixWord ++ tailWord_6981658).sum := by decide
  have hdescent : baseEnd_6981658 < baseStart_6981658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981669 : List Nat := [1, 3, 1, 2, 2, 4, 2, 1, 3, 2, 2]
def baseStart_6981669 : Nat := 118140960795 + 6981669 * 2 ^ 59
def prefixEnd_6981669 : Nat := 4983230072969 + 3 ^ 40 * 6981669 * 2
def baseEnd_6981669 : Nat := 3584951967595149921629395

theorem tailTrace_6981669 : CollatzResearch.WordTrace tailWord_6981669 prefixEnd_6981669 3584951967595149921629395 := by
  unfold tailWord_6981669
  simp only [CollatzResearch.WordTrace]
  refine ⟨254642388143613061980556061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169761592095742041320370707 254642388143613061980556061)
  ·
    refine ⟨95490895553854898242708523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254642388143613061980556061 95490895553854898242708523)
    ·
      refine ⟨143236343330782347364062785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95490895553854898242708523 143236343330782347364062785)
      ·
        refine ⟨107427257498086760523047089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143236343330782347364062785 107427257498086760523047089)
        ·
          refine ⟨80570443123565070392285317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107427257498086760523047089 80570443123565070392285317)
          ·
            refine ⟨15106958085668450698553497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80570443123565070392285317 15106958085668450698553497)
            ·
              refine ⟨11330218564251338023915123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15106958085668450698553497 11330218564251338023915123)
              ·
                refine ⟨16995327846377007035872685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11330218564251338023915123 16995327846377007035872685)
                ·
                  refine ⟨6373247942391377638452257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16995327846377007035872685 6373247942391377638452257)
                  ·
                    refine ⟨4779935956793533228839193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6373247942391377638452257 4779935956793533228839193)
                    ·
                      refine ⟨3584951967595149921629395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4779935956793533228839193 3584951967595149921629395)
                      ·
                        rfl

theorem cell23_6981669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3, 2, 2].length) (baseStart_6981669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981669 prefixEnd_6981669 := by exact prefixLift 6981669
  have htrace : WordTrace (prefixWord ++ tailWord_6981669) baseStart_6981669 baseEnd_6981669 := by
    simpa [prefixWord, tailWord_6981669, baseEnd_6981669] using wordTrace_append hprefix tailTrace_6981669
  have hstable : (prefixWord ++ tailWord_6981669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981669).length < 2 ^ (prefixWord ++ tailWord_6981669).sum := by decide
  have hdescent : baseEnd_6981669 < baseStart_6981669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981682 : List Nat := [3, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4]
def baseStart_6981682 : Nat := 118140960795 + 6981682 * 2 ^ 59
def prefixEnd_6981682 : Nat := 4983230072969 + 3 ^ 40 * 6981682 * 2
def baseEnd_6981682 : Nat := 3584958642843658370766835

theorem tailTrace_6981682 : CollatzResearch.WordTrace tailWord_6981682 prefixEnd_6981682 3584958642843658370766835 := by
  unfold tailWord_6981682
  simp only [CollatzResearch.WordTrace]
  refine ⟨63660715573141491300194825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169761908195043976800519533 63660715573141491300194825)
  ·
    refine ⟨47745536679856118475146119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63660715573141491300194825 47745536679856118475146119)
    ·
      refine ⟨71618305019784177712719179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47745536679856118475146119 71618305019784177712719179)
      ·
        refine ⟨107427457529676266569078769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71618305019784177712719179 107427457529676266569078769)
        ·
          refine ⟨80570593147257199926809077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107427457529676266569078769 80570593147257199926809077)
          ·
            refine ⟨7553493107555362493138351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80570593147257199926809077 7553493107555362493138351)
            ·
              refine ⟨11330239661333043739707527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7553493107555362493138351 11330239661333043739707527)
              ·
                refine ⟨16995359491999565609561291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11330239661333043739707527 16995359491999565609561291)
                ·
                  refine ⟨25493039237999348414341937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16995359491999565609561291 25493039237999348414341937)
                  ·
                    refine ⟨19119779428499511310756453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25493039237999348414341937 19119779428499511310756453)
                    ·
                      refine ⟨3584958642843658370766835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19119779428499511310756453 3584958642843658370766835)
                      ·
                        rfl

theorem cell23_6981682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_6981682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981682 prefixEnd_6981682 := by exact prefixLift 6981682
  have htrace : WordTrace (prefixWord ++ tailWord_6981682) baseStart_6981682 baseEnd_6981682 := by
    simpa [prefixWord, tailWord_6981682, baseEnd_6981682] using wordTrace_append hprefix tailTrace_6981682
  have hstable : (prefixWord ++ tailWord_6981682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981682).length < 2 ^ (prefixWord ++ tailWord_6981682).sum := by decide
  have hdescent : baseEnd_6981682 < baseStart_6981682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981689 : List Nat := [1, 2, 1, 5, 3, 1, 2, 2, 1, 2, 3]
def baseStart_6981689 : Nat := 118140960795 + 6981689 * 2 ^ 59
def prefixEnd_6981689 : Nat := 4983230072969 + 3 ^ 40 * 6981689 * 2
def baseEnd_6981689 : Nat := 3584962237208239843379303

theorem tailTrace_6981689 : CollatzResearch.WordTrace tailWord_6981689 prefixEnd_6981689 3584962237208239843379303 := by
  unfold tailWord_6981689
  simp only [CollatzResearch.WordTrace]
  refine ⟨254643117603540605396284121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169762078402360403597522747 254643117603540605396284121)
  ·
    refine ⟨190982338202655454047213091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254643117603540605396284121 190982338202655454047213091)
    ·
      refine ⟨286473507303983181070819637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190982338202655454047213091 286473507303983181070819637)
      ·
        refine ⟨26856891309748423225389341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 286473507303983181070819637 26856891309748423225389341)
        ·
          refine ⟨10071334241155658709521003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26856891309748423225389341 10071334241155658709521003)
          ·
            refine ⟨15107001361733488064281505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10071334241155658709521003 15107001361733488064281505)
            ·
              refine ⟨11330251021300116048211129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15107001361733488064281505 11330251021300116048211129)
              ·
                refine ⟨8497688265975087036158347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11330251021300116048211129 8497688265975087036158347)
                ·
                  refine ⟨12746532398962630554237521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8497688265975087036158347 12746532398962630554237521)
                  ·
                    refine ⟨9559899299221972915678141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12746532398962630554237521 9559899299221972915678141)
                    ·
                      refine ⟨3584962237208239843379303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9559899299221972915678141 3584962237208239843379303)
                      ·
                        rfl

theorem cell23_6981689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_6981689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981689 prefixEnd_6981689 := by exact prefixLift 6981689
  have htrace : WordTrace (prefixWord ++ tailWord_6981689) baseStart_6981689 baseEnd_6981689 := by
    simpa [prefixWord, tailWord_6981689, baseEnd_6981689] using wordTrace_append hprefix tailTrace_6981689
  have hstable : (prefixWord ++ tailWord_6981689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981689).length < 2 ^ (prefixWord ++ tailWord_6981689).sum := by decide
  have hdescent : baseEnd_6981689 < baseStart_6981689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981746 : List Nat := [3, 2, 1, 2, 2, 4, 1, 2, 1, 3, 2]
def baseStart_6981746 : Nat := 118140960795 + 6981746 * 2 ^ 59
def prefixEnd_6981746 : Nat := 4983230072969 + 3 ^ 40 * 6981746 * 2
def baseEnd_6981746 : Nat := 3584991505605546120366541

theorem tailTrace_6981746 : CollatzResearch.WordTrace tailWord_6981746 prefixEnd_6981746 3584991505605546120366541 := by
  unfold tailWord_6981746
  simp only [CollatzResearch.WordTrace]
  refine ⟨63661299141083526032777273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169763464376222736087406061 63661299141083526032777273)
  ·
    refine ⟨47745974355812644524582955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63661299141083526032777273 47745974355812644524582955)
    ·
      refine ⟨71618961533718966786874433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47745974355812644524582955 71618961533718966786874433)
      ·
        refine ⟨53714221150289225090155825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71618961533718966786874433 53714221150289225090155825)
        ·
          refine ⟨40285665862716918817616869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53714221150289225090155825 40285665862716918817616869)
          ·
            refine ⟨7553562349259422278303163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40285665862716918817616869 7553562349259422278303163)
            ·
              refine ⟨11330343523889133417454745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7553562349259422278303163 11330343523889133417454745)
              ·
                refine ⟨8497757642916850063091059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11330343523889133417454745 8497757642916850063091059)
                ·
                  refine ⟨12746636464375275094636589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8497757642916850063091059 12746636464375275094636589)
                  ·
                    refine ⟨4779988674140728160488721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12746636464375275094636589 4779988674140728160488721)
                    ·
                      refine ⟨3584991505605546120366541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4779988674140728160488721 3584991505605546120366541)
                      ·
                        rfl

theorem cell23_6981746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_6981746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981746 prefixEnd_6981746 := by exact prefixLift 6981746
  have htrace : WordTrace (prefixWord ++ tailWord_6981746) baseStart_6981746 baseEnd_6981746 := by
    simpa [prefixWord, tailWord_6981746, baseEnd_6981746] using wordTrace_append hprefix tailTrace_6981746
  have hstable : (prefixWord ++ tailWord_6981746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981746).length < 2 ^ (prefixWord ++ tailWord_6981746).sum := by decide
  have hdescent : baseEnd_6981746 < baseStart_6981746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981792 : List Nat := [2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 3]
def baseStart_6981792 : Nat := 118140960795 + 6981792 * 2 ^ 59
def prefixEnd_6981792 : Nat := 4983230072969 + 3 ^ 40 * 6981792 * 2
def baseEnd_6981792 : Nat := 3585015125715652940391329

theorem tailTrace_6981792 : CollatzResearch.WordTrace tailWord_6981792 prefixEnd_6981792 3585015125715652940391329 := by
  unfold tailWord_6981792
  simp only [CollatzResearch.WordTrace]
  refine ⟨127323437161083726993641815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169764582881444969324855753 127323437161083726993641815)
  ·
    refine ⟨190985155741625590490462723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127323437161083726993641815 190985155741625590490462723)
    ·
      refine ⟨286477733612438385735694085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190985155741625590490462723 286477733612438385735694085)
      ·
        refine ⟨53714575052332197325442641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286477733612438385735694085 53714575052332197325442641)
        ·
          refine ⟨40285931289249147994081981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53714575052332197325442641 40285931289249147994081981)
          ·
            refine ⟨15107224233468430497780743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40285931289249147994081981 15107224233468430497780743)
            ·
              refine ⟨22660836350202645746671115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15107224233468430497780743 22660836350202645746671115)
              ·
                refine ⟨33991254525303968620006673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22660836350202645746671115 33991254525303968620006673)
                ·
                  refine ⟨25493440893977976465005005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33991254525303968620006673 25493440893977976465005005)
                  ·
                    refine ⟨9560040335241741174376877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25493440893977976465005005 9560040335241741174376877)
                    ·
                      refine ⟨3585015125715652940391329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9560040335241741174376877 3585015125715652940391329)
                      ·
                        rfl

theorem cell23_6981792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_6981792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981792 prefixEnd_6981792 := by exact prefixLift 6981792
  have htrace : WordTrace (prefixWord ++ tailWord_6981792) baseStart_6981792 baseEnd_6981792 := by
    simpa [prefixWord, tailWord_6981792, baseEnd_6981792] using wordTrace_append hprefix tailTrace_6981792
  have hstable : (prefixWord ++ tailWord_6981792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981792).length < 2 ^ (prefixWord ++ tailWord_6981792).sum := by decide
  have hdescent : baseEnd_6981792 < baseStart_6981792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981826 : List Nat := [3, 5, 1, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_6981826 : Nat := 118140960795 + 6981826 * 2 ^ 59
def prefixEnd_6981826 : Nat := 4983230072969 + 3 ^ 40 * 6981826 * 2
def baseEnd_6981826 : Nat := 3585032584057905807366173

theorem tailTrace_6981826 : CollatzResearch.WordTrace tailWord_6981826 prefixEnd_6981826 3585032584057905807366173 := by
  unfold tailWord_6981826
  simp only [CollatzResearch.WordTrace]
  refine ⟨63662028601011069448505333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169765409602696185196014221 63662028601011069448505333)
  ·
    refine ⟨5968315181344787760797375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63662028601011069448505333 5968315181344787760797375)
    ·
      refine ⟨8952472772017181641196063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5968315181344787760797375 8952472772017181641196063)
      ·
        refine ⟨13428709158025772461794095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8952472772017181641196063 13428709158025772461794095)
        ·
          refine ⟨20143063737038658692691143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13428709158025772461794095 20143063737038658692691143)
          ·
            refine ⟨30214595605557988039036715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20143063737038658692691143 30214595605557988039036715)
            ·
              refine ⟨45321893408336982058555073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30214595605557988039036715 45321893408336982058555073)
              ·
                refine ⟨33991420056252736543916305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45321893408336982058555073 33991420056252736543916305)
                ·
                  refine ⟨25493565042189552407937229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33991420056252736543916305 25493565042189552407937229)
                  ·
                    refine ⟨9560086890821082152976461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25493565042189552407937229 9560086890821082152976461)
                    ·
                      refine ⟨3585032584057905807366173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9560086890821082152976461 3585032584057905807366173)
                      ·
                        rfl

theorem cell23_6981826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_6981826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981826 prefixEnd_6981826 := by exact prefixLift 6981826
  have htrace : WordTrace (prefixWord ++ tailWord_6981826) baseStart_6981826 baseEnd_6981826 := by
    simpa [prefixWord, tailWord_6981826, baseEnd_6981826] using wordTrace_append hprefix tailTrace_6981826
  have hstable : (prefixWord ++ tailWord_6981826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981826).length < 2 ^ (prefixWord ++ tailWord_6981826).sum := by decide
  have hdescent : baseEnd_6981826 < baseStart_6981826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981902 : List Nat := [4, 1, 1, 2, 1, 2, 2, 2, 3, 5]
def baseStart_6981902 : Nat := 118140960795 + 6981902 * 2 ^ 59
def prefixEnd_6981902 : Nat := 4983230072969 + 3 ^ 40 * 6981902 * 2
def baseEnd_6981902 : Nat := 1195023869529215836671941

theorem tailTrace_6981902 : CollatzResearch.WordTrace tailWord_6981902 prefixEnd_6981902 1195023869529215836671941 := by
  unfold tailWord_6981902
  simp only [CollatzResearch.WordTrace]
  refine ⟨31831360793971117846723495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169767257567845961849191973 31831360793971117846723495)
  ·
    refine ⟨47747041190956676770085243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31831360793971117846723495 47747041190956676770085243)
    ·
      refine ⟨71620561786435015155127865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47747041190956676770085243 71620561786435015155127865)
      ·
        refine ⟨53715421339826261366345899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71620561786435015155127865 53715421339826261366345899)
        ·
          refine ⟨80573132009739392049518849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53715421339826261366345899 80573132009739392049518849)
          ·
            refine ⟨60429849007304544037139137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80573132009739392049518849 60429849007304544037139137)
            ·
              refine ⟨45322386755478408027854353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60429849007304544037139137 45322386755478408027854353)
              ·
                refine ⟨33991790066608806020890765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45322386755478408027854353 33991790066608806020890765)
                ·
                  refine ⟨12746921274978302257834037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33991790066608806020890765 12746921274978302257834037)
                  ·
                    refine ⟨1195023869529215836671941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12746921274978302257834037 1195023869529215836671941)
                    ·
                      rfl

theorem cell23_6981902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_6981902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981902 prefixEnd_6981902 := by exact prefixLift 6981902
  have htrace : WordTrace (prefixWord ++ tailWord_6981902) baseStart_6981902 baseEnd_6981902 := by
    simpa [prefixWord, tailWord_6981902, baseEnd_6981902] using wordTrace_append hprefix tailTrace_6981902
  have hstable : (prefixWord ++ tailWord_6981902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981902).length < 2 ^ (prefixWord ++ tailWord_6981902).sum := by decide
  have hdescent : baseEnd_6981902 < baseStart_6981902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981919 : List Nat := [1, 1, 2, 4, 3, 1, 3, 2, 1, 5]
def baseStart_6981919 : Nat := 118140960795 + 6981919 * 2 ^ 59
def prefixEnd_6981919 : Nat := 4983230072969 + 3 ^ 40 * 6981919 * 2
def baseEnd_6981919 : Nat := 1195026779252924647834415

theorem tailTrace_6981919 : CollatzResearch.WordTrace tailWord_6981919 prefixEnd_6981919 1195026779252924647834415 := by
  unfold tailWord_6981919
  simp only [CollatzResearch.WordTrace]
  refine ⟨254651506392707354677156811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169767670928471569784771207 254651506392707354677156811)
  ·
    refine ⟨381977259589061032015735217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254651506392707354677156811 381977259589061032015735217)
    ·
      refine ⟨286482944691795774011801413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381977259589061032015735217 286482944691795774011801413)
      ·
        refine ⟨53715552129711707627212765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286482944691795774011801413 53715552129711707627212765)
        ·
          refine ⟨20143332048641890360204787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53715552129711707627212765 20143332048641890360204787)
          ·
            refine ⟨30214998072962835540307181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20143332048641890360204787 30214998072962835540307181)
            ·
              refine ⟨11330624277361063327615193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30214998072962835540307181 11330624277361063327615193)
              ·
                refine ⟨8497968208020797495711395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11330624277361063327615193 8497968208020797495711395)
                ·
                  refine ⟨12746952312031196243567093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8497968208020797495711395 12746952312031196243567093)
                  ·
                    refine ⟨1195026779252924647834415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12746952312031196243567093 1195026779252924647834415)
                    ·
                      rfl

theorem cell23_6981919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 5].length) (baseStart_6981919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981919 prefixEnd_6981919 := by exact prefixLift 6981919
  have htrace : WordTrace (prefixWord ++ tailWord_6981919) baseStart_6981919 baseEnd_6981919 := by
    simpa [prefixWord, tailWord_6981919, baseEnd_6981919] using wordTrace_append hprefix tailTrace_6981919
  have hstable : (prefixWord ++ tailWord_6981919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981919).length < 2 ^ (prefixWord ++ tailWord_6981919).sum := by decide
  have hdescent : baseEnd_6981919 < baseStart_6981919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981932 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 6, 4]
def baseStart_6981932 : Nat := 118140960795 + 6981932 * 2 ^ 59
def prefixEnd_6981932 : Nat := 4983230072969 + 3 ^ 40 * 6981932 * 2
def baseEnd_6981932 : Nat := 1195029004335760797546895

theorem tailTrace_6981932 : CollatzResearch.WordTrace tailWord_6981932 prefixEnd_6981932 1195029004335760797546895 := by
  unfold tailWord_6981932
  simp only [CollatzResearch.WordTrace]
  refine ⟨127325990270830128948690025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169767987027773505264920033 127325990270830128948690025)
  ·
    refine ⟨95494492703122596711517519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127325990270830128948690025 95494492703122596711517519)
    ·
      refine ⟨143241739054683895067276279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95494492703122596711517519 143241739054683895067276279)
      ·
        refine ⟨214862608582025842600914419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143241739054683895067276279 214862608582025842600914419)
        ·
          refine ⟨322293912873038763901371629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214862608582025842600914419 322293912873038763901371629)
          ·
            refine ⟨120860217327389536463014361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322293912873038763901371629 120860217327389536463014361)
            ·
              refine ⟨90645162995542152347260771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120860217327389536463014361 90645162995542152347260771)
              ·
                refine ⟨135967744493313228520891157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90645162995542152347260771 135967744493313228520891157)
                ·
                  refine ⟨6373488023124057586916773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135967744493313228520891157 6373488023124057586916773)
                  ·
                    refine ⟨1195029004335760797546895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6373488023124057586916773 1195029004335760797546895)
                    ·
                      rfl

theorem cell23_6981932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 4].length) (baseStart_6981932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981932 prefixEnd_6981932 := by exact prefixLift 6981932
  have htrace : WordTrace (prefixWord ++ tailWord_6981932) baseStart_6981932 baseEnd_6981932 := by
    simpa [prefixWord, tailWord_6981932, baseEnd_6981932] using wordTrace_append hprefix tailTrace_6981932
  have hstable : (prefixWord ++ tailWord_6981932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981932).length < 2 ^ (prefixWord ++ tailWord_6981932).sum := by decide
  have hdescent : baseEnd_6981932 < baseStart_6981932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981950 : List Nat := [4, 2, 1, 2, 1, 2, 4, 2, 1, 1, 3]
def baseStart_6981950 : Nat := 118140960795 + 6981950 * 2 ^ 59
def prefixEnd_6981950 : Nat := 4983230072969 + 3 ^ 40 * 6981950 * 2
def baseEnd_6981950 : Nat := 3585096255659063322215603

theorem tailTrace_6981950 : CollatzResearch.WordTrace tailWord_6981950 prefixEnd_6981950 3585096255659063322215603 := by
  unfold tailWord_6981950
  simp only [CollatzResearch.WordTrace]
  refine ⟨31831579631949380871441913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169768424703730031314356869 31831579631949380871441913)
  ·
    refine ⟨23873684723962035653581435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31831579631949380871441913 23873684723962035653581435)
    ·
      refine ⟨35810527085943053480372153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23873684723962035653581435 35810527085943053480372153)
      ·
        refine ⟨26857895314457290110279115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35810527085943053480372153 26857895314457290110279115)
        ·
          refine ⟨40286842971685935165418673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26857895314457290110279115 40286842971685935165418673)
          ·
            refine ⟨30215132228764451374064005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40286842971685935165418673 30215132228764451374064005)
            ·
              refine ⟨5665337292893334632637001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30215132228764451374064005 5665337292893334632637001)
              ·
                refine ⟨4249002969670000974477751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5665337292893334632637001 4249002969670000974477751)
                ·
                  refine ⟨6373504454505001461716627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4249002969670000974477751 6373504454505001461716627)
                  ·
                    refine ⟨9560256681757502192574941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6373504454505001461716627 9560256681757502192574941)
                    ·
                      refine ⟨3585096255659063322215603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9560256681757502192574941 3585096255659063322215603)
                      ·
                        rfl

theorem cell23_6981950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_6981950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981950 prefixEnd_6981950 := by exact prefixLift 6981950
  have htrace : WordTrace (prefixWord ++ tailWord_6981950) baseStart_6981950 baseEnd_6981950 := by
    simpa [prefixWord, tailWord_6981950, baseEnd_6981950] using wordTrace_append hprefix tailTrace_6981950
  have hstable : (prefixWord ++ tailWord_6981950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981950).length < 2 ^ (prefixWord ++ tailWord_6981950).sum := by decide
  have hdescent : baseEnd_6981950 < baseStart_6981950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981969 : List Nat := [1, 2, 2, 1, 4, 3, 2, 1, 1, 2, 4]
def baseStart_6981969 : Nat := 118140960795 + 6981969 * 2 ^ 59
def prefixEnd_6981969 : Nat := 4983230072969 + 3 ^ 40 * 6981969 * 2
def baseEnd_6981969 : Nat := 3585106011791498747878015

theorem tailTrace_6981969 : CollatzResearch.WordTrace tailWord_6981969 prefixEnd_6981969 3585106011791498747878015 := by
  unfold tailWord_6981969
  simp only [CollatzResearch.WordTrace]
  refine ⟨254653330042526213216476961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169768886695017475477651307 254653330042526213216476961)
  ·
    refine ⟨190989997531894659912357721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254653330042526213216476961 190989997531894659912357721)
    ·
      refine ⟨143242498148920994934268291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190989997531894659912357721 143242498148920994934268291)
      ·
        refine ⟨214863747223381492401402437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143242498148920994934268291 214863747223381492401402437)
        ·
          refine ⟨40286952604384029825262957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214863747223381492401402437 40286952604384029825262957)
          ·
            refine ⟨15107607226644011184473609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40286952604384029825262957 15107607226644011184473609)
            ·
              refine ⟨11330705419983008388355207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15107607226644011184473609 11330705419983008388355207)
              ·
                refine ⟨16996058129974512582532811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11330705419983008388355207 16996058129974512582532811)
                ·
                  refine ⟨25494087194961768873799217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16996058129974512582532811 25494087194961768873799217)
                  ·
                    refine ⟨19120565396221326655349413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25494087194961768873799217 19120565396221326655349413)
                    ·
                      refine ⟨3585106011791498747878015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19120565396221326655349413 3585106011791498747878015)
                      ·
                        rfl

theorem cell23_6981969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 2, 4].length) (baseStart_6981969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981969 prefixEnd_6981969 := by exact prefixLift 6981969
  have htrace : WordTrace (prefixWord ++ tailWord_6981969) baseStart_6981969 baseEnd_6981969 := by
    simpa [prefixWord, tailWord_6981969, baseEnd_6981969] using wordTrace_append hprefix tailTrace_6981969
  have hstable : (prefixWord ++ tailWord_6981969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981969).length < 2 ^ (prefixWord ++ tailWord_6981969).sum := by decide
  have hdescent : baseEnd_6981969 < baseStart_6981969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981973 : List Nat := [1, 3, 2, 2, 4, 1, 1, 2, 3, 2, 2]
def baseStart_6981973 : Nat := 118140960795 + 6981973 * 2 ^ 59
def prefixEnd_6981973 : Nat := 4983230072969 + 3 ^ 40 * 6981973 * 2
def baseEnd_6981973 : Nat := 3585108065714116732227997

theorem tailTrace_6981973 : CollatzResearch.WordTrace tailWord_6981973 prefixEnd_6981973 3585108065714116732227997 := by
  unfold tailWord_6981973
  simp only [CollatzResearch.WordTrace]
  refine ⟨254653475934511721899622573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169768983956341147933081715 254653475934511721899622573)
  ·
    refine ⟨95495053475441895712358465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254653475934511721899622573 95495053475441895712358465)
    ·
      refine ⟨71621290106581421784268849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95495053475441895712358465 71621290106581421784268849)
      ·
        refine ⟨53715967579936066338201637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71621290106581421784268849 53715967579936066338201637)
        ·
          refine ⟨10071743921238012438412807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53715967579936066338201637 10071743921238012438412807)
          ·
            refine ⟨15107615881857018657619211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10071743921238012438412807 15107615881857018657619211)
            ·
              refine ⟨22661423822785527986428817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15107615881857018657619211 22661423822785527986428817)
              ·
                refine ⟨16996067867089145989821613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22661423822785527986428817 16996067867089145989821613)
                ·
                  refine ⟨6373525450158429746183105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16996067867089145989821613 6373525450158429746183105)
                  ·
                    refine ⟨4780144087618822309637329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6373525450158429746183105 4780144087618822309637329)
                    ·
                      refine ⟨3585108065714116732227997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4780144087618822309637329 3585108065714116732227997)
                      ·
                        rfl

theorem cell23_6981973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_6981973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981973 prefixEnd_6981973 := by exact prefixLift 6981973
  have htrace : WordTrace (prefixWord ++ tailWord_6981973) baseStart_6981973 baseEnd_6981973 := by
    simpa [prefixWord, tailWord_6981973, baseEnd_6981973] using wordTrace_append hprefix tailTrace_6981973
  have hstable : (prefixWord ++ tailWord_6981973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981973).length < 2 ^ (prefixWord ++ tailWord_6981973).sum := by decide
  have hdescent : baseEnd_6981973 < baseStart_6981973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981989 : List Nat := [1, 3, 1, 3, 1, 3, 2, 2, 1, 3, 3]
def baseStart_6981989 : Nat := 118140960795 + 6981989 * 2 ^ 59
def prefixEnd_6981989 : Nat := 4983230072969 + 3 ^ 40 * 6981989 * 2
def baseEnd_6981989 : Nat := 3585116281404588669627923

theorem tailTrace_6981989 : CollatzResearch.WordTrace tailWord_6981989 prefixEnd_6981989 3585116281404588669627923 := by
  unfold tailWord_6981989
  simp only [CollatzResearch.WordTrace]
  refine ⟨254654059502453756632205021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169769373001635837754803347 254654059502453756632205021)
  ·
    refine ⟨95495272313420158737076883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254654059502453756632205021 95495272313420158737076883)
    ·
      refine ⟨143242908470130238105615325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95495272313420158737076883 143242908470130238105615325)
      ·
        refine ⟨53716090676298839289605747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143242908470130238105615325 53716090676298839289605747)
        ·
          refine ⟨80574136014448258934408621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53716090676298839289605747 80574136014448258934408621)
          ·
            refine ⟨30215301005418097100403233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80574136014448258934408621 30215301005418097100403233)
            ·
              refine ⟨22661475754063572825302425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30215301005418097100403233 22661475754063572825302425)
              ·
                refine ⟨16996106815547679618976819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22661475754063572825302425 16996106815547679618976819)
                ·
                  refine ⟨25494160223321519428465229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16996106815547679618976819 25494160223321519428465229)
                  ·
                    refine ⟨9560310083745569785674461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25494160223321519428465229 9560310083745569785674461)
                    ·
                      refine ⟨3585116281404588669627923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9560310083745569785674461 3585116281404588669627923)
                      ·
                        rfl

theorem cell23_6981989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_6981989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981989 prefixEnd_6981989 := by exact prefixLift 6981989
  have htrace : WordTrace (prefixWord ++ tailWord_6981989) baseStart_6981989 baseEnd_6981989 := by
    simpa [prefixWord, tailWord_6981989, baseEnd_6981989] using wordTrace_append hprefix tailTrace_6981989
  have hstable : (prefixWord ++ tailWord_6981989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981989).length < 2 ^ (prefixWord ++ tailWord_6981989).sum := by decide
  have hdescent : baseEnd_6981989 < baseStart_6981989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6981999 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 5, 3, 2]
def baseStart_6981999 : Nat := 118140960795 + 6981999 * 2 ^ 59
def prefixEnd_6981999 : Nat := 4983230072969 + 3 ^ 40 * 6981999 * 2
def baseEnd_6981999 : Nat := 3585121416211133630502877

theorem tailTrace_6981999 : CollatzResearch.WordTrace tailWord_6981999 prefixEnd_6981999 3585121416211133630502877 := by
  unfold tailWord_6981999
  simp only [CollatzResearch.WordTrace]
  refine ⟨254654424232417528340069051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169769616154945018893379367 254654424232417528340069051)
  ·
    refine ⟨381981636348626292510103577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254654424232417528340069051 381981636348626292510103577)
    ·
      refine ⟨286486227261469719382577683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381981636348626292510103577 286486227261469719382577683)
      ·
        refine ⟨429729340892204579073866525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286486227261469719382577683 429729340892204579073866525)
        ·
          refine ⟨161148502834576717152699947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 429729340892204579073866525 161148502834576717152699947)
          ·
            refine ⟨241722754251865075729049921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161148502834576717152699947 241722754251865075729049921)
            ·
              refine ⟨181292065688898806796787441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241722754251865075729049921 181292065688898806796787441)
              ·
                refine ⟨135969049266674105097590581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181292065688898806796787441 135969049266674105097590581)
                ·
                  refine ⟨12747098368750697352899117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135969049266674105097590581 12747098368750697352899117)
                  ·
                    refine ⟨4780161888281511507337169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12747098368750697352899117 4780161888281511507337169)
                    ·
                      refine ⟨3585121416211133630502877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4780161888281511507337169 3585121416211133630502877)
                      ·
                        rfl

theorem cell23_6981999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 3, 2].length) (baseStart_6981999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6981999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6981999 prefixEnd_6981999 := by exact prefixLift 6981999
  have htrace : WordTrace (prefixWord ++ tailWord_6981999) baseStart_6981999 baseEnd_6981999 := by
    simpa [prefixWord, tailWord_6981999, baseEnd_6981999] using wordTrace_append hprefix tailTrace_6981999
  have hstable : (prefixWord ++ tailWord_6981999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6981999).length < 2 ^ (prefixWord ++ tailWord_6981999).sum := by decide
  have hdescent : baseEnd_6981999 < baseStart_6981999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6981999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982012 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 2, 3, 4]
def baseStart_6982012 : Nat := 118140960795 + 6982012 * 2 ^ 59
def prefixEnd_6982012 : Nat := 4983230072969 + 3 ^ 40 * 6982012 * 2
def baseEnd_6982012 : Nat := 3585128091459642079640317

theorem tailTrace_6982012 : CollatzResearch.WordTrace tailWord_6982012 prefixEnd_6982012 3585128091459642079640317 := by
  unfold tailWord_6982012
  simp only [CollatzResearch.WordTrace]
  refine ⟨127327449190685215780146145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169769932254246954373528193 127327449190685215780146145)
  ·
    refine ⟨95495586893013911835109609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127327449190685215780146145 95495586893013911835109609)
    ·
      refine ⟨71621690169760433876332207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95495586893013911835109609 71621690169760433876332207)
      ·
        refine ⟨107432535254640650814498311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71621690169760433876332207 107432535254640650814498311)
        ·
          refine ⟨161148802881960976221747467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107432535254640650814498311 161148802881960976221747467)
          ·
            refine ⟨241723204322941464332621201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161148802881960976221747467 241723204322941464332621201)
            ·
              refine ⟨181292403242206098249465901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241723204322941464332621201 181292403242206098249465901)
              ·
                refine ⟨67984651215827286843549713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181292403242206098249465901 67984651215827286843549713)
                ·
                  refine ⟨50988488411870465132662285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67984651215827286843549713 50988488411870465132662285)
                  ·
                    refine ⟨19120683154451424424748357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50988488411870465132662285 19120683154451424424748357)
                    ·
                      refine ⟨3585128091459642079640317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19120683154451424424748357 3585128091459642079640317)
                      ·
                        rfl

theorem cell23_6982012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_6982012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982012 prefixEnd_6982012 := by exact prefixLift 6982012
  have htrace : WordTrace (prefixWord ++ tailWord_6982012) baseStart_6982012 baseEnd_6982012 := by
    simpa [prefixWord, tailWord_6982012, baseEnd_6982012] using wordTrace_append hprefix tailTrace_6982012
  have hstable : (prefixWord ++ tailWord_6982012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982012).length < 2 ^ (prefixWord ++ tailWord_6982012).sum := by decide
  have hdescent : baseEnd_6982012 < baseStart_6982012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982023 : List Nat := [1, 1, 4, 2, 2, 1, 5, 1, 2, 1, 3]
def baseStart_6982023 : Nat := 118140960795 + 6982023 * 2 ^ 59
def prefixEnd_6982023 : Nat := 4983230072969 + 3 ^ 40 * 6982023 * 2
def baseEnd_6982023 : Nat := 3585133739746841536602767

theorem tailTrace_6982023 : CollatzResearch.WordTrace tailWord_6982023 prefixEnd_6982023 3585133739746841536602767 := by
  unfold tailWord_6982023
  simp only [CollatzResearch.WordTrace]
  refine ⟨254655299584330580438942723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169770199722887053625961815 254655299584330580438942723)
  ·
    refine ⟨381982949376495870658414085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254655299584330580438942723 381982949376495870658414085)
    ·
      refine ⟨71621803008092975748452641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 381982949376495870658414085 71621803008092975748452641)
      ·
        refine ⟨53716352256069731811339481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71621803008092975748452641 53716352256069731811339481)
        ·
          refine ⟨40287264192052298858504611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53716352256069731811339481 40287264192052298858504611)
          ·
            refine ⟨60430896288078448287756917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40287264192052298858504611 60430896288078448287756917)
            ·
              refine ⟨5665396527007354526977211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60430896288078448287756917 5665396527007354526977211)
              ·
                refine ⟨8498094790511031790465817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5665396527007354526977211 8498094790511031790465817)
                ·
                  refine ⟨6373571092883273842849363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8498094790511031790465817 6373571092883273842849363)
                  ·
                    refine ⟨9560356639324910764274045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6373571092883273842849363 9560356639324910764274045)
                    ·
                      refine ⟨3585133739746841536602767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9560356639324910764274045 3585133739746841536602767)
                      ·
                        rfl

theorem cell23_6982023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_6982023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982023 prefixEnd_6982023 := by exact prefixLift 6982023
  have htrace : WordTrace (prefixWord ++ tailWord_6982023) baseStart_6982023 baseEnd_6982023 := by
    simpa [prefixWord, tailWord_6982023, baseEnd_6982023] using wordTrace_append hprefix tailTrace_6982023
  have hstable : (prefixWord ++ tailWord_6982023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982023).length < 2 ^ (prefixWord ++ tailWord_6982023).sum := by decide
  have hdescent : baseEnd_6982023 < baseStart_6982023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982052 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 9]
def baseStart_6982052 : Nat := 118140960795 + 6982052 * 2 ^ 59
def prefixEnd_6982052 : Nat := 4983230072969 + 3 ^ 40 * 6982052 * 2
def baseEnd_6982052 : Nat := 398349847853980213682237

theorem tailTrace_6982052 : CollatzResearch.WordTrace tailWord_6982052 prefixEnd_6982052 398349847853980213682237 := by
  unfold tailWord_6982052
  simp only [CollatzResearch.WordTrace]
  refine ⟨127328178650612759195874205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169770904867483678927832273 127328178650612759195874205)
  ·
    refine ⟨47748066993979784698452827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127328178650612759195874205 47748066993979784698452827)
    ·
      refine ⟨71622100490969677047679241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47748066993979784698452827 71622100490969677047679241)
      ·
        refine ⟨53716575368227257785759431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71622100490969677047679241 53716575368227257785759431)
        ·
          refine ⟨80574863052340886678639147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53716575368227257785759431 80574863052340886678639147)
          ·
            refine ⟨120862294578511330017958721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80574863052340886678639147 120862294578511330017958721)
            ·
              refine ⟨90646720933883497513469041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120862294578511330017958721 90646720933883497513469041)
              ·
                refine ⟨67985040700412623135101781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90646720933883497513469041 67985040700412623135101781)
                ·
                  refine ⟨398349847853980213682237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67985040700412623135101781 398349847853980213682237)
                  ·
                    rfl

theorem cell23_6982052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_6982052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982052 prefixEnd_6982052 := by exact prefixLift 6982052
  have htrace : WordTrace (prefixWord ++ tailWord_6982052) baseStart_6982052 baseEnd_6982052 := by
    simpa [prefixWord, tailWord_6982052, baseEnd_6982052] using wordTrace_append hprefix tailTrace_6982052
  have hstable : (prefixWord ++ tailWord_6982052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982052).length < 2 ^ (prefixWord ++ tailWord_6982052).sum := by decide
  have hdescent : baseEnd_6982052 < baseStart_6982052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982109 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_6982109 : Nat := 118140960795 + 6982109 * 2 ^ 59
def prefixEnd_6982109 : Nat := 4983230072969 + 3 ^ 40 * 6982109 * 2
def baseEnd_6982109 : Nat := 3585177899083128200127371

theorem tailTrace_6982109 : CollatzResearch.WordTrace tailWord_6982109 prefixEnd_6982109 3585177899083128200127371 := by
  unfold tailWord_6982109
  simp only [CollatzResearch.WordTrace]
  refine ⟨254658436262019017126573381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169772290841346011417715587 254658436262019017126573381)
  ·
    refine ⟨47748456799128565711232509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254658436262019017126573381 47748456799128565711232509)
    ·
      refine ⟨17905671299673212141712191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47748456799128565711232509 17905671299673212141712191)
      ·
        refine ⟨26858506949509818212568287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17905671299673212141712191 26858506949509818212568287)
        ·
          refine ⟨40287760424264727318852431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26858506949509818212568287 40287760424264727318852431)
          ·
            refine ⟨60431640636397090978278647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40287760424264727318852431 60431640636397090978278647)
            ·
              refine ⟨90647460954595636467417971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60431640636397090978278647 90647460954595636467417971)
              ·
                refine ⟨135971191431893454701126957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90647460954595636467417971 135971191431893454701126957)
                ·
                  refine ⟨50989196786960045512922609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135971191431893454701126957 50989196786960045512922609)
                  ·
                    refine ⟨38241897590220034134691957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50989196786960045512922609 38241897590220034134691957)
                    ·
                      refine ⟨3585177899083128200127371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38241897590220034134691957 3585177899083128200127371)
                      ·
                        rfl

theorem cell23_6982109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_6982109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982109 prefixEnd_6982109 := by exact prefixLift 6982109
  have htrace : WordTrace (prefixWord ++ tailWord_6982109) baseStart_6982109 baseEnd_6982109 := by
    simpa [prefixWord, tailWord_6982109, baseEnd_6982109] using wordTrace_append hprefix tailTrace_6982109
  have hstable : (prefixWord ++ tailWord_6982109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982109).length < 2 ^ (prefixWord ++ tailWord_6982109).sum := by decide
  have hdescent : baseEnd_6982109 < baseStart_6982109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982114 : List Nat := [3, 3, 3, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_6982114 : Nat := 118140960795 + 6982114 * 2 ^ 59
def prefixEnd_6982114 : Nat := 4983230072969 + 3 ^ 40 * 6982114 * 2
def baseEnd_6982114 : Nat := 3585180466486400680564849

theorem tailTrace_6982114 : CollatzResearch.WordTrace tailWord_6982114 prefixEnd_6982114 3585180466486400680564849 := by
  unfold tailWord_6982114
  simp only [CollatzResearch.WordTrace]
  refine ⟨63664654656750225745126349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169772412418000601987003597 63664654656750225745126349)
  ·
    refine ⟨23874245496281334654422381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63664654656750225745126349 23874245496281334654422381)
    ·
      refine ⟨8952842061105500495408393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23874245496281334654422381 8952842061105500495408393)
      ·
        refine ⟨6714631545829125371556295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8952842061105500495408393 6714631545829125371556295)
        ·
          refine ⟨10071947318743688057334443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6714631545829125371556295 10071947318743688057334443)
          ·
            refine ⟨15107920978115532086001665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10071947318743688057334443 15107920978115532086001665)
            ·
              refine ⟨11330940733586649064501249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15107920978115532086001665 11330940733586649064501249)
              ·
                refine ⟨8498205550189986798375937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11330940733586649064501249 8498205550189986798375937)
                ·
                  refine ⟨6373654162642490098781953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8498205550189986798375937 6373654162642490098781953)
                  ·
                    refine ⟨4780240621981867574086465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6373654162642490098781953 4780240621981867574086465)
                    ·
                      refine ⟨3585180466486400680564849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4780240621981867574086465 3585180466486400680564849)
                      ·
                        rfl

theorem cell23_6982114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_6982114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982114 prefixEnd_6982114 := by exact prefixLift 6982114
  have htrace : WordTrace (prefixWord ++ tailWord_6982114) baseStart_6982114 baseEnd_6982114 := by
    simpa [prefixWord, tailWord_6982114, baseEnd_6982114] using wordTrace_append hprefix tailTrace_6982114
  have hstable : (prefixWord ++ tailWord_6982114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982114).length < 2 ^ (prefixWord ++ tailWord_6982114).sum := by decide
  have hdescent : baseEnd_6982114 < baseStart_6982114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982136 : List Nat := [2, 1, 2, 1, 1, 4, 3, 1, 2, 4, 2]
def baseStart_6982136 : Nat := 118140960795 + 6982136 * 2 ^ 59
def prefixEnd_6982136 : Nat := 4983230072969 + 3 ^ 40 * 6982136 * 2
def baseEnd_6982136 : Nat := 3585191763060799594489747

theorem tailTrace_6982136 : CollatzResearch.WordTrace tailWord_6982136 prefixEnd_6982136 3585191763060799594489747 := by
  unfold tailWord_6982136
  simp only [CollatzResearch.WordTrace]
  refine ⟨127329710516460600368903131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169772947355280800491870841 127329710516460600368903131)
  ·
    refine ⟨190994565774690900553354697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127329710516460600368903131 190994565774690900553354697)
    ·
      refine ⟨143245924331018175415016023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190994565774690900553354697 143245924331018175415016023)
      ·
        refine ⟨214868886496527263122524035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143245924331018175415016023 214868886496527263122524035)
        ·
          refine ⟨322303329744790894683786053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214868886496527263122524035 322303329744790894683786053)
          ·
            refine ⟨60431874327148292753209885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 322303329744790894683786053 60431874327148292753209885)
            ·
              refine ⟨22661952872680609782453707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60431874327148292753209885 22661952872680609782453707)
              ·
                refine ⟨33992929309020914673680561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22661952872680609782453707 33992929309020914673680561)
                ·
                  refine ⟨25494696981765686005260421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33992929309020914673680561 25494696981765686005260421)
                  ·
                    refine ⟨4780255684081066125986329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25494696981765686005260421 4780255684081066125986329)
                    ·
                      refine ⟨3585191763060799594489747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4780255684081066125986329 3585191763060799594489747)
                      ·
                        rfl

theorem cell23_6982136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 2, 4, 2].length) (baseStart_6982136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982136 prefixEnd_6982136 := by exact prefixLift 6982136
  have htrace : WordTrace (prefixWord ++ tailWord_6982136) baseStart_6982136 baseEnd_6982136 := by
    simpa [prefixWord, tailWord_6982136, baseEnd_6982136] using wordTrace_append hprefix tailTrace_6982136
  have hstable : (prefixWord ++ tailWord_6982136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982136).length < 2 ^ (prefixWord ++ tailWord_6982136).sum := by decide
  have hdescent : baseEnd_6982136 < baseStart_6982136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982150 : List Nat := [6, 2, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_6982150 : Nat := 118140960795 + 6982150 * 2 ^ 59
def prefixEnd_6982150 : Nat := 4983230072969 + 3 ^ 40 * 6982150 * 2
def baseEnd_6982150 : Nat := 1195066317263320846571561

theorem tailTrace_6982150 : CollatzResearch.WordTrace tailWord_6982150 prefixEnd_6982150 1195066317263320846571561 := by
  unfold tailWord_6982150
  simp only [CollatzResearch.WordTrace]
  refine ⟨7958122864214702535275497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 169773287769913654085877269 7958122864214702535275497)
  ·
    refine ⟨5968592148161026901456623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7958122864214702535275497 5968592148161026901456623)
    ·
      refine ⟨8952888222241540352184935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5968592148161026901456623 8952888222241540352184935)
      ·
        refine ⟨13429332333362310528277403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8952888222241540352184935 13429332333362310528277403)
        ·
          refine ⟨20143998500043465792416105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13429332333362310528277403 20143998500043465792416105)
          ·
            refine ⟨15107998875032599344312079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20143998500043465792416105 15107998875032599344312079)
            ·
              refine ⟨22661998312548899016468119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15107998875032599344312079 22661998312548899016468119)
              ·
                refine ⟨33992997468823348524702179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22661998312548899016468119 33992997468823348524702179)
                ·
                  refine ⟨50989496203235022787053269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33992997468823348524702179 50989496203235022787053269)
                  ·
                    refine ⟨1195066317263320846571561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50989496203235022787053269 1195066317263320846571561)
                    ·
                      rfl

theorem cell23_6982150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_6982150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982150 prefixEnd_6982150 := by exact prefixLift 6982150
  have htrace : WordTrace (prefixWord ++ tailWord_6982150) baseStart_6982150 baseEnd_6982150 := by
    simpa [prefixWord, tailWord_6982150, baseEnd_6982150] using wordTrace_append hprefix tailTrace_6982150
  have hstable : (prefixWord ++ tailWord_6982150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982150).length < 2 ^ (prefixWord ++ tailWord_6982150).sum := by decide
  have hdescent : baseEnd_6982150 < baseStart_6982150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982156 : List Nat := [2, 2, 1, 2, 4, 2, 1, 1, 1, 4, 3]
def baseStart_6982156 : Nat := 118140960795 + 6982156 * 2 ^ 59
def prefixEnd_6982156 : Nat := 4983230072969 + 3 ^ 40 * 6982156 * 2
def baseEnd_6982156 : Nat := 3585202032673889516239655

theorem tailTrace_6982156 : CollatzResearch.WordTrace tailWord_6982156 prefixEnd_6982156 3585202032673889516239655 := by
  unfold tailWord_6982156
  simp only [CollatzResearch.WordTrace]
  refine ⟨127330075246424372076767161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169773433661899162769022881 127330075246424372076767161)
  ·
    refine ⟨95497556434818279057575371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127330075246424372076767161 95497556434818279057575371)
    ·
      refine ⟨143246334652227418586363057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95497556434818279057575371 143246334652227418586363057)
      ·
        refine ⟨107434750989170563939772293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143246334652227418586363057 107434750989170563939772293)
        ·
          refine ⟨20144015810469480738707305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107434750989170563939772293 20144015810469480738707305)
          ·
            refine ⟨15108011857852110554030479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20144015810469480738707305 15108011857852110554030479)
            ·
              refine ⟨22662017786778165831045719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15108011857852110554030479 22662017786778165831045719)
              ·
                refine ⟨33993026680167248746568579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22662017786778165831045719 33993026680167248746568579)
                ·
                  refine ⟨50989540020250873119852869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33993026680167248746568579 50989540020250873119852869)
                  ·
                    refine ⟨9560538753797038709972413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50989540020250873119852869 9560538753797038709972413)
                    ·
                      refine ⟨3585202032673889516239655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9560538753797038709972413 3585202032673889516239655)
                      ·
                        rfl

theorem cell23_6982156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_6982156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982156 prefixEnd_6982156 := by exact prefixLift 6982156
  have htrace : WordTrace (prefixWord ++ tailWord_6982156) baseStart_6982156 baseEnd_6982156 := by
    simpa [prefixWord, tailWord_6982156, baseEnd_6982156] using wordTrace_append hprefix tailTrace_6982156
  have hstable : (prefixWord ++ tailWord_6982156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982156).length < 2 ^ (prefixWord ++ tailWord_6982156).sum := by decide
  have hdescent : baseEnd_6982156 < baseStart_6982156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982163 : List Nat := [1, 1, 1, 2, 1, 5, 4, 3, 1, 4]
def baseStart_6982163 : Nat := 118140960795 + 6982163 * 2 ^ 59
def prefixEnd_6982163 : Nat := 4983230072969 + 3 ^ 40 * 6982163 * 2
def baseEnd_6982163 : Nat := 1195068542346156996284041

theorem tailTrace_6982163 : CollatzResearch.WordTrace tailWord_6982163 prefixEnd_6982163 1195068542346156996284041 := by
  unfold tailWord_6982163
  simp only [CollatzResearch.WordTrace]
  refine ⟨254660405803823384349039143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169773603869215589566026095 254660405803823384349039143)
  ·
    refine ⟨381990608705735076523558715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254660405803823384349039143 381990608705735076523558715)
    ·
      refine ⟨572985913058602614785338073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381990608705735076523558715 572985913058602614785338073)
      ·
        refine ⟨429739434793951961089003555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 572985913058602614785338073 429739434793951961089003555)
        ·
          refine ⟨644609152190927941633505333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429739434793951961089003555 644609152190927941633505333)
          ·
            refine ⟨60432108017899494528141125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 644609152190927941633505333 60432108017899494528141125)
            ·
              refine ⟨11331020253356155224026461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60432108017899494528141125 11331020253356155224026461)
              ·
                refine ⟨4249132595008558209009923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11331020253356155224026461 4249132595008558209009923)
                ·
                  refine ⟨6373698892512837313514885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4249132595008558209009923 6373698892512837313514885)
                  ·
                    refine ⟨1195068542346156996284041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6373698892512837313514885 1195068542346156996284041)
                    ·
                      rfl

theorem cell23_6982163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3, 1, 4].length) (baseStart_6982163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982163 prefixEnd_6982163 := by exact prefixLift 6982163
  have htrace : WordTrace (prefixWord ++ tailWord_6982163) baseStart_6982163 baseEnd_6982163 := by
    simpa [prefixWord, tailWord_6982163, baseEnd_6982163] using wordTrace_append hprefix tailTrace_6982163
  have hstable : (prefixWord ++ tailWord_6982163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982163).length < 2 ^ (prefixWord ++ tailWord_6982163).sum := by decide
  have hdescent : baseEnd_6982163 < baseStart_6982163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982176 : List Nat := [2, 1, 1, 6, 2, 1, 1, 1, 8]
def baseStart_6982176 : Nat := 118140960795 + 6982176 * 2 ^ 59
def prefixEnd_6982176 : Nat := 4983230072969 + 3 ^ 40 * 6982176 * 2
def baseEnd_6982176 : Nat := 398356922476331048665507

theorem tailTrace_6982176 : CollatzResearch.WordTrace tailWord_6982176 prefixEnd_6982176 398356922476331048665507 := by
  unfold tailWord_6982176
  simp only [CollatzResearch.WordTrace]
  refine ⟨127330439976388143784631191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169773919968517525046174921 127330439976388143784631191)
  ·
    refine ⟨190995659964582215676946787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127330439976388143784631191 190995659964582215676946787)
    ·
      refine ⟨286493489946873323515420181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190995659964582215676946787 286493489946873323515420181)
      ·
        refine ⟨13429382341259687039785321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 286493489946873323515420181 13429382341259687039785321)
        ·
          refine ⟨10072036755944765279838991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13429382341259687039785321 10072036755944765279838991)
          ·
            refine ⟨15108055133917147919758487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10072036755944765279838991 15108055133917147919758487)
            ·
              refine ⟨22662082700875721879637731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15108055133917147919758487 22662082700875721879637731)
              ·
                refine ⟨33993124051313582819456597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22662082700875721879637731 33993124051313582819456597)
                ·
                  refine ⟨398356922476331048665507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33993124051313582819456597 398356922476331048665507)
                  ·
                    rfl

theorem cell23_6982176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 8].length) (baseStart_6982176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982176 prefixEnd_6982176 := by exact prefixLift 6982176
  have htrace : WordTrace (prefixWord ++ tailWord_6982176) baseStart_6982176 baseEnd_6982176 := by
    simpa [prefixWord, tailWord_6982176, baseEnd_6982176] using wordTrace_append hprefix tailTrace_6982176
  have hstable : (prefixWord ++ tailWord_6982176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982176).length < 2 ^ (prefixWord ++ tailWord_6982176).sum := by decide
  have hdescent : baseEnd_6982176 < baseStart_6982176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982179 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 6]
def baseStart_6982179 : Nat := 118140960795 + 6982179 * 2 ^ 59
def prefixEnd_6982179 : Nat := 4983230072969 + 3 ^ 40 * 6982179 * 2
def baseEnd_6982179 : Nat := 3585213842728942926252049

theorem tailTrace_6982179 : CollatzResearch.WordTrace tailWord_6982179 prefixEnd_6982179 3585213842728942926252049 := by
  unfold tailWord_6982179
  simp only [CollatzResearch.WordTrace]
  refine ⟨254660989371765419081621591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169773992914510279387747727 254660989371765419081621591)
  ·
    refine ⟨381991484057648128622432387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254660989371765419081621591 381991484057648128622432387)
    ·
      refine ⟨572987226086472192933648581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381991484057648128622432387 572987226086472192933648581)
      ·
        refine ⟨107435104891213536175059109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 572987226086472192933648581 107435104891213536175059109)
        ·
          refine ⟨20144082167102538032823583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107435104891213536175059109 20144082167102538032823583)
          ·
            refine ⟨30216123250653807049235375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20144082167102538032823583 30216123250653807049235375)
            ·
              refine ⟨45324184875980710573853063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30216123250653807049235375 45324184875980710573853063)
              ·
                refine ⟨67986277313971065860779595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45324184875980710573853063 67986277313971065860779595)
                ·
                  refine ⟨101979415970956598791169393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67986277313971065860779595 101979415970956598791169393)
                  ·
                    refine ⟨76484561978217449093377045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101979415970956598791169393 76484561978217449093377045)
                    ·
                      refine ⟨3585213842728942926252049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76484561978217449093377045 3585213842728942926252049)
                      ·
                        rfl

theorem cell23_6982179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_6982179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982179 prefixEnd_6982179 := by exact prefixLift 6982179
  have htrace : WordTrace (prefixWord ++ tailWord_6982179) baseStart_6982179 baseEnd_6982179 := by
    simpa [prefixWord, tailWord_6982179, baseEnd_6982179] using wordTrace_append hprefix tailTrace_6982179
  have hstable : (prefixWord ++ tailWord_6982179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982179).length < 2 ^ (prefixWord ++ tailWord_6982179).sum := by decide
  have hdescent : baseEnd_6982179 < baseStart_6982179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982180 : List Nat := [2, 3, 1, 5, 1, 1, 2, 1, 3, 4]
def baseStart_6982180 : Nat := 118140960795 + 6982180 * 2 ^ 59
def prefixEnd_6982180 : Nat := 4983230072969 + 3 ^ 40 * 6982180 * 2
def baseEnd_6982180 : Nat := 1195071452069865807446515

theorem tailTrace_6982180 : CollatzResearch.WordTrace tailWord_6982180 prefixEnd_6982180 1195071452069865807446515 := by
  unfold tailWord_6982180
  simp only [CollatzResearch.WordTrace]
  refine ⟨127330512922380898126203997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169774017229841197501605329 127330512922380898126203997)
  ·
    refine ⟨47748942345892836797326499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127330512922380898126203997 47748942345892836797326499)
    ·
      refine ⟨71623413518839255195989749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47748942345892836797326499 71623413518839255195989749)
      ·
        refine ⟨6714695017391180174624039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71623413518839255195989749 6714695017391180174624039)
        ·
          refine ⟨10072042526086770261936059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6714695017391180174624039 10072042526086770261936059)
          ·
            refine ⟨15108063789130155392904089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10072042526086770261936059 15108063789130155392904089)
            ·
              refine ⟨11331047841847616544678067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15108063789130155392904089 11331047841847616544678067)
              ·
                refine ⟨16996571762771424817017101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11331047841847616544678067 16996571762771424817017101)
                ·
                  refine ⟨6373714411039284306381413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16996571762771424817017101 6373714411039284306381413)
                  ·
                    refine ⟨1195071452069865807446515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6373714411039284306381413 1195071452069865807446515)
                    ·
                      rfl

theorem cell23_6982180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_6982180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982180 prefixEnd_6982180 := by exact prefixLift 6982180
  have htrace : WordTrace (prefixWord ++ tailWord_6982180) baseStart_6982180 baseEnd_6982180 := by
    simpa [prefixWord, tailWord_6982180, baseEnd_6982180] using wordTrace_append hprefix tailTrace_6982180
  have hstable : (prefixWord ++ tailWord_6982180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982180).length < 2 ^ (prefixWord ++ tailWord_6982180).sum := by decide
  have hdescent : baseEnd_6982180 < baseStart_6982180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982214 : List Nat := [6, 1, 1, 1, 2, 3, 1, 3, 1, 4]
def baseStart_6982214 : Nat := 118140960795 + 6982214 * 2 ^ 59
def prefixEnd_6982214 : Nat := 4983230072969 + 3 ^ 40 * 6982214 * 2
def baseEnd_6982214 : Nat := 1195077271517283429771463

theorem tailTrace_6982214 : CollatzResearch.WordTrace tailWord_6982214 prefixEnd_6982214 1195077271517283429771463 := by
  unfold tailWord_6982214
  simp only [CollatzResearch.WordTrace]
  refine ⟨7958195810207456876848303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 169774843951092413372763797 7958195810207456876848303)
  ·
    refine ⟨11937293715311185315272455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7958195810207456876848303 11937293715311185315272455)
    ·
      refine ⟨17905940572966777972908683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11937293715311185315272455 17905940572966777972908683)
      ·
        refine ⟨26858910859450166959363025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17905940572966777972908683 26858910859450166959363025)
        ·
          refine ⟨20144183144587625219522269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26858910859450166959363025 20144183144587625219522269)
          ·
            refine ⟨7554068679220359457320851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20144183144587625219522269 7554068679220359457320851)
            ·
              refine ⟨11331103018830539185981277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7554068679220359457320851 11331103018830539185981277)
              ·
                refine ⟨4249163632061452194742979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11331103018830539185981277 4249163632061452194742979)
                ·
                  refine ⟨6373745448092178292114469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4249163632061452194742979 6373745448092178292114469)
                  ·
                    refine ⟨1195077271517283429771463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6373745448092178292114469 1195077271517283429771463)
                    ·
                      rfl

theorem cell23_6982214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_6982214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982214 prefixEnd_6982214 := by exact prefixLift 6982214
  have htrace : WordTrace (prefixWord ++ tailWord_6982214) baseStart_6982214 baseEnd_6982214 := by
    simpa [prefixWord, tailWord_6982214, baseEnd_6982214] using wordTrace_append hprefix tailTrace_6982214
  have hstable : (prefixWord ++ tailWord_6982214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982214).length < 2 ^ (prefixWord ++ tailWord_6982214).sum := by decide
  have hdescent : baseEnd_6982214 < baseStart_6982214 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982219 : List Nat := [1, 1, 1, 1, 3, 1, 4, 4, 1, 6]
def baseStart_6982219 : Nat := 118140960795 + 6982219 * 2 ^ 59
def prefixEnd_6982219 : Nat := 4983230072969 + 3 ^ 40 * 6982219 * 2
def baseEnd_6982219 : Nat := 1195078127318374256583955

theorem tailTrace_6982219 : CollatzResearch.WordTrace tailWord_6982219 prefixEnd_6982219 1195078127318374256583955 := by
  unfold tailWord_6982219
  simp only [CollatzResearch.WordTrace]
  refine ⟨254662448291620505913077711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169774965527747003942051807 254662448291620505913077711)
  ·
    refine ⟨381993672437430758869616567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254662448291620505913077711 381993672437430758869616567)
    ·
      refine ⟨572990508656146138304424851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381993672437430758869616567 572990508656146138304424851)
      ·
        refine ⟨859485762984219207456637277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572990508656146138304424851 859485762984219207456637277)
        ·
          refine ⟨322307161119082202796238979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 859485762984219207456637277 322307161119082202796238979)
          ·
            refine ⟨483460741678623304194358469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322307161119082202796238979 483460741678623304194358469)
            ·
              refine ⟨90648889064741869536442213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 483460741678623304194358469 90648889064741869536442213)
              ·
                refine ⟨16996666699639100538082915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90648889064741869536442213 16996666699639100538082915)
                ·
                  refine ⟨25495000049458650807124373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16996666699639100538082915 25495000049458650807124373)
                  ·
                    refine ⟨1195078127318374256583955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25495000049458650807124373 1195078127318374256583955)
                    ·
                      rfl

theorem cell23_6982219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 6].length) (baseStart_6982219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982219 prefixEnd_6982219 := by exact prefixLift 6982219
  have htrace : WordTrace (prefixWord ++ tailWord_6982219) baseStart_6982219 baseEnd_6982219 := by
    simpa [prefixWord, tailWord_6982219, baseEnd_6982219] using wordTrace_append hprefix tailTrace_6982219
  have hstable : (prefixWord ++ tailWord_6982219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982219).length < 2 ^ (prefixWord ++ tailWord_6982219).sum := by decide
  have hdescent : baseEnd_6982219 < baseStart_6982219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982263 : List Nat := [1, 1, 3, 1, 1, 3, 5, 2, 1, 2, 3]
def baseStart_6982263 : Nat := 118140960795 + 6982263 * 2 ^ 59
def prefixEnd_6982263 : Nat := 4983230072969 + 3 ^ 40 * 6982263 * 2
def baseEnd_6982263 : Nat := 3585256975103920597601663

theorem tailTrace_6982263 : CollatzResearch.WordTrace tailWord_6982263 prefixEnd_6982263 3585256975103920597601663 := by
  unfold tailWord_6982263
  simp only [CollatzResearch.WordTrace]
  refine ⟨254664053103461101427679443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169776035402307400951786295 254664053103461101427679443)
  ·
    refine ⟨381996079655191652141519165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254664053103461101427679443 381996079655191652141519165)
    ·
      refine ⟨143248529870696869553069687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 381996079655191652141519165 143248529870696869553069687)
      ·
        refine ⟨214872794806045304329604531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143248529870696869553069687 214872794806045304329604531)
        ·
          refine ⟨322309192209067956494406797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214872794806045304329604531 322309192209067956494406797)
          ·
            refine ⟨120865947078400483685402549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322309192209067956494406797 120865947078400483685402549)
            ·
              refine ⟨11331182538600045345506489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120865947078400483685402549 11331182538600045345506489)
              ·
                refine ⟨8498386903950034009129867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11331182538600045345506489 8498386903950034009129867)
                ·
                  refine ⟨12747580355925051013694801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8498386903950034009129867 12747580355925051013694801)
                  ·
                    refine ⟨9560685266943788260271101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12747580355925051013694801 9560685266943788260271101)
                    ·
                      refine ⟨3585256975103920597601663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9560685266943788260271101 3585256975103920597601663)
                      ·
                        rfl

theorem cell23_6982263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 2, 3].length) (baseStart_6982263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982263 prefixEnd_6982263 := by exact prefixLift 6982263
  have htrace : WordTrace (prefixWord ++ tailWord_6982263) baseStart_6982263 baseEnd_6982263 := by
    simpa [prefixWord, tailWord_6982263, baseEnd_6982263] using wordTrace_append hprefix tailTrace_6982263
  have hstable : (prefixWord ++ tailWord_6982263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982263).length < 2 ^ (prefixWord ++ tailWord_6982263).sum := by decide
  have hdescent : baseEnd_6982263 < baseStart_6982263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982289 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 5]
def baseStart_6982289 : Nat := 118140960795 + 6982289 * 2 ^ 59
def prefixEnd_6982289 : Nat := 4983230072969 + 3 ^ 40 * 6982289 * 2
def baseEnd_6982289 : Nat := 3585270325600937495876543

theorem tailTrace_6982289 : CollatzResearch.WordTrace tailWord_6982289 prefixEnd_6982289 3585270325600937495876543 := by
  unfold tailWord_6982289
  simp only [CollatzResearch.WordTrace]
  refine ⟨254665001401366907868125921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169776667600911271912083947 254665001401366907868125921)
  ·
    refine ⟨190998751051025180901094441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254665001401366907868125921 190998751051025180901094441)
    ·
      refine ⟨143249063288268885675820831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190998751051025180901094441 143249063288268885675820831)
      ·
        refine ⟨214873594932403328513731247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143249063288268885675820831 214873594932403328513731247)
        ·
          refine ⟨322310392398604992770596871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214873594932403328513731247 322310392398604992770596871)
          ·
            refine ⟨483465588597907489155895307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322310392398604992770596871 483465588597907489155895307)
            ·
              refine ⟨725198382896861233733842961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483465588597907489155895307 725198382896861233733842961)
              ·
                refine ⟨543898787172645925300382221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 725198382896861233733842961 543898787172645925300382221)
                ·
                  refine ⟨203962045189742221987643333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 543898787172645925300382221 203962045189742221987643333)
                  ·
                    refine ⟨38242883473076666622683125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 203962045189742221987643333 38242883473076666622683125)
                    ·
                      refine ⟨3585270325600937495876543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38242883473076666622683125 3585270325600937495876543)
                      ·
                        rfl

theorem cell23_6982289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_6982289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982289 prefixEnd_6982289 := by exact prefixLift 6982289
  have htrace : WordTrace (prefixWord ++ tailWord_6982289) baseStart_6982289 baseEnd_6982289 := by
    simpa [prefixWord, tailWord_6982289, baseEnd_6982289] using wordTrace_append hprefix tailTrace_6982289
  have hstable : (prefixWord ++ tailWord_6982289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982289).length < 2 ^ (prefixWord ++ tailWord_6982289).sum := by decide
  have hdescent : baseEnd_6982289 < baseStart_6982289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982407 : List Nat := [1, 1, 4, 4, 1, 2, 3, 2, 5]
def baseStart_6982407 : Nat := 118140960795 + 6982407 * 2 ^ 59
def prefixEnd_6982407 : Nat := 4983230072969 + 3 ^ 40 * 6982407 * 2
def baseEnd_6982407 : Nat := 398370101813129781577889

theorem tailTrace_6982407 : CollatzResearch.WordTrace tailWord_6982407 prefixEnd_6982407 398370101813129781577889 := by
  unfold tailWord_6982407
  simp only [CollatzResearch.WordTrace]
  refine ⟨254669305214939414020921475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169779536809959609347280983 254669305214939414020921475)
  ·
    refine ⟨382003957822409121031382213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254669305214939414020921475 382003957822409121031382213)
    ·
      refine ⟨71625742091701710193384165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 382003957822409121031382213 71625742091701710193384165)
      ·
        refine ⟨13429826642194070661259531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71625742091701710193384165 13429826642194070661259531)
        ·
          refine ⟨20144739963291105991889297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13429826642194070661259531 20144739963291105991889297)
          ·
            refine ⟨15108554972468329493916973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20144739963291105991889297 15108554972468329493916973)
            ·
              refine ⟨5665708114675623560218865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15108554972468329493916973 5665708114675623560218865)
              ·
                refine ⟨4249281086006717670164149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5665708114675623560218865 4249281086006717670164149)
                ·
                  refine ⟨398370101813129781577889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4249281086006717670164149 398370101813129781577889)
                  ·
                    rfl

theorem cell23_6982407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2, 5].length) (baseStart_6982407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982407 prefixEnd_6982407 := by exact prefixLift 6982407
  have htrace : WordTrace (prefixWord ++ tailWord_6982407) baseStart_6982407 baseEnd_6982407 := by
    simpa [prefixWord, tailWord_6982407, baseEnd_6982407] using wordTrace_append hprefix tailTrace_6982407
  have hstable : (prefixWord ++ tailWord_6982407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982407).length < 2 ^ (prefixWord ++ tailWord_6982407).sum := by decide
  have hdescent : baseEnd_6982407 < baseStart_6982407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982418 : List Nat := [3, 2, 4, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_6982418 : Nat := 118140960795 + 6982418 * 2 ^ 59
def prefixEnd_6982418 : Nat := 4983230072969 + 3 ^ 40 * 6982418 * 2
def baseEnd_6982418 : Nat := 3585336564605367491163451

theorem tailTrace_6982418 : CollatzResearch.WordTrace tailWord_6982418 prefixEnd_6982418 3585336564605367491163451 := by
  unfold tailWord_6982418
  simp only [CollatzResearch.WordTrace]
  refine ⟨63667426604474890724892977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169779804278599708599714605 63667426604474890724892977)
  ·
    refine ⟨47750569953356168043669733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63667426604474890724892977 47750569953356168043669733)
    ·
      refine ⟨8953231866254281508188075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47750569953356168043669733 8953231866254281508188075)
      ·
        refine ⟨13429847799381422262282113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8953231866254281508188075 13429847799381422262282113)
        ·
          refine ⟨10072385849536066696711585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13429847799381422262282113 10072385849536066696711585)
          ·
            refine ⟨7554289387152050022533689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10072385849536066696711585 7554289387152050022533689)
            ·
              refine ⟨5665717040364037516900267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7554289387152050022533689 5665717040364037516900267)
              ·
                refine ⟨8498575560546056275350401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5665717040364037516900267 8498575560546056275350401)
                ·
                  refine ⟨6373931670409542206512801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8498575560546056275350401 6373931670409542206512801)
                  ·
                    refine ⟨4780448752807156654884601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6373931670409542206512801 4780448752807156654884601)
                    ·
                      refine ⟨3585336564605367491163451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4780448752807156654884601 3585336564605367491163451)
                      ·
                        rfl

theorem cell23_6982418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_6982418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982418 prefixEnd_6982418 := by exact prefixLift 6982418
  have htrace : WordTrace (prefixWord ++ tailWord_6982418) baseStart_6982418 baseEnd_6982418 := by
    simpa [prefixWord, tailWord_6982418, baseEnd_6982418] using wordTrace_append hprefix tailTrace_6982418
  have hstable : (prefixWord ++ tailWord_6982418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982418).length < 2 ^ (prefixWord ++ tailWord_6982418).sum := by decide
  have hdescent : baseEnd_6982418 < baseStart_6982418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982433 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 5, 4]
def baseStart_6982433 : Nat := 118140960795 + 6982433 * 2 ^ 59
def prefixEnd_6982433 : Nat := 4983230072969 + 3 ^ 40 * 6982433 * 2
def baseEnd_6982433 : Nat := 1195114755605061644158627

theorem tailTrace_6982433 : CollatzResearch.WordTrace tailWord_6982433 prefixEnd_6982433 1195114755605061644158627 := by
  unfold tailWord_6982433
  simp only [CollatzResearch.WordTrace]
  refine ⟨254670253512845220461367953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169780169008563480307578635 254670253512845220461367953)
  ·
    refine ⟨191002690134633915346025965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254670253512845220461367953 191002690134633915346025965)
    ·
      refine ⟨71626008800487718254759737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191002690134633915346025965 71626008800487718254759737)
      ·
        refine ⟨53719506600365788691069803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71626008800487718254759737 53719506600365788691069803)
        ·
          refine ⟨80579259900548683036604705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53719506600365788691069803 80579259900548683036604705)
          ·
            refine ⟨60434444925411512277453529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80579259900548683036604705 60434444925411512277453529)
            ·
              refine ⟨45325833694058634208090147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60434444925411512277453529 45325833694058634208090147)
              ·
                refine ⟨67988750541087951312135221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45325833694058634208090147 67988750541087951312135221)
                ·
                  refine ⟨6373945363226995435512677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67988750541087951312135221 6373945363226995435512677)
                  ·
                    refine ⟨1195114755605061644158627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6373945363226995435512677 1195114755605061644158627)
                    ·
                      rfl

theorem cell23_6982433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5, 4].length) (baseStart_6982433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982433 prefixEnd_6982433 := by exact prefixLift 6982433
  have htrace : WordTrace (prefixWord ++ tailWord_6982433) baseStart_6982433 baseEnd_6982433 := by
    simpa [prefixWord, tailWord_6982433, baseEnd_6982433] using wordTrace_append hprefix tailTrace_6982433
  have hstable : (prefixWord ++ tailWord_6982433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982433).length < 2 ^ (prefixWord ++ tailWord_6982433).sum := by decide
  have hdescent : baseEnd_6982433 < baseStart_6982433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982440 : List Nat := [2, 1, 5, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_6982440 : Nat := 118140960795 + 6982440 * 2 ^ 59
def prefixEnd_6982440 : Nat := 4983230072969 + 3 ^ 40 * 6982440 * 2
def baseEnd_6982440 : Nat := 3585347861179766405088349

theorem tailTrace_6982440 : CollatzResearch.WordTrace tailWord_6982440 prefixEnd_6982440 3585347861179766405088349 := by
  unfold tailWord_6982440
  simp only [CollatzResearch.WordTrace]
  refine ⟨127335254411909930328436387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169780339215879907104581849 127335254411909930328436387)
  ·
    refine ⟨191002881617864895492654581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127335254411909930328436387 191002881617864895492654581)
    ·
      refine ⟨17906520151674833952436367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191002881617864895492654581 17906520151674833952436367)
      ·
        refine ⟨26859780227512250928654551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17906520151674833952436367 26859780227512250928654551)
        ·
          refine ⟨40289670341268376392981827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26859780227512250928654551 40289670341268376392981827)
          ·
            refine ⟨60434505511902564589472741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40289670341268376392981827 60434505511902564589472741)
            ·
              refine ⟨11331469783481730860526139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60434505511902564589472741 11331469783481730860526139)
              ·
                refine ⟨16997204675222596290789209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11331469783481730860526139 16997204675222596290789209)
                ·
                  refine ⟨12747903506416947218091907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16997204675222596290789209 12747903506416947218091907)
                  ·
                    refine ⟨19121855259625420827137861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12747903506416947218091907 19121855259625420827137861)
                    ·
                      refine ⟨3585347861179766405088349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19121855259625420827137861 3585347861179766405088349)
                      ·
                        rfl

theorem cell23_6982440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_6982440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982440 prefixEnd_6982440 := by exact prefixLift 6982440
  have htrace : WordTrace (prefixWord ++ tailWord_6982440) baseStart_6982440 baseEnd_6982440 := by
    simpa [prefixWord, tailWord_6982440, baseEnd_6982440] using wordTrace_append hprefix tailTrace_6982440
  have hstable : (prefixWord ++ tailWord_6982440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982440).length < 2 ^ (prefixWord ++ tailWord_6982440).sum := by decide
  have hdescent : baseEnd_6982440 < baseStart_6982440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982443 : List Nat := [1, 1, 1, 1, 2, 1, 2, 7, 2, 2, 3]
def baseStart_6982443 : Nat := 118140960795 + 6982443 * 2 ^ 59
def prefixEnd_6982443 : Nat := 4983230072969 + 3 ^ 40 * 6982443 * 2
def baseEnd_6982443 : Nat := 3585349401621729893350835

theorem tailTrace_6982443 : CollatzResearch.WordTrace tailWord_6982443 prefixEnd_6982443 3585349401621729893350835 := by
  unfold tailWord_6982443
  simp only [CollatzResearch.WordTrace]
  refine ⟨254670618242808992169231983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169780412161872661446154655 254670618242808992169231983)
  ·
    refine ⟨382005927364213488253847975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254670618242808992169231983 382005927364213488253847975)
    ·
      refine ⟨573008891046320232380771963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382005927364213488253847975 573008891046320232380771963)
      ·
        refine ⟨859513336569480348571157945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573008891046320232380771963 859513336569480348571157945)
        ·
          refine ⟨644635002427110261428368459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 859513336569480348571157945 644635002427110261428368459)
          ·
            refine ⟨966952503640665392142552689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644635002427110261428368459 966952503640665392142552689)
            ·
              refine ⟨725214377730499044106914517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 966952503640665392142552689 725214377730499044106914517)
              ·
                refine ⟨16997211978058571346255809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 725214377730499044106914517 16997211978058571346255809)
                ·
                  refine ⟨12747908983543928509691857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16997211978058571346255809 12747908983543928509691857)
                  ·
                    refine ⟨9560931737657946382268893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12747908983543928509691857 9560931737657946382268893)
                    ·
                      refine ⟨3585349401621729893350835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9560931737657946382268893 3585349401621729893350835)
                      ·
                        rfl

theorem cell23_6982443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2, 3].length) (baseStart_6982443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982443 prefixEnd_6982443 := by exact prefixLift 6982443
  have htrace : WordTrace (prefixWord ++ tailWord_6982443) baseStart_6982443 baseEnd_6982443 := by
    simpa [prefixWord, tailWord_6982443, baseEnd_6982443] using wordTrace_append hprefix tailTrace_6982443
  have hstable : (prefixWord ++ tailWord_6982443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982443).length < 2 ^ (prefixWord ++ tailWord_6982443).sum := by decide
  have hdescent : baseEnd_6982443 < baseStart_6982443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982463 : List Nat := [1, 1, 2, 2, 5, 1, 1, 4, 6]
def baseStart_6982463 : Nat := 118140960795 + 6982463 * 2 ^ 59
def prefixEnd_6982463 : Nat := 4983230072969 + 3 ^ 40 * 6982463 * 2
def baseEnd_6982463 : Nat := 398373296803868868344527

theorem tailTrace_6982463 : CollatzResearch.WordTrace tailWord_6982463 prefixEnd_6982463 398373296803868868344527 := by
  unfold tailWord_6982463
  simp only [CollatzResearch.WordTrace]
  refine ⟨254671347702736535584960043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169780898468491023723306695 254671347702736535584960043)
  ·
    refine ⟨382007021554104803377440065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254671347702736535584960043 382007021554104803377440065)
    ·
      refine ⟨286505266165578602533080049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382007021554104803377440065 286505266165578602533080049)
      ·
        refine ⟨214878949624183951899810037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286505266165578602533080049 214878949624183951899810037)
        ·
          refine ⟨20144901527267245490607191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 214878949624183951899810037 20144901527267245490607191)
          ·
            refine ⟨30217352290900868235910787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20144901527267245490607191 30217352290900868235910787)
            ·
              refine ⟨45326028436351302353866181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30217352290900868235910787 45326028436351302353866181)
              ·
                refine ⟨8498630331815869191349909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45326028436351302353866181 8498630331815869191349909)
                ·
                  refine ⟨398373296803868868344527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8498630331815869191349909 398373296803868868344527)
                  ·
                    rfl

theorem cell23_6982463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 6].length) (baseStart_6982463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982463 prefixEnd_6982463 := by exact prefixLift 6982463
  have htrace : WordTrace (prefixWord ++ tailWord_6982463) baseStart_6982463 baseEnd_6982463 := by
    simpa [prefixWord, tailWord_6982463, baseEnd_6982463] using wordTrace_append hprefix tailTrace_6982463
  have hstable : (prefixWord ++ tailWord_6982463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982463).length < 2 ^ (prefixWord ++ tailWord_6982463).sum := by decide
  have hdescent : baseEnd_6982463 < baseStart_6982463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982490 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3]
def baseStart_6982490 : Nat := 118140960795 + 6982490 * 2 ^ 59
def prefixEnd_6982490 : Nat := 4983230072969 + 3 ^ 40 * 6982490 * 2
def baseEnd_6982490 : Nat := 3585373535212491209463119

theorem tailTrace_6982490 : CollatzResearch.WordTrace tailWord_6982490 prefixEnd_6982490 3585373535212491209463119 := by
  unfold tailWord_6982490
  simp only [CollatzResearch.WordTrace]
  refine ⟨63668083118409679799048231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169781554982425812797461949 63668083118409679799048231)
  ·
    refine ⟨95502124677614519698572347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63668083118409679799048231 95502124677614519698572347)
    ·
      refine ⟨143253187016421779547858521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95502124677614519698572347 143253187016421779547858521)
      ·
        refine ⟨107439890262316334660893891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143253187016421779547858521 107439890262316334660893891)
        ·
          refine ⟨161159835393474501991340837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107439890262316334660893891 161159835393474501991340837)
          ·
            refine ⟨30217469136276469123376407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161159835393474501991340837 30217469136276469123376407)
            ·
              refine ⟨45326203704414703685064611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30217469136276469123376407 45326203704414703685064611)
              ·
                refine ⟨67989305556622055527596917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45326203704414703685064611 67989305556622055527596917)
                ·
                  refine ⟨6373997395933317705712211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67989305556622055527596917 6373997395933317705712211)
                  ·
                    refine ⟨9560996093899976558568317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6373997395933317705712211 9560996093899976558568317)
                    ·
                      refine ⟨3585373535212491209463119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9560996093899976558568317 3585373535212491209463119)
                      ·
                        rfl

theorem cell23_6982490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_6982490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982490 prefixEnd_6982490 := by exact prefixLift 6982490
  have htrace : WordTrace (prefixWord ++ tailWord_6982490) baseStart_6982490 baseEnd_6982490 := by
    simpa [prefixWord, tailWord_6982490, baseEnd_6982490] using wordTrace_append hprefix tailTrace_6982490
  have hstable : (prefixWord ++ tailWord_6982490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982490).length < 2 ^ (prefixWord ++ tailWord_6982490).sum := by decide
  have hdescent : baseEnd_6982490 < baseStart_6982490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982507 : List Nat := [1, 1, 1, 1, 2, 2, 5, 5, 1, 1, 3]
def baseStart_6982507 : Nat := 118140960795 + 6982507 * 2 ^ 59
def prefixEnd_6982507 : Nat := 4983230072969 + 3 ^ 40 * 6982507 * 2
def baseEnd_6982507 : Nat := 3585382264383617642950541

theorem tailTrace_6982507 : CollatzResearch.WordTrace tailWord_6982507 prefixEnd_6982507 3585382264383617642950541 := by
  unfold tailWord_6982507
  simp only [CollatzResearch.WordTrace]
  refine ⟨254672952514577131099561775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169781968343051420733041183 254672952514577131099561775)
  ·
    refine ⟨382009428771865696649342663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254672952514577131099561775 382009428771865696649342663)
    ·
      refine ⟨573014143157798544974013995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382009428771865696649342663 573014143157798544974013995)
      ·
        refine ⟨859521214736697817461020993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573014143157798544974013995 859521214736697817461020993)
        ·
          refine ⟨644640911052523363095765745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 859521214736697817461020993 644640911052523363095765745)
          ·
            refine ⟨483480683289392522321824309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 644640911052523363095765745 483480683289392522321824309)
            ·
              refine ⟨45326314058380548967671029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 483480683289392522321824309 45326314058380548967671029)
              ·
                refine ⟨4249341942973176465719159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45326314058380548967671029 4249341942973176465719159)
                ·
                  refine ⟨6374012914459764698578739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4249341942973176465719159 6374012914459764698578739)
                  ·
                    refine ⟨9561019371689647047868109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6374012914459764698578739 9561019371689647047868109)
                    ·
                      refine ⟨3585382264383617642950541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9561019371689647047868109 3585382264383617642950541)
                      ·
                        rfl

theorem cell23_6982507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 1, 1, 3].length) (baseStart_6982507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982507 prefixEnd_6982507 := by exact prefixLift 6982507
  have htrace : WordTrace (prefixWord ++ tailWord_6982507) baseStart_6982507 baseEnd_6982507 := by
    simpa [prefixWord, tailWord_6982507, baseEnd_6982507] using wordTrace_append hprefix tailTrace_6982507
  have hstable : (prefixWord ++ tailWord_6982507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982507).length < 2 ^ (prefixWord ++ tailWord_6982507).sum := by decide
  have hdescent : baseEnd_6982507 < baseStart_6982507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982533 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 3, 1, 5]
def baseStart_6982533 : Nat := 118140960795 + 6982533 * 2 ^ 59
def prefixEnd_6982533 : Nat := 4983230072969 + 3 ^ 40 * 6982533 * 2
def baseEnd_6982533 : Nat := 3585395614880634541225421

theorem tailTrace_6982533 : CollatzResearch.WordTrace tailWord_6982533 prefixEnd_6982533 3585395614880634541225421 := by
  unfold tailWord_6982533
  simp only [CollatzResearch.WordTrace]
  refine ⟨254673900812482937540008253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169782600541655291693338835 254673900812482937540008253)
  ·
    refine ⟨95502712804681101577503095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254673900812482937540008253 95502712804681101577503095)
    ·
      refine ⟨143254069207021652366254643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95502712804681101577503095 143254069207021652366254643)
      ·
        refine ⟨214881103810532478549381965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143254069207021652366254643 214881103810532478549381965)
        ·
          refine ⟨80580413928949679456018237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214881103810532478549381965 80580413928949679456018237)
          ·
            refine ⟨30217655223356129796006839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80580413928949679456018237 30217655223356129796006839)
            ·
              refine ⟨45326482835034194694010259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30217655223356129796006839 45326482835034194694010259)
              ·
                refine ⟨67989724252551292041015389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45326482835034194694010259 67989724252551292041015389)
                ·
                  refine ⟨25496146594706734515380771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67989724252551292041015389 25496146594706734515380771)
                  ·
                    refine ⟨38244219892060101773071157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25496146594706734515380771 38244219892060101773071157)
                    ·
                      refine ⟨3585395614880634541225421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38244219892060101773071157 3585395614880634541225421)
                      ·
                        rfl

theorem cell23_6982533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_6982533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982533 prefixEnd_6982533 := by exact prefixLift 6982533
  have htrace : WordTrace (prefixWord ++ tailWord_6982533) baseStart_6982533 baseEnd_6982533 := by
    simpa [prefixWord, tailWord_6982533, baseEnd_6982533] using wordTrace_append hprefix tailTrace_6982533
  have hstable : (prefixWord ++ tailWord_6982533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982533).length < 2 ^ (prefixWord ++ tailWord_6982533).sum := by decide
  have hdescent : baseEnd_6982533 < baseStart_6982533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982540 : List Nat := [2, 2, 1, 2, 1, 2, 2, 5, 2, 4]
def baseStart_6982540 : Nat := 118140960795 + 6982540 * 2 ^ 59
def prefixEnd_6982540 : Nat := 4983230072969 + 3 ^ 40 * 6982540 * 2
def baseEnd_6982540 : Nat := 1195133069748405337945963

theorem tailTrace_6982540 : CollatzResearch.WordTrace tailWord_6982540 prefixEnd_6982540 1195133069748405337945963 := by
  unfold tailWord_6982540
  simp only [CollatzResearch.WordTrace]
  refine ⟨127337078061728788867756537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169782770748971718490342049 127337078061728788867756537)
  ·
    refine ⟨95502808546296591650817403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127337078061728788867756537 95502808546296591650817403)
    ·
      refine ⟨143254212819444887476226105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95502808546296591650817403 143254212819444887476226105)
      ·
        refine ⟨107440659614583665607169579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143254212819444887476226105 107440659614583665607169579)
        ·
          refine ⟨161160989421875498410754369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107440659614583665607169579 161160989421875498410754369)
          ·
            refine ⟨120870742066406623808065777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161160989421875498410754369 120870742066406623808065777)
            ·
              refine ⟨90653056549804967856049333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120870742066406623808065777 90653056549804967856049333)
              ·
                refine ⟨8498724051544215736504625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90653056549804967856049333 8498724051544215736504625)
                ·
                  refine ⟨6374043038658161802378469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8498724051544215736504625 6374043038658161802378469)
                  ·
                    refine ⟨1195133069748405337945963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6374043038658161802378469 1195133069748405337945963)
                    ·
                      rfl

theorem cell23_6982540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 2, 4].length) (baseStart_6982540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982540 prefixEnd_6982540 := by exact prefixLift 6982540
  have htrace : WordTrace (prefixWord ++ tailWord_6982540) baseStart_6982540 baseEnd_6982540 := by
    simpa [prefixWord, tailWord_6982540, baseEnd_6982540] using wordTrace_append hprefix tailTrace_6982540
  have hstable : (prefixWord ++ tailWord_6982540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982540).length < 2 ^ (prefixWord ++ tailWord_6982540).sum := by decide
  have hdescent : baseEnd_6982540 < baseStart_6982540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982567 : List Nat := [1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 5]
def baseStart_6982567 : Nat := 118140960795 + 6982567 * 2 ^ 59
def prefixEnd_6982567 : Nat := 4983230072969 + 3 ^ 40 * 6982567 * 2
def baseEnd_6982567 : Nat := 3585413073222887408200265

theorem tailTrace_6982567 : CollatzResearch.WordTrace tailWord_6982567 prefixEnd_6982567 3585413073222887408200265 := by
  unfold tailWord_6982567
  simp only [CollatzResearch.WordTrace]
  refine ⟨254675140894359761346745955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169783427262906507564497303 254675140894359761346745955)
  ·
    refine ⟨382012711341539642020118933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254675140894359761346745955 382012711341539642020118933)
    ·
      refine ⟨17906845844134670719693075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 382012711341539642020118933 17906845844134670719693075)
      ·
        refine ⟨26860268766202006079539613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17906845844134670719693075 26860268766202006079539613)
        ·
          refine ⟨10072600787325752279827355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26860268766202006079539613 10072600787325752279827355)
          ·
            refine ⟨15108901180988628419741033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10072600787325752279827355 15108901180988628419741033)
            ·
              refine ⟨11331675885741471314805775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15108901180988628419741033 11331675885741471314805775)
              ·
                refine ⟨16997513828612206972208663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11331675885741471314805775 16997513828612206972208663)
                ·
                  refine ⟨25496270742918310458312995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16997513828612206972208663 25496270742918310458312995)
                  ·
                    refine ⟨38244406114377465687469493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25496270742918310458312995 38244406114377465687469493)
                    ·
                      refine ⟨3585413073222887408200265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38244406114377465687469493 3585413073222887408200265)
                      ·
                        rfl

theorem cell23_6982567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_6982567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982567 prefixEnd_6982567 := by exact prefixLift 6982567
  have htrace : WordTrace (prefixWord ++ tailWord_6982567) baseStart_6982567 baseEnd_6982567 := by
    simpa [prefixWord, tailWord_6982567, baseEnd_6982567] using wordTrace_append hprefix tailTrace_6982567
  have hstable : (prefixWord ++ tailWord_6982567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982567).length < 2 ^ (prefixWord ++ tailWord_6982567).sum := by decide
  have hdescent : baseEnd_6982567 < baseStart_6982567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982598 : List Nat := [6, 1, 3, 1, 1, 1, 1, 1, 3, 1, 4]
def baseStart_6982598 : Nat := 118140960795 + 6982598 * 2 ^ 59
def prefixEnd_6982598 : Nat := 4983230072969 + 3 ^ 40 * 6982598 * 2
def baseEnd_6982598 : Nat := 3585428991123176786912623

theorem tailTrace_6982598 : CollatzResearch.WordTrace tailWord_6982598 prefixEnd_6982598 3585428991123176786912623 := by
  unfold tailWord_6982598
  simp only [CollatzResearch.WordTrace]
  refine ⟨7958633486163982926285139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 169784181038164969094082965 7958633486163982926285139)
  ·
    refine ⟨11937950229245974389427709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7958633486163982926285139 11937950229245974389427709)
    ·
      refine ⟨4476731335967240396035391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11937950229245974389427709 4476731335967240396035391)
      ·
        refine ⟨6715097003950860594053087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4476731335967240396035391 6715097003950860594053087)
        ·
          refine ⟨10072645505926290891079631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6715097003950860594053087 10072645505926290891079631)
          ·
            refine ⟨15108968258889436336619447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10072645505926290891079631 15108968258889436336619447)
            ·
              refine ⟨22663452388334154504929171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15108968258889436336619447 22663452388334154504929171)
              ·
                refine ⟨33995178582501231757393757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22663452388334154504929171 33995178582501231757393757)
                ·
                  refine ⟨12748191968437961909022659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33995178582501231757393757 12748191968437961909022659)
                  ·
                    refine ⟨19122287952656942863533989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12748191968437961909022659 19122287952656942863533989)
                    ·
                      refine ⟨3585428991123176786912623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19122287952656942863533989 3585428991123176786912623)
                      ·
                        rfl

theorem cell23_6982598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_6982598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982598 prefixEnd_6982598 := by exact prefixLift 6982598
  have htrace : WordTrace (prefixWord ++ tailWord_6982598) baseStart_6982598 baseEnd_6982598 := by
    simpa [prefixWord, tailWord_6982598, baseEnd_6982598] using wordTrace_append hprefix tailTrace_6982598
  have hstable : (prefixWord ++ tailWord_6982598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982598).length < 2 ^ (prefixWord ++ tailWord_6982598).sum := by decide
  have hdescent : baseEnd_6982598 < baseStart_6982598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982607 : List Nat := [1, 1, 2, 1, 1, 7, 1, 1, 3, 3, 2]
def baseStart_6982607 : Nat := 118140960795 + 6982607 * 2 ^ 59
def prefixEnd_6982607 : Nat := 4983230072969 + 3 ^ 40 * 6982607 * 2
def baseEnd_6982607 : Nat := 3585433612449067251700081

theorem tailTrace_6982607 : CollatzResearch.WordTrace tailWord_6982607 prefixEnd_6982607 3585433612449067251700081 := by
  unfold tailWord_6982607
  simp only [CollatzResearch.WordTrace]
  refine ⟨254676599814214848178202075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169784399876143232118801383 254676599814214848178202075)
  ·
    refine ⟨382014899721322272267303113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254676599814214848178202075 382014899721322272267303113)
    ·
      refine ⟨286511174790991704200477335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382014899721322272267303113 286511174790991704200477335)
      ·
        refine ⟨429766762186487556300716003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286511174790991704200477335 429766762186487556300716003)
        ·
          refine ⟨644650143279731334451074005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429766762186487556300716003 644650143279731334451074005)
          ·
            refine ⟨15108987733118703151197047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 644650143279731334451074005 15108987733118703151197047)
            ·
              refine ⟨22663481599678054726795571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15108987733118703151197047 22663481599678054726795571)
              ·
                refine ⟨33995222399517082090193357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22663481599678054726795571 33995222399517082090193357)
                ·
                  refine ⟨12748208399818905783822509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33995222399517082090193357 12748208399818905783822509)
                  ·
                    refine ⟨4780578149932089668933441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12748208399818905783822509 4780578149932089668933441)
                    ·
                      refine ⟨3585433612449067251700081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4780578149932089668933441 3585433612449067251700081)
                      ·
                        rfl

theorem cell23_6982607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 3, 2].length) (baseStart_6982607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982607 prefixEnd_6982607 := by exact prefixLift 6982607
  have htrace : WordTrace (prefixWord ++ tailWord_6982607) baseStart_6982607 baseEnd_6982607 := by
    simpa [prefixWord, tailWord_6982607, baseEnd_6982607] using wordTrace_append hprefix tailTrace_6982607
  have hstable : (prefixWord ++ tailWord_6982607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982607).length < 2 ^ (prefixWord ++ tailWord_6982607).sum := by decide
  have hdescent : baseEnd_6982607 < baseStart_6982607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982614 : List Nat := [5, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_6982614 : Nat := 118140960795 + 6982614 * 2 ^ 59
def prefixEnd_6982614 : Nat := 4983230072969 + 3 ^ 40 * 6982614 * 2
def baseEnd_6982614 : Nat := 3585437206813648724312549

theorem tailTrace_6982614 : CollatzResearch.WordTrace tailWord_6982614 prefixEnd_6982614 3585437206813648724312549 := by
  unfold tailWord_6982614
  simp only [CollatzResearch.WordTrace]
  refine ⟨15917303445324343023356681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169784570083459658915804597 15917303445324343023356681)
  ·
    refine ⟨11937977583993257267517511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15917303445324343023356681 11937977583993257267517511)
    ·
      refine ⟨17906966375989885901276267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11937977583993257267517511 17906966375989885901276267)
      ·
        refine ⟨26860449563984828851914401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17906966375989885901276267 26860449563984828851914401)
        ·
          refine ⟨20145337172988621638935801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26860449563984828851914401 20145337172988621638935801)
          ·
            refine ⟨15109002879741466229201851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20145337172988621638935801 15109002879741466229201851)
            ·
              refine ⟨22663504319612199343802777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15109002879741466229201851 22663504319612199343802777)
              ·
                refine ⟨16997628239709149507852083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22663504319612199343802777 16997628239709149507852083)
                ·
                  refine ⟨25496442359563724261778125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16997628239709149507852083 25496442359563724261778125)
                  ·
                    refine ⟨9561165884836396598166797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25496442359563724261778125 9561165884836396598166797)
                    ·
                      refine ⟨3585437206813648724312549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9561165884836396598166797 3585437206813648724312549)
                      ·
                        rfl

theorem cell23_6982614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_6982614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982614 prefixEnd_6982614 := by exact prefixLift 6982614
  have htrace : WordTrace (prefixWord ++ tailWord_6982614) baseStart_6982614 baseEnd_6982614 := by
    simpa [prefixWord, tailWord_6982614, baseEnd_6982614] using wordTrace_append hprefix tailTrace_6982614
  have hstable : (prefixWord ++ tailWord_6982614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982614).length < 2 ^ (prefixWord ++ tailWord_6982614).sum := by decide
  have hdescent : baseEnd_6982614 < baseStart_6982614 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982633 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 5, 4, 4]
def baseStart_6982633 : Nat := 118140960795 + 6982633 * 2 ^ 59
def prefixEnd_6982633 : Nat := 4983230072969 + 3 ^ 40 * 6982633 * 2
def baseEnd_6982633 : Nat := 3585446962946084149974961

theorem tailTrace_6982633 : CollatzResearch.WordTrace tailWord_6982633 prefixEnd_6982633 3585446962946084149974961 := by
  unfold tailWord_6982633
  simp only [CollatzResearch.WordTrace]
  refine ⟨254677548112120654618648553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169785032074747103079099035 254677548112120654618648553)
  ·
    refine ⟨191008161084090490963986415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254677548112120654618648553 191008161084090490963986415)
    ·
      refine ⟨286512241626135736445979623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191008161084090490963986415 286512241626135736445979623)
      ·
        refine ⟨429768362439203604668969435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286512241626135736445979623 429768362439203604668969435)
        ·
          refine ⟨644652543658805407003454153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429768362439203604668969435 644652543658805407003454153)
          ·
            refine ⟨483489407744104055252590615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 644652543658805407003454153 483489407744104055252590615)
            ·
              refine ⟨725234111616156082878885923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483489407744104055252590615 725234111616156082878885923)
              ·
                refine ⟨1087851167424234124318328885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 725234111616156082878885923 1087851167424234124318328885)
                ·
                  refine ⟨101986046946021949154843333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1087851167424234124318328885 101986046946021949154843333)
                  ·
                    refine ⟨19122383802379115466533125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101986046946021949154843333 19122383802379115466533125)
                    ·
                      refine ⟨3585446962946084149974961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19122383802379115466533125 3585446962946084149974961)
                      ·
                        rfl

theorem cell23_6982633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 4, 4].length) (baseStart_6982633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982633 prefixEnd_6982633 := by exact prefixLift 6982633
  have htrace : WordTrace (prefixWord ++ tailWord_6982633) baseStart_6982633 baseEnd_6982633 := by
    simpa [prefixWord, tailWord_6982633, baseEnd_6982633] using wordTrace_append hprefix tailTrace_6982633
  have hstable : (prefixWord ++ tailWord_6982633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982633).length < 2 ^ (prefixWord ++ tailWord_6982633).sum := by decide
  have hdescent : baseEnd_6982633 < baseStart_6982633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982677 : List Nat := [1, 3, 2, 1, 4, 1, 1, 5, 5]
def baseStart_6982677 : Nat := 118140960795 + 6982677 * 2 ^ 59
def prefixEnd_6982677 : Nat := 4983230072969 + 3 ^ 40 * 6982677 * 2
def baseEnd_6982677 : Nat := 398385506232764664202751

theorem tailTrace_6982677 : CollatzResearch.WordTrace tailWord_6982677 prefixEnd_6982677 398385506232764664202751 := by
  unfold tailWord_6982677
  simp only [CollatzResearch.WordTrace]
  refine ⟨254679152923961250133250285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169786101949307500088833523 254679152923961250133250285)
  ·
    refine ⟨95504682346485468799968857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254679152923961250133250285 95504682346485468799968857)
    ·
      refine ⟨71628511759864101599976643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95504682346485468799968857 71628511759864101599976643)
      ·
        refine ⟨107442767639796152399964965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71628511759864101599976643 107442767639796152399964965)
        ·
          refine ⟨20145518932461778574993431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107442767639796152399964965 20145518932461778574993431)
          ·
            refine ⟨30218278398692667862490147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20145518932461778574993431 30218278398692667862490147)
            ·
              refine ⟨45327417598039001793735221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30218278398692667862490147 45327417598039001793735221)
              ·
                refine ⟨4249445399816156418162677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45327417598039001793735221 4249445399816156418162677)
                ·
                  refine ⟨398385506232764664202751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4249445399816156418162677 398385506232764664202751)
                  ·
                    rfl

theorem cell23_6982677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5, 5].length) (baseStart_6982677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982677 prefixEnd_6982677 := by exact prefixLift 6982677
  have htrace : WordTrace (prefixWord ++ tailWord_6982677) baseStart_6982677 baseEnd_6982677 := by
    simpa [prefixWord, tailWord_6982677, baseEnd_6982677] using wordTrace_append hprefix tailTrace_6982677
  have hstable : (prefixWord ++ tailWord_6982677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982677).length < 2 ^ (prefixWord ++ tailWord_6982677).sum := by decide
  have hdescent : baseEnd_6982677 < baseStart_6982677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982740 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_6982740 : Nat := 118140960795 + 6982740 * 2 ^ 59
def prefixEnd_6982740 : Nat := 4983230072969 + 3 ^ 40 * 6982740 * 2
def baseEnd_6982740 : Nat := 3585501905376115231336969

theorem tailTrace_6982740 : CollatzResearch.WordTrace tailWord_6982740 prefixEnd_6982740 3585501905376115231336969 := by
  unfold tailWord_6982740
  simp only [CollatzResearch.WordTrace]
  refine ⟨127340725361366505946396837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169787633815155341261862449 127340725361366505946396837)
  ·
    refine ⟨23876386005256219864949407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127340725361366505946396837 23876386005256219864949407)
    ·
      refine ⟨35814579007884329797424111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23876386005256219864949407 35814579007884329797424111)
      ·
        refine ⟨53721868511826494696136167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35814579007884329797424111 53721868511826494696136167)
        ·
          refine ⟨80582802767739742044204251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53721868511826494696136167 80582802767739742044204251)
          ·
            refine ⟨120874204151609613066306377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80582802767739742044204251 120874204151609613066306377)
            ·
              refine ⟨90655653113707209799729783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120874204151609613066306377 90655653113707209799729783)
              ·
                refine ⟨135983479670560814699594675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90655653113707209799729783 135983479670560814699594675)
                ·
                  refine ⟨203975219505841222049392013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135983479670560814699594675 203975219505841222049392013)
                  ·
                    refine ⟨76490707314690458268522005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 203975219505841222049392013 76490707314690458268522005)
                    ·
                      refine ⟨3585501905376115231336969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76490707314690458268522005 3585501905376115231336969)
                      ·
                        rfl

theorem cell23_6982740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_6982740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982740 prefixEnd_6982740 := by exact prefixLift 6982740
  have htrace : WordTrace (prefixWord ++ tailWord_6982740) baseStart_6982740 baseEnd_6982740 := by
    simpa [prefixWord, tailWord_6982740, baseEnd_6982740] using wordTrace_append hprefix tailTrace_6982740
  have hstable : (prefixWord ++ tailWord_6982740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982740).length < 2 ^ (prefixWord ++ tailWord_6982740).sum := by decide
  have hdescent : baseEnd_6982740 < baseStart_6982740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982814 : List Nat := [4, 3, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_6982814 : Nat := 118140960795 + 6982814 * 2 ^ 59
def prefixEnd_6982814 : Nat := 4983230072969 + 3 ^ 40 * 6982814 * 2
def baseEnd_6982814 : Nat := 1195179967648182647270543

theorem tailTrace_6982814 : CollatzResearch.WordTrace tailWord_6982814 prefixEnd_6982814 1195179967648182647270543 := by
  unfold tailWord_6982814
  simp only [CollatzResearch.WordTrace]
  refine ⟨31835518715558115316373437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169789433149643281687324997 31835518715558115316373437)
  ·
    refine ⟨11938319518334293243640039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31835518715558115316373437 11938319518334293243640039)
    ·
      refine ⟨17907479277501439865460059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11938319518334293243640039 17907479277501439865460059)
      ·
        refine ⟨26861218916252159798190089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17907479277501439865460059 26861218916252159798190089)
        ·
          refine ⟨20145914187189119848642567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26861218916252159798190089 20145914187189119848642567)
          ·
            refine ⟨30218871280783679772963851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20145914187189119848642567 30218871280783679772963851)
            ·
              refine ⟨45328306921175519659445777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30218871280783679772963851 45328306921175519659445777)
              ·
                refine ⟨33996230190881639744584333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45328306921175519659445777 33996230190881639744584333)
                ·
                  refine ⟨12748586321580614904219125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33996230190881639744584333 12748586321580614904219125)
                  ·
                    refine ⟨1195179967648182647270543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12748586321580614904219125 1195179967648182647270543)
                    ·
                      rfl

theorem cell23_6982814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_6982814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982814 prefixEnd_6982814 := by exact prefixLift 6982814
  have htrace : WordTrace (prefixWord ++ tailWord_6982814) baseStart_6982814 baseEnd_6982814 := by
    simpa [prefixWord, tailWord_6982814, baseEnd_6982814] using wordTrace_append hprefix tailTrace_6982814
  have hstable : (prefixWord ++ tailWord_6982814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982814).length < 2 ^ (prefixWord ++ tailWord_6982814).sum := by decide
  have hdescent : baseEnd_6982814 < baseStart_6982814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982817 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 5, 1, 4]
def baseStart_6982817 : Nat := 118140960795 + 6982817 * 2 ^ 59
def prefixEnd_6982817 : Nat := 4983230072969 + 3 ^ 40 * 6982817 * 2
def baseEnd_6982817 : Nat := 3585541443386511430074115

theorem tailTrace_6982817 : CollatzResearch.WordTrace tailWord_6982817 prefixEnd_6982817 3585541443386511430074115 := by
  unfold tailWord_6982817
  simp only [CollatzResearch.WordTrace]
  refine ⟨254684259143454054043346705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169789506095636036028897803 254684259143454054043346705)
  ·
    refine ⟨191013194357590540532510029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254684259143454054043346705 191013194357590540532510029)
    ·
      refine ⟨71629947884096452699691261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191013194357590540532510029 71629947884096452699691261)
      ·
        refine ⟨26861230456536169762384223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71629947884096452699691261 26861230456536169762384223)
        ·
          refine ⟨40291845684804254643576335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26861230456536169762384223 40291845684804254643576335)
          ·
            refine ⟨60437768527206381965364503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40291845684804254643576335 60437768527206381965364503)
            ·
              refine ⟨90656652790809572948046755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60437768527206381965364503 90656652790809572948046755)
              ·
                refine ⟨135984979186214359422070133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90656652790809572948046755 135984979186214359422070133)
                ·
                  refine ⟨12748591798707596195819075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135984979186214359422070133 12748591798707596195819075)
                  ·
                    refine ⟨19122887698061394293728613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12748591798707596195819075 19122887698061394293728613)
                    ·
                      refine ⟨3585541443386511430074115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19122887698061394293728613 3585541443386511430074115)
                      ·
                        rfl

theorem cell23_6982817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_6982817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982817 prefixEnd_6982817 := by exact prefixLift 6982817
  have htrace : WordTrace (prefixWord ++ tailWord_6982817) baseStart_6982817 baseEnd_6982817 := by
    simpa [prefixWord, tailWord_6982817, baseEnd_6982817] using wordTrace_append hprefix tailTrace_6982817
  have hstable : (prefixWord ++ tailWord_6982817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982817).length < 2 ^ (prefixWord ++ tailWord_6982817).sum := by decide
  have hdescent : baseEnd_6982817 < baseStart_6982817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982847 : List Nat := [1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 4]
def baseStart_6982847 : Nat := 118140960795 + 6982847 * 2 ^ 59
def prefixEnd_6982847 : Nat := 4983230072969 + 3 ^ 40 * 6982847 * 2
def baseEnd_6982847 : Nat := 3585556847806146312698977

theorem tailTrace_6982847 : CollatzResearch.WordTrace tailWord_6982847 prefixEnd_6982847 3585556847806146312698977 := by
  unfold tailWord_6982847
  simp only [CollatzResearch.WordTrace]
  refine ⟨254685353333345369166938795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169790235555563579444625863 254685353333345369166938795)
  ·
    refine ⟨382028030000018053750408193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254685353333345369166938795 382028030000018053750408193)
    ·
      refine ⟨286521022500013540312806145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382028030000018053750408193 286521022500013540312806145)
      ·
        refine ⟨214890766875010155234604609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286521022500013540312806145 214890766875010155234604609)
        ·
          refine ⟨161168075156257616425953457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214890766875010155234604609 161168075156257616425953457)
          ·
            refine ⟨120876056367193212319465093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161168075156257616425953457 120876056367193212319465093)
            ·
              refine ⟨22664260568848727309899705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120876056367193212319465093 22664260568848727309899705)
              ·
                refine ⟨16998195426636545482424779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22664260568848727309899705 16998195426636545482424779)
                ·
                  refine ⟨25497293139954818223637169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16998195426636545482424779 25497293139954818223637169)
                  ·
                    refine ⟨19122969854966113667727877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25497293139954818223637169 19122969854966113667727877)
                    ·
                      refine ⟨3585556847806146312698977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19122969854966113667727877 3585556847806146312698977)
                      ·
                        rfl

theorem cell23_6982847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_6982847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982847 prefixEnd_6982847 := by exact prefixLift 6982847
  have htrace : WordTrace (prefixWord ++ tailWord_6982847) baseStart_6982847 baseEnd_6982847 := by
    simpa [prefixWord, tailWord_6982847, baseEnd_6982847] using wordTrace_append hprefix tailTrace_6982847
  have hstable : (prefixWord ++ tailWord_6982847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982847).length < 2 ^ (prefixWord ++ tailWord_6982847).sum := by decide
  have hdescent : baseEnd_6982847 < baseStart_6982847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982848 : List Nat := [2, 1, 1, 2, 7, 1, 2, 1, 1, 5]
def baseStart_6982848 : Nat := 118140960795 + 6982848 * 2 ^ 59
def prefixEnd_6982848 : Nat := 4983230072969 + 3 ^ 40 * 6982848 * 2
def baseEnd_6982848 : Nat := 1195185787095600269595491

theorem tailTrace_6982848 : CollatzResearch.WordTrace tailWord_6982848 prefixEnd_6982848 1195185787095600269595491 := by
  unfold tailWord_6982848
  simp only [CollatzResearch.WordTrace]
  refine ⟨127342694903170873168862599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169790259870894497558483465 127342694903170873168862599)
  ·
    refine ⟨191014042354756309753293899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127342694903170873168862599 191014042354756309753293899)
    ·
      refine ⟨286521063532134464629940849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191014042354756309753293899 286521063532134464629940849)
      ·
        refine ⟨214890797649100848472455637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286521063532134464629940849 214890797649100848472455637)
        ·
          refine ⟨5036503069900801136073179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 214890797649100848472455637 5036503069900801136073179)
          ·
            refine ⟨7554754604851201704109769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5036503069900801136073179 7554754604851201704109769)
            ·
              refine ⟨5666065953638401278082327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7554754604851201704109769 5666065953638401278082327)
              ·
                refine ⟨8499098930457601917123491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5666065953638401278082327 8499098930457601917123491)
                ·
                  refine ⟨12748648395686402875685237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8499098930457601917123491 12748648395686402875685237)
                  ·
                    refine ⟨1195185787095600269595491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12748648395686402875685237 1195185787095600269595491)
                    ·
                      rfl

theorem cell23_6982848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 1, 5].length) (baseStart_6982848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982848 prefixEnd_6982848 := by exact prefixLift 6982848
  have htrace : WordTrace (prefixWord ++ tailWord_6982848) baseStart_6982848 baseEnd_6982848 := by
    simpa [prefixWord, tailWord_6982848, baseEnd_6982848] using wordTrace_append hprefix tailTrace_6982848
  have hstable : (prefixWord ++ tailWord_6982848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982848).length < 2 ^ (prefixWord ++ tailWord_6982848).sum := by decide
  have hdescent : baseEnd_6982848 < baseStart_6982848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982884 : List Nat := [2, 3, 1, 1, 1, 2, 5, 1, 1, 3, 3]
def baseStart_6982884 : Nat := 118140960795 + 6982884 * 2 ^ 59
def prefixEnd_6982884 : Nat := 4983230072969 + 3 ^ 40 * 6982884 * 2
def baseEnd_6982884 : Nat := 3585575846590362667936307

theorem tailTrace_6982884 : CollatzResearch.WordTrace tailWord_6982884 prefixEnd_6982884 3585575846590362667936307 := by
  unfold tailWord_6982884
  simp only [CollatzResearch.WordTrace]
  refine ⟨127343351417105662243017853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169791135222807549657357137 127343351417105662243017853)
  ·
    refine ⟨47753756781414623341131695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127343351417105662243017853 47753756781414623341131695)
    ·
      refine ⟨71630635172121935011697543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47753756781414623341131695 71630635172121935011697543)
      ·
        refine ⟨107445952758182902517546315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71630635172121935011697543 107445952758182902517546315)
        ·
          refine ⟨161168929137274353776319473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107445952758182902517546315 161168929137274353776319473)
          ·
            refine ⟨120876696852955765332239605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161168929137274353776319473 120876696852955765332239605)
            ·
              refine ⟨11332190329964602999897463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120876696852955765332239605 11332190329964602999897463)
              ·
                refine ⟨16998285494946904499846195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11332190329964602999897463 16998285494946904499846195)
                ·
                  refine ⟨25497428242420356749769293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16998285494946904499846195 25497428242420356749769293)
                  ·
                    refine ⟨9561535590907633781163485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25497428242420356749769293 9561535590907633781163485)
                    ·
                      refine ⟨3585575846590362667936307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9561535590907633781163485 3585575846590362667936307)
                      ·
                        rfl

theorem cell23_6982884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 1, 3, 3].length) (baseStart_6982884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982884 prefixEnd_6982884 := by exact prefixLift 6982884
  have htrace : WordTrace (prefixWord ++ tailWord_6982884) baseStart_6982884 baseEnd_6982884 := by
    simpa [prefixWord, tailWord_6982884, baseEnd_6982884] using wordTrace_append hprefix tailTrace_6982884
  have hstable : (prefixWord ++ tailWord_6982884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982884).length < 2 ^ (prefixWord ++ tailWord_6982884).sum := by decide
  have hdescent : baseEnd_6982884 < baseStart_6982884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6982911 : List Nat := [1, 1, 2, 2, 1, 5, 2, 3, 1, 3, 2]
def baseStart_6982911 : Nat := 118140960795 + 6982911 * 2 ^ 59
def prefixEnd_6982911 : Nat := 4983230072969 + 3 ^ 40 * 6982911 * 2
def baseEnd_6982911 : Nat := 3585589710568034062298683

theorem tailTrace_6982911 : CollatzResearch.WordTrace tailWord_6982911 prefixEnd_6982911 3585589710568034062298683 := by
  unfold tailWord_6982911
  simp only [CollatzResearch.WordTrace]
  refine ⟨254687687605113508097268587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169791791736742338731512391 254687687605113508097268587)
  ·
    refine ⟨382031531407670262145902881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254687687605113508097268587 382031531407670262145902881)
    ·
      refine ⟨286523648555752696609427161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382031531407670262145902881 286523648555752696609427161)
      ·
        refine ⟨214892736416814522457070371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286523648555752696609427161 214892736416814522457070371)
        ·
          refine ⟨322339104625221783685605557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214892736416814522457070371 322339104625221783685605557)
          ·
            refine ⟨30219291058614542220525521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 322339104625221783685605557 30219291058614542220525521)
            ·
              refine ⟨22664468293960906665394141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30219291058614542220525521 22664468293960906665394141)
              ·
                refine ⟨8499175610235339999522803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22664468293960906665394141 8499175610235339999522803)
                ·
                  refine ⟨12748763415353009999284205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8499175610235339999522803 12748763415353009999284205)
                  ·
                    refine ⟨4780786280757378749731577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12748763415353009999284205 4780786280757378749731577)
                    ·
                      refine ⟨3585589710568034062298683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4780786280757378749731577 3585589710568034062298683)
                      ·
                        rfl

theorem cell23_6982911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 3, 2].length) (baseStart_6982911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6982911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6982911 prefixEnd_6982911 := by exact prefixLift 6982911
  have htrace : WordTrace (prefixWord ++ tailWord_6982911) baseStart_6982911 baseEnd_6982911 := by
    simpa [prefixWord, tailWord_6982911, baseEnd_6982911] using wordTrace_append hprefix tailTrace_6982911
  have hstable : (prefixWord ++ tailWord_6982911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6982911).length < 2 ^ (prefixWord ++ tailWord_6982911).sum := by decide
  have hdescent : baseEnd_6982911 < baseStart_6982911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6982911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983011 : List Nat := [1, 1, 1, 5, 2, 4, 1, 1, 2, 5]
def baseStart_6983011 : Nat := 118140960795 + 6983011 * 2 ^ 59
def prefixEnd_6983011 : Nat := 4983230072969 + 3 ^ 40 * 6983011 * 2
def baseEnd_6983011 : Nat := 1195213686211161223682741

theorem tailTrace_6983011 : CollatzResearch.WordTrace tailWord_6983011 prefixEnd_6983011 1195213686211161223682741 := by
  unfold tailWord_6983011
  simp only [CollatzResearch.WordTrace]
  refine ⟨254691334904751225175908887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169794223269834150117272591 254691334904751225175908887)
  ·
    refine ⟨382037002357126837763863331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254691334904751225175908887 382037002357126837763863331)
    ·
      refine ⟨573055503535690256645794997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382037002357126837763863331 573055503535690256645794997)
      ·
        refine ⟨53723953456470961560543281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 573055503535690256645794997 53723953456470961560543281)
        ·
          refine ⟨40292965092353221170407461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53723953456470961560543281 40292965092353221170407461)
          ·
            refine ⟨7554930954816228969451399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40292965092353221170407461 7554930954816228969451399)
            ·
              refine ⟨11332396432224343454177099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7554930954816228969451399 11332396432224343454177099)
              ·
                refine ⟨16998594648336515181265649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11332396432224343454177099 16998594648336515181265649)
                ·
                  refine ⟨12748945986252386385949237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16998594648336515181265649 12748945986252386385949237)
                  ·
                    refine ⟨1195213686211161223682741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12748945986252386385949237 1195213686211161223682741)
                    ·
                      rfl

theorem cell23_6983011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 5].length) (baseStart_6983011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983011 prefixEnd_6983011 := by exact prefixLift 6983011
  have htrace : WordTrace (prefixWord ++ tailWord_6983011) baseStart_6983011 baseEnd_6983011 := by
    simpa [prefixWord, tailWord_6983011, baseEnd_6983011] using wordTrace_append hprefix tailTrace_6983011
  have hstable : (prefixWord ++ tailWord_6983011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983011).length < 2 ^ (prefixWord ++ tailWord_6983011).sum := by decide
  have hdescent : baseEnd_6983011 < baseStart_6983011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983017 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 2, 3, 5]
def baseStart_6983017 : Nat := 118140960795 + 6983017 * 2 ^ 59
def prefixEnd_6983017 : Nat := 4983230072969 + 3 ^ 40 * 6983017 * 2
def baseEnd_6983017 : Nat := 3585644139517410647573195

theorem tailTrace_6983017 : CollatzResearch.WordTrace tailWord_6983017 prefixEnd_6983017 3585644139517410647573195 := by
  unfold tailWord_6983017
  simp only [CollatzResearch.WordTrace]
  refine ⟨254691553742729488200627305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169794369161819658800418203 254691553742729488200627305)
  ·
    refine ⟨191018665307047116150470479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254691553742729488200627305 191018665307047116150470479)
    ·
      refine ⟨286527997960570674225705719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191018665307047116150470479 286527997960570674225705719)
      ·
        refine ⟨429791996940856011338558579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286527997960570674225705719 429791996940856011338558579)
        ·
          refine ⟨644687995411284017007837869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429791996940856011338558579 644687995411284017007837869)
          ·
            refine ⟨241757998279231506377939201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 644687995411284017007837869 241757998279231506377939201)
            ·
              refine ⟨181318498709423629783454401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241757998279231506377939201 181318498709423629783454401)
              ·
                refine ⟨135988874032067722337590801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181318498709423629783454401 135988874032067722337590801)
                ·
                  refine ⟨101991655524050791753193101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135988874032067722337590801 101991655524050791753193101)
                  ·
                    refine ⟨38246870821519046907447413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101991655524050791753193101 38246870821519046907447413)
                    ·
                      refine ⟨3585644139517410647573195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38246870821519046907447413 3585644139517410647573195)
                      ·
                        rfl

theorem cell23_6983017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 3, 5].length) (baseStart_6983017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983017 prefixEnd_6983017 := by exact prefixLift 6983017
  have htrace : WordTrace (prefixWord ++ tailWord_6983017) baseStart_6983017 baseEnd_6983017 := by
    simpa [prefixWord, tailWord_6983017, baseEnd_6983017] using wordTrace_append hprefix tailTrace_6983017
  have hstable : (prefixWord ++ tailWord_6983017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983017).length < 2 ^ (prefixWord ++ tailWord_6983017).sum := by decide
  have hdescent : baseEnd_6983017 < baseStart_6983017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983024 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 5, 4]
def baseStart_6983024 : Nat := 118140960795 + 6983024 * 2 ^ 59
def prefixEnd_6983024 : Nat := 4983230072969 + 3 ^ 40 * 6983024 * 2
def baseEnd_6983024 : Nat := 1195215911293997373395221

theorem tailTrace_6983024 : CollatzResearch.WordTrace tailWord_6983024 prefixEnd_6983024 1195215911293997373395221 := by
  unfold tailWord_6983024
  simp only [CollatzResearch.WordTrace]
  refine ⟨127345904526852064198066063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169794539369136085597421417 127345904526852064198066063)
  ·
    refine ⟨191018856790278096297099095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127345904526852064198066063 191018856790278096297099095)
    ·
      refine ⟨286528285185417144445648643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191018856790278096297099095 286528285185417144445648643)
      ·
        refine ⟨429792427778125716668472965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286528285185417144445648643 429792427778125716668472965)
        ·
          refine ⟨80586080208398571875338681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 429792427778125716668472965 80586080208398571875338681)
          ·
            refine ⟨60439560156298928906504011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80586080208398571875338681 60439560156298928906504011)
            ·
              refine ⟨90659340234448393359756017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60439560156298928906504011 90659340234448393359756017)
              ·
                refine ⟨67994505175836295019817013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90659340234448393359756017 67994505175836295019817013)
                ·
                  refine ⟨6374484860234652658107845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67994505175836295019817013 6374484860234652658107845)
                  ·
                    refine ⟨1195215911293997373395221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6374484860234652658107845 1195215911293997373395221)
                    ·
                      rfl

theorem cell23_6983024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 5, 4].length) (baseStart_6983024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983024 prefixEnd_6983024 := by exact prefixLift 6983024
  have htrace : WordTrace (prefixWord ++ tailWord_6983024) baseStart_6983024 baseEnd_6983024 := by
    simpa [prefixWord, tailWord_6983024, baseEnd_6983024] using wordTrace_append hprefix tailTrace_6983024
  have hstable : (prefixWord ++ tailWord_6983024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983024).length < 2 ^ (prefixWord ++ tailWord_6983024).sum := by decide
  have hdescent : baseEnd_6983024 < baseStart_6983024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983158 : List Nat := [5, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3]
def baseStart_6983158 : Nat := 118140960795 + 6983158 * 2 ^ 59
def prefixEnd_6983158 : Nat := 4983230072969 + 3 ^ 40 * 6983158 * 2
def baseEnd_6983158 : Nat := 3585716540289694595910047

theorem tailTrace_6983158 : CollatzResearch.WordTrace tailWord_6983158 prefixEnd_6983158 3585716540289694595910047 := by
  unfold tailWord_6983158
  simp only [CollatzResearch.WordTrace]
  refine ⟨15918543527201166830094383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169797797623479112854340085 15918543527201166830094383)
  ·
    refine ⟨23877815290801750245141575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15918543527201166830094383 23877815290801750245141575)
    ·
      refine ⟨35816722936202625367712363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23877815290801750245141575 35816722936202625367712363)
      ·
        refine ⟨53725084404303938051568545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35816722936202625367712363 53725084404303938051568545)
        ·
          refine ⟨40293813303227953538676409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53725084404303938051568545 40293813303227953538676409)
          ·
            refine ⟨30220359977420965154007307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40293813303227953538676409 30220359977420965154007307)
            ·
              refine ⟨45330539966131447731010961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30220359977420965154007307 45330539966131447731010961)
              ·
                refine ⟨33997904974598585798258221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45330539966131447731010961 33997904974598585798258221)
                ·
                  refine ⟨12749214365474469674346833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33997904974598585798258221 12749214365474469674346833)
                  ·
                    refine ⟨9561910774105852255760125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12749214365474469674346833 9561910774105852255760125)
                    ·
                      refine ⟨3585716540289694595910047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9561910774105852255760125 3585716540289694595910047)
                      ·
                        rfl

theorem cell23_6983158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_6983158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983158 prefixEnd_6983158 := by exact prefixLift 6983158
  have htrace : WordTrace (prefixWord ++ tailWord_6983158) baseStart_6983158 baseEnd_6983158 := by
    simpa [prefixWord, tailWord_6983158, baseEnd_6983158] using wordTrace_append hprefix tailTrace_6983158
  have hstable : (prefixWord ++ tailWord_6983158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983158).length < 2 ^ (prefixWord ++ tailWord_6983158).sum := by decide
  have hdescent : baseEnd_6983158 < baseStart_6983158 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983164 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 6]
def baseStart_6983164 : Nat := 118140960795 + 6983164 * 2 ^ 59
def prefixEnd_6983164 : Nat := 4983230072969 + 3 ^ 40 * 6983164 * 2
def baseEnd_6983164 : Nat := 3585719621173621572435019

theorem tailTrace_6983164 : CollatzResearch.WordTrace tailWord_6983164 prefixEnd_6983164 3585719621173621572435019 := by
  unfold tailWord_6983164
  simp only [CollatzResearch.WordTrace]
  refine ⟨127348457636598466153114273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169797943515464621537485697 127348457636598466153114273)
  ·
    refine ⟨95511343227448849614835705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127348457636598466153114273 95511343227448849614835705)
    ·
      refine ⟨71633507420586637211126779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95511343227448849614835705 71633507420586637211126779)
      ·
        refine ⟨107450261130879955816690169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71633507420586637211126779 107450261130879955816690169)
        ·
          refine ⟨80587695848159966862517627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107450261130879955816690169 80587695848159966862517627)
          ·
            refine ⟨120881543772239950293776441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80587695848159966862517627 120881543772239950293776441)
            ·
              refine ⟨90661157829179962720332331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120881543772239950293776441 90661157829179962720332331)
              ·
                refine ⟨135991736743769944080498497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90661157829179962720332331 135991736743769944080498497)
                ·
                  refine ⟨101993802557827458060373873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135991736743769944080498497 101993802557827458060373873)
                  ·
                    refine ⟨76495351918370593545280405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101993802557827458060373873 76495351918370593545280405)
                    ·
                      refine ⟨3585719621173621572435019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76495351918370593545280405 3585719621173621572435019)
                      ·
                        rfl

theorem cell23_6983164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_6983164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983164 prefixEnd_6983164 := by exact prefixLift 6983164
  have htrace : WordTrace (prefixWord ++ tailWord_6983164) baseStart_6983164 baseEnd_6983164 := by
    simpa [prefixWord, tailWord_6983164, baseEnd_6983164] using wordTrace_append hprefix tailTrace_6983164
  have hstable : (prefixWord ++ tailWord_6983164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983164).length < 2 ^ (prefixWord ++ tailWord_6983164).sum := by decide
  have hdescent : baseEnd_6983164 < baseStart_6983164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983172 : List Nat := [2, 3, 2, 3, 2, 1, 1, 2, 3, 2, 2]
def baseStart_6983172 : Nat := 118140960795 + 6983172 * 2 ^ 59
def prefixEnd_6983172 : Nat := 4983230072969 + 3 ^ 40 * 6983172 * 2
def baseEnd_6983172 : Nat := 3585723729018857541134983

theorem tailTrace_6983172 : CollatzResearch.WordTrace tailWord_6983172 prefixEnd_6983172 3585723729018857541134983 := by
  unfold tailWord_6983172
  simp only [CollatzResearch.WordTrace]
  refine ⟨127348603528583974836259885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169798138038111966448346513 127348603528583974836259885)
  ·
    refine ⟨47755726323218990563597457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127348603528583974836259885 47755726323218990563597457)
    ·
      refine ⟨35816794742414242922698093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47755726323218990563597457 35816794742414242922698093)
      ·
        refine ⟨13431298028405341096011785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35816794742414242922698093 13431298028405341096011785)
        ·
          refine ⟨10073473521304005822008839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13431298028405341096011785 10073473521304005822008839)
          ·
            refine ⟨15110210281956008733013259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10073473521304005822008839 15110210281956008733013259)
            ·
              refine ⟨22665315422934013099519889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15110210281956008733013259 22665315422934013099519889)
              ·
                refine ⟨16998986567200509824639917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22665315422934013099519889 16998986567200509824639917)
                ·
                  refine ⟨6374619962700191184239969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16998986567200509824639917 6374619962700191184239969)
                  ·
                    refine ⟨4780964972025143388179977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6374619962700191184239969 4780964972025143388179977)
                    ·
                      refine ⟨3585723729018857541134983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4780964972025143388179977 3585723729018857541134983)
                      ·
                        rfl

theorem cell23_6983172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_6983172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983172 prefixEnd_6983172 := by exact prefixLift 6983172
  have htrace : WordTrace (prefixWord ++ tailWord_6983172) baseStart_6983172 baseEnd_6983172 := by
    simpa [prefixWord, tailWord_6983172, baseEnd_6983172] using wordTrace_append hprefix tailTrace_6983172
  have hstable : (prefixWord ++ tailWord_6983172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983172).length < 2 ^ (prefixWord ++ tailWord_6983172).sum := by decide
  have hdescent : baseEnd_6983172 < baseStart_6983172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983192 : List Nat := [2, 1, 2, 3, 4, 2, 2, 1, 1, 2, 3]
def baseStart_6983192 : Nat := 118140960795 + 6983192 * 2 ^ 59
def prefixEnd_6983192 : Nat := 4983230072969 + 3 ^ 40 * 6983192 * 2
def baseEnd_6983192 : Nat := 3585733998631947462884891

theorem tailTrace_6983192 : CollatzResearch.WordTrace tailWord_6983192 prefixEnd_6983192 3585733998631947462884891 := by
  unfold tailWord_6983192
  simp only [CollatzResearch.WordTrace]
  refine ⟨127348968258547746544123915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169798624344730328725498553 127348968258547746544123915)
  ·
    refine ⟨191023452387821619816185873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127348968258547746544123915 191023452387821619816185873)
    ·
      refine ⟨143267589290866214862139405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191023452387821619816185873 143267589290866214862139405)
      ·
        refine ⟨53725345984074830573302277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143267589290866214862139405 53725345984074830573302277)
        ·
          refine ⟨10073502372014030732494177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53725345984074830573302277 10073502372014030732494177)
          ·
            refine ⟨7555126779010523049370633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10073502372014030732494177 7555126779010523049370633)
            ·
              refine ⟨5666345084257892287027975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7555126779010523049370633 5666345084257892287027975)
              ·
                refine ⟨8499517626386838430541963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5666345084257892287027975 8499517626386838430541963)
                ·
                  refine ⟨12749276439580257645812945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8499517626386838430541963 12749276439580257645812945)
                  ·
                    refine ⟨9561957329685193234359709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12749276439580257645812945 9561957329685193234359709)
                    ·
                      refine ⟨3585733998631947462884891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9561957329685193234359709 3585733998631947462884891)
                      ·
                        rfl

theorem cell23_6983192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_6983192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983192 prefixEnd_6983192 := by exact prefixLift 6983192
  have htrace : WordTrace (prefixWord ++ tailWord_6983192) baseStart_6983192 baseEnd_6983192 := by
    simpa [prefixWord, tailWord_6983192, baseEnd_6983192] using wordTrace_append hprefix tailTrace_6983192
  have hstable : (prefixWord ++ tailWord_6983192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983192).length < 2 ^ (prefixWord ++ tailWord_6983192).sum := by decide
  have hdescent : baseEnd_6983192 < baseStart_6983192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983211 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 2, 8, 2]
def baseStart_6983211 : Nat := 118140960795 + 6983211 * 2 ^ 59
def prefixEnd_6983211 : Nat := 4983230072969 + 3 ^ 40 * 6983211 * 2
def baseEnd_6983211 : Nat := 3585743754764382888547303

theorem tailTrace_6983211 : CollatzResearch.WordTrace tailWord_6983211 prefixEnd_6983211 3585743754764382888547303 := by
  unfold tailWord_6983211
  simp only [CollatzResearch.WordTrace]
  refine ⟨254698629504026659333189487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169799086336017772888792991 254698629504026659333189487)
  ·
    refine ⟨382047944256039988999784231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254698629504026659333189487 382047944256039988999784231)
    ·
      refine ⟨573071916384059983499676347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382047944256039988999784231 573071916384059983499676347)
      ·
        refine ⟨859607874576089975249514521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573071916384059983499676347 859607874576089975249514521)
        ·
          refine ⟨644705905932067481437135891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 859607874576089975249514521 644705905932067481437135891)
          ·
            refine ⟨967058858898101222155703837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644705905932067481437135891 967058858898101222155703837)
            ·
              refine ⟨362647072086787958308388939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 967058858898101222155703837 362647072086787958308388939)
              ·
                refine ⟨543970608130181937462583409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362647072086787958308388939 543970608130181937462583409)
                ·
                  refine ⟨407977956097636453096937557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 543970608130181937462583409 407977956097636453096937557)
                  ·
                    refine ⟨4780991673019177184729737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 407977956097636453096937557 4780991673019177184729737)
                    ·
                      refine ⟨3585743754764382888547303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4780991673019177184729737 3585743754764382888547303)
                      ·
                        rfl

theorem cell23_6983211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 8, 2].length) (baseStart_6983211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983211 prefixEnd_6983211 := by exact prefixLift 6983211
  have htrace : WordTrace (prefixWord ++ tailWord_6983211) baseStart_6983211 baseEnd_6983211 := by
    simpa [prefixWord, tailWord_6983211, baseEnd_6983211] using wordTrace_append hprefix tailTrace_6983211
  have hstable : (prefixWord ++ tailWord_6983211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983211).length < 2 ^ (prefixWord ++ tailWord_6983211).sum := by decide
  have hdescent : baseEnd_6983211 < baseStart_6983211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983221 : List Nat := [1, 3, 3, 1, 1, 3, 2, 1, 2, 6]
def baseStart_6983221 : Nat := 118140960795 + 6983221 * 2 ^ 59
def prefixEnd_6983221 : Nat := 4983230072969 + 3 ^ 40 * 6983221 * 2
def baseEnd_6983221 : Nat := 1195249629856975949807419

theorem tailTrace_6983221 : CollatzResearch.WordTrace tailWord_6983221 prefixEnd_6983221 1195249629856975949807419 := by
  unfold tailWord_6983221
  simp only [CollatzResearch.WordTrace]
  refine ⟨254698994233990431041053517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169799329489326954027369011 254698994233990431041053517)
  ·
    refine ⟨95512122837746411640395069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254698994233990431041053517 95512122837746411640395069)
    ·
      refine ⟨35817046064154904365148151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95512122837746411640395069 35817046064154904365148151)
      ·
        refine ⟨53725569096232356547722227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35817046064154904365148151 53725569096232356547722227)
        ·
          refine ⟨80588353644348534821583341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53725569096232356547722227 80588353644348534821583341)
          ·
            refine ⟨30220632616630700558093753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80588353644348534821583341 30220632616630700558093753)
            ·
              refine ⟨22665474462473025418570315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30220632616630700558093753 22665474462473025418570315)
              ·
                refine ⟨33998211693709538127855473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22665474462473025418570315 33998211693709538127855473)
                ·
                  refine ⟨25498658770282153595891605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33998211693709538127855473 25498658770282153595891605)
                  ·
                    refine ⟨1195249629856975949807419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25498658770282153595891605 1195249629856975949807419)
                    ·
                      rfl

theorem cell23_6983221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_6983221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983221 prefixEnd_6983221 := by exact prefixLift 6983221
  have htrace : WordTrace (prefixWord ++ tailWord_6983221) baseStart_6983221 baseEnd_6983221 := by
    simpa [prefixWord, tailWord_6983221, baseEnd_6983221] using wordTrace_append hprefix tailTrace_6983221
  have hstable : (prefixWord ++ tailWord_6983221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983221).length < 2 ^ (prefixWord ++ tailWord_6983221).sum := by decide
  have hdescent : baseEnd_6983221 < baseStart_6983221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983222 : List Nat := [5, 1, 2, 1, 3, 2, 1, 1, 1, 3, 3]
def baseStart_6983222 : Nat := 118140960795 + 6983222 * 2 ^ 59
def prefixEnd_6983222 : Nat := 4983230072969 + 3 ^ 40 * 6983222 * 2
def baseEnd_6983222 : Nat := 3585749403051582345509753

theorem tailTrace_6983222 : CollatzResearch.WordTrace tailWord_6983222 prefixEnd_6983222 3585749403051582345509753 := by
  unfold tailWord_6983222
  simp only [CollatzResearch.WordTrace]
  refine ⟨15918689419186675513239995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169799353804657872141226613 15918689419186675513239995)
  ·
    refine ⟨23878034128780013269859993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15918689419186675513239995 23878034128780013269859993)
    ·
      refine ⟨17908525596585009952394995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23878034128780013269859993 17908525596585009952394995)
      ·
        refine ⟨26862788394877514928592493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17908525596585009952394995 26862788394877514928592493)
        ·
          refine ⟨10073545648079068098222185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26862788394877514928592493 10073545648079068098222185)
          ·
            refine ⟨7555159236059301073666639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10073545648079068098222185 7555159236059301073666639)
            ·
              refine ⟨11332738854088951610499959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7555159236059301073666639 11332738854088951610499959)
              ·
                refine ⟨16999108281133427415749939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11332738854088951610499959 16999108281133427415749939)
                ·
                  refine ⟨25498662421700141123624909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16999108281133427415749939 25498662421700141123624909)
                  ·
                    refine ⟨9561998408137552921359341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25498662421700141123624909 9561998408137552921359341)
                    ·
                      refine ⟨3585749403051582345509753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9561998408137552921359341 3585749403051582345509753)
                      ·
                        rfl

theorem cell23_6983222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_6983222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983222 prefixEnd_6983222 := by exact prefixLift 6983222
  have htrace : WordTrace (prefixWord ++ tailWord_6983222) baseStart_6983222 baseEnd_6983222 := by
    simpa [prefixWord, tailWord_6983222, baseEnd_6983222] using wordTrace_append hprefix tailTrace_6983222
  have hstable : (prefixWord ++ tailWord_6983222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983222).length < 2 ^ (prefixWord ++ tailWord_6983222).sum := by decide
  have hdescent : baseEnd_6983222 < baseStart_6983222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983268 : List Nat := [2, 3, 1, 1, 2, 5, 1, 1, 7]
def baseStart_6983268 : Nat := 118140960795 + 6983268 * 2 ^ 59
def prefixEnd_6983268 : Nat := 4983230072969 + 3 ^ 40 * 6983268 * 2
def baseEnd_6983268 : Nat := 398419224795743240614949

theorem tailTrace_6983268 : CollatzResearch.WordTrace tailWord_6983268 prefixEnd_6983268 398419224795743240614949 := by
  unfold tailWord_6983268
  simp only [CollatzResearch.WordTrace]
  refine ⟨127350354232410079034007229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169800472309880105378676305 127350354232410079034007229)
  ·
    refine ⟨47756382837153779637752711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127350354232410079034007229 47756382837153779637752711)
    ·
      refine ⟨71634574255730669456629067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47756382837153779637752711 71634574255730669456629067)
      ·
        refine ⟨107451861383596004184943601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71634574255730669456629067 107451861383596004184943601)
        ·
          refine ⟨80588896037697003138707701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107451861383596004184943601 80588896037697003138707701)
          ·
            refine ⟨7555209003534094044253847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80588896037697003138707701 7555209003534094044253847)
            ·
              refine ⟨11332813505301141066380771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7555209003534094044253847 11332813505301141066380771)
              ·
                refine ⟨16999220257951711599571157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11332813505301141066380771 16999220257951711599571157)
                ·
                  refine ⟨398419224795743240614949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16999220257951711599571157 398419224795743240614949)
                  ·
                    rfl

theorem cell23_6983268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 7].length) (baseStart_6983268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983268 prefixEnd_6983268 := by exact prefixLift 6983268
  have htrace : WordTrace (prefixWord ++ tailWord_6983268) baseStart_6983268 baseEnd_6983268 := by
    simpa [prefixWord, tailWord_6983268, baseEnd_6983268] using wordTrace_append hprefix tailTrace_6983268
  have hstable : (prefixWord ++ tailWord_6983268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983268).length < 2 ^ (prefixWord ++ tailWord_6983268).sum := by decide
  have hdescent : baseEnd_6983268 < baseStart_6983268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983378 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_6983378 : Nat := 118140960795 + 6983378 * 2 ^ 59
def prefixEnd_6983378 : Nat := 4983230072969 + 3 ^ 40 * 6983378 * 2
def baseEnd_6983378 : Nat := 3585829506033683735159035

theorem tailTrace_6983378 : CollatzResearch.WordTrace tailWord_6983378 prefixEnd_6983378 3585829506033683735159035 := by
  unfold tailWord_6983378
  simp only [CollatzResearch.WordTrace]
  refine ⟨63676180123605411713629697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169803146996281097903012525 63676180123605411713629697)
  ·
    refine ⟨47757135092704058785222273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63676180123605411713629697 47757135092704058785222273)
    ·
      refine ⟨35817851319528044088916705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47757135092704058785222273 35817851319528044088916705)
      ·
        refine ⟨26863388489646033066687529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35817851319528044088916705 26863388489646033066687529)
        ·
          refine ⟨20147541367234524800015647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26863388489646033066687529 20147541367234524800015647)
          ·
            refine ⟨30221312050851787200023471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20147541367234524800015647 30221312050851787200023471)
            ·
              refine ⟨45331968076277680800035207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30221312050851787200023471 45331968076277680800035207)
              ·
                refine ⟨67997952114416521200052811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45331968076277680800035207 67997952114416521200052811)
                ·
                  refine ⟨101996928171624781800079217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67997952114416521200052811 101996928171624781800079217)
                  ·
                    refine ⟨76497696128718586350059413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101996928171624781800079217 76497696128718586350059413)
                    ·
                      refine ⟨3585829506033683735159035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76497696128718586350059413 3585829506033683735159035)
                      ·
                        rfl

theorem cell23_6983378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_6983378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983378 prefixEnd_6983378 := by exact prefixLift 6983378
  have htrace : WordTrace (prefixWord ++ tailWord_6983378) baseStart_6983378 baseEnd_6983378 := by
    simpa [prefixWord, tailWord_6983378, baseEnd_6983378] using wordTrace_append hprefix tailTrace_6983378
  have hstable : (prefixWord ++ tailWord_6983378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983378).length < 2 ^ (prefixWord ++ tailWord_6983378).sum := by decide
  have hdescent : baseEnd_6983378 < baseStart_6983378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983385 : List Nat := [1, 2, 1, 2, 3, 3, 1, 3, 3, 1, 3]
def baseStart_6983385 : Nat := 118140960795 + 6983385 * 2 ^ 59
def prefixEnd_6983385 : Nat := 4983230072969 + 3 ^ 40 * 6983385 * 2
def baseEnd_6983385 : Nat := 3585833100398265207771503

theorem tailTrace_6983385 : CollatzResearch.WordTrace tailWord_6983385 prefixEnd_6983385 3585833100398265207771503 := by
  unfold tailWord_6983385
  simp only [CollatzResearch.WordTrace]
  refine ⟨254704975805396287050023609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169803317203597524700015739 254704975805396287050023609)
  ·
    refine ⟨191028731854047215287517707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254704975805396287050023609 191028731854047215287517707)
    ·
      refine ⟨286543097781070822931276561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191028731854047215287517707 286543097781070822931276561)
      ·
        refine ⟨214907323335803117198457421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286543097781070822931276561 214907323335803117198457421)
        ·
          refine ⟨80590246250926168949421533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 214907323335803117198457421 80590246250926168949421533)
          ·
            refine ⟨30221342344097313356033075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80590246250926168949421533 30221342344097313356033075)
            ·
              refine ⟨45332013516145970034049613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30221342344097313356033075 45332013516145970034049613)
              ·
                refine ⟨16999505068554738762768605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45332013516145970034049613 16999505068554738762768605)
                ·
                  refine ⟨6374814400708027036038227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16999505068554738762768605 6374814400708027036038227)
                  ·
                    refine ⟨9562221601062040554057341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6374814400708027036038227 9562221601062040554057341)
                    ·
                      refine ⟨3585833100398265207771503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9562221601062040554057341 3585833100398265207771503)
                      ·
                        rfl

theorem cell23_6983385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3, 1, 3].length) (baseStart_6983385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983385 prefixEnd_6983385 := by exact prefixLift 6983385
  have htrace : WordTrace (prefixWord ++ tailWord_6983385) baseStart_6983385 baseEnd_6983385 := by
    simpa [prefixWord, tailWord_6983385, baseEnd_6983385] using wordTrace_append hprefix tailTrace_6983385
  have hstable : (prefixWord ++ tailWord_6983385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983385).length < 2 ^ (prefixWord ++ tailWord_6983385).sum := by decide
  have hdescent : baseEnd_6983385 < baseStart_6983385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983405 : List Nat := [1, 5, 1, 2, 1, 2, 1, 4, 1, 5]
def baseStart_6983405 : Nat := 118140960795 + 6983405 * 2 ^ 59
def prefixEnd_6983405 : Nat := 4983230072969 + 3 ^ 40 * 6983405 * 2
def baseEnd_6983405 : Nat := 1195281123337118376507137

theorem tailTrace_6983405 : CollatzResearch.WordTrace tailWord_6983405 prefixEnd_6983405 1195281123337118376507137 := by
  unfold tailWord_6983405
  simp only [CollatzResearch.WordTrace]
  refine ⟨254705705265323830465751669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169803803510215886977167779 254705705265323830465751669)
  ·
    refine ⟨23878659868624109106164219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 254705705265323830465751669 23878659868624109106164219)
    ·
      refine ⟨35817989802936163659246329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23878659868624109106164219 35817989802936163659246329)
      ·
        refine ⟨26863492352202122744434747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35817989802936163659246329 26863492352202122744434747)
        ·
          refine ⟨40295238528303184116652121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26863492352202122744434747 40295238528303184116652121)
          ·
            refine ⟨30221428896227388087489091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40295238528303184116652121 30221428896227388087489091)
            ·
              refine ⟨45332143344341082131233637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30221428896227388087489091 45332143344341082131233637)
              ·
                refine ⟨8499776877063952899606307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45332143344341082131233637 8499776877063952899606307)
                ·
                  refine ⟨12749665315595929349409461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8499776877063952899606307 12749665315595929349409461)
                  ·
                    refine ⟨1195281123337118376507137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12749665315595929349409461 1195281123337118376507137)
                    ·
                      rfl

theorem cell23_6983405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_6983405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983405 prefixEnd_6983405 := by exact prefixLift 6983405
  have htrace : WordTrace (prefixWord ++ tailWord_6983405) baseStart_6983405 baseEnd_6983405 := by
    simpa [prefixWord, tailWord_6983405, baseEnd_6983405] using wordTrace_append hprefix tailTrace_6983405
  have hstable : (prefixWord ++ tailWord_6983405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983405).length < 2 ^ (prefixWord ++ tailWord_6983405).sum := by decide
  have hdescent : baseEnd_6983405 < baseStart_6983405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983425 : List Nat := [1, 2, 4, 1, 1, 1, 4, 3, 1, 1, 4]
def baseStart_6983425 : Nat := 118140960795 + 6983425 * 2 ^ 59
def prefixEnd_6983425 : Nat := 4983230072969 + 3 ^ 40 * 6983425 * 2
def baseEnd_6983425 : Nat := 3585853639624445051271319

theorem tailTrace_6983425 : CollatzResearch.WordTrace tailWord_6983425 prefixEnd_6983425 3585853639624445051271319 := by
  unfold tailWord_6983425
  simp only [CollatzResearch.WordTrace]
  refine ⟨254706434725251373881479729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169804289816834249254319819 254706434725251373881479729)
  ·
    refine ⟨191029826043938530411109797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254706434725251373881479729 191029826043938530411109797)
    ·
      refine ⟨35818092383238474452083087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191029826043938530411109797 35818092383238474452083087)
      ·
        refine ⟨53727138574857711678124631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35818092383238474452083087 53727138574857711678124631)
        ·
          refine ⟨80590707862286567517186947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53727138574857711678124631 80590707862286567517186947)
          ·
            refine ⟨120886061793429851275780421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80590707862286567517186947 120886061793429851275780421)
            ·
              refine ⟨22666136586268097114208829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120886061793429851275780421 22666136586268097114208829)
              ·
                refine ⟨8499801219850536417828311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22666136586268097114208829 8499801219850536417828311)
                ·
                  refine ⟨12749701829775804626742467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8499801219850536417828311 12749701829775804626742467)
                  ·
                    refine ⟨19124552744663706940113701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12749701829775804626742467 19124552744663706940113701)
                    ·
                      refine ⟨3585853639624445051271319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19124552744663706940113701 3585853639624445051271319)
                      ·
                        rfl

theorem cell23_6983425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_6983425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983425 prefixEnd_6983425 := by exact prefixLift 6983425
  have htrace : WordTrace (prefixWord ++ tailWord_6983425) baseStart_6983425 baseEnd_6983425 := by
    simpa [prefixWord, tailWord_6983425, baseEnd_6983425] using wordTrace_append hprefix tailTrace_6983425
  have hstable : (prefixWord ++ tailWord_6983425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983425).length < 2 ^ (prefixWord ++ tailWord_6983425).sum := by decide
  have hdescent : baseEnd_6983425 < baseStart_6983425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983430 : List Nat := [6, 2, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_6983430 : Nat := 118140960795 + 6983430 * 2 ^ 59
def prefixEnd_6983430 : Nat := 4983230072969 + 3 ^ 40 * 6983430 * 2
def baseEnd_6983430 : Nat := 1195285402342572510569599

theorem tailTrace_6983430 : CollatzResearch.WordTrace tailWord_6983430 prefixEnd_6983430 1195285402342572510569599 := by
  unfold tailWord_6983430
  simp only [CollatzResearch.WordTrace]
  refine ⟨7959581784069789366731617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 169804411393488839823607829 7959581784069789366731617)
  ·
    refine ⟨5969686338052342025048713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7959581784069789366731617 5969686338052342025048713)
    ·
      refine ⟨4477264753539256518786535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5969686338052342025048713 4477264753539256518786535)
      ·
        refine ⟨6715897130308884778179803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4477264753539256518786535 6715897130308884778179803)
        ·
          refine ⟨10073845695463327167269705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6715897130308884778179803 10073845695463327167269705)
          ·
            refine ⟨7555384271597495375452279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10073845695463327167269705 7555384271597495375452279)
            ·
              refine ⟨11333076407396243063178419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7555384271597495375452279 11333076407396243063178419)
              ·
                refine ⟨16999614611094364594767629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11333076407396243063178419 16999614611094364594767629)
                ·
                  refine ⟨6374855479160386723037861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16999614611094364594767629 6374855479160386723037861)
                  ·
                    refine ⟨1195285402342572510569599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6374855479160386723037861 1195285402342572510569599)
                    ·
                      rfl

theorem cell23_6983430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_6983430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983430 prefixEnd_6983430 := by exact prefixLift 6983430
  have htrace : WordTrace (prefixWord ++ tailWord_6983430) baseStart_6983430 baseEnd_6983430 := by
    simpa [prefixWord, tailWord_6983430, baseEnd_6983430] using wordTrace_append hprefix tailTrace_6983430
  have hstable : (prefixWord ++ tailWord_6983430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983430).length < 2 ^ (prefixWord ++ tailWord_6983430).sum := by decide
  have hdescent : baseEnd_6983430 < baseStart_6983430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983438 : List Nat := [4, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6]
def baseStart_6983438 : Nat := 118140960795 + 6983438 * 2 ^ 59
def prefixEnd_6983438 : Nat := 4983230072969 + 3 ^ 40 * 6983438 * 2
def baseEnd_6983438 : Nat := 3585860314872953500408759

theorem tailTrace_6983438 : CollatzResearch.WordTrace tailWord_6983438 prefixEnd_6983438 3585860314872953500408759 := by
  unfold tailWord_6983438
  simp only [CollatzResearch.WordTrace]
  refine ⟨31838363609275534637712871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169804605916136184734468645 31838363609275534637712871)
  ·
    refine ⟨47757545413913301956569307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31838363609275534637712871 47757545413913301956569307)
    ·
      refine ⟨71636318120869952934853961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47757545413913301956569307 71636318120869952934853961)
      ·
        refine ⟨53727238590652464701140471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71636318120869952934853961 53727238590652464701140471)
        ·
          refine ⟨80590857885978697051710707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53727238590652464701140471 80590857885978697051710707)
          ·
            refine ⟨120886286828968045577566061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80590857885978697051710707 120886286828968045577566061)
            ·
              refine ⟨45332357560863017091587273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120886286828968045577566061 45332357560863017091587273)
              ·
                refine ⟨33999268170647262818690455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45332357560863017091587273 33999268170647262818690455)
                ·
                  refine ⟨50998902255970894228035683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33999268170647262818690455 50998902255970894228035683)
                  ·
                    refine ⟨76498353383956341342053525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50998902255970894228035683 76498353383956341342053525)
                    ·
                      refine ⟨3585860314872953500408759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76498353383956341342053525 3585860314872953500408759)
                      ·
                        rfl

theorem cell23_6983438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_6983438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983438 prefixEnd_6983438 := by exact prefixLift 6983438
  have htrace : WordTrace (prefixWord ++ tailWord_6983438) baseStart_6983438 baseEnd_6983438 := by
    simpa [prefixWord, tailWord_6983438, baseEnd_6983438] using wordTrace_append hprefix tailTrace_6983438
  have hstable : (prefixWord ++ tailWord_6983438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983438).length < 2 ^ (prefixWord ++ tailWord_6983438).sum := by decide
  have hdescent : baseEnd_6983438 < baseStart_6983438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983498 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 1, 5, 4]
def baseStart_6983498 : Nat := 118140960795 + 6983498 * 2 ^ 59
def prefixEnd_6983498 : Nat := 4983230072969 + 3 ^ 40 * 6983498 * 2
def baseEnd_6983498 : Nat := 3585891123712223265658483

theorem tailTrace_6983498 : CollatzResearch.WordTrace tailWord_6983498 prefixEnd_6983498 3585891123712223265658483 := by
  unfold tailWord_6983498
  simp only [CollatzResearch.WordTrace]
  refine ⟨63677274313496726837221787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169806064835991271565924765 63677274313496726837221787)
  ·
    refine ⟨95515911470245090255832681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63677274313496726837221787 95515911470245090255832681)
    ·
      refine ⟨71636933602683817691874511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95515911470245090255832681 71636933602683817691874511)
      ·
        refine ⟨107455400404025726537811767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71636933602683817691874511 107455400404025726537811767)
        ·
          refine ⟨161183100606038589806717651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107455400404025726537811767 161183100606038589806717651)
          ·
            refine ⟨241774650909057884710076477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161183100606038589806717651 241774650909057884710076477)
            ·
              refine ⟨90665494090896706766278679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241774650909057884710076477 90665494090896706766278679)
              ·
                refine ⟨135998241136345060149418019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90665494090896706766278679 135998241136345060149418019)
                ·
                  refine ⟨203997361704517590224127029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135998241136345060149418019 203997361704517590224127029)
                  ·
                    refine ⟨19124752659798524083511909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 203997361704517590224127029 19124752659798524083511909)
                    ·
                      refine ⟨3585891123712223265658483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19124752659798524083511909 3585891123712223265658483)
                      ·
                        rfl

theorem cell23_6983498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_6983498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983498 prefixEnd_6983498 := by exact prefixLift 6983498
  have htrace : WordTrace (prefixWord ++ tailWord_6983498) baseStart_6983498 baseEnd_6983498 := by
    simpa [prefixWord, tailWord_6983498, baseEnd_6983498] using wordTrace_append hprefix tailTrace_6983498
  have hstable : (prefixWord ++ tailWord_6983498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983498).length < 2 ^ (prefixWord ++ tailWord_6983498).sum := by decide
  have hdescent : baseEnd_6983498 < baseStart_6983498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983532 : List Nat := [2, 2, 1, 1, 4, 2, 2, 2, 1, 4, 2]
def baseStart_6983532 : Nat := 118140960795 + 6983532 * 2 ^ 59
def prefixEnd_6983532 : Nat := 4983230072969 + 3 ^ 40 * 6983532 * 2
def baseEnd_6983532 : Nat := 3585908582054476132633327

theorem tailTrace_6983532 : CollatzResearch.WordTrace tailWord_6983532 prefixEnd_6983532 3585908582054476132633327 := by
  unfold tailWord_6983532
  simp only [CollatzResearch.WordTrace]
  refine ⟨127355168667931865577812425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169806891557242487437083233 127355168667931865577812425)
  ·
    refine ⟨95516376500948899183359319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127355168667931865577812425 95516376500948899183359319)
    ·
      refine ⟨143274564751423348775038979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95516376500948899183359319 143274564751423348775038979)
      ·
        refine ⟨214911847127135023162558469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143274564751423348775038979 214911847127135023162558469)
        ·
          refine ⟨40295971336337816842979713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214911847127135023162558469 40295971336337816842979713)
          ·
            refine ⟨30221978502253362632234785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40295971336337816842979713 30221978502253362632234785)
            ·
              refine ⟨22666483876690021974176089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30221978502253362632234785 22666483876690021974176089)
              ·
                refine ⟨16999862907517516480632067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22666483876690021974176089 16999862907517516480632067)
                ·
                  refine ⟨25499794361276274720948101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16999862907517516480632067 25499794361276274720948101)
                  ·
                    refine ⟨4781211442739301510177769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25499794361276274720948101 4781211442739301510177769)
                    ·
                      refine ⟨3585908582054476132633327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4781211442739301510177769 3585908582054476132633327)
                      ·
                        rfl

theorem cell23_6983532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 4, 2].length) (baseStart_6983532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983532 prefixEnd_6983532 := by exact prefixLift 6983532
  have htrace : WordTrace (prefixWord ++ tailWord_6983532) baseStart_6983532 baseEnd_6983532 := by
    simpa [prefixWord, tailWord_6983532, baseEnd_6983532] using wordTrace_append hprefix tailTrace_6983532
  have hstable : (prefixWord ++ tailWord_6983532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983532).length < 2 ^ (prefixWord ++ tailWord_6983532).sum := by decide
  have hdescent : baseEnd_6983532 < baseStart_6983532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983538 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 11]
def baseStart_6983538 : Nat := 118140960795 + 6983538 * 2 ^ 59
def prefixEnd_6983538 : Nat := 4983230072969 + 3 ^ 40 * 6983538 * 2
def baseEnd_6983538 : Nat := 398434629215378123239811

theorem tailTrace_6983538 : CollatzResearch.WordTrace tailWord_6983538 prefixEnd_6983538 398434629215378123239811 := by
  unfold tailWord_6983538
  simp only [CollatzResearch.WordTrace]
  refine ⟨63677639043460498545085817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169807037449227996120228845 63677639043460498545085817)
  ·
    refine ⟨47758229282595373908814363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63677639043460498545085817 47758229282595373908814363)
    ·
      refine ⟨71637343923893060863221545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47758229282595373908814363 71637343923893060863221545)
      ·
        refine ⟨53728007942919795647416159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71637343923893060863221545 53728007942919795647416159)
        ·
          refine ⟨80592011914379693471124239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53728007942919795647416159 80592011914379693471124239)
          ·
            refine ⟨120888017871569540206686359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80592011914379693471124239 120888017871569540206686359)
            ·
              refine ⟨181332026807354310310029539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120888017871569540206686359 181332026807354310310029539)
              ·
                refine ⟨271998040211031465465044309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181332026807354310310029539 271998040211031465465044309)
                ·
                  refine ⟨398434629215378123239811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 271998040211031465465044309 398434629215378123239811)
                  ·
                    rfl

theorem cell23_6983538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_6983538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983538 prefixEnd_6983538 := by exact prefixLift 6983538
  have htrace : WordTrace (prefixWord ++ tailWord_6983538) baseStart_6983538 baseEnd_6983538 := by
    simpa [prefixWord, tailWord_6983538, baseEnd_6983538] using wordTrace_append hprefix tailTrace_6983538
  have hstable : (prefixWord ++ tailWord_6983538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983538).length < 2 ^ (prefixWord ++ tailWord_6983538).sum := by decide
  have hdescent : baseEnd_6983538 < baseStart_6983538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983555 : List Nat := [1, 1, 1, 3, 4, 3, 2, 1, 7]
def baseStart_6983555 : Nat := 118140960795 + 6983555 * 2 ^ 59
def prefixEnd_6983555 : Nat := 4983230072969 + 3 ^ 40 * 6983555 * 2
def baseEnd_6983555 : Nat := 398435599123281060293969

theorem tailTrace_6983555 : CollatzResearch.WordTrace tailWord_6983555 prefixEnd_6983555 398435599123281060293969 := by
  unfold tailWord_6983555
  simp only [CollatzResearch.WordTrace]
  refine ⟨254711176214780406083712119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169807450809853604055808079 254711176214780406083712119)
  ·
    refine ⟨382066764322170609125568179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254711176214780406083712119 382066764322170609125568179)
    ·
      refine ⟨573100146483255913688352269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382066764322170609125568179 573100146483255913688352269)
      ·
        refine ⟨214912554931220967633132101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 573100146483255913688352269 214912554931220967633132101)
        ·
          refine ⟨40296104049603931431212269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214912554931220967633132101 40296104049603931431212269)
          ·
            refine ⟨15111039018601474286704601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40296104049603931431212269 15111039018601474286704601)
            ·
              refine ⟨11333279263951105715028451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15111039018601474286704601 11333279263951105715028451)
              ·
                refine ⟨16999918895926658572542677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11333279263951105715028451 16999918895926658572542677)
                ·
                  refine ⟨398435599123281060293969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16999918895926658572542677 398435599123281060293969)
                  ·
                    rfl

theorem cell23_6983555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 7].length) (baseStart_6983555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983555 prefixEnd_6983555 := by exact prefixLift 6983555
  have htrace : WordTrace (prefixWord ++ tailWord_6983555) baseStart_6983555 baseEnd_6983555 := by
    simpa [prefixWord, tailWord_6983555, baseEnd_6983555] using wordTrace_append hprefix tailTrace_6983555
  have hstable : (prefixWord ++ tailWord_6983555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983555).length < 2 ^ (prefixWord ++ tailWord_6983555).sum := by decide
  have hdescent : baseEnd_6983555 < baseStart_6983555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983568 : List Nat := [2, 1, 1, 1, 1, 1, 2, 6, 1, 7]
def baseStart_6983568 : Nat := 118140960795 + 6983568 * 2 ^ 59
def prefixEnd_6983568 : Nat := 4983230072969 + 3 ^ 40 * 6983568 * 2
def baseEnd_6983568 : Nat := 1195309022452679330594387

theorem tailTrace_6983568 : CollatzResearch.WordTrace tailWord_6983568 prefixEnd_6983568 1195309022452679330594387 := by
  unfold tailWord_6983568
  simp only [CollatzResearch.WordTrace]
  refine ⟨127355825181866654651967679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169807766909155539535956905 127355825181866654651967679)
  ·
    refine ⟨191033737772799981977951519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127355825181866654651967679 191033737772799981977951519)
    ·
      refine ⟨286550606659199972966927279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191033737772799981977951519 286550606659199972966927279)
      ·
        refine ⟨429825909988799959450390919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286550606659199972966927279 429825909988799959450390919)
        ·
          refine ⟨644738864983199939175586379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429825909988799959450390919 644738864983199939175586379)
          ·
            refine ⟨967108297474799908763379569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644738864983199939175586379 967108297474799908763379569)
            ·
              refine ⟨725331223106099931572534677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 967108297474799908763379569 725331223106099931572534677)
              ·
                refine ⟨33999901083098434292462563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 725331223106099931572534677 33999901083098434292462563)
                ·
                  refine ⟨50999851624647651438693845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33999901083098434292462563 50999851624647651438693845)
                  ·
                    refine ⟨1195309022452679330594387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50999851624647651438693845 1195309022452679330594387)
                    ·
                      rfl

theorem cell23_6983568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 1, 7].length) (baseStart_6983568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983568 prefixEnd_6983568 := by exact prefixLift 6983568
  have htrace : WordTrace (prefixWord ++ tailWord_6983568) baseStart_6983568 baseEnd_6983568 := by
    simpa [prefixWord, tailWord_6983568, baseEnd_6983568] using wordTrace_append hprefix tailTrace_6983568
  have hstable : (prefixWord ++ tailWord_6983568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983568).length < 2 ^ (prefixWord ++ tailWord_6983568).sum := by decide
  have hdescent : baseEnd_6983568 < baseStart_6983568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983662 : List Nat := [4, 1, 2, 1, 3, 1, 1, 4, 6]
def baseStart_6983662 : Nat := 118140960795 + 6983662 * 2 ^ 59
def prefixEnd_6983662 : Nat := 4983230072969 + 3 ^ 40 * 6983662 * 2
def baseEnd_6983662 : Nat := 398441703837728958223081

theorem tailTrace_6983662 : CollatzResearch.WordTrace tailWord_6983662 prefixEnd_6983662 398441703837728958223081 := by
  unfold tailWord_6983662
  simp only [CollatzResearch.WordTrace]
  refine ⟨31839384853174095419732155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169810052550261842238571493 31839384853174095419732155)
  ·
    refine ⟨47759077279761143129598233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31839384853174095419732155 47759077279761143129598233)
    ·
      refine ⟨35819307959820857347198675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47759077279761143129598233 35819307959820857347198675)
      ·
        refine ⟨53728961939731286020798013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35819307959820857347198675 53728961939731286020798013)
        ·
          refine ⟨20148360727399232257799255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53728961939731286020798013 20148360727399232257799255)
          ·
            refine ⟨30222541091098848386698883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20148360727399232257799255 30222541091098848386698883)
            ·
              refine ⟨45333811636648272580048325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30222541091098848386698883 45333811636648272580048325)
              ·
                refine ⟨8500089681871551108759061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45333811636648272580048325 8500089681871551108759061)
                ·
                  refine ⟨398441703837728958223081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8500089681871551108759061 398441703837728958223081)
                  ·
                    rfl

theorem cell23_6983662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 6].length) (baseStart_6983662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983662 prefixEnd_6983662 := by exact prefixLift 6983662
  have htrace : WordTrace (prefixWord ++ tailWord_6983662) baseStart_6983662 baseEnd_6983662 := by
    simpa [prefixWord, tailWord_6983662, baseEnd_6983662] using wordTrace_append hprefix tailTrace_6983662
  have hstable : (prefixWord ++ tailWord_6983662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983662).length < 2 ^ (prefixWord ++ tailWord_6983662).sum := by decide
  have hdescent : baseEnd_6983662 < baseStart_6983662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983675 : List Nat := [1, 1, 1, 1, 1, 3, 5, 2, 3, 5]
def baseStart_6983675 : Nat := 118140960795 + 6983675 * 2 ^ 59
def prefixEnd_6983675 : Nat := 4983230072969 + 3 ^ 40 * 6983675 * 2
def baseEnd_6983675 : Nat := 1195327336596023024381723

theorem tailTrace_6983675 : CollatzResearch.WordTrace tailWord_6983675 prefixEnd_6983675 1195327336596023024381723 := by
  unfold tailWord_6983675
  simp only [CollatzResearch.WordTrace]
  refine ⟨254715552974345666578080479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169810368649563777718720319 254715552974345666578080479)
  ·
    refine ⟨382073329461518499867120719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254715552974345666578080479 382073329461518499867120719)
    ·
      refine ⟨573109994192277749800681079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382073329461518499867120719 573109994192277749800681079)
      ·
        refine ⟨859664991288416624701021619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573109994192277749800681079 859664991288416624701021619)
        ·
          refine ⟨1289497486932624937051532429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859664991288416624701021619 1289497486932624937051532429)
          ·
            refine ⟨483561557599734351394324661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1289497486932624937051532429 483561557599734351394324661)
            ·
              refine ⟨45333896024975095443217937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 483561557599734351394324661 45333896024975095443217937)
              ·
                refine ⟨34000422018731321582413453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45333896024975095443217937 34000422018731321582413453)
                ·
                  refine ⟨12750158257024245593405045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34000422018731321582413453 12750158257024245593405045)
                  ·
                    refine ⟨1195327336596023024381723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12750158257024245593405045 1195327336596023024381723)
                    ·
                      rfl

theorem cell23_6983675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 5].length) (baseStart_6983675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983675 prefixEnd_6983675 := by exact prefixLift 6983675
  have htrace : WordTrace (prefixWord ++ tailWord_6983675) baseStart_6983675 baseEnd_6983675 := by
    simpa [prefixWord, tailWord_6983675, baseEnd_6983675] using wordTrace_append hprefix tailTrace_6983675
  have hstable : (prefixWord ++ tailWord_6983675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983675).length < 2 ^ (prefixWord ++ tailWord_6983675).sum := by decide
  have hdescent : baseEnd_6983675 < baseStart_6983675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983692 : List Nat := [2, 2, 1, 2, 3, 1, 2, 4, 1, 5]
def baseStart_6983692 : Nat := 118140960795 + 6983692 * 2 ^ 59
def prefixEnd_6983692 : Nat := 4983230072969 + 3 ^ 40 * 6983692 * 2
def baseEnd_6983692 : Nat := 1195330246319731835544197

theorem tailTrace_6983692 : CollatzResearch.WordTrace tailWord_6983692 prefixEnd_6983692 1195330246319731835544197 := by
  unfold tailWord_6983692
  simp only [CollatzResearch.WordTrace]
  refine ⟨127358086507642039240724665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169810782010189385654299553 127358086507642039240724665)
  ·
    refine ⟨95518564880731529430543499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127358086507642039240724665 95518564880731529430543499)
    ·
      refine ⟨143277847321097294145815249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95518564880731529430543499 143277847321097294145815249)
      ·
        refine ⟨107458385490822970609361437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143277847321097294145815249 107458385490822970609361437)
        ·
          refine ⟨40296894559058613978510539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107458385490822970609361437 40296894559058613978510539)
          ·
            refine ⟨60445341838587920967765809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40296894559058613978510539 60445341838587920967765809)
            ·
              refine ⟨45334006378940940725824357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60445341838587920967765809 45334006378940940725824357)
              ·
                refine ⟨8500126196051426386092067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45334006378940940725824357 8500126196051426386092067)
                ·
                  refine ⟨12750189294077139579138101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8500126196051426386092067 12750189294077139579138101)
                  ·
                    refine ⟨1195330246319731835544197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12750189294077139579138101 1195330246319731835544197)
                    ·
                      rfl

theorem cell23_6983692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 1, 5].length) (baseStart_6983692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983692 prefixEnd_6983692 := by exact prefixLift 6983692
  have htrace : WordTrace (prefixWord ++ tailWord_6983692) baseStart_6983692 baseEnd_6983692 := by
    simpa [prefixWord, tailWord_6983692, baseEnd_6983692] using wordTrace_append hprefix tailTrace_6983692
  have hstable : (prefixWord ++ tailWord_6983692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983692).length < 2 ^ (prefixWord ++ tailWord_6983692).sum := by decide
  have hdescent : baseEnd_6983692 < baseStart_6983692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983693 : List Nat := [1, 7, 1, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_6983693 : Nat := 118140960795 + 6983693 * 2 ^ 59
def prefixEnd_6983693 : Nat := 4983230072969 + 3 ^ 40 * 6983693 * 2
def baseEnd_6983693 : Nat := 3585991252439850002720087

theorem tailTrace_6983693 : CollatzResearch.WordTrace tailWord_6983693 prefixEnd_6983693 3585991252439850002720087 := by
  unfold tailWord_6983693
  simp only [CollatzResearch.WordTrace]
  refine ⟨254716209488280455652235733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169810806325520303768157155 254716209488280455652235733)
  ·
    refine ⟨5969911159881573179349275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 254716209488280455652235733 5969911159881573179349275)
    ·
      refine ⟨8954866739822359769023913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5969911159881573179349275 8954866739822359769023913)
      ·
        refine ⟨6716150054866769826767935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8954866739822359769023913 6716150054866769826767935)
        ·
          refine ⟨10074225082300154740151903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6716150054866769826767935 10074225082300154740151903)
          ·
            refine ⟨15111337623450232110227855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10074225082300154740151903 15111337623450232110227855)
            ·
              refine ⟨22667006435175348165341783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15111337623450232110227855 22667006435175348165341783)
              ·
                refine ⟨34000509652763022248012675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22667006435175348165341783 34000509652763022248012675)
                ·
                  refine ⟨51000764479144533372019013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34000509652763022248012675 51000764479144533372019013)
                  ·
                    refine ⟨9562643339839600007253565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51000764479144533372019013 9562643339839600007253565)
                    ·
                      refine ⟨3585991252439850002720087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9562643339839600007253565 3585991252439850002720087)
                      ·
                        rfl

theorem cell23_6983693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_6983693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983693 prefixEnd_6983693 := by exact prefixLift 6983693
  have htrace : WordTrace (prefixWord ++ tailWord_6983693) baseStart_6983693 baseEnd_6983693 := by
    simpa [prefixWord, tailWord_6983693, baseEnd_6983693] using wordTrace_append hprefix tailTrace_6983693
  have hstable : (prefixWord ++ tailWord_6983693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983693).length < 2 ^ (prefixWord ++ tailWord_6983693).sum := by decide
  have hdescent : baseEnd_6983693 < baseStart_6983693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983699 : List Nat := [1, 1, 1, 2, 1, 4, 5, 1, 2, 3, 2]
def baseStart_6983699 : Nat := 118140960795 + 6983699 * 2 ^ 59
def prefixEnd_6983699 : Nat := 4983230072969 + 3 ^ 40 * 6983699 * 2
def baseEnd_6983699 : Nat := 3585994333323776979245059

theorem tailTrace_6983699 : CollatzResearch.WordTrace tailWord_6983699 prefixEnd_6983699 3585994333323776979245059 := by
  unfold tailWord_6983699
  simp only [CollatzResearch.WordTrace]
  refine ⟨254716428326258718676954151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169810952217505812451302767 254716428326258718676954151)
  ·
    refine ⟨382074642489388078015431227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254716428326258718676954151 382074642489388078015431227)
    ·
      refine ⟨573111963734082117023146841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382074642489388078015431227 573111963734082117023146841)
      ·
        refine ⟨429833972800561587767360131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 573111963734082117023146841 429833972800561587767360131)
        ·
          refine ⟨644750959200842381651040197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429833972800561587767360131 644750959200842381651040197)
          ·
            refine ⟨120890804850157946559570037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 644750959200842381651040197 120890804850157946559570037)
            ·
              refine ⟨11333512954702307489959691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120890804850157946559570037 11333512954702307489959691)
              ·
                refine ⟨17000269432053461234939537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11333512954702307489959691 17000269432053461234939537)
                ·
                  refine ⟨12750202074040095926204653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17000269432053461234939537 12750202074040095926204653)
                  ·
                    refine ⟨4781325777765035972326745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12750202074040095926204653 4781325777765035972326745)
                    ·
                      refine ⟨3585994333323776979245059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4781325777765035972326745 3585994333323776979245059)
                      ·
                        rfl

theorem cell23_6983699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 3, 2].length) (baseStart_6983699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983699 prefixEnd_6983699 := by exact prefixLift 6983699
  have htrace : WordTrace (prefixWord ++ tailWord_6983699) baseStart_6983699 baseEnd_6983699 := by
    simpa [prefixWord, tailWord_6983699, baseEnd_6983699] using wordTrace_append hprefix tailTrace_6983699
  have hstable : (prefixWord ++ tailWord_6983699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983699).length < 2 ^ (prefixWord ++ tailWord_6983699).sum := by decide
  have hdescent : baseEnd_6983699 < baseStart_6983699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983700 : List Nat := [2, 4, 3, 2, 1, 1, 2, 3, 1, 4]
def baseStart_6983700 : Nat := 118140960795 + 6983700 * 2 ^ 59
def prefixEnd_6983700 : Nat := 4983230072969 + 3 ^ 40 * 6983700 * 2
def baseEnd_6983700 : Nat := 1195331615601477158444185

theorem tailTrace_6983700 : CollatzResearch.WordTrace tailWord_6983700 prefixEnd_6983700 1195331615601477158444185 := by
  unfold tailWord_6983700
  simp only [CollatzResearch.WordTrace]
  refine ⟨127358232399627547923870277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169810976532836730565160369 127358232399627547923870277)
  ·
    refine ⟨23879668574930165235725677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127358232399627547923870277 23879668574930165235725677)
    ·
      refine ⟨8954875715598811963397129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23879668574930165235725677 8954875715598811963397129)
      ·
        refine ⟨6716156786699108972547847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8954875715598811963397129 6716156786699108972547847)
        ·
          refine ⟨10074235180048663458821771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6716156786699108972547847 10074235180048663458821771)
          ·
            refine ⟨15111352770072995188232657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10074235180048663458821771 15111352770072995188232657)
            ·
              refine ⟨11333514577554746391174493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15111352770072995188232657 11333514577554746391174493)
              ·
                refine ⟨4250067966583029896690435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11333514577554746391174493 4250067966583029896690435)
                ·
                  refine ⟨6375101949874544845035653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4250067966583029896690435 6375101949874544845035653)
                  ·
                    refine ⟨1195331615601477158444185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6375101949874544845035653 1195331615601477158444185)
                    ·
                      rfl

theorem cell23_6983700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_6983700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983700 prefixEnd_6983700 := by exact prefixLift 6983700
  have htrace : WordTrace (prefixWord ++ tailWord_6983700) baseStart_6983700 baseEnd_6983700 := by
    simpa [prefixWord, tailWord_6983700, baseEnd_6983700] using wordTrace_append hprefix tailTrace_6983700
  have hstable : (prefixWord ++ tailWord_6983700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983700).length < 2 ^ (prefixWord ++ tailWord_6983700).sum := by decide
  have hdescent : baseEnd_6983700 < baseStart_6983700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983706 : List Nat := [3, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3]
def baseStart_6983706 : Nat := 118140960795 + 6983706 * 2 ^ 59
def prefixEnd_6983706 : Nat := 4983230072969 + 3 ^ 40 * 6983706 * 2
def baseEnd_6983706 : Nat := 3585997927688358451857527

theorem tailTrace_6983706 : CollatzResearch.WordTrace tailWord_6983706 prefixEnd_6983706 3585997927688358451857527 := by
  unfold tailWord_6983706
  simp only [CollatzResearch.WordTrace]
  refine ⟨63679170909308339718114743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169811122424822239248305981 63679170909308339718114743)
  ·
    refine ⟨95518756363962509577172115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63679170909308339718114743 95518756363962509577172115)
    ·
      refine ⟨143278134545943764365758173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95518756363962509577172115 143278134545943764365758173)
      ·
        refine ⟨53729300454728911637159315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143278134545943764365758173 53729300454728911637159315)
        ·
          refine ⟨80593950682093367455738973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53729300454728911637159315 80593950682093367455738973)
          ·
            refine ⟨30222731505785012795902115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80593950682093367455738973 30222731505785012795902115)
            ·
              refine ⟨45334097258677519193853173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30222731505785012795902115 45334097258677519193853173)
              ·
                refine ⟨4250071618001017424423735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45334097258677519193853173 4250071618001017424423735)
                ·
                  refine ⟨6375107427001526136635603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4250071618001017424423735 6375107427001526136635603)
                  ·
                    refine ⟨9562661140502289204953405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6375107427001526136635603 9562661140502289204953405)
                    ·
                      refine ⟨3585997927688358451857527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9562661140502289204953405 3585997927688358451857527)
                      ·
                        rfl

theorem cell23_6983706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_6983706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983706 prefixEnd_6983706 := by exact prefixLift 6983706
  have htrace : WordTrace (prefixWord ++ tailWord_6983706) baseStart_6983706 baseEnd_6983706 := by
    simpa [prefixWord, tailWord_6983706, baseEnd_6983706] using wordTrace_append hprefix tailTrace_6983706
  have hstable : (prefixWord ++ tailWord_6983706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983706).length < 2 ^ (prefixWord ++ tailWord_6983706).sum := by decide
  have hdescent : baseEnd_6983706 < baseStart_6983706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983709 : List Nat := [1, 4, 2, 2, 2, 2, 1, 3, 1, 5]
def baseStart_6983709 : Nat := 118140960795 + 6983709 * 2 ^ 59
def prefixEnd_6983709 : Nat := 4983230072969 + 3 ^ 40 * 6983709 * 2
def baseEnd_6983709 : Nat := 1195333156043440646706671

theorem tailTrace_6983709 : CollatzResearch.WordTrace tailWord_6983709 prefixEnd_6983709 1195333156043440646706671 := by
  unfold tailWord_6983709
  simp only [CollatzResearch.WordTrace]
  refine ⟨254716793056222490384818181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169811195370814993589878787 254716793056222490384818181)
  ·
    refine ⟨47759398698041716947153409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254716793056222490384818181 47759398698041716947153409)
    ·
      refine ⟨35819549023531287710365057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47759398698041716947153409 35819549023531287710365057)
      ·
        refine ⟨26864661767648465782773793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35819549023531287710365057 26864661767648465782773793)
        ·
          refine ⟨20148496325736349337080345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26864661767648465782773793 20148496325736349337080345)
          ·
            refine ⟨15111372244302262002810259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20148496325736349337080345 15111372244302262002810259)
            ·
              refine ⟨22667058366453393004215389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15111372244302262002810259 22667058366453393004215389)
              ·
                refine ⟨8500146887420022376580771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22667058366453393004215389 8500146887420022376580771)
                ·
                  refine ⟨12750220331130033564871157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8500146887420022376580771 12750220331130033564871157)
                  ·
                    refine ⟨1195333156043440646706671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12750220331130033564871157 1195333156043440646706671)
                    ·
                      rfl

theorem cell23_6983709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_6983709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983709 prefixEnd_6983709 := by exact prefixLift 6983709
  have htrace : WordTrace (prefixWord ++ tailWord_6983709) baseStart_6983709 baseEnd_6983709 := by
    simpa [prefixWord, tailWord_6983709, baseEnd_6983709] using wordTrace_append hprefix tailTrace_6983709
  have hstable : (prefixWord ++ tailWord_6983709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983709).length < 2 ^ (prefixWord ++ tailWord_6983709).sum := by decide
  have hdescent : baseEnd_6983709 < baseStart_6983709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983766 : List Nat := [5, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_6983766 : Nat := 118140960795 + 6983766 * 2 ^ 59
def prefixEnd_6983766 : Nat := 4983230072969 + 3 ^ 40 * 6983766 * 2
def baseEnd_6983766 : Nat := 3586028736527628217107251

theorem tailTrace_6983766 : CollatzResearch.WordTrace tailWord_6983766 prefixEnd_6983766 3586028736527628217107251 := by
  unfold tailWord_6983766
  simp only [CollatzResearch.WordTrace]
  refine ⟨15919929501063499319977697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169812581344677326079762101 15919929501063499319977697)
  ·
    refine ⟨11939947125797624489983273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15919929501063499319977697 11939947125797624489983273)
    ·
      refine ⟨8954960344348218367487455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11939947125797624489983273 8954960344348218367487455)
      ·
        refine ⟨13432440516522327551231183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8954960344348218367487455 13432440516522327551231183)
        ·
          refine ⟨20148660774783491326846775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13432440516522327551231183 20148660774783491326846775)
          ·
            refine ⟨30222991162175236990270163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20148660774783491326846775 30222991162175236990270163)
            ·
              refine ⟨45334486743262855485405245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30222991162175236990270163 45334486743262855485405245)
              ·
                refine ⟨17000432528723570807026967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45334486743262855485405245 17000432528723570807026967)
                ·
                  refine ⟨25500648793085356210540451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17000432528723570807026967 25500648793085356210540451)
                  ·
                    refine ⟨38250973189628034315810677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25500648793085356210540451 38250973189628034315810677)
                    ·
                      refine ⟨3586028736527628217107251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38250973189628034315810677 3586028736527628217107251)
                      ·
                        rfl

theorem cell23_6983766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_6983766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983766 prefixEnd_6983766 := by exact prefixLift 6983766
  have htrace : WordTrace (prefixWord ++ tailWord_6983766) baseStart_6983766 baseEnd_6983766 := by
    simpa [prefixWord, tailWord_6983766, baseEnd_6983766] using wordTrace_append hprefix tailTrace_6983766
  have hstable : (prefixWord ++ tailWord_6983766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983766).length < 2 ^ (prefixWord ++ tailWord_6983766).sum := by decide
  have hdescent : baseEnd_6983766 < baseStart_6983766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983774 : List Nat := [4, 4, 1, 1, 2, 1, 3, 2, 1, 1, 3]
def baseStart_6983774 : Nat := 118140960795 + 6983774 * 2 ^ 59
def prefixEnd_6983774 : Nat := 4983230072969 + 3 ^ 40 * 6983774 * 2
def baseEnd_6983774 : Nat := 3586032844372864185807215

theorem tailTrace_6983774 : CollatzResearch.WordTrace tailWord_6983774 prefixEnd_6983774 3586032844372864185807215 := by
  unfold tailWord_6983774
  simp only [CollatzResearch.WordTrace]
  refine ⟨31839895475123375810741797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169812775867324670990622917 31839895475123375810741797)
  ·
    refine ⟨5969980401585632964514087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31839895475123375810741797 5969980401585632964514087)
    ·
      refine ⟨8954970602378449446771131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5969980401585632964514087 8954970602378449446771131)
      ·
        refine ⟨13432455903567674170156697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8954970602378449446771131 13432455903567674170156697)
        ·
          refine ⟨10074341927675755627617523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13432455903567674170156697 10074341927675755627617523)
          ·
            refine ⟨15111512891513633441426285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10074341927675755627617523 15111512891513633441426285)
            ·
              refine ⟨5666817334317612540534857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15111512891513633441426285 5666817334317612540534857)
              ·
                refine ⟨4250113000738209405401143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5666817334317612540534857 4250113000738209405401143)
                ·
                  refine ⟨6375169501107314108101715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4250113000738209405401143 6375169501107314108101715)
                  ·
                    refine ⟨9562754251660971162152573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6375169501107314108101715 9562754251660971162152573)
                    ·
                      refine ⟨3586032844372864185807215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9562754251660971162152573 3586032844372864185807215)
                      ·
                        rfl

theorem cell23_6983774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_6983774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983774 prefixEnd_6983774 := by exact prefixLift 6983774
  have htrace : WordTrace (prefixWord ++ tailWord_6983774) baseStart_6983774 baseEnd_6983774 := by
    simpa [prefixWord, tailWord_6983774, baseEnd_6983774] using wordTrace_append hprefix tailTrace_6983774
  have hstable : (prefixWord ++ tailWord_6983774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983774).length < 2 ^ (prefixWord ++ tailWord_6983774).sum := by decide
  have hdescent : baseEnd_6983774 < baseStart_6983774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983779 : List Nat := [1, 1, 1, 5, 1, 1, 4, 1, 4, 1, 3]
def baseStart_6983779 : Nat := 118140960795 + 6983779 * 2 ^ 59
def prefixEnd_6983779 : Nat := 4983230072969 + 3 ^ 40 * 6983779 * 2
def baseEnd_6983779 : Nat := 3586035411776136666244691

theorem tailTrace_6983779 : CollatzResearch.WordTrace tailWord_6983779 prefixEnd_6983779 3586035411776136666244691 := by
  unfold tailWord_6983779
  simp only [CollatzResearch.WordTrace]
  refine ⟨254719346165968892339866391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169812897443979261559910927 254719346165968892339866391)
  ·
    refine ⟨382079019248953338509799587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254719346165968892339866391 382079019248953338509799587)
    ·
      refine ⟨573118528873430007764699381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382079019248953338509799587 573118528873430007764699381)
      ·
        refine ⟨53729862081884063227940567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 573118528873430007764699381 53729862081884063227940567)
        ·
          refine ⟨80594793122826094841910851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53729862081884063227940567 80594793122826094841910851)
          ·
            refine ⟨120892189684239142262866277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80594793122826094841910851 120892189684239142262866277)
            ·
              refine ⟨22667285565794839174287427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120892189684239142262866277 22667285565794839174287427)
              ·
                refine ⟨34000928348692258761431141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22667285565794839174287427 34000928348692258761431141)
                ·
                  refine ⟨6375174065379798517768339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34000928348692258761431141 6375174065379798517768339)
                  ·
                    refine ⟨9562761098069697776652509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6375174065379798517768339 9562761098069697776652509)
                    ·
                      refine ⟨3586035411776136666244691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9562761098069697776652509 3586035411776136666244691)
                      ·
                        rfl

theorem cell23_6983779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_6983779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983779 prefixEnd_6983779 := by exact prefixLift 6983779
  have htrace : WordTrace (prefixWord ++ tailWord_6983779) baseStart_6983779 baseEnd_6983779 := by
    simpa [prefixWord, tailWord_6983779, baseEnd_6983779] using wordTrace_append hprefix tailTrace_6983779
  have hstable : (prefixWord ++ tailWord_6983779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983779).length < 2 ^ (prefixWord ++ tailWord_6983779).sum := by decide
  have hdescent : baseEnd_6983779 < baseStart_6983779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983839 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 2, 4, 3]
def baseStart_6983839 : Nat := 118140960795 + 6983839 * 2 ^ 59
def prefixEnd_6983839 : Nat := 4983230072969 + 3 ^ 40 * 6983839 * 2
def baseEnd_6983839 : Nat := 3586066220615406431494415

theorem tailTrace_6983839 : CollatzResearch.WordTrace tailWord_6983839 prefixEnd_6983839 3586066220615406431494415 := by
  unfold tailWord_6983839
  simp only [CollatzResearch.WordTrace]
  refine ⟨254721534545751522587050571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169814356363834348391367047 254721534545751522587050571)
  ·
    refine ⟨382082301818627283880575857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254721534545751522587050571 382082301818627283880575857)
    ·
      refine ⟨286561726363970462910431893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382082301818627283880575857 286561726363970462910431893)
      ·
        refine ⟨13432580923311115448926495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 286561726363970462910431893 13432580923311115448926495)
        ·
          refine ⟨20148871384966673173389743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13432580923311115448926495 20148871384966673173389743)
          ·
            refine ⟨30223307077450009760084615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20148871384966673173389743 30223307077450009760084615)
            ·
              refine ⟨45334960616175014640126923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30223307077450009760084615 45334960616175014640126923)
              ·
                refine ⟨68002440924262521960190385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45334960616175014640126923 68002440924262521960190385)
                ·
                  refine ⟨51001830693196891470142789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68002440924262521960190385 51001830693196891470142789)
                  ·
                    refine ⟨9562843254974417150651773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51001830693196891470142789 9562843254974417150651773)
                    ·
                      refine ⟨3586066220615406431494415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9562843254974417150651773 3586066220615406431494415)
                      ·
                        rfl

theorem cell23_6983839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_6983839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983839 prefixEnd_6983839 := by exact prefixLift 6983839
  have htrace : WordTrace (prefixWord ++ tailWord_6983839) baseStart_6983839 baseEnd_6983839 := by
    simpa [prefixWord, tailWord_6983839, baseEnd_6983839] using wordTrace_append hprefix tailTrace_6983839
  have hstable : (prefixWord ++ tailWord_6983839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983839).length < 2 ^ (prefixWord ++ tailWord_6983839).sum := by decide
  have hdescent : baseEnd_6983839 < baseStart_6983839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983853 : List Nat := [1, 5, 2, 1, 2, 2, 2, 1, 1, 4, 2]
def baseStart_6983853 : Nat := 118140960795 + 6983853 * 2 ^ 59
def prefixEnd_6983853 : Nat := 4983230072969 + 3 ^ 40 * 6983853 * 2
def baseEnd_6983853 : Nat := 3586073409344569376719351

theorem tailTrace_6983853 : CollatzResearch.WordTrace tailWord_6983853 prefixEnd_6983853 3586073409344569376719351 := by
  unfold tailWord_6983853
  simp only [CollatzResearch.WordTrace]
  refine ⟨254722045167700802978060213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169814696778467201985373475 254722045167700802978060213)
  ·
    refine ⟨23880191734471950279193145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 254722045167700802978060213 23880191734471950279193145)
    ·
      refine ⟨17910143800853962709394859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23880191734471950279193145 17910143800853962709394859)
      ·
        refine ⟨26865215701280944064092289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17910143800853962709394859 26865215701280944064092289)
        ·
          refine ⟨20148911775960708048069217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26865215701280944064092289 20148911775960708048069217)
          ·
            refine ⟨15111683831970531036051913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20148911775960708048069217 15111683831970531036051913)
            ·
              refine ⟨11333762873977898277038935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15111683831970531036051913 11333762873977898277038935)
              ·
                refine ⟨17000644310966847415558403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11333762873977898277038935 17000644310966847415558403)
                ·
                  refine ⟨25500966466450271123337605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17000644310966847415558403 25500966466450271123337605)
                  ·
                    refine ⟨4781431212459425835625801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25500966466450271123337605 4781431212459425835625801)
                    ·
                      refine ⟨3586073409344569376719351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4781431212459425835625801 3586073409344569376719351)
                      ·
                        rfl

theorem cell23_6983853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_6983853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983853 prefixEnd_6983853 := by exact prefixLift 6983853
  have htrace : WordTrace (prefixWord ++ tailWord_6983853) baseStart_6983853 baseEnd_6983853 := by
    simpa [prefixWord, tailWord_6983853, baseEnd_6983853] using wordTrace_append hprefix tailTrace_6983853
  have hstable : (prefixWord ++ tailWord_6983853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983853).length < 2 ^ (prefixWord ++ tailWord_6983853).sum := by decide
  have hdescent : baseEnd_6983853 < baseStart_6983853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983874 : List Nat := [3, 5, 1, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_6983874 : Nat := 118140960795 + 6983874 * 2 ^ 59
def prefixEnd_6983874 : Nat := 4983230072969 + 3 ^ 40 * 6983874 * 2
def baseEnd_6983874 : Nat := 3586084192438313794556755

theorem tailTrace_6983874 : CollatzResearch.WordTrace tailWord_6983874 prefixEnd_6983874 3586084192438313794556755 := by
  unfold tailWord_6983874
  simp only [CollatzResearch.WordTrace]
  refine ⟨63680702775156180891143669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169815207400416482376383117 63680702775156180891143669)
  ·
    refine ⟨5970065885170891958544719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63680702775156180891143669 5970065885170891958544719)
    ·
      refine ⟨8955098827756337937817079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5970065885170891958544719 8955098827756337937817079)
      ·
        refine ⟨13432648241634506906725619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8955098827756337937817079 13432648241634506906725619)
        ·
          refine ⟨20148972362451760360088429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13432648241634506906725619 20148972362451760360088429)
          ·
            refine ⟨7555864635919410135033161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20148972362451760360088429 7555864635919410135033161)
            ·
              refine ⟨5666898476939557601274871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7555864635919410135033161 5666898476939557601274871)
              ·
                refine ⟨8500347715409336401912307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5666898476939557601274871 8500347715409336401912307)
                ·
                  refine ⟨12750521573114004602868461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8500347715409336401912307 12750521573114004602868461)
                  ·
                    refine ⟨4781445589917751726075673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12750521573114004602868461 4781445589917751726075673)
                    ·
                      refine ⟨3586084192438313794556755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4781445589917751726075673 3586084192438313794556755)
                      ·
                        rfl

theorem cell23_6983874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_6983874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983874 prefixEnd_6983874 := by exact prefixLift 6983874
  have htrace : WordTrace (prefixWord ++ tailWord_6983874) baseStart_6983874 baseEnd_6983874 := by
    simpa [prefixWord, tailWord_6983874, baseEnd_6983874] using wordTrace_append hprefix tailTrace_6983874
  have hstable : (prefixWord ++ tailWord_6983874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983874).length < 2 ^ (prefixWord ++ tailWord_6983874).sum := by decide
  have hdescent : baseEnd_6983874 < baseStart_6983874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983876 : List Nat := [2, 3, 3, 1, 2, 1, 1, 5, 5]
def baseStart_6983876 : Nat := 118140960795 + 6983876 * 2 ^ 59
def prefixEnd_6983876 : Nat := 4983230072969 + 3 ^ 40 * 6983876 * 2
def baseEnd_6983876 : Nat := 398453913266624754081305

theorem tailTrace_6983876 : CollatzResearch.WordTrace tailWord_6983876 prefixEnd_6983876 398453913266624754081305 := by
  unfold tailWord_6983876
  simp only [CollatzResearch.WordTrace]
  refine ⟨127361442023308738953073741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169815256031078318604098321 127361442023308738953073741)
  ·
    refine ⟨47760540758740777107402653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127361442023308738953073741 47760540758740777107402653)
    ·
      refine ⟨17910202784527791415275995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47760540758740777107402653 17910202784527791415275995)
      ·
        refine ⟨26865304176791687122913993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17910202784527791415275995 26865304176791687122913993)
        ·
          refine ⟨20148978132593765342185495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26865304176791687122913993 20148978132593765342185495)
          ·
            refine ⟨30223467198890648013278243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20148978132593765342185495 30223467198890648013278243)
            ·
              refine ⟨45335200798335972019917365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30223467198890648013278243 45335200798335972019917365)
              ·
                refine ⟨4250175074843997376867253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45335200798335972019917365 4250175074843997376867253)
                ·
                  refine ⟨398453913266624754081305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4250175074843997376867253 398453913266624754081305)
                  ·
                    rfl

theorem cell23_6983876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5, 5].length) (baseStart_6983876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983876 prefixEnd_6983876 := by exact prefixLift 6983876
  have htrace : WordTrace (prefixWord ++ tailWord_6983876) baseStart_6983876 baseEnd_6983876 := by
    simpa [prefixWord, tailWord_6983876, baseEnd_6983876] using wordTrace_append hprefix tailTrace_6983876
  have hstable : (prefixWord ++ tailWord_6983876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983876).length < 2 ^ (prefixWord ++ tailWord_6983876).sum := by decide
  have hdescent : baseEnd_6983876 < baseStart_6983876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983909 : List Nat := [1, 3, 1, 4, 2, 1, 1, 2, 1, 3, 4]
def baseStart_6983909 : Nat := 118140960795 + 6983909 * 2 ^ 59
def prefixEnd_6983909 : Nat := 4983230072969 + 3 ^ 40 * 6983909 * 2
def baseEnd_6983909 : Nat := 3586102164261221157619093

theorem tailTrace_6983909 : CollatzResearch.WordTrace tailWord_6983909 prefixEnd_6983909 3586102164261221157619093 := by
  unfold tailWord_6983909
  simp only [CollatzResearch.WordTrace]
  refine ⟨254724087655497924542098781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169816058436998616361399187 254724087655497924542098781)
  ·
    refine ⟨95521532870811721703287043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254724087655497924542098781 95521532870811721703287043)
    ·
      refine ⟨143282299306217582554930565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95521532870811721703287043 143282299306217582554930565)
      ·
        refine ⟨26865431119915796729049481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143282299306217582554930565 26865431119915796729049481)
        ·
          refine ⟨20149073339936847546787111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26865431119915796729049481 20149073339936847546787111)
          ·
            refine ⟨30223610009905271320180667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20149073339936847546787111 30223610009905271320180667)
            ·
              refine ⟨45335415014857906980271001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30223610009905271320180667 45335415014857906980271001)
              ·
                refine ⟨34001561261143430235203251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45335415014857906980271001 34001561261143430235203251)
                ·
                  refine ⟨51002341891715145352804877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34001561261143430235203251 51002341891715145352804877)
                  ·
                    refine ⟨19125878209393179507301829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51002341891715145352804877 19125878209393179507301829)
                    ·
                      refine ⟨3586102164261221157619093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19125878209393179507301829 3586102164261221157619093)
                      ·
                        rfl

theorem cell23_6983909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_6983909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983909 prefixEnd_6983909 := by exact prefixLift 6983909
  have htrace : WordTrace (prefixWord ++ tailWord_6983909) baseStart_6983909 baseEnd_6983909 := by
    simpa [prefixWord, tailWord_6983909, baseEnd_6983909] using wordTrace_append hprefix tailTrace_6983909
  have hstable : (prefixWord ++ tailWord_6983909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983909).length < 2 ^ (prefixWord ++ tailWord_6983909).sum := by decide
  have hdescent : baseEnd_6983909 < baseStart_6983909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983926 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2]
def baseStart_6983926 : Nat := 118140960795 + 6983926 * 2 ^ 59
def prefixEnd_6983926 : Nat := 4983230072969 + 3 ^ 40 * 6983926 * 2
def baseEnd_6983926 : Nat := 3586110893432347591106515

theorem tailTrace_6983926 : CollatzResearch.WordTrace tailWord_6983926 prefixEnd_6983926 3586110893432347591106515 := by
  unfold tailWord_6983926
  simp only [CollatzResearch.WordTrace]
  refine ⟨15920294231027271027841727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 169816471797624224296978421 15920294231027271027841727)
  ·
    refine ⟨23880441346540906541762591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15920294231027271027841727 23880441346540906541762591)
    ·
      refine ⟨35820662019811359812643887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23880441346540906541762591 35820662019811359812643887)
      ·
        refine ⟨53730993029717039718965831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35820662019811359812643887 53730993029717039718965831)
        ·
          refine ⟨80596489544575559578448747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53730993029717039718965831 80596489544575559578448747)
          ·
            refine ⟨120894734316863339367673121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80596489544575559578448747 120894734316863339367673121)
            ·
              refine ⟨90671050737647504525754841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120894734316863339367673121 90671050737647504525754841)
              ·
                refine ⟨68003288053235628394316131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90671050737647504525754841 68003288053235628394316131)
                ·
                  refine ⟨102004932079853442591474197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68003288053235628394316131 102004932079853442591474197)
                  ·
                    refine ⟨4781481191243130121475353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 102004932079853442591474197 4781481191243130121475353)
                    ·
                      refine ⟨3586110893432347591106515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4781481191243130121475353 3586110893432347591106515)
                      ·
                        rfl

theorem cell23_6983926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_6983926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983926 prefixEnd_6983926 := by exact prefixLift 6983926
  have htrace : WordTrace (prefixWord ++ tailWord_6983926) baseStart_6983926 baseEnd_6983926 := by
    simpa [prefixWord, tailWord_6983926, baseEnd_6983926] using wordTrace_append hprefix tailTrace_6983926
  have hstable : (prefixWord ++ tailWord_6983926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983926).length < 2 ^ (prefixWord ++ tailWord_6983926).sum := by decide
  have hdescent : baseEnd_6983926 < baseStart_6983926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6983943 : List Nat := [1, 1, 4, 5, 1, 1, 1, 2, 2, 1, 4]
def baseStart_6983943 : Nat := 118140960795 + 6983943 * 2 ^ 59
def prefixEnd_6983943 : Nat := 4983230072969 + 3 ^ 40 * 6983943 * 2
def baseEnd_6983943 : Nat := 3586119622603474024593937

theorem tailTrace_6983943 : CollatzResearch.WordTrace tailWord_6983943 prefixEnd_6983943 3586119622603474024593937 := by
  unfold tailWord_6983943
  simp only [CollatzResearch.WordTrace]
  refine ⟨254725327737374748348836483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169816885158249832232557655 254725327737374748348836483)
  ·
    refine ⟨382087991606062122523254725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254725327737374748348836483 382087991606062122523254725)
    ·
      refine ⟨71641498426136647973110261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 382087991606062122523254725 71641498426136647973110261)
      ·
        refine ⟨6716390477450310747479087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71641498426136647973110261 6716390477450310747479087)
        ·
          refine ⟨10074585716175466121218631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6716390477450310747479087 10074585716175466121218631)
          ·
            refine ⟨15111878574263199181827947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10074585716175466121218631 15111878574263199181827947)
            ·
              refine ⟨22667817861394798772741921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15111878574263199181827947 22667817861394798772741921)
              ·
                refine ⟨17000863396046099079556441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22667817861394798772741921 17000863396046099079556441)
                ·
                  refine ⟨12750647547034574309667331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17000863396046099079556441 12750647547034574309667331)
                  ·
                    refine ⟨19125971320551861464500997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12750647547034574309667331 19125971320551861464500997)
                    ·
                      refine ⟨3586119622603474024593937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19125971320551861464500997 3586119622603474024593937)
                      ·
                        rfl

theorem cell23_6983943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_6983943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6983943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6983943 prefixEnd_6983943 := by exact prefixLift 6983943
  have htrace : WordTrace (prefixWord ++ tailWord_6983943) baseStart_6983943 baseEnd_6983943 := by
    simpa [prefixWord, tailWord_6983943, baseEnd_6983943] using wordTrace_append hprefix tailTrace_6983943
  have hstable : (prefixWord ++ tailWord_6983943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6983943).length < 2 ^ (prefixWord ++ tailWord_6983943).sum := by decide
  have hdescent : baseEnd_6983943 < baseStart_6983943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6983943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984004 : List Nat := [2, 3, 4, 1, 2, 2, 2, 2, 1, 4]
def baseStart_6984004 : Nat := 118140960795 + 6984004 * 2 ^ 59
def prefixEnd_6984004 : Nat := 4983230072969 + 3 ^ 40 * 6984004 * 2
def baseEnd_6984004 : Nat := 1195383648307799428643719

theorem tailTrace_6984004 : CollatzResearch.WordTrace tailWord_6984004 prefixEnd_6984004 1195383648307799428643719 := by
  unfold tailWord_6984004
  simp only [CollatzResearch.WordTrace]
  refine ⟨127363776295076877883403533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169818368393435837177871377 127363776295076877883403533)
  ·
    refine ⟨47761416110653829206276325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127363776295076877883403533 47761416110653829206276325)
    ·
      refine ⟨8955265520747592976176811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47761416110653829206276325 8955265520747592976176811)
      ·
        refine ⟨13432898281121389464265217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8955265520747592976176811 13432898281121389464265217)
        ·
          refine ⟨10074673710841042098198913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13432898281121389464265217 10074673710841042098198913)
          ·
            refine ⟨7556005283130781573649185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10074673710841042098198913 7556005283130781573649185)
            ·
              refine ⟨5667003962348086180236889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7556005283130781573649185 5667003962348086180236889)
              ·
                refine ⟨4250252971761064635177667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5667003962348086180236889 4250252971761064635177667)
                ·
                  refine ⟨6375379457641596952766501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4250252971761064635177667 6375379457641596952766501)
                  ·
                    refine ⟨1195383648307799428643719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6375379457641596952766501 1195383648307799428643719)
                    ·
                      rfl

theorem cell23_6984004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_6984004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984004 prefixEnd_6984004 := by exact prefixLift 6984004
  have htrace : WordTrace (prefixWord ++ tailWord_6984004) baseStart_6984004 baseEnd_6984004 := by
    simpa [prefixWord, tailWord_6984004, baseEnd_6984004] using wordTrace_append hprefix tailTrace_6984004
  have hstable : (prefixWord ++ tailWord_6984004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984004).length < 2 ^ (prefixWord ++ tailWord_6984004).sum := by decide
  have hdescent : baseEnd_6984004 < baseStart_6984004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984036 : List Nat := [2, 3, 1, 1, 3, 1, 1, 3, 3, 2, 3]
def baseStart_6984036 : Nat := 118140960795 + 6984036 * 2 ^ 59
def prefixEnd_6984036 : Nat := 4983230072969 + 3 ^ 40 * 6984036 * 2
def baseEnd_6984036 : Nat := 3586167376304342160731009

theorem tailTrace_6984036 : CollatzResearch.WordTrace tailWord_6984036 prefixEnd_6984036 3586167376304342160731009 := by
  unfold tailWord_6984036
  simp only [CollatzResearch.WordTrace]
  refine ⟨127364359863018912615985981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169819146484025216821314641 127364359863018912615985981)
  ·
    refine ⟨47761634948632092230994743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127364359863018912615985981 47761634948632092230994743)
    ·
      refine ⟨71642452422948138346492115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47761634948632092230994743 71642452422948138346492115)
      ·
        refine ⟨107463678634422207519738173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71642452422948138346492115 107463678634422207519738173)
        ·
          refine ⟨40298879487908327819901815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107463678634422207519738173 40298879487908327819901815)
          ·
            refine ⟨60448319231862491729852723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40298879487908327819901815 60448319231862491729852723)
            ·
              refine ⟨90672478847793737594779085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60448319231862491729852723 90672478847793737594779085)
              ·
                refine ⟨34002179567922651598042157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90672478847793737594779085 34002179567922651598042157)
                ·
                  refine ⟨12750817337970994349265809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34002179567922651598042157 12750817337970994349265809)
                  ·
                    refine ⟨9563113003478245761949357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12750817337970994349265809 9563113003478245761949357)
                    ·
                      refine ⟨3586167376304342160731009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9563113003478245761949357 3586167376304342160731009)
                      ·
                        rfl

theorem cell23_6984036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_6984036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984036 prefixEnd_6984036 := by exact prefixLift 6984036
  have htrace : WordTrace (prefixWord ++ tailWord_6984036) baseStart_6984036 baseEnd_6984036 := by
    simpa [prefixWord, tailWord_6984036, baseEnd_6984036] using wordTrace_append hprefix tailTrace_6984036
  have hstable : (prefixWord ++ tailWord_6984036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984036).length < 2 ^ (prefixWord ++ tailWord_6984036).sum := by decide
  have hdescent : baseEnd_6984036 < baseStart_6984036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984050 : List Nat := [3, 2, 1, 2, 1, 5, 2, 1, 1, 1, 4]
def baseStart_6984050 : Nat := 118140960795 + 6984050 * 2 ^ 59
def prefixEnd_6984050 : Nat := 4983230072969 + 3 ^ 40 * 6984050 * 2
def baseEnd_6984050 : Nat := 3586174565033505105955945

theorem tailTrace_6984050 : CollatzResearch.WordTrace tailWord_6984050 prefixEnd_6984050 3586174565033505105955945 := by
  unfold tailWord_6984050
  simp only [CollatzResearch.WordTrace]
  refine ⟨63682307586996776405745401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169819486898658070415321069 63682307586996776405745401)
  ·
    refine ⟨47761730690247582304309051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63682307586996776405745401 47761730690247582304309051)
    ·
      refine ⟨71642596035371373456463577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47761730690247582304309051 71642596035371373456463577)
      ·
        refine ⟨53731947026528530092347683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71642596035371373456463577 53731947026528530092347683)
        ·
          refine ⟨80597920539792795138521525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53731947026528530092347683 80597920539792795138521525)
          ·
            refine ⟨7556055050605574544236393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80597920539792795138521525 7556055050605574544236393)
            ·
              refine ⟨5667041287954180908177295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7556055050605574544236393 5667041287954180908177295)
              ·
                refine ⟨8500561931931271362265943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5667041287954180908177295 8500561931931271362265943)
                ·
                  refine ⟨12750842897896907043398915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8500561931931271362265943 12750842897896907043398915)
                  ·
                    refine ⟨19126264346845360565098373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12750842897896907043398915 19126264346845360565098373)
                    ·
                      refine ⟨3586174565033505105955945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19126264346845360565098373 3586174565033505105955945)
                      ·
                        rfl

theorem cell23_6984050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_6984050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984050 prefixEnd_6984050 := by exact prefixLift 6984050
  have htrace : WordTrace (prefixWord ++ tailWord_6984050) baseStart_6984050 baseEnd_6984050 := by
    simpa [prefixWord, tailWord_6984050, baseEnd_6984050] using wordTrace_append hprefix tailTrace_6984050
  have hstable : (prefixWord ++ tailWord_6984050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984050).length < 2 ^ (prefixWord ++ tailWord_6984050).sum := by decide
  have hdescent : baseEnd_6984050 < baseStart_6984050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984176 : List Nat := [2, 1, 1, 1, 3, 3, 1, 4, 2, 5]
def baseStart_6984176 : Nat := 118140960795 + 6984176 * 2 ^ 59
def prefixEnd_6984176 : Nat := 4983230072969 + 3 ^ 40 * 6984176 * 2
def baseEnd_6984176 : Nat := 1195413087865323870993455

theorem tailTrace_6984176 : CollatzResearch.WordTrace tailWord_6984176 prefixEnd_6984176 1195413087865323870993455 := by
  unfold tailWord_6984176
  simp only [CollatzResearch.WordTrace]
  refine ⟨127366912972765314571034191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169822550630353752761378921 127366912972765314571034191)
  ·
    refine ⟨191050369459147971856551287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127366912972765314571034191 191050369459147971856551287)
    ·
      refine ⟨286575554188721957784826931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191050369459147971856551287 286575554188721957784826931)
      ·
        refine ⟨429863331283082936677240397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286575554188721957784826931 429863331283082936677240397)
        ·
          refine ⟨161198749231156101253965149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 429863331283082936677240397 161198749231156101253965149)
          ·
            refine ⟨60449530961683537970236931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161198749231156101253965149 60449530961683537970236931)
            ·
              refine ⟨90674296442525306955355397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60449530961683537970236931 90674296442525306955355397)
              ·
                refine ⟨17001430582973495054129137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90674296442525306955355397 17001430582973495054129137)
                ·
                  refine ⟨12751072937230121290596853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17001430582973495054129137 12751072937230121290596853)
                  ·
                    refine ⟨1195413087865323870993455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12751072937230121290596853 1195413087865323870993455)
                    ·
                      rfl

theorem cell23_6984176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 2, 5].length) (baseStart_6984176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984176 prefixEnd_6984176 := by exact prefixLift 6984176
  have htrace : WordTrace (prefixWord ++ tailWord_6984176) baseStart_6984176 baseEnd_6984176 := by
    simpa [prefixWord, tailWord_6984176, baseEnd_6984176] using wordTrace_append hprefix tailTrace_6984176
  have hstable : (prefixWord ++ tailWord_6984176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984176).length < 2 ^ (prefixWord ++ tailWord_6984176).sum := by decide
  have hdescent : baseEnd_6984176 < baseStart_6984176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984213 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 1, 6, 2]
def baseStart_6984213 : Nat := 118140960795 + 6984213 * 2 ^ 59
def prefixEnd_6984213 : Nat := 4983230072969 + 3 ^ 40 * 6984213 * 2
def baseEnd_6984213 : Nat := 3586258262380187968217695

theorem tailTrace_6984213 : CollatzResearch.WordTrace tailWord_6984213 prefixEnd_6984213 3586258262380187968217695 := by
  unfold tailWord_6984213
  simp only [CollatzResearch.WordTrace]
  refine ⟨254735175446396584461165293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169823450297597722974110195 254735175446396584461165293)
  ·
    refine ⟨95525690792398719172936985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 254735175446396584461165293 95525690792398719172936985)
    ·
      refine ⟨71644268094299039379702739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95525690792398719172936985 71644268094299039379702739)
      ·
        refine ⟨107466402141448559069554109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71644268094299039379702739 107466402141448559069554109)
        ·
          refine ⟨40299900803043209651082791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107466402141448559069554109 40299900803043209651082791)
          ·
            refine ⟨60449851204564814476624187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40299900803043209651082791 60449851204564814476624187)
            ·
              refine ⟨90674776806847221714936281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60449851204564814476624187 90674776806847221714936281)
              ·
                refine ⟨68006082605135416286202211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90674776806847221714936281 68006082605135416286202211)
                ·
                  refine ⟨102009123907703124429303317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68006082605135416286202211 102009123907703124429303317)
                  ·
                    refine ⟨4781677683173583957623593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 102009123907703124429303317 4781677683173583957623593)
                    ·
                      refine ⟨3586258262380187968217695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4781677683173583957623593 3586258262380187968217695)
                      ·
                        rfl

theorem cell23_6984213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 6, 2].length) (baseStart_6984213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984213 prefixEnd_6984213 := by exact prefixLift 6984213
  have htrace : WordTrace (prefixWord ++ tailWord_6984213) baseStart_6984213 baseEnd_6984213 := by
    simpa [prefixWord, tailWord_6984213, baseEnd_6984213] using wordTrace_append hprefix tailTrace_6984213
  have hstable : (prefixWord ++ tailWord_6984213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984213).length < 2 ^ (prefixWord ++ tailWord_6984213).sum := by decide
  have hdescent : baseEnd_6984213 < baseStart_6984213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984240 : List Nat := [2, 1, 1, 1, 2, 3, 4, 4, 1, 4]
def baseStart_6984240 : Nat := 118140960795 + 6984240 * 2 ^ 59
def prefixEnd_6984240 : Nat := 4983230072969 + 3 ^ 40 * 6984240 * 2
def baseEnd_6984240 : Nat := 1195424042119286454193357

theorem tailTrace_6984240 : CollatzResearch.WordTrace tailWord_6984240 prefixEnd_6984240 1195424042119286454193357 := by
  unfold tailWord_6984240
  simp only [CollatzResearch.WordTrace]
  refine ⟨127368080108649384036199087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169824106811532512048265449 127368080108649384036199087)
  ·
    refine ⟨191052120162974076054298631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127368080108649384036199087 191052120162974076054298631)
    ·
      refine ⟨286578180244461114081447947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191052120162974076054298631 286578180244461114081447947)
      ·
        refine ⟨429867270366691671122171921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286578180244461114081447947 429867270366691671122171921)
        ·
          refine ⟨322400452775018753341628941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429867270366691671122171921 322400452775018753341628941)
          ·
            refine ⟨120900169790632032503110853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322400452775018753341628941 120900169790632032503110853)
            ·
              refine ⟨22668781835743506094333285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120900169790632032503110853 22668781835743506094333285)
              ·
                refine ⟨4250396594201907392687491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22668781835743506094333285 4250396594201907392687491)
                ·
                  refine ⟨6375594891302861089031237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4250396594201907392687491 6375594891302861089031237)
                  ·
                    refine ⟨1195424042119286454193357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6375594891302861089031237 1195424042119286454193357)
                    ·
                      rfl

theorem cell23_6984240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 4, 1, 4].length) (baseStart_6984240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984240 prefixEnd_6984240 := by exact prefixLift 6984240
  have htrace : WordTrace (prefixWord ++ tailWord_6984240) baseStart_6984240 baseEnd_6984240 := by
    simpa [prefixWord, tailWord_6984240, baseEnd_6984240] using wordTrace_append hprefix tailTrace_6984240
  have hstable : (prefixWord ++ tailWord_6984240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984240).length < 2 ^ (prefixWord ++ tailWord_6984240).sum := by decide
  have hdescent : baseEnd_6984240 < baseStart_6984240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984317 : List Nat := [1, 4, 1, 1, 5, 2, 1, 2, 1, 5]
def baseStart_6984317 : Nat := 118140960795 + 6984317 * 2 ^ 59
def prefixEnd_6984317 : Nat := 4983230072969 + 3 ^ 40 * 6984317 * 2
def baseEnd_6984317 : Nat := 1195437221456085187105739

theorem tailTrace_6984317 : CollatzResearch.WordTrace tailWord_6984317 prefixEnd_6984317 1195437221456085187105739 := by
  unfold tailWord_6984317
  simp only [CollatzResearch.WordTrace]
  refine ⟨254738968638019810222951205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169825979092013206815300803 254738968638019810222951205)
  ·
    refine ⟨47763556619628714416803351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254738968638019810222951205 47763556619628714416803351)
    ·
      refine ⟨71645334929443071625205027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47763556619628714416803351 71645334929443071625205027)
      ·
        refine ⟨107468002394164607437807541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71645334929443071625205027 107468002394164607437807541)
        ·
          refine ⟨10075125224452931947294457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107468002394164607437807541 10075125224452931947294457)
          ·
            refine ⟨7556343918339698960470843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10075125224452931947294457 7556343918339698960470843)
            ·
              refine ⟨11334515877509548440706265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7556343918339698960470843 11334515877509548440706265)
              ·
                refine ⟨8500886908132161330529699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11334515877509548440706265 8500886908132161330529699)
                ·
                  refine ⟨12751330362198241995794549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8500886908132161330529699 12751330362198241995794549)
                  ·
                    refine ⟨1195437221456085187105739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12751330362198241995794549 1195437221456085187105739)
                    ·
                      rfl

theorem cell23_6984317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_6984317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984317 prefixEnd_6984317 := by exact prefixLift 6984317
  have htrace : WordTrace (prefixWord ++ tailWord_6984317) baseStart_6984317 baseEnd_6984317 := by
    simpa [prefixWord, tailWord_6984317, baseEnd_6984317] using wordTrace_append hprefix tailTrace_6984317
  have hstable : (prefixWord ++ tailWord_6984317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984317).length < 2 ^ (prefixWord ++ tailWord_6984317).sum := by decide
  have hdescent : baseEnd_6984317 < baseStart_6984317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984320 : List Nat := [2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 4]
def baseStart_6984320 : Nat := 118140960795 + 6984320 * 2 ^ 59
def prefixEnd_6984320 : Nat := 4983230072969 + 3 ^ 40 * 6984320 * 2
def baseEnd_6984320 : Nat := 3586313204810219049579703

theorem tailTrace_6984320 : CollatzResearch.WordTrace tailWord_6984320 prefixEnd_6984320 3586313204810219049579703 := by
  unfold tailWord_6984320
  simp only [CollatzResearch.WordTrace]
  refine ⟨127369539028504470867655207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169826052038005961156873609 127369539028504470867655207)
  ·
    refine ⟨191054308542756706301482811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127369539028504470867655207 191054308542756706301482811)
    ·
      refine ⟨286581462814135059452224217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191054308542756706301482811 286581462814135059452224217)
      ·
        refine ⟨214936097110601294589168163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 286581462814135059452224217 214936097110601294589168163)
        ·
          refine ⟨322404145665901941883752245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214936097110601294589168163 322404145665901941883752245)
          ·
            refine ⟨30225388656178307051601773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 322404145665901941883752245 30225388656178307051601773)
            ·
              refine ⟨11334520746066865144350665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30225388656178307051601773 11334520746066865144350665)
              ·
                refine ⟨8500890559550148858262999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11334520746066865144350665 8500890559550148858262999)
                ·
                  refine ⟨12751335839325223287394499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8500890559550148858262999 12751335839325223287394499)
                  ·
                    refine ⟨19127003758987834931091749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12751335839325223287394499 19127003758987834931091749)
                    ·
                      refine ⟨3586313204810219049579703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19127003758987834931091749 3586313204810219049579703)
                      ·
                        rfl

theorem cell23_6984320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 4].length) (baseStart_6984320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984320 prefixEnd_6984320 := by exact prefixLift 6984320
  have htrace : WordTrace (prefixWord ++ tailWord_6984320) baseStart_6984320 baseEnd_6984320 := by
    simpa [prefixWord, tailWord_6984320, baseEnd_6984320] using wordTrace_append hprefix tailTrace_6984320
  have hstable : (prefixWord ++ tailWord_6984320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984320).length < 2 ^ (prefixWord ++ tailWord_6984320).sum := by decide
  have hdescent : baseEnd_6984320 < baseStart_6984320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984330 : List Nat := [3, 1, 2, 3, 3, 1, 1, 2, 1, 6]
def baseStart_6984330 : Nat := 118140960795 + 6984330 * 2 ^ 59
def prefixEnd_6984330 : Nat := 4983230072969 + 3 ^ 40 * 6984330 * 2
def baseEnd_6984330 : Nat := 1195439446538921336818219

theorem tailTrace_6984330 : CollatzResearch.WordTrace tailWord_6984330 prefixEnd_6984330 1195439446538921336818219 := by
  unfold tailWord_6984330
  simp only [CollatzResearch.WordTrace]
  refine ⟨63684860696743178360793611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169826295191315142295449629 63684860696743178360793611)
  ·
    refine ⟨95527291045114767541190417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63684860696743178360793611 95527291045114767541190417)
    ·
      refine ⟨71645468283836075655892813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95527291045114767541190417 71645468283836075655892813)
      ·
        refine ⟨26867050606438528370959805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71645468283836075655892813 26867050606438528370959805)
        ·
          refine ⟨10075143977414448139109927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26867050606438528370959805 10075143977414448139109927)
          ·
            refine ⟨15112715966121672208664891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10075143977414448139109927 15112715966121672208664891)
            ·
              refine ⟨22669073949182508312997337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15112715966121672208664891 22669073949182508312997337)
              ·
                refine ⟨17001805461886881234748003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22669073949182508312997337 17001805461886881234748003)
                ·
                  refine ⟨25502708192830321852122005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17001805461886881234748003 25502708192830321852122005)
                  ·
                    refine ⟨1195439446538921336818219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25502708192830321852122005 1195439446538921336818219)
                    ·
                      rfl

theorem cell23_6984330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_6984330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984330 prefixEnd_6984330 := by exact prefixLift 6984330
  have htrace : WordTrace (prefixWord ++ tailWord_6984330) baseStart_6984330 baseEnd_6984330 := by
    simpa [prefixWord, tailWord_6984330, baseEnd_6984330] using wordTrace_append hprefix tailTrace_6984330
  have hstable : (prefixWord ++ tailWord_6984330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984330).length < 2 ^ (prefixWord ++ tailWord_6984330).sum := by decide
  have hdescent : baseEnd_6984330 < baseStart_6984330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984350 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_6984350 : Nat := 118140960795 + 6984350 * 2 ^ 59
def prefixEnd_6984350 : Nat := 4983230072969 + 3 ^ 40 * 6984350 * 2
def baseEnd_6984350 : Nat := 3586328609229853932204565

theorem tailTrace_6984350 : CollatzResearch.WordTrace tailWord_6984350 prefixEnd_6984350 3586328609229853932204565 := by
  unfold tailWord_6984350
  simp only [CollatzResearch.WordTrace]
  refine ⟨31842521530862532107362813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169826781497933504572601669 31842521530862532107362813)
  ·
    refine ⟨11940945574073449540261055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31842521530862532107362813 11940945574073449540261055)
    ·
      refine ⟨17911418361110174310391583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11940945574073449540261055 17911418361110174310391583)
      ·
        refine ⟨26867127541665261465587375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17911418361110174310391583 26867127541665261465587375)
        ·
          refine ⟨40300691312497892198381063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26867127541665261465587375 40300691312497892198381063)
          ·
            refine ⟨60451036968746838297571595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40300691312497892198381063 60451036968746838297571595)
            ·
              refine ⟨90676555453120257446357393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60451036968746838297571595 90676555453120257446357393)
              ·
                refine ⟨68007416589840193084768045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90676555453120257446357393 68007416589840193084768045)
                ·
                  refine ⟨25502781221190072406788017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68007416589840193084768045 25502781221190072406788017)
                  ·
                    refine ⟨19127085915892554305091013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25502781221190072406788017 19127085915892554305091013)
                    ·
                      refine ⟨3586328609229853932204565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19127085915892554305091013 3586328609229853932204565)
                      ·
                        rfl

theorem cell23_6984350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_6984350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984350 prefixEnd_6984350 := by exact prefixLift 6984350
  have htrace : WordTrace (prefixWord ++ tailWord_6984350) baseStart_6984350 baseEnd_6984350 := by
    simpa [prefixWord, tailWord_6984350, baseEnd_6984350] using wordTrace_append hprefix tailTrace_6984350
  have hstable : (prefixWord ++ tailWord_6984350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984350).length < 2 ^ (prefixWord ++ tailWord_6984350).sum := by decide
  have hdescent : baseEnd_6984350 < baseStart_6984350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984370 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3]
def baseStart_6984370 : Nat := 118140960795 + 6984370 * 2 ^ 59
def prefixEnd_6984370 : Nat := 4983230072969 + 3 ^ 40 * 6984370 * 2
def baseEnd_6984370 : Nat := 3586338878842943853954473

theorem tailTrace_6984370 : CollatzResearch.WordTrace tailWord_6984370 prefixEnd_6984370 3586338878842943853954473 := by
  unfold tailWord_6984370
  simp only [CollatzResearch.WordTrace]
  refine ⟨63685225426706950068657641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169827267804551866849753709 63685225426706950068657641)
  ·
    refine ⟨47763919070030212551493231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63685225426706950068657641 47763919070030212551493231)
    ·
      refine ⟨71645878605045318827239847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47763919070030212551493231 71645878605045318827239847)
      ·
        refine ⟨107468817907567978240859771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71645878605045318827239847 107468817907567978240859771)
        ·
          refine ⟨161203226861351967361289657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107468817907567978240859771 161203226861351967361289657)
          ·
            refine ⟨120902420146013975520967243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161203226861351967361289657 120902420146013975520967243)
            ·
              refine ⟨181353630219020963281450865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120902420146013975520967243 181353630219020963281450865)
              ·
                refine ⟨136015222664265722461088149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181353630219020963281450865 136015222664265722461088149)
                ·
                  refine ⟨6375713562387455740363507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 136015222664265722461088149 6375713562387455740363507)
                  ·
                    refine ⟨9563570343581183610545261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6375713562387455740363507 9563570343581183610545261)
                    ·
                      refine ⟨3586338878842943853954473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9563570343581183610545261 3586338878842943853954473)
                      ·
                        rfl

theorem cell23_6984370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_6984370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984370 prefixEnd_6984370 := by exact prefixLift 6984370
  have htrace : WordTrace (prefixWord ++ tailWord_6984370) baseStart_6984370 baseEnd_6984370 := by
    simpa [prefixWord, tailWord_6984370, baseEnd_6984370] using wordTrace_append hprefix tailTrace_6984370
  have hstable : (prefixWord ++ tailWord_6984370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984370).length < 2 ^ (prefixWord ++ tailWord_6984370).sum := by decide
  have hdescent : baseEnd_6984370 < baseStart_6984370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984404 : List Nat := [2, 4, 1, 3, 2, 1, 1, 1, 4, 1, 3]
def baseStart_6984404 : Nat := 118140960795 + 6984404 * 2 ^ 59
def prefixEnd_6984404 : Nat := 4983230072969 + 3 ^ 40 * 6984404 * 2
def baseEnd_6984404 : Nat := 3586356337185196720929317

theorem tailTrace_6984404 : CollatzResearch.WordTrace tailWord_6984404 prefixEnd_6984404 3586356337185196720929317 := by
  unfold tailWord_6984404
  simp only [CollatzResearch.WordTrace]
  refine ⟨127371070894352312040684133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169828094525803082720912177 127371070894352312040684133)
  ·
    refine ⟨23882075792691058507628275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127371070894352312040684133 23882075792691058507628275)
    ·
      refine ⟨35823113689036587761442413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23882075792691058507628275 35823113689036587761442413)
      ·
        refine ⟨13433667633388720410540905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35823113689036587761442413 13433667633388720410540905)
        ·
          refine ⟨10075250725041540307905679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13433667633388720410540905 10075250725041540307905679)
          ·
            refine ⟨15112876087562310461858519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10075250725041540307905679 15112876087562310461858519)
            ·
              refine ⟨22669314131343465692787779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15112876087562310461858519 22669314131343465692787779)
              ·
                refine ⟨34003971197015198539181669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22669314131343465692787779 34003971197015198539181669)
                ·
                  refine ⟨6375744599440349726096563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34003971197015198539181669 6375744599440349726096563)
                  ·
                    refine ⟨9563616899160524589144845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6375744599440349726096563 9563616899160524589144845)
                    ·
                      refine ⟨3586356337185196720929317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9563616899160524589144845 3586356337185196720929317)
                      ·
                        rfl

theorem cell23_6984404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_6984404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984404 prefixEnd_6984404 := by exact prefixLift 6984404
  have htrace : WordTrace (prefixWord ++ tailWord_6984404) baseStart_6984404 baseEnd_6984404 := by
    simpa [prefixWord, tailWord_6984404, baseEnd_6984404] using wordTrace_append hprefix tailTrace_6984404
  have hstable : (prefixWord ++ tailWord_6984404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984404).length < 2 ^ (prefixWord ++ tailWord_6984404).sum := by decide
  have hdescent : baseEnd_6984404 < baseStart_6984404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984433 : List Nat := [1, 2, 2, 2, 2, 2, 1, 4, 7]
def baseStart_6984433 : Nat := 118140960795 + 6984433 * 2 ^ 59
def prefixEnd_6984433 : Nat := 4983230072969 + 3 ^ 40 * 6984433 * 2
def baseEnd_6984433 : Nat := 398485692013797456385187

theorem tailTrace_6984433 : CollatzResearch.WordTrace tailWord_6984433 prefixEnd_6984433 398485692013797456385187 := by
  unfold tailWord_6984433
  simp only [CollatzResearch.WordTrace]
  refine ⟨254743199505599562034173953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169828799670399708022782635 254743199505599562034173953)
  ·
    refine ⟨191057399629199671525630465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254743199505599562034173953 191057399629199671525630465)
    ·
      refine ⟨143293049721899753644222849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191057399629199671525630465 143293049721899753644222849)
      ·
        refine ⟨107469787291424815233167137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143293049721899753644222849 107469787291424815233167137)
        ·
          refine ⟨80602340468568611424875353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107469787291424815233167137 80602340468568611424875353)
          ·
            refine ⟨60451755351426458568656515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80602340468568611424875353 60451755351426458568656515)
            ·
              refine ⟨90677633027139687852984773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60451755351426458568656515 90677633027139687852984773)
              ·
                refine ⟨17002056192588691472434645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90677633027139687852984773 17002056192588691472434645)
                ·
                  refine ⟨398485692013797456385187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17002056192588691472434645 398485692013797456385187)
                  ·
                    rfl

theorem cell23_6984433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 7].length) (baseStart_6984433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984433 prefixEnd_6984433 := by exact prefixLift 6984433
  have htrace : WordTrace (prefixWord ++ tailWord_6984433) baseStart_6984433 baseEnd_6984433 := by
    simpa [prefixWord, tailWord_6984433, baseEnd_6984433] using wordTrace_append hprefix tailTrace_6984433
  have hstable : (prefixWord ++ tailWord_6984433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984433).length < 2 ^ (prefixWord ++ tailWord_6984433).sum := by decide
  have hdescent : baseEnd_6984433 < baseStart_6984433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984467 : List Nat := [1, 1, 1, 2, 1, 3, 7, 2, 5]
def baseStart_6984467 : Nat := 118140960795 + 6984467 * 2 ^ 59
def prefixEnd_6984467 : Nat := 4983230072969 + 3 ^ 40 * 6984467 * 2
def baseEnd_6984467 : Nat := 398487631829603330493503

theorem tailTrace_6984467 : CollatzResearch.WordTrace tailWord_6984467 prefixEnd_6984467 398487631829603330493503 := by
  unfold tailWord_6984467
  simp only [CollatzResearch.WordTrace]
  refine ⟨254744439587476385840911655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169829626391650923893941103 254744439587476385840911655)
  ·
    refine ⟨382116659381214578761367483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254744439587476385840911655 382116659381214578761367483)
    ·
      refine ⟨573174989071821868142051225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382116659381214578761367483 573174989071821868142051225)
      ·
        refine ⟨429881241803866401106538419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 573174989071821868142051225 429881241803866401106538419)
        ·
          refine ⟨644821862705799601659807629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429881241803866401106538419 644821862705799601659807629)
          ·
            refine ⟨241808198514674850622427861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 644821862705799601659807629 241808198514674850622427861)
            ·
              refine ⟨5667379652687691811463153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 241808198514674850622427861 5667379652687691811463153)
              ·
                refine ⟨4250534739515768858597365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5667379652687691811463153 4250534739515768858597365)
                ·
                  refine ⟨398487631829603330493503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4250534739515768858597365 398487631829603330493503)
                  ·
                    rfl

theorem cell23_6984467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2, 5].length) (baseStart_6984467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984467 prefixEnd_6984467 := by exact prefixLift 6984467
  have htrace : WordTrace (prefixWord ++ tailWord_6984467) baseStart_6984467 baseEnd_6984467 := by
    simpa [prefixWord, tailWord_6984467, baseEnd_6984467] using wordTrace_append hprefix tailTrace_6984467
  have hstable : (prefixWord ++ tailWord_6984467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984467).length < 2 ^ (prefixWord ++ tailWord_6984467).sum := by decide
  have hdescent : baseEnd_6984467 < baseStart_6984467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984574 : List Nat := [4, 2, 3, 1, 2, 1, 1, 1, 8]
def baseStart_6984574 : Nat := 118140960795 + 6984574 * 2 ^ 59
def prefixEnd_6984574 : Nat := 4983230072969 + 3 ^ 40 * 6984574 * 2
def baseEnd_6984574 : Nat := 398493736544051228422615

theorem tailTrace_6984574 : CollatzResearch.WordTrace tailWord_6984574 prefixEnd_6984574 398493736544051228422615 := by
  unfold tailWord_6984574
  simp only [CollatzResearch.WordTrace]
  refine ⟨31843542774761092889382097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169832228132059162076704517 31843542774761092889382097)
  ·
    refine ⟨23882657081070819667036573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31843542774761092889382097 23882657081070819667036573)
    ·
      refine ⟨8955996405401557375138715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23882657081070819667036573 8955996405401557375138715)
      ·
        refine ⟨13433994608102336062708073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8955996405401557375138715 13433994608102336062708073)
        ·
          refine ⟨10075495956076752047031055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13433994608102336062708073 10075495956076752047031055)
          ·
            refine ⟨15113243934115128070546583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10075495956076752047031055 15113243934115128070546583)
            ·
              refine ⟨22669865901172692105819875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15113243934115128070546583 22669865901172692105819875)
              ·
                refine ⟨34004798851759038158729813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22669865901172692105819875 34004798851759038158729813)
                ·
                  refine ⟨398493736544051228422615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34004798851759038158729813 398493736544051228422615)
                  ·
                    rfl

theorem cell23_6984574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_6984574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984574 prefixEnd_6984574 := by exact prefixLift 6984574
  have htrace : WordTrace (prefixWord ++ tailWord_6984574) baseStart_6984574 baseEnd_6984574 := by
    simpa [prefixWord, tailWord_6984574, baseEnd_6984574] using wordTrace_append hprefix tailTrace_6984574
  have hstable : (prefixWord ++ tailWord_6984574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984574).length < 2 ^ (prefixWord ++ tailWord_6984574).sum := by decide
  have hdescent : baseEnd_6984574 < baseStart_6984574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984578 : List Nat := [3, 4, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_6984578 : Nat := 118140960795 + 6984578 * 2 ^ 59
def prefixEnd_6984578 : Nat := 4983230072969 + 3 ^ 40 * 6984578 * 2
def baseEnd_6984578 : Nat := 1195481894273026346717839

theorem tailTrace_6984578 : CollatzResearch.WordTrace tailWord_6984578 prefixEnd_6984578 1195481894273026346717839 := by
  unfold tailWord_6984578
  simp only [CollatzResearch.WordTrace]
  refine ⟨63687122022518562949550597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169832325393382834532134925 63687122022518562949550597)
  ·
    refine ⟨11941335379222230553040737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63687122022518562949550597 11941335379222230553040737)
    ·
      refine ⟨8956001534416672914780553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11941335379222230553040737 8956001534416672914780553)
      ·
        refine ⟨6717001150812504686085415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8956001534416672914780553 6717001150812504686085415)
        ·
          refine ⟨10075501726218757029128123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6717001150812504686085415 10075501726218757029128123)
          ·
            refine ⟨15113252589328135543692185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10075501726218757029128123 15113252589328135543692185)
            ·
              refine ⟨11334939441996101657769139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15113252589328135543692185 11334939441996101657769139)
              ·
                refine ⟨17002409162994152486653709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11334939441996101657769139 17002409162994152486653709)
                ·
                  refine ⟨6375903436122807182495141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17002409162994152486653709 6375903436122807182495141)
                  ·
                    refine ⟨1195481894273026346717839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6375903436122807182495141 1195481894273026346717839)
                    ·
                      rfl

theorem cell23_6984578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_6984578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984578 prefixEnd_6984578 := by exact prefixLift 6984578
  have htrace : WordTrace (prefixWord ++ tailWord_6984578) baseStart_6984578 baseEnd_6984578 := by
    simpa [prefixWord, tailWord_6984578, baseEnd_6984578] using wordTrace_append hprefix tailTrace_6984578
  have hstable : (prefixWord ++ tailWord_6984578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984578).length < 2 ^ (prefixWord ++ tailWord_6984578).sum := by decide
  have hdescent : baseEnd_6984578 < baseStart_6984578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984584 : List Nat := [2, 1, 3, 3, 2, 1, 1, 3, 3, 1, 3]
def baseStart_6984584 : Nat := 118140960795 + 6984584 * 2 ^ 59
def prefixEnd_6984584 : Nat := 4983230072969 + 3 ^ 40 * 6984584 * 2
def baseEnd_6984584 : Nat := 3586448763703006016678489

theorem tailTrace_6984584 : CollatzResearch.WordTrace tailWord_6984584 prefixEnd_6984584 3586448763703006016678489 := by
  unfold tailWord_6984584
  simp only [CollatzResearch.WordTrace]
  refine ⟨127374353464026257411460403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169832471285368343215280537 127374353464026257411460403)
  ·
    refine ⟨191061530196039386117190605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127374353464026257411460403 191061530196039386117190605)
    ·
      refine ⟨71648073823514769793946477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191061530196039386117190605 71648073823514769793946477)
      ·
        refine ⟨26868027683818038672729929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71648073823514769793946477 26868027683818038672729929)
        ·
          refine ⟨20151020762863529004547447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26868027683818038672729929 20151020762863529004547447)
          ·
            refine ⟨30226531144295293506821171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20151020762863529004547447 30226531144295293506821171)
            ·
              refine ⟨45339796716442940260231757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30226531144295293506821171 45339796716442940260231757)
              ·
                refine ⟨17002423768666102597586909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45339796716442940260231757 17002423768666102597586909)
                ·
                  refine ⟨6375908913249788474095091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17002423768666102597586909 6375908913249788474095091)
                  ·
                    refine ⟨9563863369874682711142637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6375908913249788474095091 9563863369874682711142637)
                    ·
                      refine ⟨3586448763703006016678489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9563863369874682711142637 3586448763703006016678489)
                      ·
                        rfl

theorem cell23_6984584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_6984584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984584 prefixEnd_6984584 := by exact prefixLift 6984584
  have htrace : WordTrace (prefixWord ++ tailWord_6984584) baseStart_6984584 baseEnd_6984584 := by
    simpa [prefixWord, tailWord_6984584, baseEnd_6984584] using wordTrace_append hprefix tailTrace_6984584
  have hstable : (prefixWord ++ tailWord_6984584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984584).length < 2 ^ (prefixWord ++ tailWord_6984584).sum := by decide
  have hdescent : baseEnd_6984584 < baseStart_6984584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984628 : List Nat := [2, 5, 2, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_6984628 : Nat := 118140960795 + 6984628 * 2 ^ 59
def prefixEnd_6984628 : Nat := 4983230072969 + 3 ^ 40 * 6984628 * 2
def baseEnd_6984628 : Nat := 3586471356851803844528287

theorem tailTrace_6984628 : CollatzResearch.WordTrace tailWord_6984628 prefixEnd_6984628 3586471356851803844528287 := by
  unfold tailWord_6984628
  simp only [CollatzResearch.WordTrace]
  refine ⟨127375155869946555168761269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169833541159928740225015025 127375155869946555168761269)
  ·
    refine ⟨11941420862807489547071369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127375155869946555168761269 11941420862807489547071369)
    ·
      refine ⟨8956065647105617160303527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11941420862807489547071369 8956065647105617160303527)
      ·
        refine ⟨13434098470658425740455291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8956065647105617160303527 13434098470658425740455291)
        ·
          refine ⟨20151147705987638610682937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13434098470658425740455291 20151147705987638610682937)
          ·
            refine ⟨15113360779490728958012203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20151147705987638610682937 15113360779490728958012203)
            ·
              refine ⟨22670041169236093437018305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15113360779490728958012203 22670041169236093437018305)
              ·
                refine ⟨17002530876927070077763729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22670041169236093437018305 17002530876927070077763729)
                ·
                  refine ⟨12751898157695302558322797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17002530876927070077763729 12751898157695302558322797)
                  ·
                    refine ⟨4781961809135738459371049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12751898157695302558322797 4781961809135738459371049)
                    ·
                      refine ⟨3586471356851803844528287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4781961809135738459371049 3586471356851803844528287)
                      ·
                        rfl

theorem cell23_6984628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_6984628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984628 prefixEnd_6984628 := by exact prefixLift 6984628
  have htrace : WordTrace (prefixWord ++ tailWord_6984628) baseStart_6984628 baseEnd_6984628 := by
    simpa [prefixWord, tailWord_6984628, baseEnd_6984628] using wordTrace_append hprefix tailTrace_6984628
  have hstable : (prefixWord ++ tailWord_6984628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984628).length < 2 ^ (prefixWord ++ tailWord_6984628).sum := by decide
  have hdescent : baseEnd_6984628 < baseStart_6984628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984650 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 1, 4, 6]
def baseStart_6984650 : Nat := 118140960795 + 6984650 * 2 ^ 59
def prefixEnd_6984650 : Nat := 4983230072969 + 3 ^ 40 * 6984650 * 2
def baseEnd_6984650 : Nat := 3586482653426202758453185

theorem tailTrace_6984650 : CollatzResearch.WordTrace tailWord_6984650 prefixEnd_6984650 3586482653426202758453185 := by
  unfold tailWord_6984650
  simp only [CollatzResearch.WordTrace]
  refine ⟨63687778536453352023705851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169834076097208938729882269 63687778536453352023705851)
  ·
    refine ⟨95531667804680028035558777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63687778536453352023705851 95531667804680028035558777)
    ·
      refine ⟨71648750853510021026669083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95531667804680028035558777 71648750853510021026669083)
      ·
        refine ⟨107473126280265031540003625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71648750853510021026669083 107473126280265031540003625)
        ·
          refine ⟨80604844710198773655002719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107473126280265031540003625 80604844710198773655002719)
          ·
            refine ⟨120907267065298160482504079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80604844710198773655002719 120907267065298160482504079)
            ·
              refine ⟨181360900597947240723756119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120907267065298160482504079 181360900597947240723756119)
              ·
                refine ⟨272041350896920861085634179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181360900597947240723756119 272041350896920861085634179)
                ·
                  refine ⟨408062026345381291628451269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 272041350896920861085634179 408062026345381291628451269)
                  ·
                    refine ⟨76511629939758992180334613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 408062026345381291628451269 76511629939758992180334613)
                    ·
                      refine ⟨3586482653426202758453185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76511629939758992180334613 3586482653426202758453185)
                      ·
                        rfl

theorem cell23_6984650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_6984650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984650 prefixEnd_6984650 := by exact prefixLift 6984650
  have htrace : WordTrace (prefixWord ++ tailWord_6984650) baseStart_6984650 baseEnd_6984650 := by
    simpa [prefixWord, tailWord_6984650, baseEnd_6984650] using wordTrace_append hprefix tailTrace_6984650
  have hstable : (prefixWord ++ tailWord_6984650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984650).length < 2 ^ (prefixWord ++ tailWord_6984650).sum := by decide
  have hdescent : baseEnd_6984650 < baseStart_6984650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984651 : List Nat := [1, 1, 1, 1, 3, 7, 2, 1, 2, 4]
def baseStart_6984651 : Nat := 118140960795 + 6984651 * 2 ^ 59
def prefixEnd_6984651 : Nat := 4983230072969 + 3 ^ 40 * 6984651 * 2
def baseEnd_6984651 : Nat := 1195494388968952418180227

theorem tailTrace_6984651 : CollatzResearch.WordTrace tailWord_6984651 prefixEnd_6984651 1195494388968952418180227 := by
  unfold tailWord_6984651
  simp only [CollatzResearch.WordTrace]
  refine ⟨254751150618809785265609807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169834100412539856843739871 254751150618809785265609807)
  ·
    refine ⟨382126725928214677898414711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254751150618809785265609807 382126725928214677898414711)
    ·
      refine ⟨573190088892322016847622067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382126725928214677898414711 573190088892322016847622067)
      ·
        refine ⟨859785133338483025271433101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573190088892322016847622067 859785133338483025271433101)
        ·
          refine ⟨322419425001931134476787413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 859785133338483025271433101 322419425001931134476787413)
          ·
            refine ⟨7556705273482760964299705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 322419425001931134476787413 7556705273482760964299705)
            ·
              refine ⟨5667528955112070723224779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7556705273482760964299705 5667528955112070723224779)
              ·
                refine ⟨8501293432668106084837169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5667528955112070723224779 8501293432668106084837169)
                ·
                  refine ⟨6375970074501079563627877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8501293432668106084837169 6375970074501079563627877)
                  ·
                    refine ⟨1195494388968952418180227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6375970074501079563627877 1195494388968952418180227)
                    ·
                      rfl

theorem cell23_6984651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 2, 4].length) (baseStart_6984651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984651 prefixEnd_6984651 := by exact prefixLift 6984651
  have htrace : WordTrace (prefixWord ++ tailWord_6984651) baseStart_6984651 baseEnd_6984651 := by
    simpa [prefixWord, tailWord_6984651, baseEnd_6984651] using wordTrace_append hprefix tailTrace_6984651
  have hstable : (prefixWord ++ tailWord_6984651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984651).length < 2 ^ (prefixWord ++ tailWord_6984651).sum := by decide
  have hdescent : baseEnd_6984651 < baseStart_6984651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984657 : List Nat := [1, 2, 2, 1, 2, 1, 4, 3, 1, 3, 3]
def baseStart_6984657 : Nat := 118140960795 + 6984657 * 2 ^ 59
def prefixEnd_6984657 : Nat := 4983230072969 + 3 ^ 40 * 6984657 * 2
def baseEnd_6984657 : Nat := 3586486247790784231065653

theorem tailTrace_6984657 : CollatzResearch.WordTrace tailWord_6984657 prefixEnd_6984657 3586486247790784231065653 := by
  unfold tailWord_6984657
  simp only [CollatzResearch.WordTrace]
  refine ⟨254751369456788048290328225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169834246304525365526885483 254751369456788048290328225)
  ·
    refine ⟨191063527092591036217746169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254751369456788048290328225 191063527092591036217746169)
    ·
      refine ⟨143297645319443277163309627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191063527092591036217746169 143297645319443277163309627)
      ·
        refine ⟨214946467979164915744964441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143297645319443277163309627 214946467979164915744964441)
        ·
          refine ⟨161209850984373686808723331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214946467979164915744964441 161209850984373686808723331)
          ·
            refine ⟨241814776476560530213084997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161209850984373686808723331 241814776476560530213084997)
            ·
              refine ⟨45340270589355099414953437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 241814776476560530213084997 45340270589355099414953437)
              ·
                refine ⟨17002601471008162280607539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45340270589355099414953437 17002601471008162280607539)
                ·
                  refine ⟨25503902206512243420911309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17002601471008162280607539 25503902206512243420911309)
                  ·
                    refine ⟨9563963327442091282841741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25503902206512243420911309 9563963327442091282841741)
                    ·
                      refine ⟨3586486247790784231065653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9563963327442091282841741 3586486247790784231065653)
                      ·
                        rfl

theorem cell23_6984657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 3, 3].length) (baseStart_6984657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984657 prefixEnd_6984657 := by exact prefixLift 6984657
  have htrace : WordTrace (prefixWord ++ tailWord_6984657) baseStart_6984657 baseEnd_6984657 := by
    simpa [prefixWord, tailWord_6984657, baseEnd_6984657] using wordTrace_append hprefix tailTrace_6984657
  have hstable : (prefixWord ++ tailWord_6984657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984657).length < 2 ^ (prefixWord ++ tailWord_6984657).sum := by decide
  have hdescent : baseEnd_6984657 < baseStart_6984657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984747 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 4, 3, 3]
def baseStart_6984747 : Nat := 118140960795 + 6984747 * 2 ^ 59
def prefixEnd_6984747 : Nat := 4983230072969 + 3 ^ 40 * 6984747 * 2
def baseEnd_6984747 : Nat := 3586532461049688878940239

theorem tailTrace_6984747 : CollatzResearch.WordTrace tailWord_6984747 prefixEnd_6984747 3586532461049688878940239 := by
  unfold tailWord_6984747
  simp only [CollatzResearch.WordTrace]
  refine ⟨254754652026461993661104495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169836434684307995774069663 254754652026461993661104495)
  ·
    refine ⟨382131978039692990491656743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254754652026461993661104495 382131978039692990491656743)
    ·
      refine ⟨573197967059539485737485115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382131978039692990491656743 573197967059539485737485115)
      ·
        refine ⟨859796950589309228606227673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573197967059539485737485115 859796950589309228606227673)
        ·
          refine ⟨644847712941981921454670755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 859796950589309228606227673 644847712941981921454670755)
          ·
            refine ⟨967271569412972882182006133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 644847712941981921454670755 967271569412972882182006133)
            ·
              refine ⟨90681709632466207704563075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 967271569412972882182006133 90681709632466207704563075)
              ·
                refine ⟨136022564448699311556844613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90681709632466207704563075 136022564448699311556844613)
                ·
                  refine ⟨25504230834131120916908365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136022564448699311556844613 25504230834131120916908365)
                  ·
                    refine ⟨9564086562799170343840637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25504230834131120916908365 9564086562799170343840637)
                    ·
                      refine ⟨3586532461049688878940239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9564086562799170343840637 3586532461049688878940239)
                      ·
                        rfl

theorem cell23_6984747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3, 3].length) (baseStart_6984747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984747 prefixEnd_6984747 := by exact prefixLift 6984747
  have htrace : WordTrace (prefixWord ++ tailWord_6984747) baseStart_6984747 baseEnd_6984747 := by
    simpa [prefixWord, tailWord_6984747, baseEnd_6984747] using wordTrace_append hprefix tailTrace_6984747
  have hstable : (prefixWord ++ tailWord_6984747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984747).length < 2 ^ (prefixWord ++ tailWord_6984747).sum := by decide
  have hdescent : baseEnd_6984747 < baseStart_6984747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984754 : List Nat := [3, 2, 1, 1, 2, 2, 1, 6, 5]
def baseStart_6984754 : Nat := 118140960795 + 6984754 * 2 ^ 59
def prefixEnd_6984754 : Nat := 4983230072969 + 3 ^ 40 * 6984754 * 2
def baseEnd_6984754 : Nat := 398504006157141150172523

theorem tailTrace_6984754 : CollatzResearch.WordTrace tailWord_6984754 prefixEnd_6984754 398504006157141150172523 := by
  unfold tailWord_6984754
  simp only [CollatzResearch.WordTrace]
  refine ⟨63688726834359158464152329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169836604891624422571072877 63688726834359158464152329)
  ·
    refine ⟨47766545125769368848114247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63688726834359158464152329 47766545125769368848114247)
    ·
      refine ⟨71649817688654053272171371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47766545125769368848114247 71649817688654053272171371)
      ·
        refine ⟨107474726532981079908257057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71649817688654053272171371 107474726532981079908257057)
        ·
          refine ⟨80606044899735809931192793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107474726532981079908257057 80606044899735809931192793)
          ·
            refine ⟨60454533674801857448394595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80606044899735809931192793 60454533674801857448394595)
            ·
              refine ⟨90681800512202786172591893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60454533674801857448394595 90681800512202786172591893)
              ·
                refine ⟨4250709399009505601840245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 90681800512202786172591893 4250709399009505601840245)
                ·
                  refine ⟨398504006157141150172523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4250709399009505601840245 398504006157141150172523)
                  ·
                    rfl

theorem cell23_6984754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6, 5].length) (baseStart_6984754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984754 prefixEnd_6984754 := by exact prefixLift 6984754
  have htrace : WordTrace (prefixWord ++ tailWord_6984754) baseStart_6984754 baseEnd_6984754 := by
    simpa [prefixWord, tailWord_6984754, baseEnd_6984754] using wordTrace_append hprefix tailTrace_6984754
  have hstable : (prefixWord ++ tailWord_6984754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984754).length < 2 ^ (prefixWord ++ tailWord_6984754).sum := by decide
  have hdescent : baseEnd_6984754 < baseStart_6984754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984764 : List Nat := [2, 2, 2, 2, 2, 2, 2, 1, 2, 3, 3]
def baseStart_6984764 : Nat := 118140960795 + 6984764 * 2 ^ 59
def prefixEnd_6984764 : Nat := 4983230072969 + 3 ^ 40 * 6984764 * 2
def baseEnd_6984764 : Nat := 3586541190220815312427661

theorem tailTrace_6984764 : CollatzResearch.WordTrace tailWord_6984764 prefixEnd_6984764 3586541190220815312427661 := by
  unfold tailWord_6984764
  simp only [CollatzResearch.WordTrace]
  refine ⟨127377636033700202782236673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169836848044933603709648897 127377636033700202782236673)
  ·
    refine ⟨95533227025275152086677505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127377636033700202782236673 95533227025275152086677505)
    ·
      refine ⟨71649920268956364065008129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95533227025275152086677505 71649920268956364065008129)
      ·
        refine ⟨53737440201717273048756097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71649920268956364065008129 53737440201717273048756097)
        ·
          refine ⟨40303080151287954786567073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53737440201717273048756097 40303080151287954786567073)
          ·
            refine ⟨30227310113465966089925305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40303080151287954786567073 30227310113465966089925305)
            ·
              refine ⟨22670482585099474567443979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30227310113465966089925305 22670482585099474567443979)
              ·
                refine ⟨34005723877649211851165969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22670482585099474567443979 34005723877649211851165969)
                ·
                  refine ⟨25504292908236908888374477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34005723877649211851165969 25504292908236908888374477)
                  ·
                    refine ⟨9564109840588840833140429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25504292908236908888374477 9564109840588840833140429)
                    ·
                      refine ⟨3586541190220815312427661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9564109840588840833140429 3586541190220815312427661)
                      ·
                        rfl

theorem cell23_6984764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_6984764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984764 prefixEnd_6984764 := by exact prefixLift 6984764
  have htrace : WordTrace (prefixWord ++ tailWord_6984764) baseStart_6984764 baseEnd_6984764 := by
    simpa [prefixWord, tailWord_6984764, baseEnd_6984764] using wordTrace_append hprefix tailTrace_6984764
  have hstable : (prefixWord ++ tailWord_6984764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984764).length < 2 ^ (prefixWord ++ tailWord_6984764).sum := by decide
  have hdescent : baseEnd_6984764 < baseStart_6984764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984765 : List Nat := [1, 4, 1, 3, 1, 3, 3, 1, 2, 2, 2]
def baseStart_6984765 : Nat := 118140960795 + 6984765 * 2 ^ 59
def prefixEnd_6984765 : Nat := 4983230072969 + 3 ^ 40 * 6984765 * 2
def baseEnd_6984765 : Nat := 3586541703701469808515157

theorem tailTrace_6984765 : CollatzResearch.WordTrace tailWord_6984765 prefixEnd_6984765 3586541703701469808515157 := by
  unfold tailWord_6984765
  simp only [CollatzResearch.WordTrace]
  refine ⟨254755308540396782735259749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169836872360264521823506499 254755308540396782735259749)
  ·
    refine ⟨47766620351324396762861203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 254755308540396782735259749 47766620351324396762861203)
    ·
      refine ⟨71649930526986595144291805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47766620351324396762861203 71649930526986595144291805)
      ·
        refine ⟨26868723947619973179109427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71649930526986595144291805 26868723947619973179109427)
        ·
          refine ⟨40303085921429959768664141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26868723947619973179109427 40303085921429959768664141)
          ·
            refine ⟨15113657220536234913249053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40303085921429959768664141 15113657220536234913249053)
            ·
              refine ⟨5667621457701088092468395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15113657220536234913249053 5667621457701088092468395)
              ·
                refine ⟨8501432186551632138702593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5667621457701088092468395 8501432186551632138702593)
                ·
                  refine ⟨6376074139913724104026945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8501432186551632138702593 6376074139913724104026945)
                  ·
                    refine ⟨4782055604935293078020209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6376074139913724104026945 4782055604935293078020209)
                    ·
                      refine ⟨3586541703701469808515157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4782055604935293078020209 3586541703701469808515157)
                      ·
                        rfl

theorem cell23_6984765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_6984765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984765 prefixEnd_6984765 := by exact prefixLift 6984765
  have htrace : WordTrace (prefixWord ++ tailWord_6984765) baseStart_6984765 baseEnd_6984765 := by
    simpa [prefixWord, tailWord_6984765, baseEnd_6984765] using wordTrace_append hprefix tailTrace_6984765
  have hstable : (prefixWord ++ tailWord_6984765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984765).length < 2 ^ (prefixWord ++ tailWord_6984765).sum := by decide
  have hdescent : baseEnd_6984765 < baseStart_6984765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984817 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 2, 4, 4]
def baseStart_6984817 : Nat := 118140960795 + 6984817 * 2 ^ 59
def prefixEnd_6984817 : Nat := 4983230072969 + 3 ^ 40 * 6984817 * 2
def baseEnd_6984817 : Nat := 3586568404695503605064917

theorem tailTrace_6984817 : CollatzResearch.WordTrace tailWord_6984817 prefixEnd_6984817 3586568404695503605064917 := by
  unfold tailWord_6984817
  simp only [CollatzResearch.WordTrace]
  refine ⟨254757205136208395616152705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169838136757472263744101803 254757205136208395616152705)
  ·
    refine ⟨191067903852156296712114529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254757205136208395616152705 191067903852156296712114529)
    ·
      refine ⟨143300927889117222534085897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191067903852156296712114529 143300927889117222534085897)
      ·
        refine ⟨107475695916837916900564423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143300927889117222534085897 107475695916837916900564423)
        ·
          refine ⟨161213543875256875350846635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107475695916837916900564423 161213543875256875350846635)
          ·
            refine ⟨241820315812885313026269953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161213543875256875350846635 241820315812885313026269953)
            ·
              refine ⟨181365236859663984769702465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241820315812885313026269953 181365236859663984769702465)
              ·
                refine ⟨136023927644747988577276849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181365236859663984769702465 136023927644747988577276849)
                ·
                  refine ⟨102017945733560991432957637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136023927644747988577276849 102017945733560991432957637)
                  ·
                    refine ⟨19128364825042685893679557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 102017945733560991432957637 19128364825042685893679557)
                    ·
                      refine ⟨3586568404695503605064917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19128364825042685893679557 3586568404695503605064917)
                      ·
                        rfl

theorem cell23_6984817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_6984817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984817 prefixEnd_6984817 := by exact prefixLift 6984817
  have htrace : WordTrace (prefixWord ++ tailWord_6984817) baseStart_6984817 baseEnd_6984817 := by
    simpa [prefixWord, tailWord_6984817, baseEnd_6984817] using wordTrace_append hprefix tailTrace_6984817
  have hstable : (prefixWord ++ tailWord_6984817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984817).length < 2 ^ (prefixWord ++ tailWord_6984817).sum := by decide
  have hdescent : baseEnd_6984817 < baseStart_6984817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984841 : List Nat := [1, 2, 1, 1, 4, 4, 2, 1, 2, 2, 3]
def baseStart_6984841 : Nat := 118140960795 + 6984841 * 2 ^ 59
def prefixEnd_6984841 : Nat := 4983230072969 + 3 ^ 40 * 6984841 * 2
def baseEnd_6984841 : Nat := 3586580728231211511164807

theorem tailTrace_6984841 : CollatzResearch.WordTrace tailWord_6984841 prefixEnd_6984841 3586580728231211511164807 := by
  unfold tailWord_6984841
  simp only [CollatzResearch.WordTrace]
  refine ⟨254758080488121447715026377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169838720325414298476684251 254758080488121447715026377)
  ·
    refine ⟨191068560366091085786269783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254758080488121447715026377 191068560366091085786269783)
    ·
      refine ⟨286602840549136628679404675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191068560366091085786269783 286602840549136628679404675)
      ·
        refine ⟨429904260823704943019107013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286602840549136628679404675 429904260823704943019107013)
        ·
          refine ⟨80607048904444676816082565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 429904260823704943019107013 80607048904444676816082565)
          ·
            refine ⟨15113821669583376903015481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80607048904444676816082565 15113821669583376903015481)
            ·
              refine ⟨11335366252187532677261611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15113821669583376903015481 11335366252187532677261611)
              ·
                refine ⟨17003049378281299015892417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11335366252187532677261611 17003049378281299015892417)
                ·
                  refine ⟨12752287033710974261919313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17003049378281299015892417 12752287033710974261919313)
                  ·
                    refine ⟨9564215275283230696439485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12752287033710974261919313 9564215275283230696439485)
                    ·
                      refine ⟨3586580728231211511164807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9564215275283230696439485 3586580728231211511164807)
                      ·
                        rfl

theorem cell23_6984841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 2, 3].length) (baseStart_6984841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984841 prefixEnd_6984841 := by exact prefixLift 6984841
  have htrace : WordTrace (prefixWord ++ tailWord_6984841) baseStart_6984841 baseEnd_6984841 := by
    simpa [prefixWord, tailWord_6984841, baseEnd_6984841] using wordTrace_append hprefix tailTrace_6984841
  have hstable : (prefixWord ++ tailWord_6984841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984841).length < 2 ^ (prefixWord ++ tailWord_6984841).sum := by decide
  have hdescent : baseEnd_6984841 < baseStart_6984841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984867 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 5]
def baseStart_6984867 : Nat := 118140960795 + 6984867 * 2 ^ 59
def prefixEnd_6984867 : Nat := 4983230072969 + 3 ^ 40 * 6984867 * 2
def baseEnd_6984867 : Nat := 3586594078728228409439687

theorem tailTrace_6984867 : CollatzResearch.WordTrace tailWord_6984867 prefixEnd_6984867 3586594078728228409439687 := by
  unfold tailWord_6984867
  simp only [CollatzResearch.WordTrace]
  refine ⟨254759028786027254155472855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169839352524018169436981903 254759028786027254155472855)
  ·
    refine ⟨382138543179040881233209283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254759028786027254155472855 382138543179040881233209283)
    ·
      refine ⟨573207814768561321849813925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382138543179040881233209283 573207814768561321849813925)
      ·
        refine ⟨107476465269105247846840111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 573207814768561321849813925 107476465269105247846840111)
        ·
          refine ⟨161214697903657871770260167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107476465269105247846840111 161214697903657871770260167)
          ·
            refine ⟨241822046855486807655390251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161214697903657871770260167 241822046855486807655390251)
            ·
              refine ⟨362733070283230211483085377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241822046855486807655390251 362733070283230211483085377)
              ·
                refine ⟨272049802712422658612314033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362733070283230211483085377 272049802712422658612314033)
                ·
                  refine ⟨204037352034316993959235525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 272049802712422658612314033 204037352034316993959235525)
                  ·
                    refine ⟨38257003506434436367356661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 204037352034316993959235525 38257003506434436367356661)
                    ·
                      refine ⟨3586594078728228409439687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38257003506434436367356661 3586594078728228409439687)
                      ·
                        rfl

theorem cell23_6984867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_6984867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984867 prefixEnd_6984867 := by exact prefixLift 6984867
  have htrace : WordTrace (prefixWord ++ tailWord_6984867) baseStart_6984867 baseEnd_6984867 := by
    simpa [prefixWord, tailWord_6984867, baseEnd_6984867] using wordTrace_append hprefix tailTrace_6984867
  have hstable : (prefixWord ++ tailWord_6984867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984867).length < 2 ^ (prefixWord ++ tailWord_6984867).sum := by decide
  have hdescent : baseEnd_6984867 < baseStart_6984867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984904 : List Nat := [2, 1, 3, 1, 2, 1, 4, 2, 1, 6]
def baseStart_6984904 : Nat := 118140960795 + 6984904 * 2 ^ 59
def prefixEnd_6984904 : Nat := 4983230072969 + 3 ^ 40 * 6984904 * 2
def baseEnd_6984904 : Nat := 1195537692504148254892339

theorem tailTrace_6984904 : CollatzResearch.WordTrace tailWord_6984904 prefixEnd_6984904 1195537692504148254892339 := by
  unfold tailWord_6984904
  simp only [CollatzResearch.WordTrace]
  refine ⟨127380189143446604737284883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169840252191262139649713177 127380189143446604737284883)
  ·
    refine ⟨191070283715169907105927325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127380189143446604737284883 191070283715169907105927325)
    ·
      refine ⟨71651356393188715164722747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191070283715169907105927325 71651356393188715164722747)
      ·
        refine ⟨107477034589783072747084121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71651356393188715164722747 107477034589783072747084121)
        ·
          refine ⟨80607775942337304560313091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107477034589783072747084121 80607775942337304560313091)
          ·
            refine ⟨120911663913505956840469637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80607775942337304560313091 120911663913505956840469637)
            ·
              refine ⟨22670936983782366907588057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120911663913505956840469637 22670936983782366907588057)
              ·
                refine ⟨17003202737836775180691043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22670936983782366907588057 17003202737836775180691043)
                ·
                  refine ⟨25504804106755162771036565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17003202737836775180691043 25504804106755162771036565)
                  ·
                    refine ⟨1195537692504148254892339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25504804106755162771036565 1195537692504148254892339)
                    ·
                      rfl

theorem cell23_6984904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_6984904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984904 prefixEnd_6984904 := by exact prefixLift 6984904
  have htrace : WordTrace (prefixWord ++ tailWord_6984904) baseStart_6984904 baseEnd_6984904 := by
    simpa [prefixWord, tailWord_6984904, baseEnd_6984904] using wordTrace_append hprefix tailTrace_6984904
  have hstable : (prefixWord ++ tailWord_6984904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984904).length < 2 ^ (prefixWord ++ tailWord_6984904).sum := by decide
  have hdescent : baseEnd_6984904 < baseStart_6984904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984928 : List Nat := [2, 1, 1, 3, 1, 4, 1, 3, 3, 2, 2]
def baseStart_6984928 : Nat := 118140960795 + 6984928 * 2 ^ 59
def prefixEnd_6984928 : Nat := 4983230072969 + 3 ^ 40 * 6984928 * 2
def baseEnd_6984928 : Nat := 3586625401048152670776907

theorem tailTrace_6984928 : CollatzResearch.WordTrace tailWord_6984928 prefixEnd_6984928 3586625401048152670776907 := by
  unfold tailWord_6984928
  simp only [CollatzResearch.WordTrace]
  refine ⟨127380626819403130786721719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169840835759204174382295625 127380626819403130786721719)
  ·
    refine ⟨191070940229104696180082579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127380626819403130786721719 191070940229104696180082579)
    ·
      refine ⟨286606410343657044270123869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191070940229104696180082579 286606410343657044270123869)
      ·
        refine ⟨107477403878871391601296451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286606410343657044270123869 107477403878871391601296451)
        ·
          refine ⟨161216105818307087401944677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107477403878871391601296451 161216105818307087401944677)
          ·
            refine ⟨30228019840932578887864627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161216105818307087401944677 30228019840932578887864627)
            ·
              refine ⟨45342029761398868331796941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30228019840932578887864627 45342029761398868331796941)
              ·
                refine ⟨17003261160524575624423853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45342029761398868331796941 17003261160524575624423853)
                ·
                  refine ⟨6376222935196715859158945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17003261160524575624423853 6376222935196715859158945)
                  ·
                    refine ⟨4782167201397536894369209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6376222935196715859158945 4782167201397536894369209)
                    ·
                      refine ⟨3586625401048152670776907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4782167201397536894369209 3586625401048152670776907)
                      ·
                        rfl

theorem cell23_6984928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 3, 2, 2].length) (baseStart_6984928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984928 prefixEnd_6984928 := by exact prefixLift 6984928
  have htrace : WordTrace (prefixWord ++ tailWord_6984928) baseStart_6984928 baseEnd_6984928 := by
    simpa [prefixWord, tailWord_6984928, baseEnd_6984928] using wordTrace_append hprefix tailTrace_6984928
  have hstable : (prefixWord ++ tailWord_6984928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984928).length < 2 ^ (prefixWord ++ tailWord_6984928).sum := by decide
  have hdescent : baseEnd_6984928 < baseStart_6984928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984941 : List Nat := [1, 5, 1, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_6984941 : Nat := 118140960795 + 6984941 * 2 ^ 59
def prefixEnd_6984941 : Nat := 4983230072969 + 3 ^ 40 * 6984941 * 2
def baseEnd_6984941 : Nat := 3586632076296661119914347

theorem tailTrace_6984941 : CollatzResearch.WordTrace tailWord_6984941 prefixEnd_6984941 3586632076296661119914347 := by
  unfold tailWord_6984941
  simp only [CollatzResearch.WordTrace]
  refine ⟨254761727787759164793666677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169841151858506109862444451 254761727787759164793666677)
  ·
    refine ⟨23883911980102421699406251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 254761727787759164793666677 23883911980102421699406251)
    ·
      refine ⟨35825867970153632549109377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23883911980102421699406251 35825867970153632549109377)
      ·
        refine ⟨26869400977615224411832033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35825867970153632549109377 26869400977615224411832033)
        ·
          refine ⟨20152050733211418308874025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26869400977615224411832033 20152050733211418308874025)
          ·
            refine ⟨15114038049908563731655519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20152050733211418308874025 15114038049908563731655519)
            ·
              refine ⟨22671057074862845597483279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15114038049908563731655519 22671057074862845597483279)
              ·
                refine ⟨34006585612294268396224919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22671057074862845597483279 34006585612294268396224919)
                ·
                  refine ⟨51009878418441402594337379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34006585612294268396224919 51009878418441402594337379)
                  ·
                    refine ⟨76514817627662103891506069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51009878418441402594337379 76514817627662103891506069)
                    ·
                      refine ⟨3586632076296661119914347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76514817627662103891506069 3586632076296661119914347)
                      ·
                        rfl

theorem cell23_6984941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_6984941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984941 prefixEnd_6984941 := by exact prefixLift 6984941
  have htrace : WordTrace (prefixWord ++ tailWord_6984941) baseStart_6984941 baseEnd_6984941 := by
    simpa [prefixWord, tailWord_6984941, baseEnd_6984941] using wordTrace_append hprefix tailTrace_6984941
  have hstable : (prefixWord ++ tailWord_6984941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984941).length < 2 ^ (prefixWord ++ tailWord_6984941).sum := by decide
  have hdescent : baseEnd_6984941 < baseStart_6984941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6984995 : List Nat := [1, 1, 1, 4, 2, 3, 4, 1, 2, 1, 3]
def baseStart_6984995 : Nat := 118140960795 + 6984995 * 2 ^ 59
def prefixEnd_6984995 : Nat := 4983230072969 + 3 ^ 40 * 6984995 * 2
def baseEnd_6984995 : Nat := 3586659804252003908639099

theorem tailTrace_6984995 : CollatzResearch.WordTrace tailWord_6984995 prefixEnd_6984995 3586659804252003908639099 := by
  unfold tailWord_6984995
  simp only [CollatzResearch.WordTrace]
  refine ⟨254763697329563532016132439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169842464886375688010754959 254763697329563532016132439)
  ·
    refine ⟨382145545994345298024198659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 254763697329563532016132439 382145545994345298024198659)
    ·
      refine ⟨573218318991517947036297989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382145545994345298024198659 573218318991517947036297989)
      ·
        refine ⟨107478434810909615069305873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 573218318991517947036297989 107478434810909615069305873)
        ·
          refine ⟨80608826108182211301979405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107478434810909615069305873 80608826108182211301979405)
          ·
            refine ⟨30228309790568329238242277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80608826108182211301979405 30228309790568329238242277)
            ·
              refine ⟨5667808085731561732170427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30228309790568329238242277 5667808085731561732170427)
              ·
                refine ⟨8501712128597342598255641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5667808085731561732170427 8501712128597342598255641)
                ·
                  refine ⟨6376284096448006948691731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8501712128597342598255641 6376284096448006948691731)
                  ·
                    refine ⟨9564426144672010423037597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6376284096448006948691731 9564426144672010423037597)
                    ·
                      refine ⟨3586659804252003908639099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9564426144672010423037597 3586659804252003908639099)
                      ·
                        rfl

theorem cell23_6984995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 1, 2, 1, 3].length) (baseStart_6984995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6984995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6984995 prefixEnd_6984995 := by exact prefixLift 6984995
  have htrace : WordTrace (prefixWord ++ tailWord_6984995) baseStart_6984995 baseEnd_6984995 := by
    simpa [prefixWord, tailWord_6984995, baseEnd_6984995] using wordTrace_append hprefix tailTrace_6984995
  have hstable : (prefixWord ++ tailWord_6984995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6984995).length < 2 ^ (prefixWord ++ tailWord_6984995).sum := by decide
  have hdescent : baseEnd_6984995 < baseStart_6984995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6984995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985018 : List Nat := [3, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2]
def baseStart_6985018 : Nat := 118140960795 + 6985018 * 2 ^ 59
def prefixEnd_6985018 : Nat := 4983230072969 + 3 ^ 40 * 6985018 * 2
def baseEnd_6985018 : Nat := 3586671614307057318651493

theorem tailTrace_6985018 : CollatzResearch.WordTrace tailWord_6985018 prefixEnd_6985018 3586671614307057318651493 := by
  unfold tailWord_6985018
  simp only [CollatzResearch.WordTrace]
  refine ⟨63691134052120051736054927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169843024138986804629479805 63691134052120051736054927)
  ·
    refine ⟨95536701078180077604082391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63691134052120051736054927 95536701078180077604082391)
    ·
      refine ⟨143305051617270116406123587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95536701078180077604082391 143305051617270116406123587)
      ·
        refine ⟨214957577425905174609185381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143305051617270116406123587 214957577425905174609185381)
        ·
          refine ⟨40304545767357220239222259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 214957577425905174609185381 40304545767357220239222259)
          ·
            refine ⟨60456818651035830358833389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40304545767357220239222259 60456818651035830358833389)
            ·
              refine ⟨22671306994138436384562521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60456818651035830358833389 22671306994138436384562521)
              ·
                refine ⟨17003480245603827288421891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22671306994138436384562521 17003480245603827288421891)
                ·
                  refine ⟨25505220368405740932632837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17003480245603827288421891 25505220368405740932632837)
                  ·
                    refine ⟨4782228819076076424868657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25505220368405740932632837 4782228819076076424868657)
                    ·
                      refine ⟨3586671614307057318651493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4782228819076076424868657 3586671614307057318651493)
                      ·
                        rfl

theorem cell23_6985018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 1, 4, 2].length) (baseStart_6985018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985018 prefixEnd_6985018 := by exact prefixLift 6985018
  have htrace : WordTrace (prefixWord ++ tailWord_6985018) baseStart_6985018 baseEnd_6985018 := by
    simpa [prefixWord, tailWord_6985018, baseEnd_6985018] using wordTrace_append hprefix tailTrace_6985018
  have hstable : (prefixWord ++ tailWord_6985018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985018).length < 2 ^ (prefixWord ++ tailWord_6985018).sum := by decide
  have hdescent : baseEnd_6985018 < baseStart_6985018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985022 : List Nat := [4, 2, 1, 2, 1, 1, 5, 1, 1, 3, 2]
def baseStart_6985022 : Nat := 118140960795 + 6985022 * 2 ^ 59
def prefixEnd_6985022 : Nat := 4983230072969 + 3 ^ 40 * 6985022 * 2
def baseEnd_6985022 : Nat := 3586673668229675303001475

theorem tailTrace_6985022 : CollatzResearch.WordTrace tailWord_6985022 prefixEnd_6985022 3586673668229675303001475 := by
  unfold tailWord_6985022
  simp only [CollatzResearch.WordTrace]
  refine ⟨31845585262558214453420665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169843121400310477084910213 31845585262558214453420665)
  ·
    refine ⟨23884188946918660840065499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31845585262558214453420665 23884188946918660840065499)
    ·
      refine ⟨35826283420377991260098249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23884188946918660840065499 35826283420377991260098249)
      ·
        refine ⟨26869712565283493445073687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35826283420377991260098249 26869712565283493445073687)
        ·
          refine ⟨40304568847925240167610531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26869712565283493445073687 40304568847925240167610531)
          ·
            refine ⟨60456853271887860251415797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40304568847925240167610531 60456853271887860251415797)
            ·
              refine ⟨5667829994239486898570231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60456853271887860251415797 5667829994239486898570231)
              ·
                refine ⟨8501744991359230347855347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5667829994239486898570231 8501744991359230347855347)
                ·
                  refine ⟨12752617487038845521783021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8501744991359230347855347 12752617487038845521783021)
                  ·
                    refine ⟨4782231557639567070668633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12752617487038845521783021 4782231557639567070668633)
                    ·
                      refine ⟨3586673668229675303001475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4782231557639567070668633 3586673668229675303001475)
                      ·
                        rfl

theorem cell23_6985022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_6985022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985022 prefixEnd_6985022 := by exact prefixLift 6985022
  have htrace : WordTrace (prefixWord ++ tailWord_6985022) baseStart_6985022 baseEnd_6985022 := by
    simpa [prefixWord, tailWord_6985022, baseEnd_6985022] using wordTrace_append hprefix tailTrace_6985022
  have hstable : (prefixWord ++ tailWord_6985022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985022).length < 2 ^ (prefixWord ++ tailWord_6985022).sum := by decide
  have hdescent : baseEnd_6985022 < baseStart_6985022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985030 : List Nat := [6, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2]
def baseStart_6985030 : Nat := 118140960795 + 6985030 * 2 ^ 59
def prefixEnd_6985030 : Nat := 4983230072969 + 3 ^ 40 * 6985030 * 2
def baseEnd_6985030 : Nat := 3586677776074911271701439

theorem tailTrace_6985030 : CollatzResearch.WordTrace tailWord_6985030 prefixEnd_6985030 3586677776074911271701439 := by
  unfold tailWord_6985030
  simp only [CollatzResearch.WordTrace]
  refine ⟨7961405433888647906051767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 169843315922957821995771029 7961405433888647906051767)
  ·
    refine ⟨11942108150832971859077651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7961405433888647906051767 11942108150832971859077651)
    ·
      refine ⟨17913162226249457788616477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11942108150832971859077651 17913162226249457788616477)
      ·
        refine ⟨6717435834843546670731179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17913162226249457788616477 6717435834843546670731179)
        ·
          refine ⟨10076153752265320006096769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6717435834843546670731179 10076153752265320006096769)
          ·
            refine ⟨7557115314198990004572577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10076153752265320006096769 7557115314198990004572577)
            ·
              refine ⟨5667836485649242503429433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7557115314198990004572577 5667836485649242503429433)
              ·
                refine ⟨4250877364236931877572075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5667836485649242503429433 4250877364236931877572075)
                ·
                  refine ⟨6376316046355397816358113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4250877364236931877572075 6376316046355397816358113)
                  ·
                    refine ⟨4782237034766548362268585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6376316046355397816358113 4782237034766548362268585)
                    ·
                      refine ⟨3586677776074911271701439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4782237034766548362268585 3586677776074911271701439)
                      ·
                        rfl

theorem cell23_6985030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_6985030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985030 prefixEnd_6985030 := by exact prefixLift 6985030
  have htrace : WordTrace (prefixWord ++ tailWord_6985030) baseStart_6985030 baseEnd_6985030 := by
    simpa [prefixWord, tailWord_6985030, baseEnd_6985030] using wordTrace_append hprefix tailTrace_6985030
  have hstable : (prefixWord ++ tailWord_6985030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985030).length < 2 ^ (prefixWord ++ tailWord_6985030).sum := by decide
  have hdescent : baseEnd_6985030 < baseStart_6985030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985034 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 1, 2, 7]
def baseStart_6985034 : Nat := 118140960795 + 6985034 * 2 ^ 59
def prefixEnd_6985034 : Nat := 4983230072969 + 3 ^ 40 * 6985034 * 2
def baseEnd_6985034 : Nat := 3586679829997529256051419

theorem tailTrace_6985034 : CollatzResearch.WordTrace tailWord_6985034 prefixEnd_6985034 3586679829997529256051419 := by
  unfold tailWord_6985034
  simp only [CollatzResearch.WordTrace]
  refine ⟨63691279944105560419200539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169843413184281494451201437 63691279944105560419200539)
  ·
    refine ⟨95536919916158340628800809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63691279944105560419200539 95536919916158340628800809)
    ·
      refine ⟨71652689937118755471600607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95536919916158340628800809 71652689937118755471600607)
      ·
        refine ⟨107479034905678133207400911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71652689937118755471600607 107479034905678133207400911)
        ·
          refine ⟨161218552358517199811101367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107479034905678133207400911 161218552358517199811101367)
          ·
            refine ⟨241827828537775799716652051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161218552358517199811101367 241827828537775799716652051)
            ·
              refine ⟨362741742806663699574978077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241827828537775799716652051 362741742806663699574978077)
              ·
                refine ⟨136028153552498887340616779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 362741742806663699574978077 136028153552498887340616779)
                ·
                  refine ⟨204042230328748331010925169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136028153552498887340616779 204042230328748331010925169)
                  ·
                    refine ⟨153031672746561248258193877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 204042230328748331010925169 153031672746561248258193877)
                    ·
                      refine ⟨3586679829997529256051419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 153031672746561248258193877 3586679829997529256051419)
                      ·
                        rfl

theorem cell23_6985034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_6985034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985034 prefixEnd_6985034 := by exact prefixLift 6985034
  have htrace : WordTrace (prefixWord ++ tailWord_6985034) baseStart_6985034 baseEnd_6985034 := by
    simpa [prefixWord, tailWord_6985034, baseEnd_6985034] using wordTrace_append hprefix tailTrace_6985034
  have hstable : (prefixWord ++ tailWord_6985034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985034).length < 2 ^ (prefixWord ++ tailWord_6985034).sum := by decide
  have hdescent : baseEnd_6985034 < baseStart_6985034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985108 : List Nat := [2, 4, 2, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_6985108 : Nat := 118140960795 + 6985108 * 2 ^ 59
def prefixEnd_6985108 : Nat := 4983230072969 + 3 ^ 40 * 6985108 * 2
def baseEnd_6985108 : Nat := 3586717827565961966526079

theorem tailTrace_6985108 : CollatzResearch.WordTrace tailWord_6985108 prefixEnd_6985108 3586717827565961966526079 := by
  unfold tailWord_6985108
  simp only [CollatzResearch.WordTrace]
  refine ⟨127383909389077076157497989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169845212518769434876663985 127383909389077076157497989)
  ·
    refine ⟨23884483010451951779530873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127383909389077076157497989 23884483010451951779530873)
    ·
      refine ⟨17913362257838963834648155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23884483010451951779530873 17913362257838963834648155)
      ·
        refine ⟨26870043386758445751972233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17913362257838963834648155 26870043386758445751972233)
        ·
          refine ⟨20152532540068834313979175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26870043386758445751972233 20152532540068834313979175)
          ·
            refine ⟨30228798810103251470968763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20152532540068834313979175 30228798810103251470968763)
            ·
              refine ⟨45343198215154877206453145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30228798810103251470968763 45343198215154877206453145)
              ·
                refine ⟨34007398661366157904839859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45343198215154877206453145 34007398661366157904839859)
                ·
                  refine ⟨51011097992049236857259789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34007398661366157904839859 51011097992049236857259789)
                  ·
                    refine ⟨19129161747018463821472421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51011097992049236857259789 19129161747018463821472421)
                    ·
                      refine ⟨3586717827565961966526079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19129161747018463821472421 3586717827565961966526079)
                      ·
                        rfl

theorem cell23_6985108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_6985108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985108 prefixEnd_6985108 := by exact prefixLift 6985108
  have htrace : WordTrace (prefixWord ++ tailWord_6985108) baseStart_6985108 baseEnd_6985108 := by
    simpa [prefixWord, tailWord_6985108, baseEnd_6985108] using wordTrace_append hprefix tailTrace_6985108
  have hstable : (prefixWord ++ tailWord_6985108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985108).length < 2 ^ (prefixWord ++ tailWord_6985108).sum := by decide
  have hdescent : baseEnd_6985108 < baseStart_6985108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985145 : List Nat := [1, 2, 1, 4, 4, 1, 1, 2, 2, 2, 3]
def baseStart_6985145 : Nat := 118140960795 + 6985145 * 2 ^ 59
def prefixEnd_6985145 : Nat := 4983230072969 + 3 ^ 40 * 6985145 * 2
def baseEnd_6985145 : Nat := 3586736826350178321763409

theorem tailTrace_6985145 : CollatzResearch.WordTrace tailWord_6985145 prefixEnd_6985145 3586736826350178321763409 := by
  unfold tailWord_6985145
  simp only [CollatzResearch.WordTrace]
  refine ⟨254769168279020107634092889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169846112186013405089395259 254769168279020107634092889)
  ·
    refine ⟨191076876209265080725569667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254769168279020107634092889 191076876209265080725569667)
    ·
      refine ⟨286615314313897621088354501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191076876209265080725569667 286615314313897621088354501)
      ·
        refine ⟨53740371433855803954066469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 286615314313897621088354501 53740371433855803954066469)
        ·
          refine ⟨10076319643847963241387463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53740371433855803954066469 10076319643847963241387463)
          ·
            refine ⟨15114479465771944862081195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10076319643847963241387463 15114479465771944862081195)
            ·
              refine ⟨22671719198657917293121793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15114479465771944862081195 22671719198657917293121793)
              ·
                refine ⟨17003789398993437969841345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22671719198657917293121793 17003789398993437969841345)
                ·
                  refine ⟨12752842049245078477381009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17003789398993437969841345 12752842049245078477381009)
                  ·
                    refine ⟨9564631536933808858035757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12752842049245078477381009 9564631536933808858035757)
                    ·
                      refine ⟨3586736826350178321763409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9564631536933808858035757 3586736826350178321763409)
                      ·
                        rfl

theorem cell23_6985145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_6985145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985145 prefixEnd_6985145 := by exact prefixLift 6985145
  have htrace : WordTrace (prefixWord ++ tailWord_6985145) baseStart_6985145 baseEnd_6985145 := by
    simpa [prefixWord, tailWord_6985145, baseEnd_6985145] using wordTrace_append hprefix tailTrace_6985145
  have hstable : (prefixWord ++ tailWord_6985145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985145).length < 2 ^ (prefixWord ++ tailWord_6985145).sum := by decide
  have hdescent : baseEnd_6985145 < baseStart_6985145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985161 : List Nat := [1, 2, 1, 1, 2, 1, 3, 4, 3, 5]
def baseStart_6985161 : Nat := 118140960795 + 6985161 * 2 ^ 59
def prefixEnd_6985161 : Nat := 4983230072969 + 3 ^ 40 * 6985161 * 2
def baseEnd_6985161 : Nat := 1195581680680216753054445

theorem tailTrace_6985161 : CollatzResearch.WordTrace tailWord_6985161 prefixEnd_6985161 1195581680680216753054445 := by
  unfold tailWord_6985161
  simp only [CollatzResearch.WordTrace]
  refine ⟨254769751846962142366675337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169846501231308094911116891 254769751846962142366675337)
  ·
    refine ⟨191077313885221606775006503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254769751846962142366675337 191077313885221606775006503)
    ·
      refine ⟨286615970827832410162509755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191077313885221606775006503 286615970827832410162509755)
      ·
        refine ⟨429923956241748615243764633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286615970827832410162509755 429923956241748615243764633)
        ·
          refine ⟨322442967181311461432823475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429923956241748615243764633 322442967181311461432823475)
          ·
            refine ⟨483664450771967192149235213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322442967181311461432823475 483664450771967192149235213)
            ·
              refine ⟨181374169039487697055963205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 483664450771967192149235213 181374169039487697055963205)
              ·
                refine ⟨34007656694903943197993101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181374169039487697055963205 34007656694903943197993101)
                ·
                  refine ⟨12752871260588978699247413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34007656694903943197993101 12752871260588978699247413)
                  ·
                    refine ⟨1195581680680216753054445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12752871260588978699247413 1195581680680216753054445)
                    ·
                      rfl

theorem cell23_6985161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 5].length) (baseStart_6985161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985161 prefixEnd_6985161 := by exact prefixLift 6985161
  have htrace : WordTrace (prefixWord ++ tailWord_6985161) baseStart_6985161 baseEnd_6985161 := by
    simpa [prefixWord, tailWord_6985161, baseEnd_6985161] using wordTrace_append hprefix tailTrace_6985161
  have hstable : (prefixWord ++ tailWord_6985161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985161).length < 2 ^ (prefixWord ++ tailWord_6985161).sum := by decide
  have hdescent : baseEnd_6985161 < baseStart_6985161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985178 : List Nat := [3, 1, 1, 2, 3, 3, 1, 1, 3, 5]
def baseStart_6985178 : Nat := 118140960795 + 6985178 * 2 ^ 59
def prefixEnd_6985178 : Nat := 4983230072969 + 3 ^ 40 * 6985178 * 2
def baseEnd_6985178 : Nat := 1195584590403925564216919

theorem tailTrace_6985178 : CollatzResearch.WordTrace tailWord_6985178 prefixEnd_6985178 1195584590403925564216919 := by
  unfold tailWord_6985178
  simp only [CollatzResearch.WordTrace]
  refine ⟨63692592971975138567511047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169846914591933702846696125 63692592971975138567511047)
  ·
    refine ⟨95538889457962707851266571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63692592971975138567511047 95538889457962707851266571)
    ·
      refine ⟨143308334186944061776899857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95538889457962707851266571 143308334186944061776899857)
      ·
        refine ⟨107481250640208046332674893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143308334186944061776899857 107481250640208046332674893)
        ·
          refine ⟨40305468990078017374753085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107481250640208046332674893 40305468990078017374753085)
          ·
            refine ⟨15114550871279256515532407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40305468990078017374753085 15114550871279256515532407)
            ·
              refine ⟨22671826306918884773298611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15114550871279256515532407 22671826306918884773298611)
              ·
                refine ⟨34007739460378327159947917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22671826306918884773298611 34007739460378327159947917)
                ·
                  refine ⟨12752902297641872684980469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34007739460378327159947917 12752902297641872684980469)
                  ·
                    refine ⟨1195584590403925564216919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12752902297641872684980469 1195584590403925564216919)
                    ·
                      rfl

theorem cell23_6985178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 3, 5].length) (baseStart_6985178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985178 prefixEnd_6985178 := by exact prefixLift 6985178
  have htrace : WordTrace (prefixWord ++ tailWord_6985178) baseStart_6985178 baseEnd_6985178 := by
    simpa [prefixWord, tailWord_6985178, baseEnd_6985178] using wordTrace_append hprefix tailTrace_6985178
  have hstable : (prefixWord ++ tailWord_6985178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985178).length < 2 ^ (prefixWord ++ tailWord_6985178).sum := by decide
  have hdescent : baseEnd_6985178 < baseStart_6985178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985185 : List Nat := [1, 2, 3, 1, 2, 3, 1, 3, 2, 3, 2]
def baseStart_6985185 : Nat := 118140960795 + 6985185 * 2 ^ 59
def prefixEnd_6985185 : Nat := 4983230072969 + 3 ^ 40 * 6985185 * 2
def baseEnd_6985185 : Nat := 3586757365576358165263225

theorem tailTrace_6985185 : CollatzResearch.WordTrace tailWord_6985185 prefixEnd_6985185 3586757365576358165263225 := by
  unfold tailWord_6985185
  simp only [CollatzResearch.WordTrace]
  refine ⟨254770627198875194465549009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169847084799250129643699339 254770627198875194465549009)
  ·
    refine ⟨191077970399156395849161757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254770627198875194465549009 191077970399156395849161757)
    ·
      refine ⟨71654238899683648443435659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191077970399156395849161757 71654238899683648443435659)
      ·
        refine ⟨107481358349525472665153489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71654238899683648443435659 107481358349525472665153489)
        ·
          refine ⟨80611018762144104498865117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107481358349525472665153489 80611018762144104498865117)
          ·
            refine ⟨30229132035804039187074419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80611018762144104498865117 30229132035804039187074419)
            ·
              refine ⟨45343698053706058780611629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30229132035804039187074419 45343698053706058780611629)
              ·
                refine ⟨17003886770139772042729361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45343698053706058780611629 17003886770139772042729361)
                ·
                  refine ⟨12752915077604829032047021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17003886770139772042729361 12752915077604829032047021)
                  ·
                    refine ⟨4782343154101810887017633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12752915077604829032047021 4782343154101810887017633)
                    ·
                      refine ⟨3586757365576358165263225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4782343154101810887017633 3586757365576358165263225)
                      ·
                        rfl

theorem cell23_6985185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 3, 2].length) (baseStart_6985185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985185 prefixEnd_6985185 := by exact prefixLift 6985185
  have htrace : WordTrace (prefixWord ++ tailWord_6985185) baseStart_6985185 baseEnd_6985185 := by
    simpa [prefixWord, tailWord_6985185, baseEnd_6985185] using wordTrace_append hprefix tailTrace_6985185
  have hstable : (prefixWord ++ tailWord_6985185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985185).length < 2 ^ (prefixWord ++ tailWord_6985185).sum := by decide
  have hdescent : baseEnd_6985185 < baseStart_6985185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985192 : List Nat := [2, 1, 4, 1, 1, 2, 2, 5, 1, 1, 3]
def baseStart_6985192 : Nat := 118140960795 + 6985192 * 2 ^ 59
def prefixEnd_6985192 : Nat := 4983230072969 + 3 ^ 40 * 6985192 * 2
def baseEnd_6985192 : Nat := 3586760959940939637875693

theorem tailTrace_6985192 : CollatzResearch.WordTrace tailWord_6985192 prefixEnd_6985192 3586760959940939637875693 := by
  unfold tailWord_6985192
  simp only [CollatzResearch.WordTrace]
  refine ⟨127385441254924917330526915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169847255006566556440702553 127385441254924917330526915)
  ·
    refine ⟨191078161882387375995790373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127385441254924917330526915 191078161882387375995790373)
    ·
      refine ⟨35827155352947632999210695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191078161882387375995790373 35827155352947632999210695)
      ·
        refine ⟨53740733029421449498816043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35827155352947632999210695 53740733029421449498816043)
        ·
          refine ⟨80611099544132174248224065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53740733029421449498816043 80611099544132174248224065)
          ·
            refine ⟨60458324658099130686168049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80611099544132174248224065 60458324658099130686168049)
            ·
              refine ⟨45343743493574348014626037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60458324658099130686168049 45343743493574348014626037)
              ·
                refine ⟨4250975952522595126371191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45343743493574348014626037 4250975952522595126371191)
                ·
                  refine ⟨6376463928783892689556787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4250975952522595126371191 6376463928783892689556787)
                  ·
                    refine ⟨9564695893175839034335181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6376463928783892689556787 9564695893175839034335181)
                    ·
                      refine ⟨3586760959940939637875693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9564695893175839034335181 3586760959940939637875693)
                      ·
                        rfl

theorem cell23_6985192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_6985192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985192 prefixEnd_6985192 := by exact prefixLift 6985192
  have htrace : WordTrace (prefixWord ++ tailWord_6985192) baseStart_6985192 baseEnd_6985192 := by
    simpa [prefixWord, tailWord_6985192, baseEnd_6985192] using wordTrace_append hprefix tailTrace_6985192
  have hstable : (prefixWord ++ tailWord_6985192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985192).length < 2 ^ (prefixWord ++ tailWord_6985192).sum := by decide
  have hdescent : baseEnd_6985192 < baseStart_6985192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985202 : List Nat := [3, 2, 1, 4, 1, 1, 2, 2, 2, 3, 2]
def baseStart_6985202 : Nat := 118140960795 + 6985202 * 2 ^ 59
def prefixEnd_6985202 : Nat := 4983230072969 + 3 ^ 40 * 6985202 * 2
def baseEnd_6985202 : Nat := 3586766094747484598750647

theorem tailTrace_6985202 : CollatzResearch.WordTrace tailWord_6985202 prefixEnd_6985202 3586766094747484598750647 := by
  unfold tailWord_6985202
  simp only [CollatzResearch.WordTrace]
  refine ⟨63692811809953401592229465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 169847498159875737579278573 63692811809953401592229465)
  ·
    refine ⟨47769608857465051194172099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63692811809953401592229465 47769608857465051194172099)
    ·
      refine ⟨71654413286197576791258149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47769608857465051194172099 71654413286197576791258149)
      ·
        refine ⟨13435202491162045648360903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71654413286197576791258149 13435202491162045648360903)
        ·
          refine ⟨20152803736743068472541355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13435202491162045648360903 20152803736743068472541355)
          ·
            refine ⟨30229205605114602708812033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20152803736743068472541355 30229205605114602708812033)
            ·
              refine ⟨22671904203835952031609025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30229205605114602708812033 22671904203835952031609025)
              ·
                refine ⟨17003928152876964023706769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22671904203835952031609025 17003928152876964023706769)
                ·
                  refine ⟨12752946114657723017780077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17003928152876964023706769 12752946114657723017780077)
                  ·
                    refine ⟨4782354792996646131667529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12752946114657723017780077 4782354792996646131667529)
                    ·
                      refine ⟨3586766094747484598750647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4782354792996646131667529 3586766094747484598750647)
                      ·
                        rfl

theorem cell23_6985202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_6985202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985202 prefixEnd_6985202 := by exact prefixLift 6985202
  have htrace : WordTrace (prefixWord ++ tailWord_6985202) baseStart_6985202 baseEnd_6985202 := by
    simpa [prefixWord, tailWord_6985202, baseEnd_6985202] using wordTrace_append hprefix tailTrace_6985202
  have hstable : (prefixWord ++ tailWord_6985202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985202).length < 2 ^ (prefixWord ++ tailWord_6985202).sum := by decide
  have hdescent : baseEnd_6985202 < baseStart_6985202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985236 : List Nat := [2, 4, 3, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_6985236 : Nat := 118140960795 + 6985236 * 2 ^ 59
def prefixEnd_6985236 : Nat := 4983230072969 + 3 ^ 40 * 6985236 * 2
def baseEnd_6985236 : Nat := 3586783553089737465725491

theorem tailTrace_6985236 : CollatzResearch.WordTrace tailWord_6985236 prefixEnd_6985236 3586783553089737465725491 := by
  unfold tailWord_6985236
  simp only [CollatzResearch.WordTrace]
  refine ⟨127386243660845215087827781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169848324881126953450437041 127386243660845215087827781)
  ·
    refine ⟨23884920686408477828967709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127386243660845215087827781 23884920686408477828967709)
    ·
      refine ⟨8956845257403179185862891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23884920686408477828967709 8956845257403179185862891)
      ·
        refine ⟨13435267886104768778794337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8956845257403179185862891 13435267886104768778794337)
        ·
          refine ⟨10076450914578576584095753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13435267886104768778794337 10076450914578576584095753)
          ·
            refine ⟨7557338185933932438071815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10076450914578576584095753 7557338185933932438071815)
            ·
              refine ⟨11336007278900898657107723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7557338185933932438071815 11336007278900898657107723)
              ·
                refine ⟨17004010918351347985661585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11336007278900898657107723 17004010918351347985661585)
                ·
                  refine ⟨12753008188763510989246189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17004010918351347985661585 12753008188763510989246189)
                  ·
                    refine ⟨4782378070786316620967321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12753008188763510989246189 4782378070786316620967321)
                    ·
                      refine ⟨3586783553089737465725491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4782378070786316620967321 3586783553089737465725491)
                      ·
                        rfl

theorem cell23_6985236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_6985236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985236 prefixEnd_6985236 := by exact prefixLift 6985236
  have htrace : WordTrace (prefixWord ++ tailWord_6985236) baseStart_6985236 baseEnd_6985236 := by
    simpa [prefixWord, tailWord_6985236, baseEnd_6985236] using wordTrace_append hprefix tailTrace_6985236
  have hstable : (prefixWord ++ tailWord_6985236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985236).length < 2 ^ (prefixWord ++ tailWord_6985236).sum := by decide
  have hdescent : baseEnd_6985236 < baseStart_6985236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985246 : List Nat := [4, 3, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_6985246 : Nat := 118140960795 + 6985246 * 2 ^ 59
def prefixEnd_6985246 : Nat := 4983230072969 + 3 ^ 40 * 6985246 * 2
def baseEnd_6985246 : Nat := 1195596229298760808866815

theorem tailTrace_6985246 : CollatzResearch.WordTrace tailWord_6985246 prefixEnd_6985246 1195596229298760808866815 := by
  unfold tailWord_6985246
  simp only [CollatzResearch.WordTrace]
  refine ⟨31846606506456775235439949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 169848568034436134589013061 31846606506456775235439949)
  ·
    refine ⟨11942477439921290713289981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31846606506456775235439949 11942477439921290713289981)
    ·
      refine ⟨4478429039970484017483743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11942477439921290713289981 4478429039970484017483743)
      ·
        refine ⟨6717643559955726026225615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4478429039970484017483743 6717643559955726026225615)
        ·
          refine ⟨10076465339933589039338423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6717643559955726026225615 10076465339933589039338423)
          ·
            refine ⟨15114698009900383559007635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10076465339933589039338423 15114698009900383559007635)
            ·
              refine ⟨22672047014850575338511453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15114698009900383559007635 22672047014850575338511453)
              ·
                refine ⟨8502017630568965751941795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22672047014850575338511453 8502017630568965751941795)
                ·
                  refine ⟨12753026445853448627912693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8502017630568965751941795 12753026445853448627912693)
                  ·
                    refine ⟨1195596229298760808866815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12753026445853448627912693 1195596229298760808866815)
                    ·
                      rfl

theorem cell23_6985246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_6985246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985246 prefixEnd_6985246 := by exact prefixLift 6985246
  have htrace : WordTrace (prefixWord ++ tailWord_6985246) baseStart_6985246 baseEnd_6985246 := by
    simpa [prefixWord, tailWord_6985246, baseEnd_6985246] using wordTrace_append hprefix tailTrace_6985246
  have hstable : (prefixWord ++ tailWord_6985246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985246).length < 2 ^ (prefixWord ++ tailWord_6985246).sum := by decide
  have hdescent : baseEnd_6985246 < baseStart_6985246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985249 : List Nat := [1, 2, 3, 2, 2, 2, 1, 5, 1, 2, 2]
def baseStart_6985249 : Nat := 118140960795 + 6985249 * 2 ^ 59
def prefixEnd_6985249 : Nat := 4983230072969 + 3 ^ 40 * 6985249 * 2
def baseEnd_6985249 : Nat := 3586790228338245914862931

theorem tailTrace_6985249 : CollatzResearch.WordTrace tailWord_6985249 prefixEnd_6985249 3586790228338245914862931 := by
  unfold tailWord_6985249
  simp only [CollatzResearch.WordTrace]
  refine ⟨254772961470643333395878801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 169848640980428888930585867 254772961470643333395878801)
  ·
    refine ⟨191079721102982500046909101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 254772961470643333395878801 191079721102982500046909101)
    ·
      refine ⟨71654895413618437517590913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191079721102982500046909101 71654895413618437517590913)
      ·
        refine ⟨53741171560213828138193185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71654895413618437517590913 53741171560213828138193185)
        ·
          refine ⟨40305878670160371103644889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53741171560213828138193185 40305878670160371103644889)
          ·
            refine ⟨30229409002620278327733667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40305878670160371103644889 30229409002620278327733667)
            ·
              refine ⟨45344113503930417491600501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30229409002620278327733667 45344113503930417491600501)
              ·
                refine ⟨4251010640993476639837547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45344113503930417491600501 4251010640993476639837547)
                ·
                  refine ⟨6376515961490214959756321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4251010640993476639837547 6376515961490214959756321)
                  ·
                    refine ⟨4782386971117661219817241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6376515961490214959756321 4782386971117661219817241)
                    ·
                      refine ⟨3586790228338245914862931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4782386971117661219817241 3586790228338245914862931)
                      ·
                        rfl

theorem cell23_6985249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_6985249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985249 prefixEnd_6985249 := by exact prefixLift 6985249
  have htrace : WordTrace (prefixWord ++ tailWord_6985249) baseStart_6985249 baseEnd_6985249 := by
    simpa [prefixWord, tailWord_6985249, baseEnd_6985249] using wordTrace_append hprefix tailTrace_6985249
  have hstable : (prefixWord ++ tailWord_6985249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985249).length < 2 ^ (prefixWord ++ tailWord_6985249).sum := by decide
  have hdescent : baseEnd_6985249 < baseStart_6985249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985286 : List Nat := [6, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_6985286 : Nat := 118140960795 + 6985286 * 2 ^ 59
def prefixEnd_6985286 : Nat := 4983230072969 + 3 ^ 40 * 6985286 * 2
def baseEnd_6985286 : Nat := 3586809227122462270100261

theorem tailTrace_6985286 : CollatzResearch.WordTrace tailWord_6985286 prefixEnd_6985286 3586809227122462270100261 := by
  unfold tailWord_6985286
  simp only [CollatzResearch.WordTrace]
  refine ⟨7961697217859665272342991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 169849540647672859143317141 7961697217859665272342991)
  ·
    refine ⟨11942545826789497908514487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7961697217859665272342991 11942545826789497908514487)
    ·
      refine ⟨17913818740184246862771731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11942545826789497908514487 17913818740184246862771731)
      ·
        refine ⟨26870728110276370294157597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17913818740184246862771731 26870728110276370294157597)
        ·
          refine ⟨10076523041353638860309099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26870728110276370294157597 10076523041353638860309099)
          ·
            refine ⟨15114784562030458290463649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10076523041353638860309099 15114784562030458290463649)
            ·
              refine ⟨11336088421522843717847737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15114784562030458290463649 11336088421522843717847737)
              ·
                refine ⟨8502066316142132788385803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11336088421522843717847737 8502066316142132788385803)
                ·
                  refine ⟨12753099474213199182578705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8502066316142132788385803 12753099474213199182578705)
                  ·
                    refine ⟨9564824605659899386934029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12753099474213199182578705 9564824605659899386934029)
                    ·
                      refine ⟨3586809227122462270100261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9564824605659899386934029 3586809227122462270100261)
                      ·
                        rfl

theorem cell23_6985286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_6985286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985286 prefixEnd_6985286 := by exact prefixLift 6985286
  have htrace : WordTrace (prefixWord ++ tailWord_6985286) baseStart_6985286 baseEnd_6985286 := by
    simpa [prefixWord, tailWord_6985286, baseEnd_6985286] using wordTrace_append hprefix tailTrace_6985286
  have hstable : (prefixWord ++ tailWord_6985286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985286).length < 2 ^ (prefixWord ++ tailWord_6985286).sum := by decide
  have hdescent : baseEnd_6985286 < baseStart_6985286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6985292 : List Nat := [2, 2, 1, 3, 1, 3, 1, 4, 1, 3, 2]
def baseStart_6985292 : Nat := 118140960795 + 6985292 * 2 ^ 59
def prefixEnd_6985292 : Nat := 4983230072969 + 3 ^ 40 * 6985292 * 2
def baseEnd_6985292 : Nat := 3586812308006389246625233

theorem tailTrace_6985292 : CollatzResearch.WordTrace tailWord_6985292 prefixEnd_6985292 3586812308006389246625233 := by
  unfold tailWord_6985292
  simp only [CollatzResearch.WordTrace]
  refine ⟨127387264904743775869847065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 169849686539658367826462753 127387264904743775869847065)
  ·
    refine ⟨95540448678557831902385299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127387264904743775869847065 95540448678557831902385299)
    ·
      refine ⟨143310673017836747853577949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95540448678557831902385299 143310673017836747853577949)
      ·
        refine ⟨53741502381688780445091731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143310673017836747853577949 53741502381688780445091731)
        ·
          refine ⟨80612253572533170667637597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53741502381688780445091731 80612253572533170667637597)
          ·
            refine ⟨30229595089699939000364099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80612253572533170667637597 30229595089699939000364099)
            ·
              refine ⟨45344392634549908500546149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30229595089699939000364099 45344392634549908500546149)
              ·
                refine ⟨8502073618978107843852403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45344392634549908500546149 8502073618978107843852403)
                ·
                  refine ⟨12753110428467161765778605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8502073618978107843852403 12753110428467161765778605)
                  ·
                    refine ⟨4782416410675185662166977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12753110428467161765778605 4782416410675185662166977)
                    ·
                      refine ⟨3586812308006389246625233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4782416410675185662166977 3586812308006389246625233)
                      ·
                        rfl

theorem cell23_6985292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_6985292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6985292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6985292 prefixEnd_6985292 := by exact prefixLift 6985292
  have htrace : WordTrace (prefixWord ++ tailWord_6985292) baseStart_6985292 baseEnd_6985292 := by
    simpa [prefixWord, tailWord_6985292, baseEnd_6985292] using wordTrace_append hprefix tailTrace_6985292
  have hstable : (prefixWord ++ tailWord_6985292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6985292).length < 2 ^ (prefixWord ++ tailWord_6985292).sum := by decide
  have hdescent : baseEnd_6985292 < baseStart_6985292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6985292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
