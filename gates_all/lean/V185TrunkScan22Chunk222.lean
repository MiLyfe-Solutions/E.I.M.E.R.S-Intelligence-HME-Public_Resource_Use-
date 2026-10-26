import V185TrunkScan22Chunk221

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1979054 : List Nat := [4, 1, 4, 1, 1, 2, 1, 3, 5]
def baseStart_1979054 : Nat := 118140960795 + 1979054 * 2 ^ 59
def prefixEnd_1979054 : Nat := 4983230072969 + 3 ^ 40 * 1979054 * 2
def baseEnd_1979054 : Nat := 225823542934045594627445

theorem tailTrace_1979054 : CollatzResearch.WordTrace tailWord_1979054 prefixEnd_1979054 225823542934045594627445 := by
  unfold tailWord_1979054
  simp only [CollatzResearch.WordTrace]
  refine ⟨9022753671529103544889027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48121352914821885572741477 9022753671529103544889027)
  ·
    refine ⟨13534130507293655317333541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9022753671529103544889027 13534130507293655317333541)
    ·
      refine ⟨2537649470117560372000039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13534130507293655317333541 2537649470117560372000039)
      ·
        refine ⟨3806474205176340558000059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2537649470117560372000039 3806474205176340558000059)
        ·
          refine ⟨5709711307764510837000089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3806474205176340558000059 5709711307764510837000089)
          ·
            refine ⟨4282283480823383127750067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5709711307764510837000089 4282283480823383127750067)
            ·
              refine ⟨6423425221235074691625101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4282283480823383127750067 6423425221235074691625101)
              ·
                refine ⟨2408784457963153009359413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6423425221235074691625101 2408784457963153009359413)
                ·
                  refine ⟨225823542934045594627445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2408784457963153009359413 225823542934045594627445)
                  ·
                    rfl

theorem cell22_1979054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_1979054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979054 prefixEnd_1979054 := by exact prefixLift 1979054
  have htrace : WordTrace (prefixWord ++ tailWord_1979054) baseStart_1979054 baseEnd_1979054 := by
    simpa [prefixWord, tailWord_1979054, baseEnd_1979054] using wordTrace_append hprefix tailTrace_1979054
  have hstable : (prefixWord ++ tailWord_1979054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979054).length < 2 ^ (prefixWord ++ tailWord_1979054).sum := by decide
  have hdescent : baseEnd_1979054 < baseStart_1979054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979080 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 3, 5]
def baseStart_1979080 : Nat := 118140960795 + 1979080 * 2 ^ 59
def prefixEnd_1979080 : Nat := 4983230072969 + 3 ^ 40 * 1979080 * 2
def baseEnd_1979080 : Nat := 677479529133481382732255

theorem tailTrace_1979080 : CollatzResearch.WordTrace tailWord_1979080 prefixEnd_1979080 677479529133481382732255 := by
  unfold tailWord_1979080
  simp only [CollatzResearch.WordTrace]
  refine ⟨36091488835069317399779347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48121985113425756533039129 36091488835069317399779347)
  ·
    refine ⟨54137233252603976099669021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36091488835069317399779347 54137233252603976099669021)
    ·
      refine ⟨20301462469726491037375883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54137233252603976099669021 20301462469726491037375883)
      ·
        refine ⟨30452193704589736556063825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20301462469726491037375883 30452193704589736556063825)
        ·
          refine ⟨22839145278442302417047869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30452193704589736556063825 22839145278442302417047869)
          ·
            refine ⟨8564679479415863406392951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22839145278442302417047869 8564679479415863406392951)
            ·
              refine ⟨12847019219123795109589427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8564679479415863406392951 12847019219123795109589427)
              ·
                refine ⟨19270528828685692664384141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12847019219123795109589427 19270528828685692664384141)
                ·
                  refine ⟨7226448310757134749144053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19270528828685692664384141 7226448310757134749144053)
                  ·
                    refine ⟨677479529133481382732255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7226448310757134749144053 677479529133481382732255)
                    ·
                      rfl

theorem cell22_1979080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_1979080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979080 prefixEnd_1979080 := by exact prefixLift 1979080
  have htrace : WordTrace (prefixWord ++ tailWord_1979080) baseStart_1979080 baseEnd_1979080 := by
    simpa [prefixWord, tailWord_1979080, baseEnd_1979080] using wordTrace_append hprefix tailTrace_1979080
  have hstable : (prefixWord ++ tailWord_1979080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979080).length < 2 ^ (prefixWord ++ tailWord_1979080).sum := by decide
  have hdescent : baseEnd_1979080 < baseStart_1979080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979155 : List Nat := [1, 1, 1, 2, 1, 3, 5, 1, 7]
def baseStart_1979155 : Nat := 118140960795 + 1979155 * 2 ^ 59
def prefixEnd_1979155 : Nat := 4983230072969 + 3 ^ 40 * 1979155 * 2
def baseEnd_1979155 : Nat := 225835067722068729035675

theorem tailTrace_1979155 : CollatzResearch.WordTrace tailWord_1979155 prefixEnd_1979155 225835067722068729035675 := by
  unfold tailWord_1979155
  simp only [CollatzResearch.WordTrace]
  refine ⟨72185713144866922608538919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48123808763244615072359279 72185713144866922608538919)
  ·
    refine ⟨108278569717300383912808379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72185713144866922608538919 108278569717300383912808379)
    ·
      refine ⟨162417854575950575869212569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108278569717300383912808379 162417854575950575869212569)
      ·
        refine ⟨121813390931962931901909427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162417854575950575869212569 121813390931962931901909427)
        ·
          refine ⟨182720086397944397852864141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121813390931962931901909427 182720086397944397852864141)
          ·
            refine ⟨68520032399229149194824053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 182720086397944397852864141 68520032399229149194824053)
            ·
              refine ⟨6423753037427732737014755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68520032399229149194824053 6423753037427732737014755)
              ·
                refine ⟨9635629556141599105522133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6423753037427732737014755 9635629556141599105522133)
                ·
                  refine ⟨225835067722068729035675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9635629556141599105522133 225835067722068729035675)
                  ·
                    rfl

theorem cell22_1979155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 7].length) (baseStart_1979155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979155 prefixEnd_1979155 := by exact prefixLift 1979155
  have htrace : WordTrace (prefixWord ++ tailWord_1979155) baseStart_1979155 baseEnd_1979155 := by
    simpa [prefixWord, tailWord_1979155, baseEnd_1979155] using wordTrace_append hprefix tailTrace_1979155
  have hstable : (prefixWord ++ tailWord_1979155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979155).length < 2 ^ (prefixWord ++ tailWord_1979155).sum := by decide
  have hdescent : baseEnd_1979155 < baseStart_1979155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979178 : List Nat := [3, 1, 4, 3, 2, 1, 2, 6]
def baseStart_1979178 : Nat := 118140960795 + 1979178 * 2 ^ 59
def prefixEnd_1979178 : Nat := 4983230072969 + 3 ^ 40 * 1979178 * 2
def baseEnd_1979178 : Nat := 75279230726249088197995

theorem tailTrace_1979178 : CollatzResearch.WordTrace tailWord_1979178 prefixEnd_1979178 75279230726249088197995 := by
  unfold tailWord_1979178
  simp only [CollatzResearch.WordTrace]
  refine ⟨18046638005945899384156547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48124368015855731691084125 18046638005945899384156547)
  ·
    refine ⟨27069957008918849076234821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18046638005945899384156547 27069957008918849076234821)
    ·
      refine ⟨5075616939172284201794029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27069957008918849076234821 5075616939172284201794029)
      ·
        refine ⟨1903356352189606575672761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5075616939172284201794029 1903356352189606575672761)
        ·
          refine ⟨1427517264142204931754571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1903356352189606575672761 1427517264142204931754571)
          ·
            refine ⟨2141275896213307397631857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427517264142204931754571 2141275896213307397631857)
            ·
              refine ⟨1605956922159980548223893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2141275896213307397631857 1605956922159980548223893)
              ·
                refine ⟨75279230726249088197995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1605956922159980548223893 75279230726249088197995)
                ·
                  rfl

theorem cell22_1979178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 6].length) (baseStart_1979178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979178 prefixEnd_1979178 := by exact prefixLift 1979178
  have htrace : WordTrace (prefixWord ++ tailWord_1979178) baseStart_1979178 baseEnd_1979178 := by
    simpa [prefixWord, tailWord_1979178, baseEnd_1979178] using wordTrace_append hprefix tailTrace_1979178
  have hstable : (prefixWord ++ tailWord_1979178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979178).length < 2 ^ (prefixWord ++ tailWord_1979178).sum := by decide
  have hdescent : baseEnd_1979178 < baseStart_1979178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979200 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 8]
def baseStart_1979200 : Nat := 118140960795 + 1979200 * 2 ^ 59
def prefixEnd_1979200 : Nat := 4983230072969 + 3 ^ 40 * 1979200 * 2
def baseEnd_1979200 : Nat := 225840202528613689910629

theorem tailTrace_1979200 : CollatzResearch.WordTrace tailWord_1979200 prefixEnd_1979200 225840202528613689910629 := by
  unfold tailWord_1979200
  simp only [CollatzResearch.WordTrace]
  refine ⟨36093677214851947646963527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48124902953135930195951369 36093677214851947646963527)
  ·
    refine ⟨54140515822277921470445291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36093677214851947646963527 54140515822277921470445291)
    ·
      refine ⟨81210773733416882205667937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54140515822277921470445291 81210773733416882205667937)
      ·
        refine ⟨60908080300062661654250953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81210773733416882205667937 60908080300062661654250953)
        ·
          refine ⟨45681060225046996240688215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60908080300062661654250953 45681060225046996240688215)
          ·
            refine ⟨68521590337570494361032323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45681060225046996240688215 68521590337570494361032323)
            ·
              refine ⟨102782385506355741541548485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68521590337570494361032323 102782385506355741541548485)
              ·
                refine ⟨19271697282441701539040341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102782385506355741541548485 19271697282441701539040341)
                ·
                  refine ⟨225840202528613689910629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19271697282441701539040341 225840202528613689910629)
                  ·
                    rfl

theorem cell22_1979200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 8].length) (baseStart_1979200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979200 prefixEnd_1979200 := by exact prefixLift 1979200
  have htrace : WordTrace (prefixWord ++ tailWord_1979200) baseStart_1979200 baseEnd_1979200 := by
    simpa [prefixWord, tailWord_1979200, baseEnd_1979200] using wordTrace_append hprefix tailTrace_1979200
  have hstable : (prefixWord ++ tailWord_1979200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979200).length < 2 ^ (prefixWord ++ tailWord_1979200).sum := by decide
  have hdescent : baseEnd_1979200 < baseStart_1979200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979232 : List Nat := [2, 1, 1, 3, 3, 1, 2, 3, 1, 5]
def baseStart_1979232 : Nat := 118140960795 + 1979232 * 2 ^ 59
def prefixEnd_1979232 : Nat := 4983230072969 + 3 ^ 40 * 1979232 * 2
def baseEnd_1979232 : Nat := 677531561839803652931789

theorem tailTrace_1979232 : CollatzResearch.WordTrace tailWord_1979232 prefixEnd_1979232 677531561839803652931789 := by
  unfold tailWord_1979232
  simp only [CollatzResearch.WordTrace]
  refine ⟨36094260782793982379545975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48125681043725309839394633 36094260782793982379545975)
  ·
    refine ⟨54141391174190973569318963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36094260782793982379545975 54141391174190973569318963)
    ·
      refine ⟨81212086761286460353978445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54141391174190973569318963 81212086761286460353978445)
      ·
        refine ⟨30454532535482422632741917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81212086761286460353978445 30454532535482422632741917)
        ·
          refine ⟨11420449700805908487278219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30454532535482422632741917 11420449700805908487278219)
          ·
            refine ⟨17130674551208862730917329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11420449700805908487278219 17130674551208862730917329)
            ·
              refine ⟨12848005913406647048187997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17130674551208862730917329 12848005913406647048187997)
              ·
                refine ⟨4818002217527492643070499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12848005913406647048187997 4818002217527492643070499)
                ·
                  refine ⟨7227003326291238964605749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4818002217527492643070499 7227003326291238964605749)
                  ·
                    refine ⟨677531561839803652931789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7227003326291238964605749 677531561839803652931789)
                    ·
                      rfl

theorem cell22_1979232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 1, 5].length) (baseStart_1979232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979232 prefixEnd_1979232 := by exact prefixLift 1979232
  have htrace : WordTrace (prefixWord ++ tailWord_1979232) baseStart_1979232 baseEnd_1979232 := by
    simpa [prefixWord, tailWord_1979232, baseEnd_1979232] using wordTrace_append hprefix tailTrace_1979232
  have hstable : (prefixWord ++ tailWord_1979232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979232).length < 2 ^ (prefixWord ++ tailWord_1979232).sum := by decide
  have hdescent : baseEnd_1979232 < baseStart_1979232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979236 : List Nat := [2, 3, 1, 1, 4, 3, 1, 2, 1, 4]
def baseStart_1979236 : Nat := 118140960795 + 1979236 * 2 ^ 59
def prefixEnd_1979236 : Nat := 4983230072969 + 3 ^ 40 * 1979236 * 2
def baseEnd_1979236 : Nat := 677532931121548975831777

theorem tailTrace_1979236 : CollatzResearch.WordTrace tailWord_1979236 prefixEnd_1979236 677532931121548975831777 := by
  unfold tailWord_1979236
  simp only [CollatzResearch.WordTrace]
  refine ⟨36094333728786736721118781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48125778305048982294825041 36094333728786736721118781)
  ·
    refine ⟨13535375148295026270419543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36094333728786736721118781 13535375148295026270419543)
    ·
      refine ⟨20303062722442539405629315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13535375148295026270419543 20303062722442539405629315)
      ·
        refine ⟨30454594083663809108443973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20303062722442539405629315 30454594083663809108443973)
        ·
          refine ⟨5710236390686964207833245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30454594083663809108443973 5710236390686964207833245)
          ·
            refine ⟨2141338646507611577937467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5710236390686964207833245 2141338646507611577937467)
            ·
              refine ⟨3212007969761417366906201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2141338646507611577937467 3212007969761417366906201)
              ·
                refine ⟨2409005977321063025179651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3212007969761417366906201 2409005977321063025179651)
                ·
                  refine ⟨3613508965981594537769477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2409005977321063025179651 3613508965981594537769477)
                  ·
                    refine ⟨677532931121548975831777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3613508965981594537769477 677532931121548975831777)
                    ·
                      rfl

theorem cell22_1979236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_1979236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979236 prefixEnd_1979236 := by exact prefixLift 1979236
  have htrace : WordTrace (prefixWord ++ tailWord_1979236) baseStart_1979236 baseEnd_1979236 := by
    simpa [prefixWord, tailWord_1979236, baseEnd_1979236] using wordTrace_append hprefix tailTrace_1979236
  have hstable : (prefixWord ++ tailWord_1979236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979236).length < 2 ^ (prefixWord ++ tailWord_1979236).sum := by decide
  have hdescent : baseEnd_1979236 < baseStart_1979236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979322 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 4, 5]
def baseStart_1979322 : Nat := 118140960795 + 1979322 * 2 ^ 59
def prefixEnd_1979322 : Nat := 4983230072969 + 3 ^ 40 * 1979322 * 2
def baseEnd_1979322 : Nat := 677562370679073418181513

theorem tailTrace_1979322 : CollatzResearch.WordTrace tailWord_1979322 prefixEnd_1979322 677562370679073418181513 := by
  unfold tailWord_1979322
  simp only [CollatzResearch.WordTrace]
  refine ⟨18047951033815477532467055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48127869423507940086578813 18047951033815477532467055)
  ·
    refine ⟨27071926550723216298700583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18047951033815477532467055 27071926550723216298700583)
    ·
      refine ⟨40607889826084824448050875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27071926550723216298700583 40607889826084824448050875)
      ·
        refine ⟨60911834739127236672076313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40607889826084824448050875 60911834739127236672076313)
        ·
          refine ⟨45683876054345427504057235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60911834739127236672076313 45683876054345427504057235)
          ·
            refine ⟨68525814081518141256085853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45683876054345427504057235 68525814081518141256085853)
            ·
              refine ⟨25697180280569302971032195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68525814081518141256085853 25697180280569302971032195)
              ·
                refine ⟨38545770420853954456548293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25697180280569302971032195 38545770420853954456548293)
                ·
                  refine ⟨7227331953910116460602805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38545770420853954456548293 7227331953910116460602805)
                  ·
                    refine ⟨677562370679073418181513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7227331953910116460602805 677562370679073418181513)
                    ·
                      rfl

theorem cell22_1979322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_1979322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979322 prefixEnd_1979322 := by exact prefixLift 1979322
  have htrace : WordTrace (prefixWord ++ tailWord_1979322) baseStart_1979322 baseEnd_1979322 := by
    simpa [prefixWord, tailWord_1979322, baseEnd_1979322] using wordTrace_append hprefix tailTrace_1979322
  have hstable : (prefixWord ++ tailWord_1979322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979322).length < 2 ^ (prefixWord ++ tailWord_1979322).sum := by decide
  have hdescent : baseEnd_1979322 < baseStart_1979322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979334 : List Nat := [6, 1, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_1979334 : Nat := 118140960795 + 1979334 * 2 ^ 59
def prefixEnd_1979334 : Nat := 4983230072969 + 3 ^ 40 * 1979334 * 2
def baseEnd_1979334 : Nat := 677566478524309386881477

theorem tailTrace_1979334 : CollatzResearch.WordTrace tailWord_1979334 prefixEnd_1979334 677566478524309386881477 := by
  unfold tailWord_1979334
  simp only [CollatzResearch.WordTrace]
  refine ⟨2256007556600576130603283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48128161207478957452870037 2256007556600576130603283)
  ·
    refine ⟨3384011334900864195904925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2256007556600576130603283 3384011334900864195904925)
    ·
      refine ⟨1269004250587824073464347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3384011334900864195904925 1269004250587824073464347)
      ·
        refine ⟨1903506375881736110196521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1269004250587824073464347 1903506375881736110196521)
        ·
          refine ⟨1427629781911302082647391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1903506375881736110196521 1427629781911302082647391)
          ·
            refine ⟨2141444672866953123971087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427629781911302082647391 2141444672866953123971087)
            ·
              refine ⟨3212167009300429685956631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2141444672866953123971087 3212167009300429685956631)
              ·
                refine ⟨4818250513950644528934947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3212167009300429685956631 4818250513950644528934947)
                ·
                  refine ⟨7227375770925966793402421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4818250513950644528934947 7227375770925966793402421)
                  ·
                    refine ⟨677566478524309386881477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7227375770925966793402421 677566478524309386881477)
                    ·
                      rfl

theorem cell22_1979334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_1979334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979334 prefixEnd_1979334 := by exact prefixLift 1979334
  have htrace : WordTrace (prefixWord ++ tailWord_1979334) baseStart_1979334 baseEnd_1979334 := by
    simpa [prefixWord, tailWord_1979334, baseEnd_1979334] using wordTrace_append hprefix tailTrace_1979334
  have hstable : (prefixWord ++ tailWord_1979334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979334).length < 2 ^ (prefixWord ++ tailWord_1979334).sum := by decide
  have hdescent : baseEnd_1979334 < baseStart_1979334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979362 : List Nat := [3, 3, 3, 1, 1, 3, 1, 3, 1, 3]
def baseStart_1979362 : Nat := 118140960795 + 1979362 * 2 ^ 59
def prefixEnd_1979362 : Nat := 4983230072969 + 3 ^ 40 * 1979362 * 2
def baseEnd_1979362 : Nat := 677576063496526647181391

theorem tailTrace_1979362 : CollatzResearch.WordTrace tailWord_1979362 prefixEnd_1979362 677576063496526647181391 := by
  unfold tailWord_1979362
  simp only [CollatzResearch.WordTrace]
  refine ⟨18048315763779249240331085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48128842036744664640882893 18048315763779249240331085)
  ·
    refine ⟨6768118411417218465124157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18048315763779249240331085 6768118411417218465124157)
    ·
      refine ⟨2538044404281456924421559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6768118411417218465124157 2538044404281456924421559)
      ·
        refine ⟨3807066606422185386632339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2538044404281456924421559 3807066606422185386632339)
        ·
          refine ⟨5710599909633278079948509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3807066606422185386632339 5710599909633278079948509)
          ·
            refine ⟨2141474966112479279980691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5710599909633278079948509 2141474966112479279980691)
            ·
              refine ⟨3212212449168718919971037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2141474966112479279980691 3212212449168718919971037)
              ·
                refine ⟨1204579668438269594989139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3212212449168718919971037 1204579668438269594989139)
                ·
                  refine ⟨1806869502657404392483709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1204579668438269594989139 1806869502657404392483709)
                  ·
                    refine ⟨677576063496526647181391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1806869502657404392483709 677576063496526647181391)
                    ·
                      rfl

theorem cell22_1979362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_1979362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979362 prefixEnd_1979362 := by exact prefixLift 1979362
  have htrace : WordTrace (prefixWord ++ tailWord_1979362) baseStart_1979362 baseEnd_1979362 := by
    simpa [prefixWord, tailWord_1979362, baseEnd_1979362] using wordTrace_append hprefix tailTrace_1979362
  have hstable : (prefixWord ++ tailWord_1979362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979362).length < 2 ^ (prefixWord ++ tailWord_1979362).sum := by decide
  have hdescent : baseEnd_1979362 < baseStart_1979362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979399 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 4, 4]
def baseStart_1979399 : Nat := 118140960795 + 1979399 * 2 ^ 59
def prefixEnd_1979399 : Nat := 4983230072969 + 3 ^ 40 * 1979399 * 2
def baseEnd_1979399 : Nat := 677588729352670884006277

theorem tailTrace_1979399 : CollatzResearch.WordTrace tailWord_1979399 prefixEnd_1979399 677588729352670884006277 := by
  unfold tailWord_1979399
  simp only [CollatzResearch.WordTrace]
  refine ⟨72194612555982952280421251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48129741703988634853614167 72194612555982952280421251)
  ·
    refine ⟨108291918833974428420631877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72194612555982952280421251 108291918833974428420631877)
    ·
      refine ⟨20304734781370205328868477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108291918833974428420631877 20304734781370205328868477)
      ·
        refine ⟨7614275543013826998325679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20304734781370205328868477 7614275543013826998325679)
        ·
          refine ⟨11421413314520740497488519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7614275543013826998325679 11421413314520740497488519)
          ·
            refine ⟨17132119971781110746232779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11421413314520740497488519 17132119971781110746232779)
            ·
              refine ⟨25698179957671666119349169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17132119971781110746232779 25698179957671666119349169)
              ·
                refine ⟨19273634968253749589511877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25698179957671666119349169 19273634968253749589511877)
                ·
                  refine ⟨3613806556547578048033477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19273634968253749589511877 3613806556547578048033477)
                  ·
                    refine ⟨677588729352670884006277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3613806556547578048033477 677588729352670884006277)
                    ·
                      rfl

theorem cell22_1979399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_1979399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979399 prefixEnd_1979399 := by exact prefixLift 1979399
  have htrace : WordTrace (prefixWord ++ tailWord_1979399) baseStart_1979399 baseEnd_1979399 := by
    simpa [prefixWord, tailWord_1979399, baseEnd_1979399] using wordTrace_append hprefix tailTrace_1979399
  have hstable : (prefixWord ++ tailWord_1979399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979399).length < 2 ^ (prefixWord ++ tailWord_1979399).sum := by decide
  have hdescent : baseEnd_1979399 < baseStart_1979399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979416 : List Nat := [2, 1, 2, 3, 2, 3, 2, 1, 2, 4]
def baseStart_1979416 : Nat := 118140960795 + 1979416 * 2 ^ 59
def prefixEnd_1979416 : Nat := 4983230072969 + 3 ^ 40 * 1979416 * 2
def baseEnd_1979416 : Nat := 677594548800088506331225

theorem tailTrace_1979416 : CollatzResearch.WordTrace tailWord_1979416 prefixEnd_1979416 677594548800088506331225 := by
  unfold tailWord_1979416
  simp only [CollatzResearch.WordTrace]
  refine ⟨36097616298460682091895051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48130155064614242789193401 36097616298460682091895051)
  ·
    refine ⟨54146424447691023137842577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36097616298460682091895051 54146424447691023137842577)
    ·
      refine ⟨40609818335768267353381933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54146424447691023137842577 40609818335768267353381933)
      ·
        refine ⟨15228681875913100257518225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40609818335768267353381933 15228681875913100257518225)
        ·
          refine ⟨11421511406934825193138669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15228681875913100257518225 11421511406934825193138669)
          ·
            refine ⟨4283066777600559447427001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11421511406934825193138669 4283066777600559447427001)
            ·
              refine ⟨3212300083200419585570251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4283066777600559447427001 3212300083200419585570251)
              ·
                refine ⟨4818450124800629378355377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3212300083200419585570251 4818450124800629378355377)
                ·
                  refine ⟨3613837593600472033766533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4818450124800629378355377 3613837593600472033766533)
                  ·
                    refine ⟨677594548800088506331225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3613837593600472033766533 677594548800088506331225)
                    ·
                      rfl

theorem cell22_1979416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_1979416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979416 prefixEnd_1979416 := by exact prefixLift 1979416
  have htrace : WordTrace (prefixWord ++ tailWord_1979416) baseStart_1979416 baseEnd_1979416 := by
    simpa [prefixWord, tailWord_1979416, baseEnd_1979416] using wordTrace_append hprefix tailTrace_1979416
  have hstable : (prefixWord ++ tailWord_1979416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979416).length < 2 ^ (prefixWord ++ tailWord_1979416).sum := by decide
  have hdescent : baseEnd_1979416 < baseStart_1979416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979459 : List Nat := [1, 1, 1, 3, 1, 2, 3, 5, 5]
def baseStart_1979459 : Nat := 118140960795 + 1979459 * 2 ^ 59
def prefixEnd_1979459 : Nat := 4983230072969 + 3 ^ 40 * 1979459 * 2
def baseEnd_1979459 : Nat := 225869756192950242502031

theorem tailTrace_1979459 : CollatzResearch.WordTrace tailWord_1979459 prefixEnd_1979459 225869756192950242502031 := by
  unfold tailWord_1979459
  simp only [CollatzResearch.WordTrace]
  refine ⟨72196800935765582527605431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48131200623843721685070287 72196800935765582527605431)
  ·
    refine ⟨108295201403648373791408147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72196800935765582527605431 108295201403648373791408147)
    ·
      refine ⟨162442802105472560687112221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108295201403648373791408147 162442802105472560687112221)
      ·
        refine ⟨60916050789552210257667083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162442802105472560687112221 60916050789552210257667083)
        ·
          refine ⟨91374076184328315386500625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60916050789552210257667083 91374076184328315386500625)
          ·
            refine ⟨68530557138246236539875469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91374076184328315386500625 68530557138246236539875469)
            ·
              refine ⟨25698958926842338702453301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68530557138246236539875469 25698958926842338702453301)
              ·
                refine ⟨2409277399391469253354997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25698958926842338702453301 2409277399391469253354997)
                ·
                  refine ⟨225869756192950242502031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2409277399391469253354997 225869756192950242502031)
                  ·
                    rfl

theorem cell22_1979459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 5].length) (baseStart_1979459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979459 prefixEnd_1979459 := by exact prefixLift 1979459
  have htrace : WordTrace (prefixWord ++ tailWord_1979459) baseStart_1979459 baseEnd_1979459 := by
    simpa [prefixWord, tailWord_1979459, baseEnd_1979459] using wordTrace_append hprefix tailTrace_1979459
  have hstable : (prefixWord ++ tailWord_1979459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979459).length < 2 ^ (prefixWord ++ tailWord_1979459).sum := by decide
  have hdescent : baseEnd_1979459 < baseStart_1979459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979521 : List Nat := [1, 2, 4, 2, 2, 1, 2, 2, 6]
def baseStart_1979521 : Nat := 118140960795 + 1979521 * 2 ^ 59
def prefixEnd_1979521 : Nat := 4983230072969 + 3 ^ 40 * 1979521 * 2
def baseEnd_1979521 : Nat := 225876830815301077485301

theorem tailTrace_1979521 : CollatzResearch.WordTrace tailWord_1979521 prefixEnd_1979521 225876830815301077485301 := by
  unfold tailWord_1979521
  simp only [CollatzResearch.WordTrace]
  refine ⟨72199062261540967116362417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48132708174360644744241611 72199062261540967116362417)
  ·
    refine ⟨54149296696155725337271813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72199062261540967116362417 54149296696155725337271813)
    ·
      refine ⟨10152993130529198500738465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54149296696155725337271813 10152993130529198500738465)
      ·
        refine ⟨7614744847896898875553849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10152993130529198500738465 7614744847896898875553849)
        ·
          refine ⟨5711058635922674156665387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7614744847896898875553849 5711058635922674156665387)
          ·
            refine ⟨8566587953884011234998081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5711058635922674156665387 8566587953884011234998081)
            ·
              refine ⟨6424940965413008426248561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8566587953884011234998081 6424940965413008426248561)
              ·
                refine ⟨4818705724059756319686421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6424940965413008426248561 4818705724059756319686421)
                ·
                  refine ⟨225876830815301077485301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4818705724059756319686421 225876830815301077485301)
                  ·
                    rfl

theorem cell22_1979521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 6].length) (baseStart_1979521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979521 prefixEnd_1979521 := by exact prefixLift 1979521
  have htrace : WordTrace (prefixWord ++ tailWord_1979521) baseStart_1979521 baseEnd_1979521 := by
    simpa [prefixWord, tailWord_1979521, baseEnd_1979521] using wordTrace_append hprefix tailTrace_1979521
  have hstable : (prefixWord ++ tailWord_1979521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979521).length < 2 ^ (prefixWord ++ tailWord_1979521).sum := by decide
  have hdescent : baseEnd_1979521 < baseStart_1979521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979553 : List Nat := [1, 2, 3, 3, 1, 1, 2, 4, 2, 3]
def baseStart_1979553 : Nat := 118140960795 + 1979553 * 2 ^ 59
def prefixEnd_1979553 : Nat := 4983230072969 + 3 ^ 40 * 1979553 * 2
def baseEnd_1979553 : Nat := 677641446699865815655805

theorem tailTrace_1979553 : CollatzResearch.WordTrace tailWord_1979553 prefixEnd_1979553 677641446699865815655805 := by
  unfold tailWord_1979553
  simp only [CollatzResearch.WordTrace]
  refine ⟨72200229397425036581527313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48133486264950024387684875 72200229397425036581527313)
  ·
    refine ⟨54150172048068777436145485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72200229397425036581527313 54150172048068777436145485)
    ·
      refine ⟨20306314518025791538554557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54150172048068777436145485 20306314518025791538554557)
      ·
        refine ⟨7614867944259671826957959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20306314518025791538554557 7614867944259671826957959)
        ·
          refine ⟨11422301916389507740436939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7614867944259671826957959 11422301916389507740436939)
          ·
            refine ⟨17133452874584261610655409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11422301916389507740436939 17133452874584261610655409)
            ·
              refine ⟨12850089655938196207991557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17133452874584261610655409 12850089655938196207991557)
              ·
                refine ⟨2409391810488411788998417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12850089655938196207991557 2409391810488411788998417)
                ·
                  refine ⟨1807043857866308841748813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2409391810488411788998417 1807043857866308841748813)
                  ·
                    refine ⟨677641446699865815655805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1807043857866308841748813 677641446699865815655805)
                    ·
                      rfl

theorem cell22_1979553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_1979553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979553 prefixEnd_1979553 := by exact prefixLift 1979553
  have htrace : WordTrace (prefixWord ++ tailWord_1979553) baseStart_1979553 baseEnd_1979553 := by
    simpa [prefixWord, tailWord_1979553, baseEnd_1979553] using wordTrace_append hprefix tailTrace_1979553
  have hstable : (prefixWord ++ tailWord_1979553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979553).length < 2 ^ (prefixWord ++ tailWord_1979553).sum := by decide
  have hdescent : baseEnd_1979553 < baseStart_1979553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979564 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 2, 7]
def baseStart_1979564 : Nat := 118140960795 + 1979564 * 2 ^ 59
def prefixEnd_1979564 : Nat := 4983230072969 + 3 ^ 40 * 1979564 * 2
def baseEnd_1979564 : Nat := 677645212224665453630771

theorem tailTrace_1979564 : CollatzResearch.WordTrace tailWord_1979564 prefixEnd_1979564 677645212224665453630771 := by
  unfold tailWord_1979564
  simp only [CollatzResearch.WordTrace]
  refine ⟨36100315300192592730088873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48133753733590123640118497 36100315300192592730088873)
  ·
    refine ⟨27075236475144444547566655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36100315300192592730088873 27075236475144444547566655)
    ·
      refine ⟨40612854712716666821349983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27075236475144444547566655 40612854712716666821349983)
      ·
        refine ⟨60919282069075000232024975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40612854712716666821349983 60919282069075000232024975)
        ·
          refine ⟨91378923103612500348037463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60919282069075000232024975 91378923103612500348037463)
          ·
            refine ⟨137068384655418750522056195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91378923103612500348037463 137068384655418750522056195)
            ·
              refine ⟨205602576983128125783084293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137068384655418750522056195 205602576983128125783084293)
              ·
                refine ⟨38550483184336523584328305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 205602576983128125783084293 38550483184336523584328305)
                ·
                  refine ⟨28912862388252392688246229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38550483184336523584328305 28912862388252392688246229)
                  ·
                    refine ⟨677645212224665453630771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28912862388252392688246229 677645212224665453630771)
                    ·
                      rfl

theorem cell22_1979564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_1979564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979564 prefixEnd_1979564 := by exact prefixLift 1979564
  have htrace : WordTrace (prefixWord ++ tailWord_1979564) baseStart_1979564 baseEnd_1979564 := by
    simpa [prefixWord, tailWord_1979564, baseEnd_1979564] using wordTrace_append hprefix tailTrace_1979564
  have hstable : (prefixWord ++ tailWord_1979564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979564).length < 2 ^ (prefixWord ++ tailWord_1979564).sum := by decide
  have hdescent : baseEnd_1979564 < baseStart_1979564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979570 : List Nat := [3, 2, 1, 1, 1, 4, 4, 1, 2, 3]
def baseStart_1979570 : Nat := 118140960795 + 1979570 * 2 ^ 59
def prefixEnd_1979570 : Nat := 4983230072969 + 3 ^ 40 * 1979570 * 2
def baseEnd_1979570 : Nat := 677647266147283437980753

theorem tailTrace_1979570 : CollatzResearch.WordTrace tailWord_1979570 prefixEnd_1979570 677647266147283437980753 := by
  unfold tailWord_1979570
  simp only [CollatzResearch.WordTrace]
  refine ⟨18050212359590862121224041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48133899625575632323264109 18050212359590862121224041)
  ·
    refine ⟨13537659269693146590918031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18050212359590862121224041 13537659269693146590918031)
    ·
      refine ⟨20306488904539719886377047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13537659269693146590918031 20306488904539719886377047)
      ·
        refine ⟨30459733356809579829565571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20306488904539719886377047 30459733356809579829565571)
        ·
          refine ⟨45689600035214369744348357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30459733356809579829565571 45689600035214369744348357)
          ·
            refine ⟨8566800006602694327065317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45689600035214369744348357 8566800006602694327065317)
            ·
              refine ⟨1606275001238005186324747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8566800006602694327065317 1606275001238005186324747)
              ·
                refine ⟨2409412501857007779487121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1606275001238005186324747 2409412501857007779487121)
                ·
                  refine ⟨1807059376392755834615341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2409412501857007779487121 1807059376392755834615341)
                  ·
                    refine ⟨677647266147283437980753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1807059376392755834615341 677647266147283437980753)
                    ·
                      rfl

theorem cell22_1979570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_1979570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979570 prefixEnd_1979570 := by exact prefixLift 1979570
  have htrace : WordTrace (prefixWord ++ tailWord_1979570) baseStart_1979570 baseEnd_1979570 := by
    simpa [prefixWord, tailWord_1979570, baseEnd_1979570] using wordTrace_append hprefix tailTrace_1979570
  have hstable : (prefixWord ++ tailWord_1979570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979570).length < 2 ^ (prefixWord ++ tailWord_1979570).sum := by decide
  have hdescent : baseEnd_1979570 < baseStart_1979570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979574 : List Nat := [5, 1, 3, 2, 1, 2, 1, 2, 1, 4]
def baseStart_1979574 : Nat := 118140960795 + 1979574 * 2 ^ 59
def prefixEnd_1979574 : Nat := 4983230072969 + 3 ^ 40 * 1979574 * 2
def baseEnd_1979574 : Nat := 677648635429028760880741

theorem tailTrace_1979574 : CollatzResearch.WordTrace tailWord_1979574 prefixEnd_1979574 677648635429028760880741 := by
  unfold tailWord_1979574
  simp only [CollatzResearch.WordTrace]
  refine ⟨4512562208146809823002611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48133996886899304778694517 4512562208146809823002611)
  ·
    refine ⟨6768843312220214734503917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4512562208146809823002611 6768843312220214734503917)
    ·
      refine ⟨2538316242082580525438969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6768843312220214734503917 2538316242082580525438969)
      ·
        refine ⟨1903737181561935394079227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2538316242082580525438969 1903737181561935394079227)
        ·
          refine ⟨2855605772342903091118841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1903737181561935394079227 2855605772342903091118841)
          ·
            refine ⟨2141704329257177318339131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2855605772342903091118841 2141704329257177318339131)
            ·
              refine ⟨3212556493885765977508697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2141704329257177318339131 3212556493885765977508697)
              ·
                refine ⟨2409417370414324483131523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3212556493885765977508697 2409417370414324483131523)
                ·
                  refine ⟨3614126055621486724697285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2409417370414324483131523 3614126055621486724697285)
                  ·
                    refine ⟨677648635429028760880741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3614126055621486724697285 677648635429028760880741)
                    ·
                      rfl

theorem cell22_1979574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_1979574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979574 prefixEnd_1979574 := by exact prefixLift 1979574
  have htrace : WordTrace (prefixWord ++ tailWord_1979574) baseStart_1979574 baseEnd_1979574 := by
    simpa [prefixWord, tailWord_1979574, baseEnd_1979574] using wordTrace_append hprefix tailTrace_1979574
  have hstable : (prefixWord ++ tailWord_1979574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979574).length < 2 ^ (prefixWord ++ tailWord_1979574).sum := by decide
  have hdescent : baseEnd_1979574 < baseStart_1979574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979579 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 4, 6]
def baseStart_1979579 : Nat := 118140960795 + 1979579 * 2 ^ 59
def prefixEnd_1979579 : Nat := 4983230072969 + 3 ^ 40 * 1979579 * 2
def baseEnd_1979579 : Nat := 677650347031210414505725

theorem tailTrace_1979579 : CollatzResearch.WordTrace tailWord_1979579 prefixEnd_1979579 677650347031210414505725 := by
  unfold tailWord_1979579
  simp only [CollatzResearch.WordTrace]
  refine ⟨72201177695330843021973791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48134118463553895347982527 72201177695330843021973791)
  ·
    refine ⟨108301766542996264532960687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72201177695330843021973791 108301766542996264532960687)
    ·
      refine ⟨162452649814494396799441031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108301766542996264532960687 162452649814494396799441031)
      ·
        refine ⟨243678974721741595199161547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162452649814494396799441031 243678974721741595199161547)
        ·
          refine ⟨365518462082612392798742321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243678974721741595199161547 365518462082612392798742321)
          ·
            refine ⟨274138846561959294599056741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365518462082612392798742321 274138846561959294599056741)
            ·
              refine ⟨51401033730367367737323139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 274138846561959294599056741 51401033730367367737323139)
              ·
                refine ⟨77101550595551051605984709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51401033730367367737323139 77101550595551051605984709)
                ·
                  refine ⟨14456540736665822176122133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 77101550595551051605984709 14456540736665822176122133)
                  ·
                    refine ⟨677650347031210414505725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14456540736665822176122133 677650347031210414505725)
                    ·
                      rfl

theorem cell22_1979579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 6].length) (baseStart_1979579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979579 prefixEnd_1979579 := by exact prefixLift 1979579
  have htrace : WordTrace (prefixWord ++ tailWord_1979579) baseStart_1979579 baseEnd_1979579 := by
    simpa [prefixWord, tailWord_1979579, baseEnd_1979579] using wordTrace_append hprefix tailTrace_1979579
  have hstable : (prefixWord ++ tailWord_1979579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979579).length < 2 ^ (prefixWord ++ tailWord_1979579).sum := by decide
  have hdescent : baseEnd_1979579 < baseStart_1979579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979585 : List Nat := [1, 2, 6, 1, 1, 2, 2, 1, 2, 4]
def baseStart_1979585 : Nat := 118140960795 + 1979585 * 2 ^ 59
def prefixEnd_1979585 : Nat := 4983230072969 + 3 ^ 40 * 1979585 * 2
def baseEnd_1979585 : Nat := 677652400953828398855707

theorem tailTrace_1979585 : CollatzResearch.WordTrace tailWord_1979585 prefixEnd_1979585 677652400953828398855707 := by
  unfold tailWord_1979585
  simp only [CollatzResearch.WordTrace]
  refine ⟨72201396533309106046692209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48134264355539404031128139 72201396533309106046692209)
  ·
    refine ⟨54151047399981829535019157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72201396533309106046692209 54151047399981829535019157)
    ·
      refine ⟨2538330346874148259454023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54151047399981829535019157 2538330346874148259454023)
      ·
        refine ⟨3807495520311222389181035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2538330346874148259454023 3807495520311222389181035)
        ·
          refine ⟨5711243280466833583771553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3807495520311222389181035 5711243280466833583771553)
          ·
            refine ⟨4283432460350125187828665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5711243280466833583771553 4283432460350125187828665)
            ·
              refine ⟨3212574345262593890871499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4283432460350125187828665 3212574345262593890871499)
              ·
                refine ⟨4818861517893890836307249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3212574345262593890871499 4818861517893890836307249)
                ·
                  refine ⟨3614146138420418127230437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4818861517893890836307249 3614146138420418127230437)
                  ·
                    refine ⟨677652400953828398855707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3614146138420418127230437 677652400953828398855707)
                    ·
                      rfl

theorem cell22_1979585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_1979585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979585 prefixEnd_1979585 := by exact prefixLift 1979585
  have htrace : WordTrace (prefixWord ++ tailWord_1979585) baseStart_1979585 baseEnd_1979585 := by
    simpa [prefixWord, tailWord_1979585, baseEnd_1979585] using wordTrace_append hprefix tailTrace_1979585
  have hstable : (prefixWord ++ tailWord_1979585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979585).length < 2 ^ (prefixWord ++ tailWord_1979585).sum := by decide
  have hdescent : baseEnd_1979585 < baseStart_1979585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979606 : List Nat := [5, 2, 1, 2, 3, 1, 2, 2, 4]
def baseStart_1979606 : Nat := 118140960795 + 1979606 * 2 ^ 59
def prefixEnd_1979606 : Nat := 4983230072969 + 3 ^ 40 * 1979606 * 2
def baseEnd_1979606 : Nat := 225886529894330448026881

theorem tailTrace_1979606 : CollatzResearch.WordTrace tailWord_1979606 prefixEnd_1979606 225886529894330448026881 := by
  unfold tailWord_1979606
  simp only [CollatzResearch.WordTrace]
  refine ⟨4512635154139564164575417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48134774977488684422137781 4512635154139564164575417)
  ·
    refine ⟨3384476365604673123431563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4512635154139564164575417 3384476365604673123431563)
    ·
      refine ⟨5076714548407009685147345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3384476365604673123431563 5076714548407009685147345)
      ·
        refine ⟨3807535911305257263860509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5076714548407009685147345 3807535911305257263860509)
        ·
          refine ⟨1427825966739471473947691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3807535911305257263860509 1427825966739471473947691)
          ·
            refine ⟨2141738950109207210921537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427825966739471473947691 2141738950109207210921537)
            ·
              refine ⟨1606304212581905408191153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2141738950109207210921537 1606304212581905408191153)
              ·
                refine ⟨1204728159436429056143365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1606304212581905408191153 1204728159436429056143365)
                ·
                  refine ⟨225886529894330448026881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1204728159436429056143365 225886529894330448026881)
                  ·
                    rfl

theorem cell22_1979606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_1979606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979606 prefixEnd_1979606 := by exact prefixLift 1979606
  have htrace : WordTrace (prefixWord ++ tailWord_1979606) baseStart_1979606 baseEnd_1979606 := by
    simpa [prefixWord, tailWord_1979606, baseEnd_1979606] using wordTrace_append hprefix tailTrace_1979606
  have hstable : (prefixWord ++ tailWord_1979606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979606).length < 2 ^ (prefixWord ++ tailWord_1979606).sum := by decide
  have hdescent : baseEnd_1979606 < baseStart_1979606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979626 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 1, 7]
def baseStart_1979626 : Nat := 118140960795 + 1979626 * 2 ^ 59
def prefixEnd_1979626 : Nat := 4983230072969 + 3 ^ 40 * 1979626 * 2
def baseEnd_1979626 : Nat := 677666436091717958580581

theorem tailTrace_1979626 : CollatzResearch.WordTrace tailWord_1979626 prefixEnd_1979626 677666436091717958580581 := by
  unfold tailWord_1979626
  simp only [CollatzResearch.WordTrace]
  refine ⟨18050722981540142512233683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48135261284107046699289821 18050722981540142512233683)
  ·
    refine ⟨27076084472310213768350525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18050722981540142512233683 27076084472310213768350525)
    ·
      refine ⟨10153531677116330163131447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27076084472310213768350525 10153531677116330163131447)
      ·
        refine ⟨15230297515674495244697171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10153531677116330163131447 15230297515674495244697171)
        ·
          refine ⟨22845446273511742867045757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15230297515674495244697171 22845446273511742867045757)
          ·
            refine ⟨8567042352566903575142159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22845446273511742867045757 8567042352566903575142159)
            ·
              refine ⟨12850563528850355362713239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8567042352566903575142159 12850563528850355362713239)
              ·
                refine ⟨19275845293275533044069859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12850563528850355362713239 19275845293275533044069859)
                ·
                  refine ⟨28913767939913299566104789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19275845293275533044069859 28913767939913299566104789)
                  ·
                    refine ⟨677666436091717958580581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28913767939913299566104789 677666436091717958580581)
                    ·
                      rfl

theorem cell22_1979626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_1979626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979626 prefixEnd_1979626 := by exact prefixLift 1979626
  have htrace : WordTrace (prefixWord ++ tailWord_1979626) baseStart_1979626 baseEnd_1979626 := by
    simpa [prefixWord, tailWord_1979626, baseEnd_1979626] using wordTrace_append hprefix tailTrace_1979626
  have hstable : (prefixWord ++ tailWord_1979626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979626).length < 2 ^ (prefixWord ++ tailWord_1979626).sum := by decide
  have hdescent : baseEnd_1979626 < baseStart_1979626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979636 : List Nat := [2, 6, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_1979636 : Nat := 118140960795 + 1979636 * 2 ^ 59
def prefixEnd_1979636 : Nat := 4983230072969 + 3 ^ 40 * 1979636 * 2
def baseEnd_1979636 : Nat := 677669859296081265830551

theorem tailTrace_1979636 : CollatzResearch.WordTrace tailWord_1979636 prefixEnd_1979636 677669859296081265830551 := by
  unfold tailWord_1979636
  simp only [CollatzResearch.WordTrace]
  refine ⟨36101628328062170878399381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48135504437416227837865841 36101628328062170878399381)
  ·
    refine ⟨1692263827877914259924971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36101628328062170878399381 1692263827877914259924971)
    ·
      refine ⟨2538395741816871389887457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1692263827877914259924971 2538395741816871389887457)
      ·
        refine ⟨1903796806362653542415593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2538395741816871389887457 1903796806362653542415593)
        ·
          refine ⟨1427847604771990156811695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1903796806362653542415593 1427847604771990156811695)
          ·
            refine ⟨2141771407157985235217543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427847604771990156811695 2141771407157985235217543)
            ·
              refine ⟨3212657110736977852826315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2141771407157985235217543 3212657110736977852826315)
              ·
                refine ⟨4818985666105466779239473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3212657110736977852826315 4818985666105466779239473)
                ·
                  refine ⟨3614239249579100084429605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4818985666105466779239473 3614239249579100084429605)
                  ·
                    refine ⟨677669859296081265830551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3614239249579100084429605 677669859296081265830551)
                    ·
                      rfl

theorem cell22_1979636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_1979636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979636 prefixEnd_1979636 := by exact prefixLift 1979636
  have htrace : WordTrace (prefixWord ++ tailWord_1979636) baseStart_1979636 baseEnd_1979636 := by
    simpa [prefixWord, tailWord_1979636, baseEnd_1979636] using wordTrace_append hprefix tailTrace_1979636
  have hstable : (prefixWord ++ tailWord_1979636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979636).length < 2 ^ (prefixWord ++ tailWord_1979636).sum := by decide
  have hdescent : baseEnd_1979636 < baseStart_1979636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979641 : List Nat := [1, 2, 1, 3, 1, 1, 3, 3, 3, 4]
def baseStart_1979641 : Nat := 118140960795 + 1979641 * 2 ^ 59
def prefixEnd_1979641 : Nat := 4983230072969 + 3 ^ 40 * 1979641 * 2
def baseEnd_1979641 : Nat := 677671570898262919455535

theorem tailTrace_1979641 : CollatzResearch.WordTrace tailWord_1979641 prefixEnd_1979641 677671570898262919455535 := by
  unfold tailWord_1979641
  simp only [CollatzResearch.WordTrace]
  refine ⟨72203439021106227610730777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48135626014070818407153851 72203439021106227610730777)
  ·
    refine ⟨54152579265829670708048083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72203439021106227610730777 54152579265829670708048083)
    ·
      refine ⟨81228868898744506062072125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54152579265829670708048083 81228868898744506062072125)
      ·
        refine ⟨30460825837029189773277047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81228868898744506062072125 30460825837029189773277047)
        ·
          refine ⟨45691238755543784659915571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30460825837029189773277047 45691238755543784659915571)
          ·
            refine ⟨68536858133315676989873357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45691238755543784659915571 68536858133315676989873357)
            ·
              refine ⟨25701321799993378871202509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68536858133315676989873357 25701321799993378871202509)
              ·
                refine ⟨9637995674997517076700941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25701321799993378871202509 9637995674997517076700941)
                ·
                  refine ⟨3614248378124068903762853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9637995674997517076700941 3614248378124068903762853)
                  ·
                    refine ⟨677671570898262919455535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3614248378124068903762853 677671570898262919455535)
                    ·
                      rfl

theorem cell22_1979641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 4].length) (baseStart_1979641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979641 prefixEnd_1979641 := by exact prefixLift 1979641
  have htrace : WordTrace (prefixWord ++ tailWord_1979641) baseStart_1979641 baseEnd_1979641 := by
    simpa [prefixWord, tailWord_1979641, baseEnd_1979641] using wordTrace_append hprefix tailTrace_1979641
  have hstable : (prefixWord ++ tailWord_1979641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979641).length < 2 ^ (prefixWord ++ tailWord_1979641).sum := by decide
  have hdescent : baseEnd_1979641 < baseStart_1979641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979731 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 2, 6]
def baseStart_1979731 : Nat := 118140960795 + 1979731 * 2 ^ 59
def prefixEnd_1979731 : Nat := 4983230072969 + 3 ^ 40 * 1979731 * 2
def baseEnd_1979731 : Nat := 677702379737532684705259

theorem tailTrace_1979731 : CollatzResearch.WordTrace tailWord_1979731 prefixEnd_1979731 677702379737532684705259 := by
  unfold tailWord_1979731
  simp only [CollatzResearch.WordTrace]
  refine ⟨72206721590780172981507047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48137814393853448654338031 72206721590780172981507047)
  ·
    refine ⟨108310082386170259472260571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72206721590780172981507047 108310082386170259472260571)
    ·
      refine ⟨162465123579255389208390857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108310082386170259472260571 162465123579255389208390857)
      ·
        refine ⟨121848842684441541906293143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162465123579255389208390857 121848842684441541906293143)
        ·
          refine ⟨182773264026662312859439715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121848842684441541906293143 182773264026662312859439715)
          ·
            refine ⟨274159896039993469289159573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182773264026662312859439715 274159896039993469289159573)
            ·
              refine ⟨12851245126874693872929355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 274159896039993469289159573 12851245126874693872929355)
              ·
                refine ⟨19276867690312040809394033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12851245126874693872929355 19276867690312040809394033)
                ·
                  refine ⟨14457650767734030607045525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19276867690312040809394033 14457650767734030607045525)
                  ·
                    refine ⟨677702379737532684705259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14457650767734030607045525 677702379737532684705259)
                    ·
                      rfl

theorem cell22_1979731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 6].length) (baseStart_1979731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979731 prefixEnd_1979731 := by exact prefixLift 1979731
  have htrace : WordTrace (prefixWord ++ tailWord_1979731) baseStart_1979731 baseEnd_1979731 := by
    simpa [prefixWord, tailWord_1979731, baseEnd_1979731] using wordTrace_append hprefix tailTrace_1979731
  have hstable : (prefixWord ++ tailWord_1979731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979731).length < 2 ^ (prefixWord ++ tailWord_1979731).sum := by decide
  have hdescent : baseEnd_1979731 < baseStart_1979731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979780 : List Nat := [2, 3, 2, 1, 1, 4, 2, 2, 5]
def baseStart_1979780 : Nat := 118140960795 + 1979780 * 2 ^ 59
def prefixEnd_1979780 : Nat := 4983230072969 + 3 ^ 40 * 1979780 * 2
def baseEnd_1979780 : Nat := 225906384479637630076703

theorem tailTrace_1979780 : CollatzResearch.WordTrace tailWord_1979780 prefixEnd_1979780 225906384479637630076703 := by
  unfold tailWord_1979780
  simp only [CollatzResearch.WordTrace]
  refine ⟨36104254383801327175020397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48139005845068436233360529 36104254383801327175020397)
  ·
    refine ⟨13539095393925497690632649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36104254383801327175020397 13539095393925497690632649)
    ·
      refine ⟨10154321545444123267974487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13539095393925497690632649 10154321545444123267974487)
      ·
        refine ⟨15231482318166184901961731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10154321545444123267974487 15231482318166184901961731)
        ·
          refine ⟨22847223477249277352942597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15231482318166184901961731 22847223477249277352942597)
          ·
            refine ⟨4283854401984239503676737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22847223477249277352942597 4283854401984239503676737)
            ·
              refine ⟨3212890801488179627757553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4283854401984239503676737 3212890801488179627757553)
              ·
                refine ⟨2409668101116134720818165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3212890801488179627757553 2409668101116134720818165)
                ·
                  refine ⟨225906384479637630076703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2409668101116134720818165 225906384479637630076703)
                  ·
                    rfl

theorem cell22_1979780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_1979780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979780 prefixEnd_1979780 := by exact prefixLift 1979780
  have htrace : WordTrace (prefixWord ++ tailWord_1979780) baseStart_1979780 baseEnd_1979780 := by
    simpa [prefixWord, tailWord_1979780, baseEnd_1979780] using wordTrace_append hprefix tailTrace_1979780
  have hstable : (prefixWord ++ tailWord_1979780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979780).length < 2 ^ (prefixWord ++ tailWord_1979780).sum := by decide
  have hdescent : baseEnd_1979780 < baseStart_1979780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979784 : List Nat := [2, 1, 3, 3, 1, 2, 4, 2, 1, 3]
def baseStart_1979784 : Nat := 118140960795 + 1979784 * 2 ^ 59
def prefixEnd_1979784 : Nat := 4983230072969 + 3 ^ 40 * 1979784 * 2
def baseEnd_1979784 : Nat := 677720522720658213130097

theorem tailTrace_1979784 : CollatzResearch.WordTrace tailWord_1979784 prefixEnd_1979784 677720522720658213130097 := by
  unfold tailWord_1979784
  simp only [CollatzResearch.WordTrace]
  refine ⟨36104327329794081516593203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48139103106392108688790937 36104327329794081516593203)
  ·
    refine ⟨54156490994691122274889805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36104327329794081516593203 54156490994691122274889805)
    ·
      refine ⟨20308684123009170853083677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54156490994691122274889805 20308684123009170853083677)
      ·
        refine ⟨7615756546128439069906379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20308684123009170853083677 7615756546128439069906379)
        ·
          refine ⟨11423634819192658604859569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7615756546128439069906379 11423634819192658604859569)
          ·
            refine ⟨8567726114394493953644677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11423634819192658604859569 8567726114394493953644677)
            ·
              refine ⟨1606448646448967616308377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8567726114394493953644677 1606448646448967616308377)
              ·
                refine ⟨1204836484836725712231283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1606448646448967616308377 1204836484836725712231283)
                ·
                  refine ⟨1807254727255088568346925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1204836484836725712231283 1807254727255088568346925)
                  ·
                    refine ⟨677720522720658213130097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1807254727255088568346925 677720522720658213130097)
                    ·
                      rfl

theorem cell22_1979784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_1979784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979784 prefixEnd_1979784 := by exact prefixLift 1979784
  have htrace : WordTrace (prefixWord ++ tailWord_1979784) baseStart_1979784 baseEnd_1979784 := by
    simpa [prefixWord, tailWord_1979784, baseEnd_1979784] using wordTrace_append hprefix tailTrace_1979784
  have hstable : (prefixWord ++ tailWord_1979784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979784).length < 2 ^ (prefixWord ++ tailWord_1979784).sum := by decide
  have hdescent : baseEnd_1979784 < baseStart_1979784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979808 : List Nat := [2, 1, 1, 4, 1, 2, 3, 2, 6]
def baseStart_1979808 : Nat := 118140960795 + 1979808 * 2 ^ 59
def prefixEnd_1979808 : Nat := 4983230072969 + 3 ^ 40 * 1979808 * 2
def baseEnd_1979808 : Nat := 225909579470376716843341

theorem tailTrace_1979808 : CollatzResearch.WordTrace tailWord_1979808 prefixEnd_1979808 225909579470376716843341 := by
  unfold tailWord_1979808
  simp only [CollatzResearch.WordTrace]
  refine ⟨36104765005750607566030039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48139686674334143421373385 36104765005750607566030039)
  ·
    refine ⟨54157147508625911349045059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36104765005750607566030039 54157147508625911349045059)
    ·
      refine ⟨81235721262938867023567589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54157147508625911349045059 81235721262938867023567589)
      ·
        refine ⟨15231697736801037566918923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81235721262938867023567589 15231697736801037566918923)
        ·
          refine ⟨22847546605201556350378385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15231697736801037566918923 22847546605201556350378385)
          ·
            refine ⟨17135659953901167262783789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22847546605201556350378385 17135659953901167262783789)
            ·
              refine ⟨6425872482712937723543921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17135659953901167262783789 6425872482712937723543921)
              ·
                refine ⟨4819404362034703292657941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6425872482712937723543921 4819404362034703292657941)
                ·
                  refine ⟨225909579470376716843341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4819404362034703292657941 225909579470376716843341)
                  ·
                    rfl

theorem cell22_1979808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 6].length) (baseStart_1979808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979808 prefixEnd_1979808 := by exact prefixLift 1979808
  have htrace : WordTrace (prefixWord ++ tailWord_1979808) baseStart_1979808 baseEnd_1979808 := by
    simpa [prefixWord, tailWord_1979808, baseEnd_1979808] using wordTrace_append hprefix tailTrace_1979808
  have hstable : (prefixWord ++ tailWord_1979808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979808).length < 2 ^ (prefixWord ++ tailWord_1979808).sum := by decide
  have hdescent : baseEnd_1979808 < baseStart_1979808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979810 : List Nat := [3, 3, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_1979810 : Nat := 118140960795 + 1979810 * 2 ^ 59
def prefixEnd_1979810 : Nat := 4983230072969 + 3 ^ 40 * 1979810 * 2
def baseEnd_1979810 : Nat := 677729423052002811980017

theorem tailTrace_1979810 : CollatzResearch.WordTrace tailWord_1979810 prefixEnd_1979810 677729423052002811980017 := by
  unfold tailWord_1979810
  simp only [CollatzResearch.WordTrace]
  refine ⟨18052400739373492368408221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48139735304995979649088589 18052400739373492368408221)
  ·
    refine ⟨6769650277265059638153083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18052400739373492368408221 6769650277265059638153083)
    ·
      refine ⟨10154475415897589457229625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6769650277265059638153083 10154475415897589457229625)
      ·
        refine ⟨7615856561923192092922219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10154475415897589457229625 7615856561923192092922219)
        ·
          refine ⟨11423784842884788139383329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7615856561923192092922219 11423784842884788139383329)
          ·
            refine ⟨8567838632163591104537497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11423784842884788139383329 8567838632163591104537497)
            ·
              refine ⟨6425878974122693328403123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8567838632163591104537497 6425878974122693328403123)
              ·
                refine ⟨9638818461184039992604685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6425878974122693328403123 9638818461184039992604685)
                ·
                  refine ⟨3614556922944014997226757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9638818461184039992604685 3614556922944014997226757)
                  ·
                    refine ⟨677729423052002811980017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3614556922944014997226757 677729423052002811980017)
                    ·
                      rfl

theorem cell22_1979810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_1979810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979810 prefixEnd_1979810 := by exact prefixLift 1979810
  have htrace : WordTrace (prefixWord ++ tailWord_1979810) baseStart_1979810 baseEnd_1979810 := by
    simpa [prefixWord, tailWord_1979810, baseEnd_1979810] using wordTrace_append hprefix tailTrace_1979810
  have hstable : (prefixWord ++ tailWord_1979810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979810).length < 2 ^ (prefixWord ++ tailWord_1979810).sum := by decide
  have hdescent : baseEnd_1979810 < baseStart_1979810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979898 : List Nat := [3, 1, 1, 1, 1, 2, 3, 3, 7]
def baseStart_1979898 : Nat := 118140960795 + 1979898 * 2 ^ 59
def prefixEnd_1979898 : Nat := 4983230072969 + 3 ^ 40 * 1979898 * 2
def baseEnd_1979898 : Nat := 225919849083466638593249

theorem tailTrace_1979898 : CollatzResearch.WordTrace tailWord_1979898 prefixEnd_1979898 225919849083466638593249 := by
  unfold tailWord_1979898
  simp only [CollatzResearch.WordTrace]
  refine ⟨18053203145293790125709087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48141875054116773668557565 18053203145293790125709087)
  ·
    refine ⟨27079804717940685188563631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18053203145293790125709087 27079804717940685188563631)
    ·
      refine ⟨40619707076911027782845447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27079804717940685188563631 40619707076911027782845447)
      ·
        refine ⟨60929560615366541674268171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40619707076911027782845447 60929560615366541674268171)
        ·
          refine ⟨91394340923049812511402257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60929560615366541674268171 91394340923049812511402257)
          ·
            refine ⟨68545755692287359383551693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91394340923049812511402257 68545755692287359383551693)
            ·
              refine ⟨25704658384607759768831885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68545755692287359383551693 25704658384607759768831885)
              ·
                refine ⟨9639246894227909913311957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25704658384607759768831885 9639246894227909913311957)
                ·
                  refine ⟨225919849083466638593249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9639246894227909913311957 225919849083466638593249)
                  ·
                    rfl

theorem cell22_1979898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_1979898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979898 prefixEnd_1979898 := by exact prefixLift 1979898
  have htrace : WordTrace (prefixWord ++ tailWord_1979898) baseStart_1979898 baseEnd_1979898 := by
    simpa [prefixWord, tailWord_1979898, baseEnd_1979898] using wordTrace_append hprefix tailTrace_1979898
  have hstable : (prefixWord ++ tailWord_1979898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979898).length < 2 ^ (prefixWord ++ tailWord_1979898).sum := by decide
  have hdescent : baseEnd_1979898 < baseStart_1979898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979908 : List Nat := [2, 3, 2, 3, 3, 1, 2, 1, 2, 3]
def baseStart_1979908 : Nat := 118140960795 + 1979908 * 2 ^ 59
def prefixEnd_1979908 : Nat := 4983230072969 + 3 ^ 40 * 1979908 * 2
def baseEnd_1979908 : Nat := 677762970454763223029717

theorem tailTrace_1979908 : CollatzResearch.WordTrace tailWord_1979908 prefixEnd_1979908 677762970454763223029717 := by
  unfold tailWord_1979908
  simp only [CollatzResearch.WordTrace]
  refine ⟨36106588655569466105350189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48142118207425954807133585 36106588655569466105350189)
  ·
    refine ⟨13539970745838549789506321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36106588655569466105350189 13539970745838549789506321)
    ·
      refine ⟨10154978059378912342129741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13539970745838549789506321 10154978059378912342129741)
      ·
        refine ⟨3808116772267092128298653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10154978059378912342129741 3808116772267092128298653)
        ·
          refine ⟨1428043789600159548111995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3808116772267092128298653 1428043789600159548111995)
          ·
            refine ⟨2142065684400239322167993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1428043789600159548111995 2142065684400239322167993)
            ·
              refine ⟨1606549263300179491625995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2142065684400239322167993 1606549263300179491625995)
              ·
                refine ⟨2409823894950269237438993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1606549263300179491625995 2409823894950269237438993)
                ·
                  refine ⟨1807367921212701928079245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2409823894950269237438993 1807367921212701928079245)
                  ·
                    refine ⟨677762970454763223029717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1807367921212701928079245 677762970454763223029717)
                    ·
                      rfl

theorem cell22_1979908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_1979908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979908 prefixEnd_1979908 := by exact prefixLift 1979908
  have htrace : WordTrace (prefixWord ++ tailWord_1979908) baseStart_1979908 baseEnd_1979908 := by
    simpa [prefixWord, tailWord_1979908, baseEnd_1979908] using wordTrace_append hprefix tailTrace_1979908
  have hstable : (prefixWord ++ tailWord_1979908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979908).length < 2 ^ (prefixWord ++ tailWord_1979908).sum := by decide
  have hdescent : baseEnd_1979908 < baseStart_1979908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979913 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 1, 7]
def baseStart_1979913 : Nat := 118140960795 + 1979913 * 2 ^ 59
def prefixEnd_1979913 : Nat := 4983230072969 + 3 ^ 40 * 1979913 * 2
def baseEnd_1979913 : Nat := 677764682056944876654701

theorem tailTrace_1979913 : CollatzResearch.WordTrace tailWord_1979913 prefixEnd_1979913 677764682056944876654701 := by
  unfold tailWord_1979913
  simp only [CollatzResearch.WordTrace]
  refine ⟨72213359676120818064632393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48142239784080545376421595 72213359676120818064632393)
  ·
    refine ⟨54160019757090613548474295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72213359676120818064632393 54160019757090613548474295)
    ·
      refine ⟨81240029635635920322711443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54160019757090613548474295 81240029635635920322711443)
      ·
        refine ⟨121860044453453880484067165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81240029635635920322711443 121860044453453880484067165)
        ·
          refine ⟨45697516670045205181525187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121860044453453880484067165 45697516670045205181525187)
          ·
            refine ⟨68546275005067807772287781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45697516670045205181525187 68546275005067807772287781)
            ·
              refine ⟨12852426563450213957303959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68546275005067807772287781 12852426563450213957303959)
              ·
                refine ⟨19278639845175320935955939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12852426563450213957303959 19278639845175320935955939)
                ·
                  refine ⟨28917959767762981403933909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19278639845175320935955939 28917959767762981403933909)
                  ·
                    refine ⟨677764682056944876654701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28917959767762981403933909 677764682056944876654701)
                    ·
                      rfl

theorem cell22_1979913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 7].length) (baseStart_1979913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979913 prefixEnd_1979913 := by exact prefixLift 1979913
  have htrace : WordTrace (prefixWord ++ tailWord_1979913) baseStart_1979913 baseEnd_1979913 := by
    simpa [prefixWord, tailWord_1979913, baseEnd_1979913] using wordTrace_append hprefix tailTrace_1979913
  have hstable : (prefixWord ++ tailWord_1979913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979913).length < 2 ^ (prefixWord ++ tailWord_1979913).sum := by decide
  have hdescent : baseEnd_1979913 < baseStart_1979913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1979996 : List Nat := [2, 2, 4, 1, 2, 3, 2, 1, 1, 4]
def baseStart_1979996 : Nat := 118140960795 + 1979996 * 2 ^ 59
def prefixEnd_1979996 : Nat := 4983230072969 + 3 ^ 40 * 1979996 * 2
def baseEnd_1979996 : Nat := 677793094653160326829447

theorem tailTrace_1979996 : CollatzResearch.WordTrace tailWord_1979996 prefixEnd_1979996 677793094653160326829447 := by
  unfold tailWord_1979996
  simp only [CollatzResearch.WordTrace]
  refine ⟨36108193467410061619951921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48144257956546748826602561 36108193467410061619951921)
  ·
    refine ⟨27081145100557546214963941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36108193467410061619951921 27081145100557546214963941)
    ·
      refine ⟨5077714706354539915305739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27081145100557546214963941 5077714706354539915305739)
      ·
        refine ⟨7616572059531809872958609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5077714706354539915305739 7616572059531809872958609)
        ·
          refine ⟨5712429044648857404718957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7616572059531809872958609 5712429044648857404718957)
          ·
            refine ⟨2142160891743321526769609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5712429044648857404718957 2142160891743321526769609)
            ·
              refine ⟨1606620668807491145077207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2142160891743321526769609 1606620668807491145077207)
              ·
                refine ⟨2409931003211236717615811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1606620668807491145077207 2409931003211236717615811)
                ·
                  refine ⟨3614896504816855076423717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2409931003211236717615811 3614896504816855076423717)
                  ·
                    refine ⟨677793094653160326829447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3614896504816855076423717 677793094653160326829447)
                    ·
                      rfl

theorem cell22_1979996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_1979996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1979996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1979996 prefixEnd_1979996 := by exact prefixLift 1979996
  have htrace : WordTrace (prefixWord ++ tailWord_1979996) baseStart_1979996 baseEnd_1979996 := by
    simpa [prefixWord, tailWord_1979996, baseEnd_1979996] using wordTrace_append hprefix tailTrace_1979996
  have hstable : (prefixWord ++ tailWord_1979996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1979996).length < 2 ^ (prefixWord ++ tailWord_1979996).sum := by decide
  have hdescent : baseEnd_1979996 < baseStart_1979996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1979996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980005 : List Nat := [1, 3, 1, 3, 3, 2, 9]
def baseStart_1980005 : Nat := 118140960795 + 1980005 * 2 ^ 59
def prefixEnd_1980005 : Nat := 4983230072969 + 3 ^ 40 * 1980005 * 2
def baseEnd_1980005 : Nat := 25103562056929159383497

theorem tailTrace_1980005 : CollatzResearch.WordTrace tailWord_1980005 prefixEnd_1980005 25103562056929159383497 := by
  unfold tailWord_1980005
  simp only [CollatzResearch.WordTrace]
  refine ⟨72216715191787517776981469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48144476794525011851320979 72216715191787517776981469)
  ·
    refine ⟨27081268196920319166368051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72216715191787517776981469 27081268196920319166368051)
    ·
      refine ⟨40621902295380478749552077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27081268196920319166368051 40621902295380478749552077)
      ·
        refine ⟨15233213360767679531082029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40621902295380478749552077 15233213360767679531082029)
        ·
          refine ⟨5712455010287879824155761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15233213360767679531082029 5712455010287879824155761)
          ·
            refine ⟨4284341257715909868116821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5712455010287879824155761 4284341257715909868116821)
            ·
              refine ⟨25103562056929159383497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4284341257715909868116821 25103562056929159383497)
              ·
                rfl

theorem cell22_1980005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 9].length) (baseStart_1980005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1980005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1980005 prefixEnd_1980005 := by exact prefixLift 1980005
  have htrace : WordTrace (prefixWord ++ tailWord_1980005) baseStart_1980005 baseEnd_1980005 := by
    simpa [prefixWord, tailWord_1980005, baseEnd_1980005] using wordTrace_append hprefix tailTrace_1980005
  have hstable : (prefixWord ++ tailWord_1980005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980005).length < 2 ^ (prefixWord ++ tailWord_1980005).sum := by decide
  have hdescent : baseEnd_1980005 < baseStart_1980005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980037 : List Nat := [1, 3, 1, 1, 4, 1, 1, 4, 3, 3]
def baseStart_1980037 : Nat := 118140960795 + 1980037 * 2 ^ 59
def prefixEnd_1980037 : Nat := 4983230072969 + 3 ^ 40 * 1980037 * 2
def baseEnd_1980037 : Nat := 677807129791049886554321

theorem tailTrace_1980037 : CollatzResearch.WordTrace tailWord_1980037 prefixEnd_1980037 677807129791049886554321 := by
  unfold tailWord_1980037
  simp only [CollatzResearch.WordTrace]
  refine ⟨72217882327671587242146365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48145254885114391494764243 72217882327671587242146365)
  ·
    refine ⟨27081705872876845215804887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72217882327671587242146365 27081705872876845215804887)
    ·
      refine ⟨40622558809315267823707331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27081705872876845215804887 40622558809315267823707331)
      ·
        refine ⟨60933838213972901735560997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40622558809315267823707331 60933838213972901735560997)
        ·
          refine ⟨11425094665119919075417687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60933838213972901735560997 11425094665119919075417687)
          ·
            refine ⟨17137641997679878613126531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11425094665119919075417687 17137641997679878613126531)
            ·
              refine ⟨25706462996519817919689797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17137641997679878613126531 25706462996519817919689797)
              ·
                refine ⟨4819961811847465859941837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25706462996519817919689797 4819961811847465859941837)
                ·
                  refine ⟨1807485679442799697478189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4819961811847465859941837 1807485679442799697478189)
                  ·
                    refine ⟨677807129791049886554321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1807485679442799697478189 677807129791049886554321)
                    ·
                      rfl

theorem cell22_1980037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3, 3].length) (baseStart_1980037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1980037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1980037 prefixEnd_1980037 := by exact prefixLift 1980037
  have htrace : WordTrace (prefixWord ++ tailWord_1980037) baseStart_1980037 baseEnd_1980037 := by
    simpa [prefixWord, tailWord_1980037, baseEnd_1980037] using wordTrace_append hprefix tailTrace_1980037
  have hstable : (prefixWord ++ tailWord_1980037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980037).length < 2 ^ (prefixWord ++ tailWord_1980037).sum := by decide
  have hdescent : baseEnd_1980037 < baseStart_1980037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980095 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 8]
def baseStart_1980095 : Nat := 118140960795 + 1980095 * 2 ^ 59
def prefixEnd_1980095 : Nat := 4983230072969 + 3 ^ 40 * 1980095 * 2
def baseEnd_1980095 : Nat := 225942328125452356201381

theorem tailTrace_1980095 : CollatzResearch.WordTrace tailWord_1980095 prefixEnd_1980095 225942328125452356201381 := by
  unfold tailWord_1980095
  simp only [CollatzResearch.WordTrace]
  refine ⟨72219997761461463147757739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48146665174307642098505159 72219997761461463147757739)
  ·
    refine ⟨108329996642192194721636609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72219997761461463147757739 108329996642192194721636609)
    ·
      refine ⟨81247497481644146041227457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108329996642192194721636609 81247497481644146041227457)
      ·
        refine ⟨60935623111233109530920593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81247497481644146041227457 60935623111233109530920593)
        ·
          refine ⟨45701717333424832148190445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60935623111233109530920593 45701717333424832148190445)
          ·
            refine ⟨17138144000034312055571417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45701717333424832148190445 17138144000034312055571417)
            ·
              refine ⟨12853608000025734041678563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17138144000034312055571417 12853608000025734041678563)
              ·
                refine ⟨19280412000038601062517845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12853608000025734041678563 19280412000038601062517845)
                ·
                  refine ⟨225942328125452356201381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19280412000038601062517845 225942328125452356201381)
                  ·
                    rfl

theorem cell22_1980095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 8].length) (baseStart_1980095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1980095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1980095 prefixEnd_1980095 := by exact prefixLift 1980095
  have htrace : WordTrace (prefixWord ++ tailWord_1980095) baseStart_1980095 baseEnd_1980095 := by
    simpa [prefixWord, tailWord_1980095, baseEnd_1980095] using wordTrace_append hprefix tailTrace_1980095
  have hstable : (prefixWord ++ tailWord_1980095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980095).length < 2 ^ (prefixWord ++ tailWord_1980095).sum := by decide
  have hdescent : baseEnd_1980095 < baseStart_1980095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980118 : List Nat := [5, 2, 1, 3, 1, 1, 2, 2, 5]
def baseStart_1980118 : Nat := 118140960795 + 1980118 * 2 ^ 59
def prefixEnd_1980118 : Nat := 4983230072969 + 3 ^ 40 * 1980118 * 2
def baseEnd_1980118 : Nat := 225944952582130891759691

theorem tailTrace_1980118 : CollatzResearch.WordTrace tailWord_1980118 prefixEnd_1980118 225944952582130891759691 := by
  unfold tailWord_1980118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4513802290023633629740313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48147224426918758717230005 4513802290023633629740313)
  ·
    refine ⟨3385351717517725222305235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4513802290023633629740313 3385351717517725222305235)
    ·
      refine ⟨5078027576276587833457853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3385351717517725222305235 5078027576276587833457853)
      ·
        refine ⟨1904260341103720437546695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5078027576276587833457853 1904260341103720437546695)
        ·
          refine ⟨2856390511655580656320043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1904260341103720437546695 2856390511655580656320043)
          ·
            refine ⟨4284585767483370984480065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2856390511655580656320043 4284585767483370984480065)
            ·
              refine ⟨3213439325612528238360049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4284585767483370984480065 3213439325612528238360049)
              ·
                refine ⟨2410079494209396178770037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3213439325612528238360049 2410079494209396178770037)
                ·
                  refine ⟨225944952582130891759691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2410079494209396178770037 225944952582130891759691)
                  ·
                    rfl

theorem cell22_1980118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_1980118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1980118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1980118 prefixEnd_1980118 := by exact prefixLift 1980118
  have htrace : WordTrace (prefixWord ++ tailWord_1980118) baseStart_1980118 baseEnd_1980118 := by
    simpa [prefixWord, tailWord_1980118, baseEnd_1980118] using wordTrace_append hprefix tailTrace_1980118
  have hstable : (prefixWord ++ tailWord_1980118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980118).length < 2 ^ (prefixWord ++ tailWord_1980118).sum := by decide
  have hdescent : baseEnd_1980118 < baseStart_1980118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980142 : List Nat := [4, 1, 2, 1, 1, 2, 2, 2, 1, 6]
def baseStart_1980142 : Nat := 118140960795 + 1980142 * 2 ^ 59
def prefixEnd_1980142 : Nat := 4983230072969 + 3 ^ 40 * 1980142 * 2
def baseEnd_1980142 : Nat := 677843073436864612678999

theorem tailTrace_1980142 : CollatzResearch.WordTrace tailWord_1980142 prefixEnd_1980142 677843073436864612678999 := by
  unfold tailWord_1980142
  simp only [CollatzResearch.WordTrace]
  refine ⟨9027713999036398771839835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48147807994860793449812453 9027713999036398771839835)
  ·
    refine ⟨13541570998554598157759753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9027713999036398771839835 13541570998554598157759753)
    ·
      refine ⟨10156178248915948618319815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13541570998554598157759753 10156178248915948618319815)
      ·
        refine ⟨15234267373373922927479723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10156178248915948618319815 15234267373373922927479723)
        ·
          refine ⟨22851401060060884391219585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15234267373373922927479723 22851401060060884391219585)
          ·
            refine ⟨17138550795045663293414689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22851401060060884391219585 17138550795045663293414689)
            ·
              refine ⟨12853913096284247470061017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17138550795045663293414689 12853913096284247470061017)
              ·
                refine ⟨9640434822213185602545763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12853913096284247470061017 9640434822213185602545763)
                ·
                  refine ⟨14460652233319778403818645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9640434822213185602545763 14460652233319778403818645)
                  ·
                    refine ⟨677843073436864612678999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14460652233319778403818645 677843073436864612678999)
                    ·
                      rfl

theorem cell22_1980142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_1980142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1980142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1980142 prefixEnd_1980142 := by exact prefixLift 1980142
  have htrace : WordTrace (prefixWord ++ tailWord_1980142) baseStart_1980142 baseEnd_1980142 := by
    simpa [prefixWord, tailWord_1980142, baseEnd_1980142] using wordTrace_append hprefix tailTrace_1980142
  have hstable : (prefixWord ++ tailWord_1980142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980142).length < 2 ^ (prefixWord ++ tailWord_1980142).sum := by decide
  have hdescent : baseEnd_1980142 < baseStart_1980142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980155 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 1, 9]
def baseStart_1980155 : Nat := 118140960795 + 1980155 * 2 ^ 59
def prefixEnd_1980155 : Nat := 4983230072969 + 3 ^ 40 * 1980155 * 2
def baseEnd_1980155 : Nat := 677847523602536912103959

theorem tailTrace_1980155 : CollatzResearch.WordTrace tailWord_1980155 prefixEnd_1980155 677847523602536912103959 := by
  unfold tailWord_1980155
  simp only [CollatzResearch.WordTrace]
  refine ⟨72222186141244093394941919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48148124094162728929961279 72222186141244093394941919)
  ·
    refine ⟨108333279211866140092412879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72222186141244093394941919 108333279211866140092412879)
    ·
      refine ⟨162499918817799210138619319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108333279211866140092412879 162499918817799210138619319)
      ·
        refine ⟨243749878226698815207928979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162499918817799210138619319 243749878226698815207928979)
        ·
          refine ⟨365624817340048222811893469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243749878226698815207928979 365624817340048222811893469)
          ·
            refine ⟨137109306502518083554460051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 365624817340048222811893469 137109306502518083554460051)
            ·
              refine ⟨205663959753777125331690077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137109306502518083554460051 205663959753777125331690077)
              ·
                refine ⟨77123984907666421999383779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 205663959753777125331690077 77123984907666421999383779)
                ·
                  refine ⟨115685977361499632999075669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77123984907666421999383779 115685977361499632999075669)
                  ·
                    refine ⟨677847523602536912103959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 115685977361499632999075669 677847523602536912103959)
                    ·
                      rfl

theorem cell22_1980155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 9].length) (baseStart_1980155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1980155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1980155 prefixEnd_1980155 := by exact prefixLift 1980155
  have htrace : WordTrace (prefixWord ++ tailWord_1980155) baseStart_1980155 baseEnd_1980155 := by
    simpa [prefixWord, tailWord_1980155, baseEnd_1980155] using wordTrace_append hprefix tailTrace_1980155
  have hstable : (prefixWord ++ tailWord_1980155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980155).length < 2 ^ (prefixWord ++ tailWord_1980155).sum := by decide
  have hdescent : baseEnd_1980155 < baseStart_1980155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980178 : List Nat := [3, 2, 4, 1, 1, 1, 3, 2, 2, 3]
def baseStart_1980178 : Nat := 118140960795 + 1980178 * 2 ^ 59
def prefixEnd_1980178 : Nat := 4983230072969 + 3 ^ 40 * 1980178 * 2
def baseEnd_1980178 : Nat := 677855396972572518778889

theorem tailTrace_1980178 : CollatzResearch.WordTrace tailWord_1980178 prefixEnd_1980178 677855396972572518778889 := by
  unfold tailWord_1980178
  simp only [CollatzResearch.WordTrace]
  refine ⟨18055756255040192080757297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48148683346773845548686125 18055756255040192080757297)
  ·
    refine ⟨13541817191280144060567973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18055756255040192080757297 13541817191280144060567973)
    ·
      refine ⟨2539090723365027011356495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13541817191280144060567973 2539090723365027011356495)
      ·
        refine ⟨3808636085047540517034743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2539090723365027011356495 3808636085047540517034743)
        ·
          refine ⟨5712954127571310775552115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3808636085047540517034743 5712954127571310775552115)
          ·
            refine ⟨8569431191356966163328173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5712954127571310775552115 8569431191356966163328173)
            ·
              refine ⟨3213536696758862311248065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8569431191356966163328173 3213536696758862311248065)
              ·
                refine ⟨2410152522569146733436049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3213536696758862311248065 2410152522569146733436049)
                ·
                  refine ⟨1807614391926860050077037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2410152522569146733436049 1807614391926860050077037)
                  ·
                    refine ⟨677855396972572518778889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1807614391926860050077037 677855396972572518778889)
                    ·
                      rfl

theorem cell22_1980178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_1980178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1980178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1980178 prefixEnd_1980178 := by exact prefixLift 1980178
  have htrace : WordTrace (prefixWord ++ tailWord_1980178) baseStart_1980178 baseEnd_1980178 := by
    simpa [prefixWord, tailWord_1980178, baseEnd_1980178] using wordTrace_append hprefix tailTrace_1980178
  have hstable : (prefixWord ++ tailWord_1980178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980178).length < 2 ^ (prefixWord ++ tailWord_1980178).sum := by decide
  have hdescent : baseEnd_1980178 < baseStart_1980178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980298 : List Nat := [3, 1, 2, 4, 2, 1, 1, 4, 4]
def baseStart_1980298 : Nat := 118140960795 + 1980298 * 2 ^ 59
def prefixEnd_1980298 : Nat := 4983230072969 + 3 ^ 40 * 1980298 * 2
def baseEnd_1980298 : Nat := 225965491808310735259507

theorem tailTrace_1980298 : CollatzResearch.WordTrace tailWord_1980298 prefixEnd_1980298 225965491808310735259507 := by
  unfold tailWord_1980298
  simp only [CollatzResearch.WordTrace]
  refine ⟨18056850444931507204349387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48151601186484019211598365 18056850444931507204349387)
  ·
    refine ⟨27085275667397260806524081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18056850444931507204349387 27085275667397260806524081)
    ·
      refine ⟨20313956750547945604893061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27085275667397260806524081 20313956750547945604893061)
      ·
        refine ⟨3808866890727739800917449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20313956750547945604893061 3808866890727739800917449)
        ·
          refine ⟨2856650168045804850688087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3808866890727739800917449 2856650168045804850688087)
          ·
            refine ⟨4284975252068707276032131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2856650168045804850688087 4284975252068707276032131)
            ·
              refine ⟨6427462878103060914048197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4284975252068707276032131 6427462878103060914048197)
              ·
                refine ⟨1205149289644323921384037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6427462878103060914048197 1205149289644323921384037)
                ·
                  refine ⟨225965491808310735259507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1205149289644323921384037 225965491808310735259507)
                  ·
                    rfl

theorem cell22_1980298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4, 4].length) (baseStart_1980298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1980298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1980298 prefixEnd_1980298 := by exact prefixLift 1980298
  have htrace : WordTrace (prefixWord ++ tailWord_1980298) baseStart_1980298 baseEnd_1980298 := by
    simpa [prefixWord, tailWord_1980298, baseEnd_1980298] using wordTrace_append hprefix tailTrace_1980298
  have hstable : (prefixWord ++ tailWord_1980298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980298).length < 2 ^ (prefixWord ++ tailWord_1980298).sum := by decide
  have hdescent : baseEnd_1980298 < baseStart_1980298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980328 : List Nat := [2, 1, 6, 2, 1, 1, 1, 1, 1, 6]
def baseStart_1980328 : Nat := 118140960795 + 1980328 * 2 ^ 59
def prefixEnd_1980328 : Nat := 4983230072969 + 3 ^ 40 * 1980328 * 2
def baseEnd_1980328 : Nat := 677906745038022127528429

theorem tailTrace_1980328 : CollatzResearch.WordTrace tailWord_1980328 prefixEnd_1980328 677906745038022127528429 := by
  unfold tailWord_1980328
  simp only [CollatzResearch.WordTrace]
  refine ⟨36114247984808671970494819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48152330646411562627326425 36114247984808671970494819)
  ·
    refine ⟨54171371977213007955742229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36114247984808671970494819 54171371977213007955742229)
    ·
      refine ⟨2539283061431859747925417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54171371977213007955742229 2539283061431859747925417)
      ·
        refine ⟨1904462296073894810944063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2539283061431859747925417 1904462296073894810944063)
        ·
          refine ⟨2856693444110842216416095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1904462296073894810944063 2856693444110842216416095)
          ·
            refine ⟨4285040166166263324624143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2856693444110842216416095 4285040166166263324624143)
            ·
              refine ⟨6427560249249394986936215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4285040166166263324624143 6427560249249394986936215)
              ·
                refine ⟨9641340373874092480404323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6427560249249394986936215 9641340373874092480404323)
                ·
                  refine ⟨14462010560811138720606485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9641340373874092480404323 14462010560811138720606485)
                  ·
                    refine ⟨677906745038022127528429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14462010560811138720606485 677906745038022127528429)
                    ·
                      rfl

theorem cell22_1980328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_1980328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1980328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1980328 prefixEnd_1980328 := by exact prefixLift 1980328
  have htrace : WordTrace (prefixWord ++ tailWord_1980328) baseStart_1980328 baseEnd_1980328 := by
    simpa [prefixWord, tailWord_1980328, baseEnd_1980328] using wordTrace_append hprefix tailTrace_1980328
  have hstable : (prefixWord ++ tailWord_1980328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980328).length < 2 ^ (prefixWord ++ tailWord_1980328).sum := by decide
  have hdescent : baseEnd_1980328 < baseStart_1980328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980334 : List Nat := [4, 1, 5, 1, 1, 2, 2, 1, 1, 4]
def baseStart_1980334 : Nat := 118140960795 + 1980334 * 2 ^ 59
def prefixEnd_1980334 : Nat := 4983230072969 + 3 ^ 40 * 1980334 * 2
def baseEnd_1980334 : Nat := 677908798960640111878411

theorem tailTrace_1980334 : CollatzResearch.WordTrace tailWord_1980334 prefixEnd_1980334 677908798960640111878411 := by
  unfold tailWord_1980334
  simp only [CollatzResearch.WordTrace]
  refine ⟨9028589350949450870713507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48152476538397071310472037 9028589350949450870713507)
  ·
    refine ⟨13542884026424176306070261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9028589350949450870713507 13542884026424176306070261)
    ·
      refine ⟨1269645377477266528694087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13542884026424176306070261 1269645377477266528694087)
      ·
        refine ⟨1904468066215899793041131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1269645377477266528694087 1904468066215899793041131)
        ·
          refine ⟨2856702099323849689561697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1904468066215899793041131 2856702099323849689561697)
          ·
            refine ⟨2142526574492887267171273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2856702099323849689561697 2142526574492887267171273)
            ·
              refine ⟨1606894930869665450378455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2142526574492887267171273 1606894930869665450378455)
              ·
                refine ⟨2410342396304498175567683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1606894930869665450378455 2410342396304498175567683)
                ·
                  refine ⟨3615513594456747263351525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2410342396304498175567683 3615513594456747263351525)
                  ·
                    refine ⟨677908798960640111878411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3615513594456747263351525 677908798960640111878411)
                    ·
                      rfl

theorem cell22_1980334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_1980334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1980334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1980334 prefixEnd_1980334 := by exact prefixLift 1980334
  have htrace : WordTrace (prefixWord ++ tailWord_1980334) baseStart_1980334 baseEnd_1980334 := by
    simpa [prefixWord, tailWord_1980334, baseEnd_1980334] using wordTrace_append hprefix tailTrace_1980334
  have hstable : (prefixWord ++ tailWord_1980334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980334).length < 2 ^ (prefixWord ++ tailWord_1980334).sum := by decide
  have hdescent : baseEnd_1980334 < baseStart_1980334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980384 : List Nat := [2, 1, 1, 3, 1, 1, 1, 5, 3, 4]
def baseStart_1980384 : Nat := 118140960795 + 1980384 * 2 ^ 59
def prefixEnd_1980384 : Nat := 4983230072969 + 3 ^ 40 * 1980384 * 2
def baseEnd_1980384 : Nat := 677925914982456648128257

theorem tailTrace_1980384 : CollatzResearch.WordTrace tailWord_1980384 prefixEnd_1980384 677925914982456648128257 := by
  unfold tailWord_1980384
  simp only [CollatzResearch.WordTrace]
  refine ⟨36115269228707232752514103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48153692304942977003352137 36115269228707232752514103)
  ·
    refine ⟨54172903843060849128771155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36115269228707232752514103 54172903843060849128771155)
    ·
      refine ⟨81259355764591273693156733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54172903843060849128771155 81259355764591273693156733)
      ·
        refine ⟨30472258411721727634933775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81259355764591273693156733 30472258411721727634933775)
        ·
          refine ⟨45708387617582591452400663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30472258411721727634933775 45708387617582591452400663)
          ·
            refine ⟨68562581426373887178600995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45708387617582591452400663 68562581426373887178600995)
            ·
              refine ⟨102843872139560830767901493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68562581426373887178600995 102843872139560830767901493)
              ·
                refine ⟨9641613013083827884490765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 102843872139560830767901493 9641613013083827884490765)
                ·
                  refine ⟨3615604879906435456684037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9641613013083827884490765 3615604879906435456684037)
                  ·
                    refine ⟨677925914982456648128257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3615604879906435456684037 677925914982456648128257)
                    ·
                      rfl

theorem cell22_1980384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 3, 4].length) (baseStart_1980384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1980384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1980384 prefixEnd_1980384 := by exact prefixLift 1980384
  have htrace : WordTrace (prefixWord ++ tailWord_1980384) baseStart_1980384 baseEnd_1980384 := by
    simpa [prefixWord, tailWord_1980384, baseEnd_1980384] using wordTrace_append hprefix tailTrace_1980384
  have hstable : (prefixWord ++ tailWord_1980384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980384).length < 2 ^ (prefixWord ++ tailWord_1980384).sum := by decide
  have hdescent : baseEnd_1980384 < baseStart_1980384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980551 : List Nat := [1, 1, 4, 2, 1, 1, 4, 2, 6]
def baseStart_1980551 : Nat := 118140960795 + 1980551 * 2 ^ 59
def prefixEnd_1980551 : Nat := 4983230072969 + 3 ^ 40 * 1980551 * 2
def baseEnd_1980551 : Nat := 225994360831774626400915

theorem tailTrace_1980551 : CollatzResearch.WordTrace tailWord_1980551 prefixEnd_1980551 225994360831774626400915 := by
  unfold tailWord_1980551
  simp only [CollatzResearch.WordTrace]
  refine ⟨72236629447809453026357507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48157752965206302017571671 72236629447809453026357507)
  ·
    refine ⟨108354944171714179539536261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72236629447809453026357507 108354944171714179539536261)
    ·
      refine ⟨20316552032196408663663049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108354944171714179539536261 20316552032196408663663049)
      ·
        refine ⟨15237414024147306497747287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20316552032196408663663049 15237414024147306497747287)
        ·
          refine ⟨22856121036220959746620931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15237414024147306497747287 22856121036220959746620931)
          ·
            refine ⟨34284181554331439619931397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22856121036220959746620931 34284181554331439619931397)
            ·
              refine ⟨6428284041437144928737137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34284181554331439619931397 6428284041437144928737137)
              ·
                refine ⟨4821213031077858696552853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6428284041437144928737137 4821213031077858696552853)
                ·
                  refine ⟨225994360831774626400915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4821213031077858696552853 225994360831774626400915)
                  ·
                    rfl

theorem cell22_1980551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 6].length) (baseStart_1980551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1980551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1980551 prefixEnd_1980551 := by exact prefixLift 1980551
  have htrace : WordTrace (prefixWord ++ tailWord_1980551) baseStart_1980551 baseEnd_1980551 := by
    simpa [prefixWord, tailWord_1980551, baseEnd_1980551] using wordTrace_append hprefix tailTrace_1980551
  have hstable : (prefixWord ++ tailWord_1980551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980551).length < 2 ^ (prefixWord ++ tailWord_1980551).sum := by decide
  have hdescent : baseEnd_1980551 < baseStart_1980551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980553 : List Nat := [1, 2, 1, 1, 4, 2, 4, 2, 1, 4]
def baseStart_1980553 : Nat := 118140960795 + 1980553 * 2 ^ 59
def prefixEnd_1980553 : Nat := 4983230072969 + 3 ^ 40 * 1980553 * 2
def baseEnd_1980553 : Nat := 677983767136196540652739

theorem tailTrace_1980553 : CollatzResearch.WordTrace tailWord_1980553 prefixEnd_1980553 677983767136196540652739 := by
  unfold tailWord_1980553
  simp only [CollatzResearch.WordTrace]
  refine ⟨72236702393802207367930313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48157801595868138245286875 72236702393802207367930313)
  ·
    refine ⟨54177526795351655525947735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72236702393802207367930313 54177526795351655525947735)
    ·
      refine ⟨81266290193027483288921603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54177526795351655525947735 81266290193027483288921603)
      ·
        refine ⟨121899435289541224933382405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81266290193027483288921603 121899435289541224933382405)
        ·
          refine ⟨22856144116788979675009201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121899435289541224933382405 22856144116788979675009201)
          ·
            refine ⟨17142108087591734756256901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22856144116788979675009201 17142108087591734756256901)
            ·
              refine ⟨3214145266423450266798169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17142108087591734756256901 3214145266423450266798169)
              ·
                refine ⟨2410608949817587700098627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3214145266423450266798169 2410608949817587700098627)
                ·
                  refine ⟨3615913424726381550147941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2410608949817587700098627 3615913424726381550147941)
                  ·
                    refine ⟨677983767136196540652739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3615913424726381550147941 677983767136196540652739)
                    ·
                      rfl

theorem cell22_1980553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 1, 4].length) (baseStart_1980553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1980553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1980553 prefixEnd_1980553 := by exact prefixLift 1980553
  have htrace : WordTrace (prefixWord ++ tailWord_1980553) baseStart_1980553 baseEnd_1980553 := by
    simpa [prefixWord, tailWord_1980553, baseEnd_1980553] using wordTrace_append hprefix tailTrace_1980553
  have hstable : (prefixWord ++ tailWord_1980553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980553).length < 2 ^ (prefixWord ++ tailWord_1980553).sum := by decide
  have hdescent : baseEnd_1980553 < baseStart_1980553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980636 : List Nat := [2, 2, 5, 2, 1, 2, 2, 2, 4]
def baseStart_1980636 : Nat := 118140960795 + 1980636 * 2 ^ 59
def prefixEnd_1980636 : Nat := 4983230072969 + 3 ^ 40 * 1980636 * 2
def baseEnd_1980636 : Nat := 226004059910803996942495

theorem tailTrace_1980636 : CollatzResearch.WordTrace tailWord_1980636 prefixEnd_1980636 226004059910803996942495 := by
  unfold tailWord_1980636
  simp only [CollatzResearch.WordTrace]
  refine ⟨36119864826250756271600881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48159819768334341695467841 36119864826250756271600881)
  ·
    refine ⟨27089898619688067203700661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36119864826250756271600881 27089898619688067203700661)
    ·
      refine ⟨2539677995595756300346937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27089898619688067203700661 2539677995595756300346937)
      ·
        refine ⟨1904758496696817225260203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2539677995595756300346937 1904758496696817225260203)
        ·
          refine ⟨2857137745045225837890305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1904758496696817225260203 2857137745045225837890305)
          ·
            refine ⟨2142853308783919378417729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2857137745045225837890305 2142853308783919378417729)
            ·
              refine ⟨1607139981587939533813297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2142853308783919378417729 1607139981587939533813297)
              ·
                refine ⟨1205354986190954650359973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1607139981587939533813297 1205354986190954650359973)
                ·
                  refine ⟨226004059910803996942495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1205354986190954650359973 226004059910803996942495)
                  ·
                    rfl

theorem cell22_1980636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2, 4].length) (baseStart_1980636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1980636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1980636 prefixEnd_1980636 := by exact prefixLift 1980636
  have htrace : WordTrace (prefixWord ++ tailWord_1980636) baseStart_1980636 baseEnd_1980636 := by
    simpa [prefixWord, tailWord_1980636, baseEnd_1980636] using wordTrace_append hprefix tailTrace_1980636
  have hstable : (prefixWord ++ tailWord_1980636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980636).length < 2 ^ (prefixWord ++ tailWord_1980636).sum := by decide
  have hdescent : baseEnd_1980636 < baseStart_1980636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980703 : List Nat := [1, 1, 2, 4, 3, 1, 1, 3, 6]
def baseStart_1980703 : Nat := 118140960795 + 1980703 * 2 ^ 59
def prefixEnd_1980703 : Nat := 4983230072969 + 3 ^ 40 * 1980703 * 2
def baseEnd_1980703 : Nat := 226011705067215383134093

theorem tailTrace_1980703 : CollatzResearch.WordTrace tailWord_1980703 prefixEnd_1980703 226011705067215383134093 := by
  unfold tailWord_1980703
  simp only [CollatzResearch.WordTrace]
  refine ⟨72242173343258782985890763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48161448895505855323927175 72242173343258782985890763)
  ·
    refine ⟨108363260014888174478836145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72242173343258782985890763 108363260014888174478836145)
    ·
      refine ⟨81272445011166130859127109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108363260014888174478836145 81272445011166130859127109)
      ·
        refine ⟨15238583439593649536086333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81272445011166130859127109 15238583439593649536086333)
        ·
          refine ⟨5714468789847618576032375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15238583439593649536086333 5714468789847618576032375)
          ·
            refine ⟨8571703184771427864048563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5714468789847618576032375 8571703184771427864048563)
            ·
              refine ⟨12857554777157141796072845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8571703184771427864048563 12857554777157141796072845)
              ·
                refine ⟨4821583041433928173527317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12857554777157141796072845 4821583041433928173527317)
                ·
                  refine ⟨226011705067215383134093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4821583041433928173527317 226011705067215383134093)
                  ·
                    rfl

theorem cell22_1980703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 6].length) (baseStart_1980703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1980703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1980703 prefixEnd_1980703 := by exact prefixLift 1980703
  have htrace : WordTrace (prefixWord ++ tailWord_1980703) baseStart_1980703 baseEnd_1980703 := by
    simpa [prefixWord, tailWord_1980703, baseEnd_1980703] using wordTrace_append hprefix tailTrace_1980703
  have hstable : (prefixWord ++ tailWord_1980703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980703).length < 2 ^ (prefixWord ++ tailWord_1980703).sum := by decide
  have hdescent : baseEnd_1980703 < baseStart_1980703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980722 : List Nat := [3, 2, 1, 1, 5, 1, 2, 2, 1, 4]
def baseStart_1980722 : Nat := 118140960795 + 1980722 * 2 ^ 59
def prefixEnd_1980722 : Nat := 4983230072969 + 3 ^ 40 * 1980722 * 2
def baseEnd_1980722 : Nat := 678041619289936433177221

theorem tailTrace_1980722 : CollatzResearch.WordTrace tailWord_1980722 prefixEnd_1980722 678041619289936433177221 := by
  unfold tailWord_1980722
  simp only [CollatzResearch.WordTrace]
  refine ⟨18060716582547487307708105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48161910886793299487221613 18060716582547487307708105)
  ·
    refine ⟨13545537436910615480781079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18060716582547487307708105 13545537436910615480781079)
    ·
      refine ⟨20318306155365923221171619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13545537436910615480781079 20318306155365923221171619)
      ·
        refine ⟨30477459233048884831757429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20318306155365923221171619 30477459233048884831757429)
        ·
          refine ⟨2857261803098332952977259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30477459233048884831757429 2857261803098332952977259)
          ·
            refine ⟨4285892704647499429465889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2857261803098332952977259 4285892704647499429465889)
            ·
              refine ⟨3214419528485624572099417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4285892704647499429465889 3214419528485624572099417)
              ·
                refine ⟨2410814646364218429074563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3214419528485624572099417 2410814646364218429074563)
                ·
                  refine ⟨3616221969546327643611845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2410814646364218429074563 3616221969546327643611845)
                  ·
                    refine ⟨678041619289936433177221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3616221969546327643611845 678041619289936433177221)
                    ·
                      rfl

theorem cell22_1980722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_1980722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1980722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1980722 prefixEnd_1980722 := by exact prefixLift 1980722
  have htrace : WordTrace (prefixWord ++ tailWord_1980722) baseStart_1980722 baseEnd_1980722 := by
    simpa [prefixWord, tailWord_1980722, baseEnd_1980722] using wordTrace_append hprefix tailTrace_1980722
  have hstable : (prefixWord ++ tailWord_1980722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980722).length < 2 ^ (prefixWord ++ tailWord_1980722).sum := by decide
  have hdescent : baseEnd_1980722 < baseStart_1980722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980857 : List Nat := [1, 2, 1, 4, 3, 2, 1, 3, 1, 4]
def baseStart_1980857 : Nat := 118140960795 + 1980857 * 2 ^ 59
def prefixEnd_1980857 : Nat := 4983230072969 + 3 ^ 40 * 1980857 * 2
def baseEnd_1980857 : Nat := 678087832548841081051807

theorem tailTrace_1980857 : CollatzResearch.WordTrace tailWord_1980857 prefixEnd_1980857 678087832548841081051807 := by
  unfold tailWord_1980857
  simp only [CollatzResearch.WordTrace]
  refine ⟨72247790184700867286996825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48165193456467244857997883 72247790184700867286996825)
  ·
    refine ⟨54185842638525650465247619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72247790184700867286996825 54185842638525650465247619)
    ·
      refine ⟨81278763957788475697871429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54185842638525650465247619 81278763957788475697871429)
      ·
        refine ⟨15239768242085339193350893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81278763957788475697871429 15239768242085339193350893)
        ·
          refine ⟨5714913090782002197506585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15239768242085339193350893 5714913090782002197506585)
          ·
            refine ⟨4286184818086501648129939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5714913090782002197506585 4286184818086501648129939)
            ·
              refine ⟨6429277227129752472194909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4286184818086501648129939 6429277227129752472194909)
              ·
                refine ⟨2410978960173657177073091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6429277227129752472194909 2410978960173657177073091)
                ·
                  refine ⟨3616468440260485765609637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2410978960173657177073091 3616468440260485765609637)
                  ·
                    refine ⟨678087832548841081051807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3616468440260485765609637 678087832548841081051807)
                    ·
                      rfl

theorem cell22_1980857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 1, 4].length) (baseStart_1980857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1980857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1980857 prefixEnd_1980857 := by exact prefixLift 1980857
  have htrace : WordTrace (prefixWord ++ tailWord_1980857) baseStart_1980857 baseEnd_1980857 := by
    simpa [prefixWord, tailWord_1980857, baseEnd_1980857] using wordTrace_append hprefix tailTrace_1980857
  have hstable : (prefixWord ++ tailWord_1980857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980857).length < 2 ^ (prefixWord ++ tailWord_1980857).sum := by decide
  have hdescent : baseEnd_1980857 < baseStart_1980857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980872 : List Nat := [2, 1, 3, 1, 3, 2, 2, 4, 4]
def baseStart_1980872 : Nat := 118140960795 + 1980872 * 2 ^ 59
def prefixEnd_1980872 : Nat := 4983230072969 + 3 ^ 40 * 1980872 * 2
def baseEnd_1980872 : Nat := 226030989118462013975587

theorem tailTrace_1980872 : CollatzResearch.WordTrace tailWord_1980872 prefixEnd_1980872 226030989118462013975587 := by
  unfold tailWord_1980872
  simp only [CollatzResearch.WordTrace]
  refine ⟨36124168639823262424396435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48165558186431016565861913 36124168639823262424396435)
  ·
    refine ⟨54186252959734893636594653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36124168639823262424396435 54186252959734893636594653)
    ·
      refine ⟨20319844859900585113722995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54186252959734893636594653 20319844859900585113722995)
      ·
        refine ⟨30479767289850877670584493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20319844859900585113722995 30479767289850877670584493)
        ·
          refine ⟨11429912733694079126469185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30479767289850877670584493 11429912733694079126469185)
          ·
            refine ⟨8572434550270559344851889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11429912733694079126469185 8572434550270559344851889)
            ·
              refine ⟨6429325912702919508638917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8572434550270559344851889 6429325912702919508638917)
              ·
                refine ⟨1205498608631797407869797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6429325912702919508638917 1205498608631797407869797)
                ·
                  refine ⟨226030989118462013975587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1205498608631797407869797 226030989118462013975587)
                  ·
                    rfl

theorem cell22_1980872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4, 4].length) (baseStart_1980872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1980872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1980872 prefixEnd_1980872 := by exact prefixLift 1980872
  have htrace : WordTrace (prefixWord ++ tailWord_1980872) baseStart_1980872 baseEnd_1980872 := by
    simpa [prefixWord, tailWord_1980872, baseEnd_1980872] using wordTrace_append hprefix tailTrace_1980872
  have hstable : (prefixWord ++ tailWord_1980872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980872).length < 2 ^ (prefixWord ++ tailWord_1980872).sum := by decide
  have hdescent : baseEnd_1980872 < baseStart_1980872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1980885 : List Nat := [1, 3, 2, 3, 1, 2, 1, 2, 1, 6]
def baseStart_1980885 : Nat := 118140960795 + 1980885 * 2 ^ 59
def prefixEnd_1980885 : Nat := 4983230072969 + 3 ^ 40 * 1980885 * 2
def baseEnd_1980885 : Nat := 678097417521058341351721

theorem tailTrace_1980885 : CollatzResearch.WordTrace tailWord_1980885 prefixEnd_1980885 678097417521058341351721 := by
  unfold tailWord_1980885
  simp only [CollatzResearch.WordTrace]
  refine ⟨72248811428599428069016109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48165874285732952046010739 72248811428599428069016109)
  ·
    refine ⟨27093304285724785525881041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72248811428599428069016109 27093304285724785525881041)
    ·
      refine ⟨20319978214293589144410781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27093304285724785525881041 20319978214293589144410781)
      ·
        refine ⟨7619991830360095929154043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20319978214293589144410781 7619991830360095929154043)
        ·
          refine ⟨11429987745540143893731065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7619991830360095929154043 11429987745540143893731065)
          ·
            refine ⟨8572490809155107920298299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11429987745540143893731065 8572490809155107920298299)
            ·
              refine ⟨12858736213732661880447449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8572490809155107920298299 12858736213732661880447449)
              ·
                refine ⟨9644052160299496410335587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12858736213732661880447449 9644052160299496410335587)
                ·
                  refine ⟨14466078240449244615503381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9644052160299496410335587 14466078240449244615503381)
                  ·
                    refine ⟨678097417521058341351721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14466078240449244615503381 678097417521058341351721)
                    ·
                      rfl

theorem cell22_1980885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_1980885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1980885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1980885 prefixEnd_1980885 := by exact prefixLift 1980885
  have htrace : WordTrace (prefixWord ++ tailWord_1980885) baseStart_1980885 baseEnd_1980885 := by
    simpa [prefixWord, tailWord_1980885, baseEnd_1980885] using wordTrace_append hprefix tailTrace_1980885
  have hstable : (prefixWord ++ tailWord_1980885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1980885).length < 2 ^ (prefixWord ++ tailWord_1980885).sum := by decide
  have hdescent : baseEnd_1980885 < baseStart_1980885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1980885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981039 : List Nat := [1, 1, 2, 1, 3, 2, 5, 2, 2, 3]
def baseStart_1981039 : Nat := 118140960795 + 1981039 * 2 ^ 59
def prefixEnd_1981039 : Nat := 4983230072969 + 3 ^ 40 * 1981039 * 2
def baseEnd_1981039 : Nat := 678150134868253273001249

theorem tailTrace_1981039 : CollatzResearch.WordTrace tailWord_1981039 prefixEnd_1981039 678150134868253273001249 := by
  unfold tailWord_1981039
  simp only [CollatzResearch.WordTrace]
  refine ⟨72254428270041512370122171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48169618846694341580081447 72254428270041512370122171)
  ·
    refine ⟨108381642405062268555183257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72254428270041512370122171 108381642405062268555183257)
    ·
      refine ⟨81286231803796701416387443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108381642405062268555183257 81286231803796701416387443)
      ·
        refine ⟨121929347705695052124581165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81286231803796701416387443 121929347705695052124581165)
        ·
          refine ⟨45723505389635644546717937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121929347705695052124581165 45723505389635644546717937)
          ·
            refine ⟨34292629042226733410038453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45723505389635644546717937 34292629042226733410038453)
            ·
              refine ⟨3214933972708756257191105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34292629042226733410038453 3214933972708756257191105)
              ·
                refine ⟨2411200479531567192893329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3214933972708756257191105 2411200479531567192893329)
                ·
                  refine ⟨1808400359648675394669997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2411200479531567192893329 1808400359648675394669997)
                  ·
                    refine ⟨678150134868253273001249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1808400359648675394669997 678150134868253273001249)
                    ·
                      rfl

theorem cell22_1981039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2, 3].length) (baseStart_1981039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1981039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1981039 prefixEnd_1981039 := by exact prefixLift 1981039
  have htrace : WordTrace (prefixWord ++ tailWord_1981039) baseStart_1981039 baseEnd_1981039 := by
    simpa [prefixWord, tailWord_1981039, baseEnd_1981039] using wordTrace_append hprefix tailTrace_1981039
  have hstable : (prefixWord ++ tailWord_1981039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981039).length < 2 ^ (prefixWord ++ tailWord_1981039).sum := by decide
  have hdescent : baseEnd_1981039 < baseStart_1981039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981056 : List Nat := [2, 1, 1, 2, 1, 6, 3, 1, 2, 3]
def baseStart_1981056 : Nat := 118140960795 + 1981056 * 2 ^ 59
def prefixEnd_1981056 : Nat := 4983230072969 + 3 ^ 40 * 1981056 * 2
def baseEnd_1981056 : Nat := 678155954315670895326197

theorem tailTrace_1981056 : CollatzResearch.WordTrace tailWord_1981056 prefixEnd_1981056 678155954315670895326197 := by
  unfold tailWord_1981056
  simp only [CollatzResearch.WordTrace]
  refine ⟨36127524155489962136745511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48170032207319949515660681 36127524155489962136745511)
  ·
    refine ⟨54191286233234943205118267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36127524155489962136745511 54191286233234943205118267)
    ·
      refine ⟨81286929349852414807677401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54191286233234943205118267 81286929349852414807677401)
      ·
        refine ⟨60965197012389311105758051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81286929349852414807677401 60965197012389311105758051)
        ·
          refine ⟨91447795518583966658637077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60965197012389311105758051 91447795518583966658637077)
          ·
            refine ⟨4286615414933623437123613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91447795518583966658637077 4286615414933623437123613)
            ·
              refine ⟨1607480780600108788921355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4286615414933623437123613 1607480780600108788921355)
              ·
                refine ⟨2411221170900163183382033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1607480780600108788921355 2411221170900163183382033)
                ·
                  refine ⟨1808415878175122387536525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2411221170900163183382033 1808415878175122387536525)
                  ·
                    refine ⟨678155954315670895326197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1808415878175122387536525 678155954315670895326197)
                    ·
                      rfl

theorem cell22_1981056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 2, 3].length) (baseStart_1981056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1981056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1981056 prefixEnd_1981056 := by exact prefixLift 1981056
  have htrace : WordTrace (prefixWord ++ tailWord_1981056) baseStart_1981056 baseEnd_1981056 := by
    simpa [prefixWord, tailWord_1981056, baseEnd_1981056] using wordTrace_append hprefix tailTrace_1981056
  have hstable : (prefixWord ++ tailWord_1981056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981056).length < 2 ^ (prefixWord ++ tailWord_1981056).sum := by decide
  have hdescent : baseEnd_1981056 < baseStart_1981056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981067 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 5, 3]
def baseStart_1981067 : Nat := 118140960795 + 1981067 * 2 ^ 59
def prefixEnd_1981067 : Nat := 4983230072969 + 3 ^ 40 * 1981067 * 2
def baseEnd_1981067 : Nat := 678159719840470533301163

theorem tailTrace_1981067 : CollatzResearch.WordTrace tailWord_1981067 prefixEnd_1981067 678159719840470533301163 := by
  unfold tailWord_1981067
  simp only [CollatzResearch.WordTrace]
  refine ⟨72255449513940073152141455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48170299675960048768094303 72255449513940073152141455)
  ·
    refine ⟨108383174270910109728212183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72255449513940073152141455 108383174270910109728212183)
    ·
      refine ⟨162574761406365164592318275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108383174270910109728212183 162574761406365164592318275)
      ·
        refine ⟨243862142109547746888477413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162574761406365164592318275 243862142109547746888477413)
        ·
          refine ⟨45724151645540202541589515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 243862142109547746888477413 45724151645540202541589515)
          ·
            refine ⟨68586227468310303812384273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45724151645540202541589515 68586227468310303812384273)
            ·
              refine ⟨51439670601232727859288205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68586227468310303812384273 51439670601232727859288205)
              ·
                refine ⟨19289876475462272947233077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51439670601232727859288205 19289876475462272947233077)
                ·
                  refine ⟨1808425919574588088803101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19289876475462272947233077 1808425919574588088803101)
                  ·
                    refine ⟨678159719840470533301163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1808425919574588088803101 678159719840470533301163)
                    ·
                      rfl

theorem cell22_1981067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5, 3].length) (baseStart_1981067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1981067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1981067 prefixEnd_1981067 := by exact prefixLift 1981067
  have htrace : WordTrace (prefixWord ++ tailWord_1981067) baseStart_1981067 baseEnd_1981067 := by
    simpa [prefixWord, tailWord_1981067, baseEnd_1981067] using wordTrace_append hprefix tailTrace_1981067
  have hstable : (prefixWord ++ tailWord_1981067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981067).length < 2 ^ (prefixWord ++ tailWord_1981067).sum := by decide
  have hdescent : baseEnd_1981067 < baseStart_1981067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981101 : List Nat := [1, 5, 2, 1, 1, 2, 3, 1, 3, 3]
def baseStart_1981101 : Nat := 118140960795 + 1981101 * 2 ^ 59
def prefixEnd_1981101 : Nat := 4983230072969 + 3 ^ 40 * 1981101 * 2
def baseEnd_1981101 : Nat := 678171358735305777951059

theorem tailTrace_1981101 : CollatzResearch.WordTrace tailWord_1981101 prefixEnd_1981101 678171358735305777951059 := by
  unfold tailWord_1981101
  simp only [CollatzResearch.WordTrace]
  refine ⟨72256689595816896958879157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48171126397211264639252771 72256689595816896958879157)
  ·
    refine ⟨6774064649607834089894921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72256689595816896958879157 6774064649607834089894921)
    ·
      refine ⟨5080548487205875567421191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6774064649607834089894921 5080548487205875567421191)
      ·
        refine ⟨7620822730808813351131787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5080548487205875567421191 7620822730808813351131787)
        ·
          refine ⟨11431234096213220026697681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7620822730808813351131787 11431234096213220026697681)
          ·
            refine ⟨8573425572159915020023261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11431234096213220026697681 8573425572159915020023261)
            ·
              refine ⟨3215034589559968132508723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8573425572159915020023261 3215034589559968132508723)
              ·
                refine ⟨4822551884339952198763085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3215034589559968132508723 4822551884339952198763085)
                ·
                  refine ⟨1808456956627482074536157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4822551884339952198763085 1808456956627482074536157)
                  ·
                    refine ⟨678171358735305777951059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1808456956627482074536157 678171358735305777951059)
                    ·
                      rfl

theorem cell22_1981101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_1981101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1981101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1981101 prefixEnd_1981101 := by exact prefixLift 1981101
  have htrace : WordTrace (prefixWord ++ tailWord_1981101) baseStart_1981101 baseEnd_1981101 := by
    simpa [prefixWord, tailWord_1981101, baseEnd_1981101] using wordTrace_append hprefix tailTrace_1981101
  have hstable : (prefixWord ++ tailWord_1981101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981101).length < 2 ^ (prefixWord ++ tailWord_1981101).sum := by decide
  have hdescent : baseEnd_1981101 < baseStart_1981101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981279 : List Nat := [1, 1, 2, 3, 1, 3, 2, 2, 3, 4]
def baseStart_1981279 : Nat := 118140960795 + 1981279 * 2 ^ 59
def prefixEnd_1981279 : Nat := 4983230072969 + 3 ^ 40 * 1981279 * 2
def baseEnd_1981279 : Nat := 678232291772972647000513

theorem tailTrace_1981279 : CollatzResearch.WordTrace tailWord_1981279 prefixEnd_1981279 678232291772972647000513 := by
  unfold tailWord_1981279
  simp only [CollatzResearch.WordTrace]
  refine ⟨72263181789172033358858891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48175454526114688905905927 72263181789172033358858891)
  ·
    refine ⟨108394772683758050038288337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72263181789172033358858891 108394772683758050038288337)
    ·
      refine ⟨81296079512818537528716253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108394772683758050038288337 81296079512818537528716253)
      ·
        refine ⟨30486029817306951573268595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81296079512818537528716253 30486029817306951573268595)
        ·
          refine ⟨45729044725960427359902893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30486029817306951573268595 45729044725960427359902893)
          ·
            refine ⟨17148391772235160259963585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45729044725960427359902893 17148391772235160259963585)
            ·
              refine ⟨12861293829176370194972689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17148391772235160259963585 12861293829176370194972689)
              ·
                refine ⟨9645970371882277646229517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12861293829176370194972689 9645970371882277646229517)
                ·
                  refine ⟨3617238889455854117336069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9645970371882277646229517 3617238889455854117336069)
                  ·
                    refine ⟨678232291772972647000513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3617238889455854117336069 678232291772972647000513)
                    ·
                      rfl

theorem cell22_1981279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 4].length) (baseStart_1981279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1981279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1981279 prefixEnd_1981279 := by exact prefixLift 1981279
  have htrace : WordTrace (prefixWord ++ tailWord_1981279) baseStart_1981279 baseEnd_1981279 := by
    simpa [prefixWord, tailWord_1981279, baseEnd_1981279] using wordTrace_append hprefix tailTrace_1981279
  have hstable : (prefixWord ++ tailWord_1981279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981279).length < 2 ^ (prefixWord ++ tailWord_1981279).sum := by decide
  have hdescent : baseEnd_1981279 < baseStart_1981279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981283 : List Nat := [1, 1, 1, 5, 3, 3, 2, 1, 5]
def baseStart_1981283 : Nat := 118140960795 + 1981283 * 2 ^ 59
def prefixEnd_1981283 : Nat := 4983230072969 + 3 ^ 40 * 1981283 * 2
def baseEnd_1981283 : Nat := 226077887018239323300167

theorem tailTrace_1981283 : CollatzResearch.WordTrace tailWord_1981283 prefixEnd_1981283 226077887018239323300167 := by
  unfold tailWord_1981283
  simp only [CollatzResearch.WordTrace]
  refine ⟨72263327681157542042004503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48175551787438361361336335 72263327681157542042004503)
  ·
    refine ⟨108394991521736313063006755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72263327681157542042004503 108394991521736313063006755)
    ·
      refine ⟨162592487282604469594510133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108394991521736313063006755 162592487282604469594510133)
      ·
        refine ⟨15243045682744169024485325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162592487282604469594510133 15243045682744169024485325)
        ·
          refine ⟨5716142131029063384181997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15243045682744169024485325 5716142131029063384181997)
          ·
            refine ⟨2143553299135898769068249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5716142131029063384181997 2143553299135898769068249)
            ·
              refine ⟨1607664974351924076801187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2143553299135898769068249 1607664974351924076801187)
              ·
                refine ⟨2411497461527886115201781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1607664974351924076801187 2411497461527886115201781)
                ·
                  refine ⟨226077887018239323300167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2411497461527886115201781 226077887018239323300167)
                  ·
                    rfl

theorem cell22_1981283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 5].length) (baseStart_1981283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1981283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1981283 prefixEnd_1981283 := by exact prefixLift 1981283
  have htrace : WordTrace (prefixWord ++ tailWord_1981283) baseStart_1981283 baseEnd_1981283 := by
    simpa [prefixWord, tailWord_1981283, baseEnd_1981283] using wordTrace_append hprefix tailTrace_1981283
  have hstable : (prefixWord ++ tailWord_1981283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981283).length < 2 ^ (prefixWord ++ tailWord_1981283).sum := by decide
  have hdescent : baseEnd_1981283 < baseStart_1981283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981296 : List Nat := [2, 1, 1, 1, 4, 1, 5, 2, 1, 4]
def baseStart_1981296 : Nat := 118140960795 + 1981296 * 2 ^ 59
def prefixEnd_1981296 : Nat := 4983230072969 + 3 ^ 40 * 1981296 * 2
def baseEnd_1981296 : Nat := 678238111220390269325461

theorem tailTrace_1981296 : CollatzResearch.WordTrace tailWord_1981296 prefixEnd_1981296 678238111220390269325461 := by
  unfold tailWord_1981296
  simp only [CollatzResearch.WordTrace]
  refine ⟨36131900915055222631113871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48175867886740296841485161 36131900915055222631113871)
  ·
    refine ⟨54197851372582833946670807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36131900915055222631113871 54197851372582833946670807)
    ·
      refine ⟨81296777058874250920006211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54197851372582833946670807 81296777058874250920006211)
      ·
        refine ⟨121945165588311376380009317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81296777058874250920006211 121945165588311376380009317)
        ·
          refine ⟨22864718547808383071251747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 121945165588311376380009317 22864718547808383071251747)
          ·
            refine ⟨34297077821712574606877621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22864718547808383071251747 34297077821712574606877621)
            ·
              refine ⟨3215351045785553869394777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34297077821712574606877621 3215351045785553869394777)
              ·
                refine ⟨2411513284339165402046083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3215351045785553869394777 2411513284339165402046083)
                ·
                  refine ⟨3617269926508748103069125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2411513284339165402046083 3617269926508748103069125)
                  ·
                    refine ⟨678238111220390269325461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3617269926508748103069125 678238111220390269325461)
                    ·
                      rfl

theorem cell22_1981296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 1, 4].length) (baseStart_1981296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1981296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1981296 prefixEnd_1981296 := by exact prefixLift 1981296
  have htrace : WordTrace (prefixWord ++ tailWord_1981296) baseStart_1981296 baseEnd_1981296 := by
    simpa [prefixWord, tailWord_1981296, baseEnd_1981296] using wordTrace_append hprefix tailTrace_1981296
  have hstable : (prefixWord ++ tailWord_1981296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981296).length < 2 ^ (prefixWord ++ tailWord_1981296).sum := by decide
  have hdescent : baseEnd_1981296 < baseStart_1981296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981309 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 3, 5]
def baseStart_1981309 : Nat := 118140960795 + 1981309 * 2 ^ 59
def prefixEnd_1981309 : Nat := 4983230072969 + 3 ^ 40 * 1981309 * 2
def baseEnd_1981309 : Nat := 678242561386062568750421

theorem tailTrace_1981309 : CollatzResearch.WordTrace tailWord_1981309 prefixEnd_1981309 678242561386062568750421 := by
  unfold tailWord_1981309
  simp only [CollatzResearch.WordTrace]
  refine ⟨72264275979063348482450981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48176183986042232321633987 72264275979063348482450981)
  ·
    refine ⟨13549551746074377840459559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72264275979063348482450981 13549551746074377840459559)
    ·
      refine ⟨20324327619111566760689339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13549551746074377840459559 20324327619111566760689339)
      ·
        refine ⟨30486491428667350141034009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20324327619111566760689339 30486491428667350141034009)
        ·
          refine ⟨22864868571500512605775507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30486491428667350141034009 22864868571500512605775507)
          ·
            refine ⟨34297302857250768908663261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22864868571500512605775507 34297302857250768908663261)
            ·
              refine ⟨12861488571469038340748723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34297302857250768908663261 12861488571469038340748723)
              ·
                refine ⟨19292232857203557511123085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12861488571469038340748723 19292232857203557511123085)
                ·
                  refine ⟨7234587321451334066671157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19292232857203557511123085 7234587321451334066671157)
                  ·
                    refine ⟨678242561386062568750421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7234587321451334066671157 678242561386062568750421)
                    ·
                      rfl

theorem cell22_1981309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_1981309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1981309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1981309 prefixEnd_1981309 := by exact prefixLift 1981309
  have htrace : WordTrace (prefixWord ++ tailWord_1981309) baseStart_1981309 baseEnd_1981309 := by
    simpa [prefixWord, tailWord_1981309, baseEnd_1981309] using wordTrace_append hprefix tailTrace_1981309
  have hstable : (prefixWord ++ tailWord_1981309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981309).length < 2 ^ (prefixWord ++ tailWord_1981309).sum := by decide
  have hdescent : baseEnd_1981309 < baseStart_1981309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981343 : List Nat := [1, 1, 2, 5, 2, 1, 2, 3, 2, 3]
def baseStart_1981343 : Nat := 118140960795 + 1981343 * 2 ^ 59
def prefixEnd_1981343 : Nat := 4983230072969 + 3 ^ 40 * 1981343 * 2
def baseEnd_1981343 : Nat := 678254200280897813400317

theorem tailTrace_1981343 : CollatzResearch.WordTrace tailWord_1981343 prefixEnd_1981343 678254200280897813400317 := by
  unfold tailWord_1981343
  simp only [CollatzResearch.WordTrace]
  refine ⟨72265516060940172289188683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48177010707293448192792455 72265516060940172289188683)
  ·
    refine ⟨108398274091410258433783025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72265516060940172289188683 108398274091410258433783025)
    ·
      refine ⟨81298705568557693825337269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108398274091410258433783025 81298705568557693825337269)
      ·
        refine ⟨7621753647052283796125369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81298705568557693825337269 7621753647052283796125369)
        ·
          refine ⟨5716315235289212847094027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7621753647052283796125369 5716315235289212847094027)
          ·
            refine ⟨8574472852933819270641041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5716315235289212847094027 8574472852933819270641041)
            ·
              refine ⟨6430854639700364452980781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8574472852933819270641041 6430854639700364452980781)
              ·
                refine ⟨2411570489887636669867793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6430854639700364452980781 2411570489887636669867793)
                ·
                  refine ⟨1808677867415727502400845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2411570489887636669867793 1808677867415727502400845)
                  ·
                    refine ⟨678254200280897813400317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1808677867415727502400845 678254200280897813400317)
                    ·
                      rfl

theorem cell22_1981343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2, 3].length) (baseStart_1981343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1981343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1981343 prefixEnd_1981343 := by exact prefixLift 1981343
  have htrace : WordTrace (prefixWord ++ tailWord_1981343) baseStart_1981343 baseEnd_1981343 := by
    simpa [prefixWord, tailWord_1981343, baseEnd_1981343] using wordTrace_append hprefix tailTrace_1981343
  have hstable : (prefixWord ++ tailWord_1981343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981343).length < 2 ^ (prefixWord ++ tailWord_1981343).sum := by decide
  have hdescent : baseEnd_1981343 < baseStart_1981343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981388 : List Nat := [2, 2, 1, 4, 1, 1, 4, 1, 3, 3]
def baseStart_1981388 : Nat := 118140960795 + 1981388 * 2 ^ 59
def prefixEnd_1981388 : Nat := 4983230072969 + 3 ^ 40 * 1981388 * 2
def baseEnd_1981388 : Nat := 678269604700532696025179

theorem tailTrace_1981388 : CollatzResearch.WordTrace tailWord_1981388 prefixEnd_1981388 678269604700532696025179 := by
  unfold tailWord_1981388
  simp only [CollatzResearch.WordTrace]
  refine ⟨36133578672888572487288409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48178104897184763316384545 36133578672888572487288409)
  ·
    refine ⟨27100184004666429365466307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36133578672888572487288409 27100184004666429365466307)
    ·
      refine ⟨40650276006999644048199461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27100184004666429365466307 40650276006999644048199461)
      ·
        refine ⟨7621926751312433259037399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40650276006999644048199461 7621926751312433259037399)
        ·
          refine ⟨11432890126968649888556099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7621926751312433259037399 11432890126968649888556099)
          ·
            refine ⟨17149335190452974832834149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11432890126968649888556099 17149335190452974832834149)
            ·
              refine ⟨3215500348209932781156403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17149335190452974832834149 3215500348209932781156403)
              ·
                refine ⟨4823250522314899171734605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3215500348209932781156403 4823250522314899171734605)
                ·
                  refine ⟨1808718945868087189400477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4823250522314899171734605 1808718945868087189400477)
                  ·
                    refine ⟨678269604700532696025179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1808718945868087189400477 678269604700532696025179)
                    ·
                      rfl

theorem cell22_1981388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 3, 3].length) (baseStart_1981388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1981388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1981388 prefixEnd_1981388 := by exact prefixLift 1981388
  have htrace : WordTrace (prefixWord ++ tailWord_1981388) baseStart_1981388 baseEnd_1981388 := by
    simpa [prefixWord, tailWord_1981388, baseEnd_1981388] using wordTrace_append hprefix tailTrace_1981388
  have hstable : (prefixWord ++ tailWord_1981388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981388).length < 2 ^ (prefixWord ++ tailWord_1981388).sum := by decide
  have hdescent : baseEnd_1981388 < baseStart_1981388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981399 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 1, 7]
def baseStart_1981399 : Nat := 118140960795 + 1981399 * 2 ^ 59
def prefixEnd_1981399 : Nat := 4983230072969 + 3 ^ 40 * 1981399 * 2
def baseEnd_1981399 : Nat := 678273370225332334000145

theorem tailTrace_1981399 : CollatzResearch.WordTrace tailWord_1981399 prefixEnd_1981399 678273370225332334000145 := by
  unfold tailWord_1981399
  simp only [CollatzResearch.WordTrace]
  refine ⟨72267558548737293853227251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48178372365824862568818167 72267558548737293853227251)
  ·
    refine ⟨108401337823105940779840877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72267558548737293853227251 108401337823105940779840877)
    ·
      refine ⟨40650501683664727792440329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108401337823105940779840877 40650501683664727792440329)
      ·
        refine ⟨30487876262748545844330247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40650501683664727792440329 30487876262748545844330247)
        ·
          refine ⟨45731814394122818766495371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30487876262748545844330247 45731814394122818766495371)
          ·
            refine ⟨68597721591184228149743057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45731814394122818766495371 68597721591184228149743057)
            ·
              refine ⟨51448291193388171112307293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68597721591184228149743057 51448291193388171112307293)
              ·
                refine ⟨19293109197520564167115235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51448291193388171112307293 19293109197520564167115235)
                ·
                  refine ⟨28939663796280846250672853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19293109197520564167115235 28939663796280846250672853)
                  ·
                    refine ⟨678273370225332334000145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28939663796280846250672853 678273370225332334000145)
                    ·
                      rfl

theorem cell22_1981399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_1981399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1981399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1981399 prefixEnd_1981399 := by exact prefixLift 1981399
  have htrace : WordTrace (prefixWord ++ tailWord_1981399) baseStart_1981399 baseEnd_1981399 := by
    simpa [prefixWord, tailWord_1981399, baseEnd_1981399] using wordTrace_append hprefix tailTrace_1981399
  have hstable : (prefixWord ++ tailWord_1981399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981399).length < 2 ^ (prefixWord ++ tailWord_1981399).sum := by decide
  have hdescent : baseEnd_1981399 < baseStart_1981399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981482 : List Nat := [3, 1, 4, 1, 3, 1, 3, 1, 1, 4]
def baseStart_1981482 : Nat := 118140960795 + 1981482 * 2 ^ 59
def prefixEnd_1981482 : Nat := 4983230072969 + 3 ^ 40 * 1981482 * 2
def baseEnd_1981482 : Nat := 678301782821547784174891

theorem tailTrace_1981482 : CollatzResearch.WordTrace tailWord_1981482 prefixEnd_1981482 678301782821547784174891 := by
  unfold tailWord_1981482
  simp only [CollatzResearch.WordTrace]
  refine ⟨18067646451859149757124675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48180390538291066018999133 18067646451859149757124675)
  ·
    refine ⟨27101469677788724635687013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18067646451859149757124675 27101469677788724635687013)
    ·
      refine ⟨5081525564585385869191315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27101469677788724635687013 5081525564585385869191315)
      ·
        refine ⟨7622288346878078803786973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5081525564585385869191315 7622288346878078803786973)
        ·
          refine ⟨2858358130079279551420115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7622288346878078803786973 2858358130079279551420115)
          ·
            refine ⟨4287537195118919327130173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2858358130079279551420115 4287537195118919327130173)
            ·
              refine ⟨1607826448169594747673815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4287537195118919327130173 1607826448169594747673815)
              ·
                refine ⟨2411739672254392121510723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1607826448169594747673815 2411739672254392121510723)
                ·
                  refine ⟨3617609508381588182266085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2411739672254392121510723 3617609508381588182266085)
                  ·
                    refine ⟨678301782821547784174891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3617609508381588182266085 678301782821547784174891)
                    ·
                      rfl

theorem cell22_1981482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_1981482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1981482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1981482 prefixEnd_1981482 := by exact prefixLift 1981482
  have htrace : WordTrace (prefixWord ++ tailWord_1981482) baseStart_1981482 baseEnd_1981482 := by
    simpa [prefixWord, tailWord_1981482, baseEnd_1981482] using wordTrace_append hprefix tailTrace_1981482
  have hstable : (prefixWord ++ tailWord_1981482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981482).length < 2 ^ (prefixWord ++ tailWord_1981482).sum := by decide
  have hdescent : baseEnd_1981482 < baseStart_1981482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981497 : List Nat := [1, 2, 1, 5, 2, 3, 2, 2, 4]
def baseStart_1981497 : Nat := 118140960795 + 1981497 * 2 ^ 59
def prefixEnd_1981497 : Nat := 4983230072969 + 3 ^ 40 * 1981497 * 2
def baseEnd_1981497 : Nat := 226102305876030915016615

theorem tailTrace_1981497 : CollatzResearch.WordTrace tailWord_1981497 prefixEnd_1981497 226102305876030915016615 := by
  unfold tailWord_1981497
  simp only [CollatzResearch.WordTrace]
  refine ⟨72271132902382256590294745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48180755268254837726863163 72271132902382256590294745)
  ·
    refine ⟨54203349676786692442721059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72271132902382256590294745 54203349676786692442721059)
    ·
      refine ⟨81305024515180038664081589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54203349676786692442721059 81305024515180038664081589)
      ·
        refine ⟨7622346048298128624757649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81305024515180038664081589 7622346048298128624757649)
        ·
          refine ⟨5716759536223596468568237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7622346048298128624757649 5716759536223596468568237)
          ·
            refine ⟨2143784826083848675713089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5716759536223596468568237 2143784826083848675713089)
            ·
              refine ⟨1607838619562886506784817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2143784826083848675713089 1607838619562886506784817)
              ·
                refine ⟨1205878964672164880088613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1607838619562886506784817 1205878964672164880088613)
                ·
                  refine ⟨226102305876030915016615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1205878964672164880088613 226102305876030915016615)
                  ·
                    rfl

theorem cell22_1981497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2, 4].length) (baseStart_1981497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1981497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1981497 prefixEnd_1981497 := by exact prefixLift 1981497
  have htrace : WordTrace (prefixWord ++ tailWord_1981497) baseStart_1981497 baseEnd_1981497 := by
    simpa [prefixWord, tailWord_1981497, baseEnd_1981497] using wordTrace_append hprefix tailTrace_1981497
  have hstable : (prefixWord ++ tailWord_1981497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981497).length < 2 ^ (prefixWord ++ tailWord_1981497).sum := by decide
  have hdescent : baseEnd_1981497 < baseStart_1981497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981536 : List Nat := [2, 1, 1, 3, 2, 2, 2, 2, 7]
def baseStart_1981536 : Nat := 118140960795 + 1981536 * 2 ^ 59
def prefixEnd_1981536 : Nat := 4983230072969 + 3 ^ 40 * 1981536 * 2
def baseEnd_1981536 : Nat := 226106756041703214441575

theorem tailTrace_1981536 : CollatzResearch.WordTrace tailWord_1981536 prefixEnd_1981536 226106756041703214441575 := by
  unfold tailWord_1981536
  simp only [CollatzResearch.WordTrace]
  refine ⟨36136277674620483125482231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48181703566160644167309641 36136277674620483125482231)
  ·
    refine ⟨54204416511930724688223347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36136277674620483125482231 54204416511930724688223347)
    ·
      refine ⟨81306624767896087032335021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54204416511930724688223347 81306624767896087032335021)
      ·
        refine ⟨30489984287961032637125633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81306624767896087032335021 30489984287961032637125633)
        ·
          refine ⟨22867488215970774477844225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30489984287961032637125633 22867488215970774477844225)
          ·
            refine ⟨17150616161978080858383169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22867488215970774477844225 17150616161978080858383169)
            ·
              refine ⟨12862962121483560643787377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17150616161978080858383169 12862962121483560643787377)
              ·
                refine ⟨9647221591112670482840533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12862962121483560643787377 9647221591112670482840533)
                ·
                  refine ⟨226106756041703214441575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9647221591112670482840533 226106756041703214441575)
                  ·
                    rfl

theorem cell22_1981536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 7].length) (baseStart_1981536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1981536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1981536 prefixEnd_1981536 := by exact prefixLift 1981536
  have htrace : WordTrace (prefixWord ++ tailWord_1981536) baseStart_1981536 baseEnd_1981536 := by
    simpa [prefixWord, tailWord_1981536, baseEnd_1981536] using wordTrace_append hprefix tailTrace_1981536
  have hstable : (prefixWord ++ tailWord_1981536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981536).length < 2 ^ (prefixWord ++ tailWord_1981536).sum := by decide
  have hdescent : baseEnd_1981536 < baseStart_1981536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981551 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 4, 5]
def baseStart_1981551 : Nat := 118140960795 + 1981551 * 2 ^ 59
def prefixEnd_1981551 : Nat := 4983230072969 + 3 ^ 40 * 1981551 * 2
def baseEnd_1981551 : Nat := 678325402931654604199679

theorem tailTrace_1981551 : CollatzResearch.WordTrace tailWord_1981551 prefixEnd_1981551 678325402931654604199679 := by
  unfold tailWord_1981551
  simp only [CollatzResearch.WordTrace]
  refine ⟨72273102444186623812760507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48182068296124415875173671 72273102444186623812760507)
  ·
    refine ⟨108409653666279935719140761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72273102444186623812760507 108409653666279935719140761)
    ·
      refine ⟨81307240249709951789355571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108409653666279935719140761 81307240249709951789355571)
      ·
        refine ⟨121960860374564927684033357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81307240249709951789355571 121960860374564927684033357)
        ·
          refine ⟨45735322640461847881512509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121960860374564927684033357 45735322640461847881512509)
          ·
            refine ⟨17150745990173192955567191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45735322640461847881512509 17150745990173192955567191)
            ·
              refine ⟨25726118985259789433350787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17150745990173192955567191 25726118985259789433350787)
              ·
                refine ⟨38589178477889684150026181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25726118985259789433350787 38589178477889684150026181)
                ·
                  refine ⟨7235470964604315778129909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38589178477889684150026181 7235470964604315778129909)
                  ·
                    refine ⟨678325402931654604199679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7235470964604315778129909 678325402931654604199679)
                    ·
                      rfl

theorem cell22_1981551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 5].length) (baseStart_1981551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1981551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1981551 prefixEnd_1981551 := by exact prefixLift 1981551
  have htrace : WordTrace (prefixWord ++ tailWord_1981551) baseStart_1981551 baseEnd_1981551 := by
    simpa [prefixWord, tailWord_1981551, baseEnd_1981551] using wordTrace_append hprefix tailTrace_1981551
  have hstable : (prefixWord ++ tailWord_1981551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981551).length < 2 ^ (prefixWord ++ tailWord_1981551).sum := by decide
  have hdescent : baseEnd_1981551 < baseStart_1981551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981634 : List Nat := [3, 5, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_1981634 : Nat := 118140960795 + 1981634 * 2 ^ 59
def prefixEnd_1981634 : Nat := 4983230072969 + 3 ^ 40 * 1981634 * 2
def baseEnd_1981634 : Nat := 678353815527870054374425

theorem tailTrace_1981634 : CollatzResearch.WordTrace tailWord_1981634 prefixEnd_1981634 678353815527870054374425 := by
  unfold tailWord_1981634
  simp only [CollatzResearch.WordTrace]
  refine ⟨18069032425721482247007989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48184086468590619325354637 18069032425721482247007989)
  ·
    refine ⟨1693971789911388960656999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18069032425721482247007989 1693971789911388960656999)
    ·
      refine ⟨2540957684867083440985499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1693971789911388960656999 2540957684867083440985499)
      ·
        refine ⟨3811436527300625161478249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2540957684867083440985499 3811436527300625161478249)
        ·
          refine ⟨2858577395475468871108687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3811436527300625161478249 2858577395475468871108687)
          ·
            refine ⟨4287866093213203306663031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2858577395475468871108687 4287866093213203306663031)
            ·
              refine ⟨6431799139819804959994547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4287866093213203306663031 6431799139819804959994547)
              ·
                refine ⟨9647698709729707439991821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6431799139819804959994547 9647698709729707439991821)
                ·
                  refine ⟨3617887016148640289996933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9647698709729707439991821 3617887016148640289996933)
                  ·
                    refine ⟨678353815527870054374425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3617887016148640289996933 678353815527870054374425)
                    ·
                      rfl

theorem cell22_1981634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_1981634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1981634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1981634 prefixEnd_1981634 := by exact prefixLift 1981634
  have htrace : WordTrace (prefixWord ++ tailWord_1981634) baseStart_1981634 baseEnd_1981634 := by
    simpa [prefixWord, tailWord_1981634, baseEnd_1981634] using wordTrace_append hprefix tailTrace_1981634
  have hstable : (prefixWord ++ tailWord_1981634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981634).length < 2 ^ (prefixWord ++ tailWord_1981634).sum := by decide
  have hdescent : baseEnd_1981634 < baseStart_1981634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981692 : List Nat := [2, 2, 2, 1, 5, 1, 1, 2, 3, 3]
def baseStart_1981692 : Nat := 118140960795 + 1981692 * 2 ^ 59
def prefixEnd_1981692 : Nat := 4983230072969 + 3 ^ 40 * 1981692 * 2
def baseEnd_1981692 : Nat := 678373670113177236424247

theorem tailTrace_1981692 : CollatzResearch.WordTrace tailWord_1981692 prefixEnd_1981692 678373670113177236424247 := by
  unfold tailWord_1981692
  simp only [CollatzResearch.WordTrace]
  refine ⟨36139122568337902446821665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48185496757783869929095553 36139122568337902446821665)
  ·
    refine ⟨27104341926253426835116249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36139122568337902446821665 27104341926253426835116249)
    ·
      refine ⟨20328256444690070126337187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27104341926253426835116249 20328256444690070126337187)
      ·
        refine ⟨30492384667035105189505781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20328256444690070126337187 30492384667035105189505781)
        ·
          refine ⟨2858661062534541111516167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30492384667035105189505781 2858661062534541111516167)
          ·
            refine ⟨4287991593801811667274251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2858661062534541111516167 4287991593801811667274251)
            ·
              refine ⟨6431987390702717500911377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4287991593801811667274251 6431987390702717500911377)
              ·
                refine ⟨4823990543027038125683533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6431987390702717500911377 4823990543027038125683533)
                ·
                  refine ⟨1808996453635139297131325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4823990543027038125683533 1808996453635139297131325)
                  ·
                    refine ⟨678373670113177236424247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1808996453635139297131325 678373670113177236424247)
                    ·
                      rfl

theorem cell22_1981692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_1981692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1981692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1981692 prefixEnd_1981692 := by exact prefixLift 1981692
  have htrace : WordTrace (prefixWord ++ tailWord_1981692) baseStart_1981692 baseEnd_1981692 := by
    simpa [prefixWord, tailWord_1981692, baseEnd_1981692] using wordTrace_append hprefix tailTrace_1981692
  have hstable : (prefixWord ++ tailWord_1981692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981692).length < 2 ^ (prefixWord ++ tailWord_1981692).sum := by decide
  have hdescent : baseEnd_1981692 < baseStart_1981692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981722 : List Nat := [3, 1, 1, 3, 3, 3, 1, 2, 5]
def baseStart_1981722 : Nat := 118140960795 + 1981722 * 2 ^ 59
def prefixEnd_1981722 : Nat := 4983230072969 + 3 ^ 40 * 1981722 * 2
def baseEnd_1981722 : Nat := 226127979908755719391385

theorem tailTrace_1981722 : CollatzResearch.WordTrace tailWord_1981722 prefixEnd_1981722 226127979908755719391385 := by
  unfold tailWord_1981722
  simp only [CollatzResearch.WordTrace]
  refine ⟨18069834831641780004308855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48186226217711413344823613 18069834831641780004308855)
  ·
    refine ⟨27104752247462670006463283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18069834831641780004308855 27104752247462670006463283)
    ·
      refine ⟨40657128371194005009694925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27104752247462670006463283 40657128371194005009694925)
      ·
        refine ⟨15246423139197751878635597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40657128371194005009694925 15246423139197751878635597)
        ·
          refine ⟨5717408677199156954488349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15246423139197751878635597 5717408677199156954488349)
          ·
            refine ⟨2144028253949683857933131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5717408677199156954488349 2144028253949683857933131)
            ·
              refine ⟨3216042380924525786899697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2144028253949683857933131 3216042380924525786899697)
              ·
                refine ⟨2412031785693394340174773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3216042380924525786899697 2412031785693394340174773)
                ·
                  refine ⟨226127979908755719391385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2412031785693394340174773 226127979908755719391385)
                  ·
                    rfl

theorem cell22_1981722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 5].length) (baseStart_1981722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1981722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1981722 prefixEnd_1981722 := by exact prefixLift 1981722
  have htrace : WordTrace (prefixWord ++ tailWord_1981722) baseStart_1981722 baseEnd_1981722 := by
    simpa [prefixWord, tailWord_1981722, baseEnd_1981722] using wordTrace_append hprefix tailTrace_1981722
  have hstable : (prefixWord ++ tailWord_1981722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981722).length < 2 ^ (prefixWord ++ tailWord_1981722).sum := by decide
  have hdescent : baseEnd_1981722 < baseStart_1981722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981726 : List Nat := [4, 3, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_1981726 : Nat := 118140960795 + 1981726 * 2 ^ 59
def prefixEnd_1981726 : Nat := 4983230072969 + 3 ^ 40 * 1981726 * 2
def baseEnd_1981726 : Nat := 678385309008012481074143

theorem tailTrace_1981726 : CollatzResearch.WordTrace tailWord_1981726 prefixEnd_1981726 678385309008012481074143 := by
  unfold tailWord_1981726
  simp only [CollatzResearch.WordTrace]
  refine ⟨9034935652319078587547629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48186323479035085800254021 9034935652319078587547629)
  ·
    refine ⟨3388100869619654470330361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9034935652319078587547629 3388100869619654470330361)
    ·
      refine ⟨2541075652214740852747771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3388100869619654470330361 2541075652214740852747771)
      ·
        refine ⟨3811613478322111279121657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2541075652214740852747771 3811613478322111279121657)
        ·
          refine ⟨2858710108741583459341243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3811613478322111279121657 2858710108741583459341243)
          ·
            refine ⟨4288065163112375189011865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2858710108741583459341243 4288065163112375189011865)
            ·
              refine ⟨3216048872334281391758899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4288065163112375189011865 3216048872334281391758899)
              ·
                refine ⟨4824073308501422087638349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3216048872334281391758899 4824073308501422087638349)
                ·
                  refine ⟨1809027490688033282864381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4824073308501422087638349 1809027490688033282864381)
                  ·
                    refine ⟨678385309008012481074143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1809027490688033282864381 678385309008012481074143)
                    ·
                      rfl

theorem cell22_1981726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_1981726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1981726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1981726 prefixEnd_1981726 := by exact prefixLift 1981726
  have htrace : WordTrace (prefixWord ++ tailWord_1981726) baseStart_1981726 baseEnd_1981726 := by
    simpa [prefixWord, tailWord_1981726, baseEnd_1981726] using wordTrace_append hprefix tailTrace_1981726
  have hstable : (prefixWord ++ tailWord_1981726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981726).length < 2 ^ (prefixWord ++ tailWord_1981726).sum := by decide
  have hdescent : baseEnd_1981726 < baseStart_1981726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981767 : List Nat := [1, 1, 4, 1, 2, 3, 3, 3, 4]
def baseStart_1981767 : Nat := 118140960795 + 1981767 * 2 ^ 59
def prefixEnd_1981767 : Nat := 4983230072969 + 3 ^ 40 * 1981767 * 2
def baseEnd_1981767 : Nat := 226133114715300680266339

theorem tailTrace_1981767 : CollatzResearch.WordTrace tailWord_1981767 prefixEnd_1981767 226133114715300680266339 := by
  unfold tailWord_1981767
  simp only [CollatzResearch.WordTrace]
  refine ⟨72280980611404092702623555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48187320407602728468415703 72280980611404092702623555)
  ·
    refine ⟨108421470917106139053935333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72280980611404092702623555 108421470917106139053935333)
    ·
      refine ⟨20329025796957401072612875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108421470917106139053935333 20329025796957401072612875)
      ·
        refine ⟨30493538695436101608919313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20329025796957401072612875 30493538695436101608919313)
        ·
          refine ⟨22870154021577076206689485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30493538695436101608919313 22870154021577076206689485)
          ·
            refine ⟨8576307758091403577508557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22870154021577076206689485 8576307758091403577508557)
            ·
              refine ⟨3216115409284276341565709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8576307758091403577508557 3216115409284276341565709)
              ·
                refine ⟨1206043278481603628087141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3216115409284276341565709 1206043278481603628087141)
                ·
                  refine ⟨226133114715300680266339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1206043278481603628087141 226133114715300680266339)
                  ·
                    rfl

theorem cell22_1981767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3, 4].length) (baseStart_1981767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1981767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1981767 prefixEnd_1981767 := by exact prefixLift 1981767
  have htrace : WordTrace (prefixWord ++ tailWord_1981767) baseStart_1981767 baseEnd_1981767 := by
    simpa [prefixWord, tailWord_1981767, baseEnd_1981767] using wordTrace_append hprefix tailTrace_1981767
  have hstable : (prefixWord ++ tailWord_1981767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981767).length < 2 ^ (prefixWord ++ tailWord_1981767).sum := by decide
  have hdescent : baseEnd_1981767 < baseStart_1981767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981795 : List Nat := [1, 1, 1, 5, 2, 3, 2, 7]
def baseStart_1981795 : Nat := 118140960795 + 1981795 * 2 ^ 59
def prefixEnd_1981795 : Nat := 4983230072969 + 3 ^ 40 * 1981795 * 2
def baseEnd_1981795 : Nat := 75378769902013255677659

theorem tailTrace_1981795 : CollatzResearch.WordTrace tailWord_1981795 prefixEnd_1981795 75378769902013255677659 := by
  unfold tailWord_1981795
  simp only [CollatzResearch.WordTrace]
  refine ⟨72282001855302653484642839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48188001236868435656428559 72282001855302653484642839)
  ·
    refine ⟨108423002782953980226964259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72282001855302653484642839 108423002782953980226964259)
    ·
      refine ⟨162634504174430970340446389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108423002782953980226964259 162634504174430970340446389)
      ·
        refine ⟨15246984766352903469416849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 162634504174430970340446389 15246984766352903469416849)
        ·
          refine ⟨11435238574764677602062637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15246984766352903469416849 11435238574764677602062637)
          ·
            refine ⟨4288214465536754100773489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11435238574764677602062637 4288214465536754100773489)
            ·
              refine ⟨3216160849152565575580117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4288214465536754100773489 3216160849152565575580117)
              ·
                refine ⟨75378769902013255677659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3216160849152565575580117 75378769902013255677659)
                ·
                  rfl

theorem cell22_1981795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 7].length) (baseStart_1981795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1981795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1981795 prefixEnd_1981795 := by exact prefixLift 1981795
  have htrace : WordTrace (prefixWord ++ tailWord_1981795) baseStart_1981795 baseEnd_1981795 := by
    simpa [prefixWord, tailWord_1981795, baseEnd_1981795] using wordTrace_append hprefix tailTrace_1981795
  have hstable : (prefixWord ++ tailWord_1981795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981795).length < 2 ^ (prefixWord ++ tailWord_1981795).sum := by decide
  have hdescent : baseEnd_1981795 < baseStart_1981795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981799 : List Nat := [1, 1, 5, 1, 4, 1, 1, 3, 2, 3]
def baseStart_1981799 : Nat := 118140960795 + 1981799 * 2 ^ 59
def prefixEnd_1981799 : Nat := 4983230072969 + 3 ^ 40 * 1981799 * 2
def baseEnd_1981799 : Nat := 678410298399864623998919

theorem tailTrace_1981799 : CollatzResearch.WordTrace tailWord_1981799 prefixEnd_1981799 678410298399864623998919 := by
  unfold tailWord_1981799
  simp only [CollatzResearch.WordTrace]
  refine ⟨72282147747288162167788451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48188098498192108111858967 72282147747288162167788451)
  ·
    refine ⟨108423221620932243251682677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72282147747288162167788451 108423221620932243251682677)
    ·
      refine ⟨10164677026962397804845251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108423221620932243251682677 10164677026962397804845251)
      ·
        refine ⟨15247015540443596707267877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10164677026962397804845251 15247015540443596707267877)
        ·
          refine ⟨2858815413833174382612727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15247015540443596707267877 2858815413833174382612727)
          ·
            refine ⟨4288223120749761573919091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2858815413833174382612727 4288223120749761573919091)
            ·
              refine ⟨6432334681124642360878637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4288223120749761573919091 6432334681124642360878637)
              ·
                refine ⟨2412125505421740885329489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6432334681124642360878637 2412125505421740885329489)
                ·
                  refine ⟨1809094129066305663997117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2412125505421740885329489 1809094129066305663997117)
                  ·
                    refine ⟨678410298399864623998919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1809094129066305663997117 678410298399864623998919)
                    ·
                      rfl

theorem cell22_1981799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_1981799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1981799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1981799 prefixEnd_1981799 := by exact prefixLift 1981799
  have htrace : WordTrace (prefixWord ++ tailWord_1981799) baseStart_1981799 baseEnd_1981799 := by
    simpa [prefixWord, tailWord_1981799, baseEnd_1981799] using wordTrace_append hprefix tailTrace_1981799
  have hstable : (prefixWord ++ tailWord_1981799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981799).length < 2 ^ (prefixWord ++ tailWord_1981799).sum := by decide
  have hdescent : baseEnd_1981799 < baseStart_1981799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981855 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 1, 7]
def baseStart_1981855 : Nat := 118140960795 + 1981855 * 2 ^ 59
def prefixEnd_1981855 : Nat := 4983230072969 + 3 ^ 40 * 1981855 * 2
def baseEnd_1981855 : Nat := 678429468344299144598747

theorem tailTrace_1981855 : CollatzResearch.WordTrace tailWord_1981855 prefixEnd_1981855 678429468344299144598747 := by
  unfold tailWord_1981855
  simp only [CollatzResearch.WordTrace]
  refine ⟨72284190235085283731827019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48189460156723522487884679 72284190235085283731827019)
  ·
    refine ⟨108426285352627925597740529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72284190235085283731827019 108426285352627925597740529)
    ·
      refine ⟨81319714014470944198305397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108426285352627925597740529 81319714014470944198305397)
      ·
        refine ⟨7623723188856651018591131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81319714014470944198305397 7623723188856651018591131)
        ·
          refine ⟨11435584783284976527886697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7623723188856651018591131 11435584783284976527886697)
          ·
            refine ⟨8576688587463732395915023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11435584783284976527886697 8576688587463732395915023)
            ·
              refine ⟨12865032881195598593872535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8576688587463732395915023 12865032881195598593872535)
              ·
                refine ⟨19297549321793397890808803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12865032881195598593872535 19297549321793397890808803)
                ·
                  refine ⟨28946323982690096836213205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19297549321793397890808803 28946323982690096836213205)
                  ·
                    refine ⟨678429468344299144598747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28946323982690096836213205 678429468344299144598747)
                    ·
                      rfl

theorem cell22_1981855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 7].length) (baseStart_1981855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1981855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1981855 prefixEnd_1981855 := by exact prefixLift 1981855
  have htrace : WordTrace (prefixWord ++ tailWord_1981855) baseStart_1981855 baseEnd_1981855 := by
    simpa [prefixWord, tailWord_1981855, baseEnd_1981855] using wordTrace_append hprefix tailTrace_1981855
  have hstable : (prefixWord ++ tailWord_1981855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981855).length < 2 ^ (prefixWord ++ tailWord_1981855).sum := by decide
  have hdescent : baseEnd_1981855 < baseStart_1981855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1981885 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 8]
def baseStart_1981885 : Nat := 118140960795 + 1981885 * 2 ^ 59
def prefixEnd_1981885 : Nat := 4983230072969 + 3 ^ 40 * 1981885 * 2
def baseEnd_1981885 : Nat := 226146579319129688782885

theorem tailTrace_1981885 : CollatzResearch.WordTrace tailWord_1981885 prefixEnd_1981885 226146579319129688782885 := by
  unfold tailWord_1981885
  simp only [CollatzResearch.WordTrace]
  refine ⟨72285284424976598855419109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48190189616651065903612739 72285284424976598855419109)
  ·
    refine ⟨13553490829683112285391083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72285284424976598855419109 13553490829683112285391083)
    ·
      refine ⟨20330236244524668428086625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13553490829683112285391083 20330236244524668428086625)
      ·
        refine ⟨15247677183393501321064969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20330236244524668428086625 15247677183393501321064969)
        ·
          refine ⟨11435757887545125990798727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15247677183393501321064969 11435757887545125990798727)
          ·
            refine ⟨17153636831317688986198091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11435757887545125990798727 17153636831317688986198091)
            ·
              refine ⟨25730455246976533479297137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17153636831317688986198091 25730455246976533479297137)
              ·
                refine ⟨19297841435232400109472853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25730455246976533479297137 19297841435232400109472853)
                ·
                  refine ⟨226146579319129688782885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19297841435232400109472853 226146579319129688782885)
                  ·
                    rfl

theorem cell22_1981885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_1981885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1981885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1981885 prefixEnd_1981885 := by exact prefixLift 1981885
  have htrace : WordTrace (prefixWord ++ tailWord_1981885) baseStart_1981885 baseEnd_1981885 := by
    simpa [prefixWord, tailWord_1981885, baseEnd_1981885] using wordTrace_append hprefix tailTrace_1981885
  have hstable : (prefixWord ++ tailWord_1981885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1981885).length < 2 ^ (prefixWord ++ tailWord_1981885).sum := by decide
  have hdescent : baseEnd_1981885 < baseStart_1981885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1981885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982009 : List Nat := [1, 2, 1, 5, 1, 3, 2, 2, 5]
def baseStart_1982009 : Nat := 118140960795 + 1982009 * 2 ^ 59
def prefixEnd_1982009 : Nat := 4983230072969 + 3 ^ 40 * 1982009 * 2
def baseEnd_1982009 : Nat := 226160728563831358749425

theorem tailTrace_1982009 : CollatzResearch.WordTrace tailWord_1982009 prefixEnd_1982009 226160728563831358749425 := by
  unfold tailWord_1982009
  simp only [CollatzResearch.WordTrace]
  refine ⟨72289807076527368032933081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48193204717684912021955387 72289807076527368032933081)
  ·
    refine ⟨54217355307395526024699811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72289807076527368032933081 54217355307395526024699811)
    ·
      refine ⟨81326032961093289037049717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54217355307395526024699811 81326032961093289037049717)
      ·
        refine ⟨7624315590102495847223411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81326032961093289037049717 7624315590102495847223411)
        ·
          refine ⟨11436473385153743770835117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7624315590102495847223411 11436473385153743770835117)
          ·
            refine ⟨4288677519432653914063169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11436473385153743770835117 4288677519432653914063169)
            ·
              refine ⟨3216508139574490435547377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4288677519432653914063169 3216508139574490435547377)
              ·
                refine ⟨2412381104680867826660533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3216508139574490435547377 2412381104680867826660533)
                ·
                  refine ⟨226160728563831358749425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2412381104680867826660533 226160728563831358749425)
                  ·
                    rfl

theorem cell22_1982009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 5].length) (baseStart_1982009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1982009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1982009 prefixEnd_1982009 := by exact prefixLift 1982009
  have htrace : WordTrace (prefixWord ++ tailWord_1982009) baseStart_1982009 baseEnd_1982009 := by
    simpa [prefixWord, tailWord_1982009, baseEnd_1982009] using wordTrace_append hprefix tailTrace_1982009
  have hstable : (prefixWord ++ tailWord_1982009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982009).length < 2 ^ (prefixWord ++ tailWord_1982009).sum := by decide
  have hdescent : baseEnd_1982009 < baseStart_1982009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982013 : List Nat := [1, 4, 1, 3, 3, 1, 1, 4, 1, 3]
def baseStart_1982013 : Nat := 118140960795 + 1982013 * 2 ^ 59
def prefixEnd_1982013 : Nat := 4983230072969 + 3 ^ 40 * 1982013 * 2
def baseEnd_1982013 : Nat := 678483554973239399148263

theorem tailTrace_1982013 : CollatzResearch.WordTrace tailWord_1982013 prefixEnd_1982013 678483554973239399148263 := by
  unfold tailWord_1982013
  simp only [CollatzResearch.WordTrace]
  refine ⟨72289952968512876716078693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48193301979008584477385795 72289952968512876716078693)
  ·
    refine ⟨13554366181596164384264755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72289952968512876716078693 13554366181596164384264755)
    ·
      refine ⟨20331549272394246576397133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13554366181596164384264755 20331549272394246576397133)
      ·
        refine ⟨7624330977147842466148925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20331549272394246576397133 7624330977147842466148925)
        ·
          refine ⟨2859124116430440924805847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7624330977147842466148925 2859124116430440924805847)
          ·
            refine ⟨4288686174645661387208771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2859124116430440924805847 4288686174645661387208771)
            ·
              refine ⟨6433029261968492080813157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4288686174645661387208771 6433029261968492080813157)
              ·
                refine ⟨1206192986619092265152467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6433029261968492080813157 1206192986619092265152467)
                ·
                  refine ⟨1809289479928638397728701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1206192986619092265152467 1809289479928638397728701)
                  ·
                    refine ⟨678483554973239399148263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1809289479928638397728701 678483554973239399148263)
                    ·
                      rfl

theorem cell22_1982013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_1982013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1982013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1982013 prefixEnd_1982013 := by exact prefixLift 1982013
  have htrace : WordTrace (prefixWord ++ tailWord_1982013) baseStart_1982013 baseEnd_1982013 := by
    simpa [prefixWord, tailWord_1982013, baseEnd_1982013] using wordTrace_append hprefix tailTrace_1982013
  have hstable : (prefixWord ++ tailWord_1982013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982013).length < 2 ^ (prefixWord ++ tailWord_1982013).sum := by decide
  have hdescent : baseEnd_1982013 < baseStart_1982013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982056 : List Nat := [2, 1, 4, 3, 1, 2, 1, 3, 1, 4]
def baseStart_1982056 : Nat := 118140960795 + 1982056 * 2 ^ 59
def prefixEnd_1982056 : Nat := 4983230072969 + 3 ^ 40 * 1982056 * 2
def baseEnd_1982056 : Nat := 678498274752001620323131

theorem tailTrace_1982056 : CollatzResearch.WordTrace tailWord_1982056 prefixEnd_1982056 678498274752001620323131 := by
  unfold tailWord_1982056
  simp only [CollatzResearch.WordTrace]
  refine ⟨36145760653678547529947011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48194347538238063373262681 36145760653678547529947011)
  ·
    refine ⟨54218640980517821294920517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36145760653678547529947011 54218640980517821294920517)
    ·
      refine ⟨10165995183847091492797597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54218640980517821294920517 10165995183847091492797597)
      ·
        refine ⟨3812248193942659309799099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10165995183847091492797597 3812248193942659309799099)
        ·
          refine ⟨5718372290913988964698649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3812248193942659309799099 5718372290913988964698649)
          ·
            refine ⟨4288779218185491723523987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5718372290913988964698649 4288779218185491723523987)
            ·
              refine ⟨6433168827278237585285981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4288779218185491723523987 6433168827278237585285981)
              ·
                refine ⟨2412438310229339094482243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6433168827278237585285981 2412438310229339094482243)
                ·
                  refine ⟨3618657465344008641723365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2412438310229339094482243 3618657465344008641723365)
                  ·
                    refine ⟨678498274752001620323131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3618657465344008641723365 678498274752001620323131)
                    ·
                      rfl

theorem cell22_1982056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_1982056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1982056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1982056 prefixEnd_1982056 := by exact prefixLift 1982056
  have htrace : WordTrace (prefixWord ++ tailWord_1982056) baseStart_1982056 baseEnd_1982056 := by
    simpa [prefixWord, tailWord_1982056, baseEnd_1982056] using wordTrace_append hprefix tailTrace_1982056
  have hstable : (prefixWord ++ tailWord_1982056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982056).length < 2 ^ (prefixWord ++ tailWord_1982056).sum := by decide
  have hdescent : baseEnd_1982056 < baseStart_1982056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982127 : List Nat := [1, 1, 2, 1, 2, 4, 1, 3, 7]
def baseStart_1982127 : Nat := 118140960795 + 1982127 * 2 ^ 59
def prefixEnd_1982127 : Nat := 4983230072969 + 3 ^ 40 * 1982127 * 2
def baseEnd_1982127 : Nat := 226174193167660367265971

theorem tailTrace_1982127 : CollatzResearch.WordTrace tailWord_1982127 prefixEnd_1982127 226174193167660367265971 := by
  unfold tailWord_1982127
  simp only [CollatzResearch.WordTrace]
  refine ⟨72294110890099874185728635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48196073926733249457152423 72294110890099874185728635)
  ·
    refine ⟨108441166335149811278592953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72294110890099874185728635 108441166335149811278592953)
    ·
      refine ⟨81330874751362358458944715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108441166335149811278592953 81330874751362358458944715)
      ·
        refine ⟨121996312127043537688417073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81330874751362358458944715 121996312127043537688417073)
        ·
          refine ⟨91497234095282653266312805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121996312127043537688417073 91497234095282653266312805)
          ·
            refine ⟨17155731392865497487433651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91497234095282653266312805 17155731392865497487433651)
            ·
              refine ⟨25733597089298246231150477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17155731392865497487433651 25733597089298246231150477)
              ·
                refine ⟨9650098908486842336681429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25733597089298246231150477 9650098908486842336681429)
                ·
                  refine ⟨226174193167660367265971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9650098908486842336681429 226174193167660367265971)
                  ·
                    rfl

theorem cell22_1982127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 7].length) (baseStart_1982127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1982127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1982127 prefixEnd_1982127 := by exact prefixLift 1982127
  have htrace : WordTrace (prefixWord ++ tailWord_1982127) baseStart_1982127 baseEnd_1982127 := by
    simpa [prefixWord, tailWord_1982127, baseEnd_1982127] using wordTrace_append hprefix tailTrace_1982127
  have hstable : (prefixWord ++ tailWord_1982127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982127).length < 2 ^ (prefixWord ++ tailWord_1982127).sum := by decide
  have hdescent : baseEnd_1982127 < baseStart_1982127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982144 : List Nat := [2, 1, 1, 2, 4, 1, 3, 3, 5]
def baseStart_1982144 : Nat := 118140960795 + 1982144 * 2 ^ 59
def prefixEnd_1982144 : Nat := 4983230072969 + 3 ^ 40 * 1982144 * 2
def baseEnd_1982144 : Nat := 226176132983466241374287

theorem tailTrace_1982144 : CollatzResearch.WordTrace tailWord_1982144 prefixEnd_1982144 226176132983466241374287 := by
  unfold tailWord_1982144
  simp only [CollatzResearch.WordTrace]
  refine ⟨36147365465519143044548743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48196487287358857392731657 36147365465519143044548743)
  ·
    refine ⟨54221048198278714566823115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36147365465519143044548743 54221048198278714566823115)
    ·
      refine ⟨81331572297418071850234673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54221048198278714566823115 81331572297418071850234673)
      ·
        refine ⟨60998679223063553887676005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81331572297418071850234673 60998679223063553887676005)
        ·
          refine ⟨11437252354324416353939251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60998679223063553887676005 11437252354324416353939251)
          ·
            refine ⟨17155878531486624530908877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11437252354324416353939251 17155878531486624530908877)
            ·
              refine ⟨6433454449307484199090829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17155878531486624530908877 6433454449307484199090829)
              ·
                refine ⟨2412545418490306574659061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6433454449307484199090829 2412545418490306574659061)
                ·
                  refine ⟨226176132983466241374287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2412545418490306574659061 226176132983466241374287)
                  ·
                    rfl

theorem cell22_1982144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 5].length) (baseStart_1982144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1982144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1982144 prefixEnd_1982144 := by exact prefixLift 1982144
  have htrace : WordTrace (prefixWord ++ tailWord_1982144) baseStart_1982144 baseEnd_1982144 := by
    simpa [prefixWord, tailWord_1982144, baseEnd_1982144] using wordTrace_append hprefix tailTrace_1982144
  have hstable : (prefixWord ++ tailWord_1982144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982144).length < 2 ^ (prefixWord ++ tailWord_1982144).sum := by decide
  have hdescent : baseEnd_1982144 < baseStart_1982144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982234 : List Nat := [3, 1, 1, 3, 2, 3, 9]
def baseStart_1982234 : Nat := 118140960795 + 1982234 * 2 ^ 59
def prefixEnd_1982234 : Nat := 4983230072969 + 3 ^ 40 * 1982234 * 2
def baseEnd_1982234 : Nat := 25131822510728462569355

theorem tailTrace_1982234 : CollatzResearch.WordTrace tailWord_1982234 prefixEnd_1982234 25131822510728462569355 := by
  unfold tailWord_1982234
  simp only [CollatzResearch.WordTrace]
  refine ⟨18074503375178057864968439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48198675667141487639915837 18074503375178057864968439)
  ·
    refine ⟨27111755062767086797452659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18074503375178057864968439 27111755062767086797452659)
    ·
      refine ⟨40667632594150630196178989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27111755062767086797452659 40667632594150630196178989)
      ·
        refine ⟨15250362222806486323567121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40667632594150630196178989 15250362222806486323567121)
        ·
          refine ⟨11437771667104864742675341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15250362222806486323567121 11437771667104864742675341)
          ·
            refine ⟨4289164375164324278503253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11437771667104864742675341 4289164375164324278503253)
            ·
              refine ⟨25131822510728462569355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4289164375164324278503253 25131822510728462569355)
              ·
                rfl

theorem cell22_1982234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 9].length) (baseStart_1982234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1982234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1982234 prefixEnd_1982234 := by exact prefixLift 1982234
  have htrace : WordTrace (prefixWord ++ tailWord_1982234) baseStart_1982234 baseEnd_1982234 := by
    simpa [prefixWord, tailWord_1982234, baseEnd_1982234] using wordTrace_append hprefix tailTrace_1982234
  have hstable : (prefixWord ++ tailWord_1982234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982234).length < 2 ^ (prefixWord ++ tailWord_1982234).sum := by decide
  have hdescent : baseEnd_1982234 < baseStart_1982234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982279 : List Nat := [1, 1, 4, 1, 2, 1, 3, 2, 7]
def baseStart_1982279 : Nat := 118140960795 + 1982279 * 2 ^ 59
def prefixEnd_1982279 : Nat := 4983230072969 + 3 ^ 40 * 1982279 * 2
def baseEnd_1982279 : Nat := 226191537403101123999149

theorem tailTrace_1982279 : CollatzResearch.WordTrace tailWord_1982279 prefixEnd_1982279 226191537403101123999149 := by
  unfold tailWord_1982279
  simp only [CollatzResearch.WordTrace]
  refine ⟨72299654785549204145261891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48199769857032802763507927 72299654785549204145261891)
  ·
    refine ⟨108449482178323806217892837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72299654785549204145261891 108449482178323806217892837)
    ·
      refine ⟨20334277908435713665854907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108449482178323806217892837 20334277908435713665854907)
      ·
        refine ⟨30501416862653570498782361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20334277908435713665854907 30501416862653570498782361)
        ·
          refine ⟨22876062646990177874086771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30501416862653570498782361 22876062646990177874086771)
          ·
            refine ⟨34314093970485266811130157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22876062646990177874086771 34314093970485266811130157)
            ·
              refine ⟨12867785238931975054173809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34314093970485266811130157 12867785238931975054173809)
              ·
                refine ⟨9650838929198981290630357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12867785238931975054173809 9650838929198981290630357)
                ·
                  refine ⟨226191537403101123999149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9650838929198981290630357 226191537403101123999149)
                  ·
                    rfl

theorem cell22_1982279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 7].length) (baseStart_1982279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1982279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1982279 prefixEnd_1982279 := by exact prefixLift 1982279
  have htrace : WordTrace (prefixWord ++ tailWord_1982279) baseStart_1982279 baseEnd_1982279 := by
    simpa [prefixWord, tailWord_1982279, baseEnd_1982279] using wordTrace_append hprefix tailTrace_1982279
  have hstable : (prefixWord ++ tailWord_1982279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982279).length < 2 ^ (prefixWord ++ tailWord_1982279).sum := by decide
  have hdescent : baseEnd_1982279 < baseStart_1982279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982309 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 2, 8]
def baseStart_1982309 : Nat := 118140960795 + 1982309 * 2 ^ 59
def prefixEnd_1982309 : Nat := 4983230072969 + 3 ^ 40 * 1982309 * 2
def baseEnd_1982309 : Nat := 678584881822393293747355

theorem tailTrace_1982309 : CollatzResearch.WordTrace tailWord_1982309 prefixEnd_1982309 678584881822393293747355 := by
  unfold tailWord_1982309
  simp only [CollatzResearch.WordTrace]
  refine ⟨72300748975440519268853981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48200499316960346179235987 72300748975440519268853981)
  ·
    refine ⟨27112780865790194725820243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72300748975440519268853981 27112780865790194725820243)
    ·
      refine ⟨40669171298685292088730365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27112780865790194725820243 40669171298685292088730365)
      ·
        refine ⟨15250939237006984533273887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40669171298685292088730365 15250939237006984533273887)
        ·
          refine ⟨22876408855510476799910831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15250939237006984533273887 22876408855510476799910831)
          ·
            refine ⟨34314613283265715199866247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22876408855510476799910831 34314613283265715199866247)
            ·
              refine ⟨51471919924898572799799371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34314613283265715199866247 51471919924898572799799371)
              ·
                refine ⟨77207879887347859199699057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51471919924898572799799371 77207879887347859199699057)
                ·
                  refine ⟨57905909915510894399774293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 77207879887347859199699057 57905909915510894399774293)
                  ·
                    refine ⟨678584881822393293747355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57905909915510894399774293 678584881822393293747355)
                    ·
                      rfl

theorem cell22_1982309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_1982309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1982309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1982309 prefixEnd_1982309 := by exact prefixLift 1982309
  have htrace : WordTrace (prefixWord ++ tailWord_1982309) baseStart_1982309 baseEnd_1982309 := by
    simpa [prefixWord, tailWord_1982309, baseEnd_1982309] using wordTrace_append hprefix tailTrace_1982309
  have hstable : (prefixWord ++ tailWord_1982309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982309).length < 2 ^ (prefixWord ++ tailWord_1982309).sum := by decide
  have hdescent : baseEnd_1982309 < baseStart_1982309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982478 : List Nat := [4, 1, 1, 2, 2, 1, 2, 2, 3, 4]
def baseStart_1982478 : Nat := 118140960795 + 1982478 * 2 ^ 59
def prefixEnd_1982478 : Nat := 4983230072969 + 3 ^ 40 * 1982478 * 2
def baseEnd_1982478 : Nat := 678642733976133186271837

theorem tailTrace_1982478 : CollatzResearch.WordTrace tailWord_1982478 prefixEnd_1982478 678642733976133186271837 := by
  unfold tailWord_1982478
  simp only [CollatzResearch.WordTrace]
  refine ⟨9038364113978532641469511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48204608607885507421170725 9038364113978532641469511)
  ·
    refine ⟨13557546170967798962204267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9038364113978532641469511 13557546170967798962204267)
    ·
      refine ⟨20336319256451698443306401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13557546170967798962204267 20336319256451698443306401)
      ·
        refine ⟨15252239442338773832479801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20336319256451698443306401 15252239442338773832479801)
        ·
          refine ⟨11439179581754080374359851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15252239442338773832479801 11439179581754080374359851)
          ·
            refine ⟨17158769372631120561539777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11439179581754080374359851 17158769372631120561539777)
            ·
              refine ⟨12869077029473340421154833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17158769372631120561539777 12869077029473340421154833)
              ·
                refine ⟨9651807772105005315866125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12869077029473340421154833 9651807772105005315866125)
                ·
                  refine ⟨3619427914539376993449797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9651807772105005315866125 3619427914539376993449797)
                  ·
                    refine ⟨678642733976133186271837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3619427914539376993449797 678642733976133186271837)
                    ·
                      rfl

theorem cell22_1982478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_1982478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1982478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1982478 prefixEnd_1982478 := by exact prefixLift 1982478
  have htrace : WordTrace (prefixWord ++ tailWord_1982478) baseStart_1982478 baseEnd_1982478 := by
    simpa [prefixWord, tailWord_1982478, baseEnd_1982478] using wordTrace_append hprefix tailTrace_1982478
  have hstable : (prefixWord ++ tailWord_1982478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982478).length < 2 ^ (prefixWord ++ tailWord_1982478).sum := by decide
  have hdescent : baseEnd_1982478 < baseStart_1982478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982508 : List Nat := [2, 2, 1, 1, 1, 2, 2, 4, 4, 3]
def baseStart_1982508 : Nat := 118140960795 + 1982508 * 2 ^ 59
def prefixEnd_1982508 : Nat := 4983230072969 + 3 ^ 40 * 1982508 * 2
def baseEnd_1982508 : Nat := 678653003589223108021745

theorem tailTrace_1982508 : CollatzResearch.WordTrace tailWord_1982508 prefixEnd_1982508 678653003589223108021745 := by
  unfold tailWord_1982508
  simp only [CollatzResearch.WordTrace]
  refine ⟨36154003550859788127674089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48205338067813050836898785 36154003550859788127674089)
  ·
    refine ⟨27115502663144841095755567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36154003550859788127674089 27115502663144841095755567)
    ·
      refine ⟨40673253994717261643633351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27115502663144841095755567 40673253994717261643633351)
      ·
        refine ⟨61009880992075892465450027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40673253994717261643633351 61009880992075892465450027)
        ·
          refine ⟨91514821488113838698175041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61009880992075892465450027 91514821488113838698175041)
          ·
            refine ⟨68636116116085379023631281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91514821488113838698175041 68636116116085379023631281)
            ·
              refine ⟨51477087087064034267723461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68636116116085379023631281 51477087087064034267723461)
              ·
                refine ⟨9651953828824506425198149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51477087087064034267723461 9651953828824506425198149)
                ·
                  refine ⟨1809741342904594954724653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9651953828824506425198149 1809741342904594954724653)
                  ·
                    refine ⟨678653003589223108021745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1809741342904594954724653 678653003589223108021745)
                    ·
                      rfl

theorem cell22_1982508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 3].length) (baseStart_1982508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1982508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1982508 prefixEnd_1982508 := by exact prefixLift 1982508
  have htrace : WordTrace (prefixWord ++ tailWord_1982508) baseStart_1982508 baseEnd_1982508 := by
    simpa [prefixWord, tailWord_1982508, baseEnd_1982508] using wordTrace_append hprefix tailTrace_1982508
  have hstable : (prefixWord ++ tailWord_1982508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982508).length < 2 ^ (prefixWord ++ tailWord_1982508).sum := by decide
  have hdescent : baseEnd_1982508 < baseStart_1982508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982521 : List Nat := [1, 2, 1, 5, 13]
def baseStart_1982521 : Nat := 118140960795 + 1982521 * 2 ^ 59
def prefixEnd_1982521 : Nat := 4983230072969 + 3 ^ 40 * 1982521 * 2
def baseEnd_1982521 : Nat := 2792829027797923487435

theorem tailTrace_1982521 : CollatzResearch.WordTrace tailWord_1982521 prefixEnd_1982521 2792829027797923487435 := by
  unfold tailWord_1982521
  simp only [CollatzResearch.WordTrace]
  refine ⟨72308481250672479475571417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48205654167114986317047611 72308481250672479475571417)
  ·
    refine ⟨54231360938004359606678563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72308481250672479475571417 54231360938004359606678563)
    ·
      refine ⟨81347041407006539410017845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54231360938004359606678563 81347041407006539410017845)
      ·
        refine ⟨7626285131906863069689173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81347041407006539410017845 7626285131906863069689173)
        ·
          refine ⟨2792829027797923487435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 7626285131906863069689173 2792829027797923487435)
          ·
            rfl

theorem cell22_1982521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 13].length) (baseStart_1982521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1982521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1982521 prefixEnd_1982521 := by exact prefixLift 1982521
  have htrace : WordTrace (prefixWord ++ tailWord_1982521) baseStart_1982521 baseEnd_1982521 := by
    simpa [prefixWord, tailWord_1982521, baseEnd_1982521] using wordTrace_append hprefix tailTrace_1982521
  have hstable : (prefixWord ++ tailWord_1982521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982521).length < 2 ^ (prefixWord ++ tailWord_1982521).sum := by decide
  have hdescent : baseEnd_1982521 < baseStart_1982521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982557 : List Nat := [1, 4, 4, 1, 1, 1, 3, 1, 2, 4]
def baseStart_1982557 : Nat := 118140960795 + 1982557 * 2 ^ 59
def prefixEnd_1982557 : Nat := 4983230072969 + 3 ^ 40 * 1982557 * 2
def baseEnd_1982557 : Nat := 678669777290603313546595

theorem tailTrace_1982557 : CollatzResearch.WordTrace tailWord_1982557 prefixEnd_1982557 678669777290603313546595 := by
  unfold tailWord_1982557
  simp only [CollatzResearch.WordTrace]
  refine ⟨72309794278542057623881925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48206529519028038415921283 72309794278542057623881925)
  ·
    refine ⟨13558086427226635804477861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72309794278542057623881925 13558086427226635804477861)
    ·
      refine ⟨2542141205104994213339599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13558086427226635804477861 2542141205104994213339599)
      ·
        refine ⟨3813211807657491320009399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2542141205104994213339599 3813211807657491320009399)
        ·
          refine ⟨5719817711486236980014099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3813211807657491320009399 5719817711486236980014099)
          ·
            refine ⟨8579726567229355470021149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5719817711486236980014099 8579726567229355470021149)
            ·
              refine ⟨3217397462711008301257931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8579726567229355470021149 3217397462711008301257931)
              ·
                refine ⟨4826096194066512451886897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3217397462711008301257931 4826096194066512451886897)
                ·
                  refine ⟨3619572145549884338915173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4826096194066512451886897 3619572145549884338915173)
                  ·
                    refine ⟨678669777290603313546595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3619572145549884338915173 678669777290603313546595)
                    ·
                      rfl

theorem cell22_1982557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_1982557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1982557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1982557 prefixEnd_1982557 := by exact prefixLift 1982557
  have htrace : WordTrace (prefixWord ++ tailWord_1982557) baseStart_1982557 baseEnd_1982557 := by
    simpa [prefixWord, tailWord_1982557, baseEnd_1982557] using wordTrace_append hprefix tailTrace_1982557
  have hstable : (prefixWord ++ tailWord_1982557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982557).length < 2 ^ (prefixWord ++ tailWord_1982557).sum := by decide
  have hdescent : baseEnd_1982557 < baseStart_1982557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982583 : List Nat := [1, 1, 3, 1, 1, 6, 1, 1, 7]
def baseStart_1982583 : Nat := 118140960795 + 1982583 * 2 ^ 59
def prefixEnd_1982583 : Nat := 4983230072969 + 3 ^ 40 * 1982583 * 2
def baseEnd_1982583 : Nat := 226226225873982637465505

theorem tailTrace_1982583 : CollatzResearch.WordTrace tailWord_1982583 prefixEnd_1982583 226226225873982637465505 := by
  unfold tailWord_1982583
  simp only [CollatzResearch.WordTrace]
  refine ⟨72310742576447864064328403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48207161717631909376218935 72310742576447864064328403)
  ·
    refine ⟨108466113864671796096492605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72310742576447864064328403 108466113864671796096492605)
    ·
      refine ⟨40674792699251923536184727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108466113864671796096492605 40674792699251923536184727)
      ·
        refine ⟨61012189048877885304277091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40674792699251923536184727 61012189048877885304277091)
        ·
          refine ⟨91518283573316827956415637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61012189048877885304277091 91518283573316827956415637)
          ·
            refine ⟨4289919542499226310456983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91518283573316827956415637 4289919542499226310456983)
            ·
              refine ⟨6434879313748839465685475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4289919542499226310456983 6434879313748839465685475)
              ·
                refine ⟨9652318970623259198528213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6434879313748839465685475 9652318970623259198528213)
                ·
                  refine ⟨226226225873982637465505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9652318970623259198528213 226226225873982637465505)
                  ·
                    rfl

theorem cell22_1982583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 7].length) (baseStart_1982583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1982583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1982583 prefixEnd_1982583 := by exact prefixLift 1982583
  have htrace : WordTrace (prefixWord ++ tailWord_1982583) baseStart_1982583 baseEnd_1982583 := by
    simpa [prefixWord, tailWord_1982583, baseEnd_1982583] using wordTrace_append hprefix tailTrace_1982583
  have hstable : (prefixWord ++ tailWord_1982583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982583).length < 2 ^ (prefixWord ++ tailWord_1982583).sum := by decide
  have hdescent : baseEnd_1982583 < baseStart_1982583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982638 : List Nat := [4, 1, 4, 2, 2, 1, 1, 1, 3, 3]
def baseStart_1982638 : Nat := 118140960795 + 1982638 * 2 ^ 59
def prefixEnd_1982638 : Nat := 4983230072969 + 3 ^ 40 * 1982638 * 2
def baseEnd_1982638 : Nat := 678697505245946102271347

theorem tailTrace_1982638 : CollatzResearch.WordTrace tailWord_1982638 prefixEnd_1982638 678697505245946102271347 := by
  unfold tailWord_1982638
  simp only [CollatzResearch.WordTrace]
  refine ⟨9039093573906076057197571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48208499060832405638387045 9039093573906076057197571)
  ·
    refine ⟨13558640360859114085796357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9039093573906076057197571 13558640360859114085796357)
    ·
      refine ⟨2542245067661083891086817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13558640360859114085796357 2542245067661083891086817)
      ·
        refine ⟨1906683800745812918315113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2542245067661083891086817 1906683800745812918315113)
        ·
          refine ⟨1430012850559359688736335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1906683800745812918315113 1430012850559359688736335)
          ·
            refine ⟨2145019275839039533104503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1430012850559359688736335 2145019275839039533104503)
            ·
              refine ⟨3217528913758559299656755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2145019275839039533104503 3217528913758559299656755)
              ·
                refine ⟨4826293370637838949485133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3217528913758559299656755 4826293370637838949485133)
                ·
                  refine ⟨1809860013989189606056925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4826293370637838949485133 1809860013989189606056925)
                  ·
                    refine ⟨678697505245946102271347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1809860013989189606056925 678697505245946102271347)
                    ·
                      rfl

theorem cell22_1982638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_1982638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1982638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1982638 prefixEnd_1982638 := by exact prefixLift 1982638
  have htrace : WordTrace (prefixWord ++ tailWord_1982638) baseStart_1982638 baseEnd_1982638 := by
    simpa [prefixWord, tailWord_1982638, baseEnd_1982638] using wordTrace_append hprefix tailTrace_1982638
  have hstable : (prefixWord ++ tailWord_1982638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982638).length < 2 ^ (prefixWord ++ tailWord_1982638).sum := by decide
  have hdescent : baseEnd_1982638 < baseStart_1982638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982673 : List Nat := [1, 2, 2, 1, 2, 2, 4, 8]
def baseStart_1982673 : Nat := 118140960795 + 1982673 * 2 ^ 59
def prefixEnd_1982673 : Nat := 4983230072969 + 3 ^ 40 * 1982673 * 2
def baseEnd_1982673 : Nat := 75412165162357519738471

theorem tailTrace_1982673 : CollatzResearch.WordTrace tailWord_1982673 prefixEnd_1982673 75412165162357519738471 := by
  unfold tailWord_1982673
  simp only [CollatzResearch.WordTrace]
  refine ⟨72314025146121809435104673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48209350097414539623403115 72314025146121809435104673)
  ·
    refine ⟨54235518859591357076328505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72314025146121809435104673 54235518859591357076328505)
    ·
      refine ⟨40676639144693517807246379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54235518859591357076328505 40676639144693517807246379)
      ·
        refine ⟨61014958717040276710869569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40676639144693517807246379 61014958717040276710869569)
        ·
          refine ⟨45761219037780207533152177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61014958717040276710869569 45761219037780207533152177)
          ·
            refine ⟨34320914278335155649864133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45761219037780207533152177 34320914278335155649864133)
            ·
              refine ⟨6435171427187841684349525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34320914278335155649864133 6435171427187841684349525)
              ·
                refine ⟨75412165162357519738471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6435171427187841684349525 75412165162357519738471)
                ·
                  rfl

theorem cell22_1982673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 8].length) (baseStart_1982673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1982673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1982673 prefixEnd_1982673 := by exact prefixLift 1982673
  have htrace : WordTrace (prefixWord ++ tailWord_1982673) baseStart_1982673 baseEnd_1982673 := by
    simpa [prefixWord, tailWord_1982673, baseEnd_1982673] using wordTrace_append hprefix tailTrace_1982673
  have hstable : (prefixWord ++ tailWord_1982673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982673).length < 2 ^ (prefixWord ++ tailWord_1982673).sum := by decide
  have hdescent : baseEnd_1982673 < baseStart_1982673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982677 : List Nat := [1, 3, 2, 4, 2, 1, 1, 2, 1, 5]
def baseStart_1982677 : Nat := 118140960795 + 1982677 * 2 ^ 59
def prefixEnd_1982677 : Nat := 4983230072969 + 3 ^ 40 * 1982677 * 2
def baseEnd_1982677 : Nat := 678710855742963000546227

theorem tailTrace_1982677 : CollatzResearch.WordTrace tailWord_1982677 prefixEnd_1982677 678710855742963000546227 := by
  unfold tailWord_1982677
  simp only [CollatzResearch.WordTrace]
  refine ⟨72314171038107318118250285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48209447358738212078833523 72314171038107318118250285)
  ·
    refine ⟨27117814139290244294343857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72314171038107318118250285 27117814139290244294343857)
    ·
      refine ⟨20338360604467683220757893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27117814139290244294343857 20338360604467683220757893)
      ·
        refine ⟨3813442613337690603892105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20338360604467683220757893 3813442613337690603892105)
        ·
          refine ⟨2860081960003267952919079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3813442613337690603892105 2860081960003267952919079)
          ·
            refine ⟨4290122940004901929378619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2860081960003267952919079 4290122940004901929378619)
            ·
              refine ⟨6435184410007352894067929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4290122940004901929378619 6435184410007352894067929)
              ·
                refine ⟨4826388307505514670550947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6435184410007352894067929 4826388307505514670550947)
                ·
                  refine ⟨7239582461258272005826421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4826388307505514670550947 7239582461258272005826421)
                  ·
                    refine ⟨678710855742963000546227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7239582461258272005826421 678710855742963000546227)
                    ·
                      rfl

theorem cell22_1982677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_1982677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1982677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1982677 prefixEnd_1982677 := by exact prefixLift 1982677
  have htrace : WordTrace (prefixWord ++ tailWord_1982677) baseStart_1982677 baseEnd_1982677 := by
    simpa [prefixWord, tailWord_1982677, baseEnd_1982677] using wordTrace_append hprefix tailTrace_1982677
  have hstable : (prefixWord ++ tailWord_1982677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982677).length < 2 ^ (prefixWord ++ tailWord_1982677).sum := by decide
  have hdescent : baseEnd_1982677 < baseStart_1982677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982752 : List Nat := [2, 1, 1, 5, 2, 1, 3, 2, 5]
def baseStart_1982752 : Nat := 118140960795 + 1982752 * 2 ^ 59
def prefixEnd_1982752 : Nat := 4983230072969 + 3 ^ 40 * 1982752 * 2
def baseEnd_1982752 : Nat := 226245509925229268306999

theorem tailTrace_1982752 : CollatzResearch.WordTrace tailWord_1982752 prefixEnd_1982752 226245509925229268306999 := by
  unfold tailWord_1982752
  simp only [CollatzResearch.WordTrace]
  refine ⟨36158453256417802963615255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48211271008557070618153673 36158453256417802963615255)
  ·
    refine ⟨54237679884626704445422883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36158453256417802963615255 54237679884626704445422883)
    ·
      refine ⟨81356519826940056668134325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54237679884626704445422883 81356519826940056668134325)
      ·
        refine ⟨7627173733775630312637593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81356519826940056668134325 7627173733775630312637593)
        ·
          refine ⟨5720380300331722734478195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7627173733775630312637593 5720380300331722734478195)
          ·
            refine ⟨8580570450497584101717293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5720380300331722734478195 8580570450497584101717293)
            ·
              refine ⟨3217713918936594038143985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8580570450497584101717293 3217713918936594038143985)
              ·
                refine ⟨2413285439202445528607989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3217713918936594038143985 2413285439202445528607989)
                ·
                  refine ⟨226245509925229268306999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2413285439202445528607989 226245509925229268306999)
                  ·
                    rfl

theorem cell22_1982752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 5].length) (baseStart_1982752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1982752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1982752 prefixEnd_1982752 := by exact prefixLift 1982752
  have htrace : WordTrace (prefixWord ++ tailWord_1982752) baseStart_1982752 baseEnd_1982752 := by
    simpa [prefixWord, tailWord_1982752, baseEnd_1982752] using wordTrace_append hprefix tailTrace_1982752
  have hstable : (prefixWord ++ tailWord_1982752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982752).length < 2 ^ (prefixWord ++ tailWord_1982752).sum := by decide
  have hdescent : baseEnd_1982752 < baseStart_1982752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982769 : List Nat := [1, 2, 2, 3, 4, 1, 3, 1, 5]
def baseStart_1982769 : Nat := 118140960795 + 1982769 * 2 ^ 59
def prefixEnd_1982769 : Nat := 4983230072969 + 3 ^ 40 * 1982769 * 2
def baseEnd_1982769 : Nat := 226247449741035142415315

theorem tailTrace_1982769 : CollatzResearch.WordTrace tailWord_1982769 prefixEnd_1982769 226247449741035142415315 := by
  unfold tailWord_1982769
  simp only [CollatzResearch.WordTrace]
  refine ⟨72317526553774017830599361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48211684369182678553732907 72317526553774017830599361)
  ·
    refine ⟨54238144915330513372949521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72317526553774017830599361 54238144915330513372949521)
    ·
      refine ⟨40678608686497885029712141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54238144915330513372949521 40678608686497885029712141)
      ·
        refine ⟨15254478257436706886142053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40678608686497885029712141 15254478257436706886142053)
        ·
          refine ⟨2860214673269382541151635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15254478257436706886142053 2860214673269382541151635)
          ·
            refine ⟨4290322009904073811727453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2860214673269382541151635 4290322009904073811727453)
            ·
              refine ⟨1608870753714027679397795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4290322009904073811727453 1608870753714027679397795)
              ·
                refine ⟨2413306130571041519096693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1608870753714027679397795 2413306130571041519096693)
                ·
                  refine ⟨226247449741035142415315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2413306130571041519096693 226247449741035142415315)
                  ·
                    rfl

theorem cell22_1982769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 5].length) (baseStart_1982769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1982769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1982769 prefixEnd_1982769 := by exact prefixLift 1982769
  have htrace : WordTrace (prefixWord ++ tailWord_1982769) baseStart_1982769 baseEnd_1982769 := by
    simpa [prefixWord, tailWord_1982769, baseEnd_1982769] using wordTrace_append hprefix tailTrace_1982769
  have hstable : (prefixWord ++ tailWord_1982769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982769).length < 2 ^ (prefixWord ++ tailWord_1982769).sum := by decide
  have hdescent : baseEnd_1982769 < baseStart_1982769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982780 : List Nat := [2, 2, 2, 2, 1, 2, 1, 4, 6]
def baseStart_1982780 : Nat := 118140960795 + 1982780 * 2 ^ 59
def prefixEnd_1982780 : Nat := 4983230072969 + 3 ^ 40 * 1982780 * 2
def baseEnd_1982780 : Nat := 226248704915968355073637

theorem tailTrace_1982780 : CollatzResearch.WordTrace tailWord_1982780 prefixEnd_1982780 226248704915968355073637 := by
  unfold tailWord_1982780
  simp only [CollatzResearch.WordTrace]
  refine ⟨36158963878367083354624897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48211951837822777806166529 36158963878367083354624897)
  ·
    refine ⟨27119222908775312515968673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36158963878367083354624897 27119222908775312515968673)
    ·
      refine ⟨20339417181581484386976505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27119222908775312515968673 20339417181581484386976505)
      ·
        refine ⟨15254562886186113290232379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20339417181581484386976505 15254562886186113290232379)
        ·
          refine ⟨22881844329279169935348569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15254562886186113290232379 22881844329279169935348569)
          ·
            refine ⟨17161383246959377451511427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22881844329279169935348569 17161383246959377451511427)
            ·
              refine ⟨25742074870439066177267141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17161383246959377451511427 25742074870439066177267141)
              ·
                refine ⟨4826639038207324908237589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25742074870439066177267141 4826639038207324908237589)
                ·
                  refine ⟨226248704915968355073637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4826639038207324908237589 226248704915968355073637)
                  ·
                    rfl

theorem cell22_1982780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 6].length) (baseStart_1982780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1982780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1982780 prefixEnd_1982780 := by exact prefixLift 1982780
  have htrace : WordTrace (prefixWord ++ tailWord_1982780) baseStart_1982780 baseEnd_1982780 := by
    simpa [prefixWord, tailWord_1982780, baseEnd_1982780] using wordTrace_append hprefix tailTrace_1982780
  have hstable : (prefixWord ++ tailWord_1982780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982780).length < 2 ^ (prefixWord ++ tailWord_1982780).sum := by decide
  have hdescent : baseEnd_1982780 < baseStart_1982780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982825 : List Nat := [1, 2, 1, 1, 1, 3, 6, 7]
def baseStart_1982825 : Nat := 118140960795 + 1982825 * 2 ^ 59
def prefixEnd_1982825 : Nat := 4983230072969 + 3 ^ 40 * 1982825 * 2
def baseEnd_1982825 : Nat := 75417946574171105316197

theorem tailTrace_1982825 : CollatzResearch.WordTrace tailWord_1982825 prefixEnd_1982825 75417946574171105316197 := by
  unfold tailWord_1982825
  simp only [CollatzResearch.WordTrace]
  refine ⟨72319569041571139394637929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48213046027714092929758619 72319569041571139394637929)
  ·
    refine ⟨54239676781178354545978447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72319569041571139394637929 54239676781178354545978447)
    ·
      refine ⟨81359515171767531818967671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54239676781178354545978447 81359515171767531818967671)
      ·
        refine ⟨122039272757651297728451507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81359515171767531818967671 122039272757651297728451507)
        ·
          refine ⟨183058909136476946592677261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122039272757651297728451507 183058909136476946592677261)
          ·
            refine ⟨68647090926178854972253973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183058909136476946592677261 68647090926178854972253973)
            ·
              refine ⟨3217832387164633826824405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68647090926178854972253973 3217832387164633826824405)
              ·
                refine ⟨75417946574171105316197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3217832387164633826824405 75417946574171105316197)
                ·
                  rfl

theorem cell22_1982825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 7].length) (baseStart_1982825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1982825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1982825 prefixEnd_1982825 := by exact prefixLift 1982825
  have htrace : WordTrace (prefixWord ++ tailWord_1982825) baseStart_1982825 baseEnd_1982825 := by
    simpa [prefixWord, tailWord_1982825, baseEnd_1982825] using wordTrace_append hprefix tailTrace_1982825
  have hstable : (prefixWord ++ tailWord_1982825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982825).length < 2 ^ (prefixWord ++ tailWord_1982825).sum := by decide
  have hdescent : baseEnd_1982825 < baseStart_1982825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982829 : List Nat := [1, 5, 1, 1, 1, 2, 3, 3, 2, 3]
def baseStart_1982829 : Nat := 118140960795 + 1982829 * 2 ^ 59
def prefixEnd_1982829 : Nat := 4983230072969 + 3 ^ 40 * 1982829 * 2
def baseEnd_1982829 : Nat := 678762888449285270745761

theorem tailTrace_1982829 : CollatzResearch.WordTrace tailWord_1982829 prefixEnd_1982829 678762888449285270745761 := by
  unfold tailWord_1982829
  simp only [CollatzResearch.WordTrace]
  refine ⟨72319714933556648077783541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48213143289037765385189027 72319714933556648077783541)
  ·
    refine ⟨6779973275020935757292207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72319714933556648077783541 6779973275020935757292207)
    ·
      refine ⟨10169959912531403635938311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6779973275020935757292207 10169959912531403635938311)
      ·
        refine ⟨15254939868797105453907467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10169959912531403635938311 15254939868797105453907467)
        ·
          refine ⟨22882409803195658180861201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15254939868797105453907467 22882409803195658180861201)
          ·
            refine ⟨17161807352396743635645901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22882409803195658180861201 17161807352396743635645901)
            ·
              refine ⟨6435677757148778863367213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17161807352396743635645901 6435677757148778863367213)
              ·
                refine ⟨2413379158930792073762705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6435677757148778863367213 2413379158930792073762705)
                ·
                  refine ⟨1810034369198094055322029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2413379158930792073762705 1810034369198094055322029)
                  ·
                    refine ⟨678762888449285270745761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1810034369198094055322029 678762888449285270745761)
                    ·
                      rfl

theorem cell22_1982829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_1982829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1982829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1982829 prefixEnd_1982829 := by exact prefixLift 1982829
  have htrace : WordTrace (prefixWord ++ tailWord_1982829) baseStart_1982829 baseEnd_1982829 := by
    simpa [prefixWord, tailWord_1982829, baseEnd_1982829] using wordTrace_append hprefix tailTrace_1982829
  have hstable : (prefixWord ++ tailWord_1982829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982829).length < 2 ^ (prefixWord ++ tailWord_1982829).sum := by decide
  have hdescent : baseEnd_1982829 < baseStart_1982829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982872 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 2, 6]
def baseStart_1982872 : Nat := 118140960795 + 1982872 * 2 ^ 59
def prefixEnd_1982872 : Nat := 4983230072969 + 3 ^ 40 * 1982872 * 2
def baseEnd_1982872 : Nat := 678777608228047491920629

theorem tailTrace_1982872 : CollatzResearch.WordTrace tailWord_1982872 prefixEnd_1982872 678777608228047491920629 := by
  unfold tailWord_1982872
  simp only [CollatzResearch.WordTrace]
  refine ⟨36160641636200433210799435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48214188848267244281065913 36160641636200433210799435)
  ·
    refine ⟨54240962454300649816199153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36160641636200433210799435 54240962454300649816199153)
    ·
      refine ⟨40680721840725487362149365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54240962454300649816199153 40680721840725487362149365)
      ·
        refine ⟨3813817672568014440201503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40680721840725487362149365 3813817672568014440201503)
        ·
          refine ⟨5720726508852021660302255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3813817672568014440201503 5720726508852021660302255)
          ·
            refine ⟨8581089763278032490453383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5720726508852021660302255 8581089763278032490453383)
            ·
              refine ⟨12871634644917048735680075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8581089763278032490453383 12871634644917048735680075)
              ·
                refine ⟨19307451967375573103520113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12871634644917048735680075 19307451967375573103520113)
                ·
                  refine ⟨14480588975531679827640085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19307451967375573103520113 14480588975531679827640085)
                  ·
                    refine ⟨678777608228047491920629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14480588975531679827640085 678777608228047491920629)
                    ·
                      rfl

theorem cell22_1982872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_1982872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1982872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1982872 prefixEnd_1982872 := by exact prefixLift 1982872
  have htrace : WordTrace (prefixWord ++ tailWord_1982872) baseStart_1982872 baseEnd_1982872 := by
    simpa [prefixWord, tailWord_1982872, baseEnd_1982872] using wordTrace_append hprefix tailTrace_1982872
  have hstable : (prefixWord ++ tailWord_1982872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982872).length < 2 ^ (prefixWord ++ tailWord_1982872).sum := by decide
  have hdescent : baseEnd_1982872 < baseStart_1982872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982908 : List Nat := [2, 2, 2, 4, 1, 2, 2, 3, 1, 3]
def baseStart_1982908 : Nat := 118140960795 + 1982908 * 2 ^ 59
def prefixEnd_1982908 : Nat := 4983230072969 + 3 ^ 40 * 1982908 * 2
def baseEnd_1982908 : Nat := 678789931763755398020519

theorem tailTrace_1982908 : CollatzResearch.WordTrace tailWord_1982908 prefixEnd_1982908 678789931763755398020519 := by
  unfold tailWord_1982908
  simp only [CollatzResearch.WordTrace]
  refine ⟨36161298150135222284954689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48215064200180296379939585 36161298150135222284954689)
  ·
    refine ⟨27120973612601416713716017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36161298150135222284954689 27120973612601416713716017)
    ·
      refine ⟨20340730209451062535287013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27120973612601416713716017 20340730209451062535287013)
      ·
        refine ⟨3813886914272074225366315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20340730209451062535287013 3813886914272074225366315)
        ·
          refine ⟨5720830371408111338049473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3813886914272074225366315 5720830371408111338049473)
          ·
            refine ⟨4290622778556083503537105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5720830371408111338049473 4290622778556083503537105)
            ·
              refine ⟨3217967083917062627652829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4290622778556083503537105 3217967083917062627652829)
              ·
                refine ⟨1206737656468898485369811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3217967083917062627652829 1206737656468898485369811)
                ·
                  refine ⟨1810106484703347728054717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1206737656468898485369811 1810106484703347728054717)
                  ·
                    refine ⟨678789931763755398020519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1810106484703347728054717 678789931763755398020519)
                    ·
                      rfl

theorem cell22_1982908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_1982908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1982908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1982908 prefixEnd_1982908 := by exact prefixLift 1982908
  have htrace : WordTrace (prefixWord ++ tailWord_1982908) baseStart_1982908 baseEnd_1982908 := by
    simpa [prefixWord, tailWord_1982908, baseEnd_1982908] using wordTrace_append hprefix tailTrace_1982908
  have hstable : (prefixWord ++ tailWord_1982908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982908).length < 2 ^ (prefixWord ++ tailWord_1982908).sum := by decide
  have hdescent : baseEnd_1982908 < baseStart_1982908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982915 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 10]
def baseStart_1982915 : Nat := 118140960795 + 1982915 * 2 ^ 59
def prefixEnd_1982915 : Nat := 4983230072969 + 3 ^ 40 * 1982915 * 2
def baseEnd_1982915 : Nat := 226264109335603237698499

theorem tailTrace_1982915 : CollatzResearch.WordTrace tailWord_1982915 prefixEnd_1982915 226264109335603237698499 := by
  unfold tailWord_1982915
  simp only [CollatzResearch.WordTrace]
  refine ⟨72322851611245084765414199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48215234407496723176942799 72322851611245084765414199)
  ·
    refine ⟨108484277416867627148121299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72322851611245084765414199 108484277416867627148121299)
    ·
      refine ⟨162726416125301440722181949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108484277416867627148121299 162726416125301440722181949)
      ·
        refine ⟨61022406046988040270818231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162726416125301440722181949 61022406046988040270818231)
        ·
          refine ⟨91533609070482060406227347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61022406046988040270818231 91533609070482060406227347)
          ·
            refine ⟨137300413605723090609341021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91533609070482060406227347 137300413605723090609341021)
            ·
              refine ⟨51487655102146158978502883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137300413605723090609341021 51487655102146158978502883)
              ·
                refine ⟨77231482653219238467754325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 51487655102146158978502883 77231482653219238467754325)
                ·
                  refine ⟨226264109335603237698499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 77231482653219238467754325 226264109335603237698499)
                  ·
                    rfl

theorem cell22_1982915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 10].length) (baseStart_1982915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1982915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1982915 prefixEnd_1982915 := by exact prefixLift 1982915
  have htrace : WordTrace (prefixWord ++ tailWord_1982915) baseStart_1982915 baseEnd_1982915 := by
    simpa [prefixWord, tailWord_1982915, baseEnd_1982915] using wordTrace_append hprefix tailTrace_1982915
  have hstable : (prefixWord ++ tailWord_1982915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982915).length < 2 ^ (prefixWord ++ tailWord_1982915).sum := by decide
  have hdescent : baseEnd_1982915 < baseStart_1982915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982977 : List Nat := [1, 2, 4, 1, 3, 1, 10]
def baseStart_1982977 : Nat := 118140960795 + 1982977 * 2 ^ 59
def prefixEnd_1982977 : Nat := 4983230072969 + 3 ^ 40 * 1982977 * 2
def baseEnd_1982977 : Nat := 25141242661994896964641

theorem tailTrace_1982977 : CollatzResearch.WordTrace tailWord_1982977 prefixEnd_1982977 25141242661994896964641 := by
  unfold tailWord_1982977
  simp only [CollatzResearch.WordTrace]
  refine ⟨72325112937020469354171185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48216741958013646236114123 72325112937020469354171185)
  ·
    refine ⟨54243834702765352015628389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72325112937020469354171185 54243834702765352015628389)
    ·
      refine ⟨10170719006768503502930323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54243834702765352015628389 10170719006768503502930323)
      ·
        refine ⟨15256078510152755254395485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10170719006768503502930323 15256078510152755254395485)
        ·
          refine ⟨5721029441307283220398307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15256078510152755254395485 5721029441307283220398307)
          ·
            refine ⟨8581544161960924830597461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5721029441307283220398307 8581544161960924830597461)
            ·
              refine ⟨25141242661994896964641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8581544161960924830597461 25141242661994896964641)
              ·
                rfl

theorem cell22_1982977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 10].length) (baseStart_1982977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1982977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1982977 prefixEnd_1982977 := by exact prefixLift 1982977
  have htrace : WordTrace (prefixWord ++ tailWord_1982977) baseStart_1982977 baseEnd_1982977 := by
    simpa [prefixWord, tailWord_1982977, baseEnd_1982977] using wordTrace_append hprefix tailTrace_1982977
  have hstable : (prefixWord ++ tailWord_1982977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982977).length < 2 ^ (prefixWord ++ tailWord_1982977).sum := by decide
  have hdescent : baseEnd_1982977 < baseStart_1982977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1982983 : List Nat := [1, 1, 4, 3, 3, 1, 3, 2, 4]
def baseStart_1982983 : Nat := 118140960795 + 1982983 * 2 ^ 59
def prefixEnd_1982983 : Nat := 4983230072969 + 3 ^ 40 * 1982983 * 2
def baseEnd_1982983 : Nat := 226271868598826734131763

theorem tailTrace_1982983 : CollatzResearch.WordTrace tailWord_1982983 prefixEnd_1982983 226271868598826734131763 := by
  unfold tailWord_1982983
  simp only [CollatzResearch.WordTrace]
  refine ⟨72325331774998732378889603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48216887849999154919259735 72325331774998732378889603)
  ·
    refine ⟨108487997662498098568334405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72325331774998732378889603 108487997662498098568334405)
    ·
      refine ⟨20341499561718393481562701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108487997662498098568334405 20341499561718393481562701)
      ·
        refine ⟨7628062335644397555586013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20341499561718393481562701 7628062335644397555586013)
        ·
          refine ⟨2860523375866649083344755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7628062335644397555586013 2860523375866649083344755)
          ·
            refine ⟨4290785063799973625017133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2860523375866649083344755 4290785063799973625017133)
            ·
              refine ⟨1609044398924990109381425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4290785063799973625017133 1609044398924990109381425)
              ·
                refine ⟨1206783299193742582036069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1609044398924990109381425 1206783299193742582036069)
                ·
                  refine ⟨226271868598826734131763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1206783299193742582036069 226271868598826734131763)
                  ·
                    rfl

theorem cell22_1982983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2, 4].length) (baseStart_1982983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1982983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1982983 prefixEnd_1982983 := by exact prefixLift 1982983
  have htrace : WordTrace (prefixWord ++ tailWord_1982983) baseStart_1982983 baseEnd_1982983 := by
    simpa [prefixWord, tailWord_1982983, baseEnd_1982983] using wordTrace_append hprefix tailTrace_1982983
  have hstable : (prefixWord ++ tailWord_1982983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1982983).length < 2 ^ (prefixWord ++ tailWord_1982983).sum := by decide
  have hdescent : baseEnd_1982983 < baseStart_1982983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1982983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983009 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 5, 3]
def baseStart_1983009 : Nat := 118140960795 + 1983009 * 2 ^ 59
def prefixEnd_1983009 : Nat := 4983230072969 + 3 ^ 40 * 1983009 * 2
def baseEnd_1983009 : Nat := 678824506127824801245209

theorem tailTrace_1983009 : CollatzResearch.WordTrace tailWord_1983009 prefixEnd_1983009 678824506127824801245209 := by
  unfold tailWord_1983009
  simp only [CollatzResearch.WordTrace]
  refine ⟨72326280072904538819336081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48217520048603025879557387 72326280072904538819336081)
  ·
    refine ⟨54244710054678404114502061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72326280072904538819336081 54244710054678404114502061)
    ·
      refine ⟨20341766270504401542938273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54244710054678404114502061 20341766270504401542938273)
      ·
        refine ⟨15256324702878301157203705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20341766270504401542938273 15256324702878301157203705)
        ·
          refine ⟨11442243527158725867902779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15256324702878301157203705 11442243527158725867902779)
          ·
            refine ⟨17163365290738088801854169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11442243527158725867902779 17163365290738088801854169)
            ·
              refine ⟨12872523968053566601390627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17163365290738088801854169 12872523968053566601390627)
              ·
                refine ⟨19308785952080349902085941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12872523968053566601390627 19308785952080349902085941)
                ·
                  refine ⟨1810198683007532803320557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19308785952080349902085941 1810198683007532803320557)
                  ·
                    refine ⟨678824506127824801245209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1810198683007532803320557 678824506127824801245209)
                    ·
                      rfl

theorem cell22_1983009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_1983009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983009 prefixEnd_1983009 := by exact prefixLift 1983009
  have htrace : WordTrace (prefixWord ++ tailWord_1983009) baseStart_1983009 baseEnd_1983009 := by
    simpa [prefixWord, tailWord_1983009, baseEnd_1983009] using wordTrace_append hprefix tailTrace_1983009
  have hstable : (prefixWord ++ tailWord_1983009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983009).length < 2 ^ (prefixWord ++ tailWord_1983009).sum := by decide
  have hdescent : baseEnd_1983009 < baseStart_1983009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983039 : List Nat := [1, 1, 2, 2, 3, 2, 4, 2, 5]
def baseStart_1983039 : Nat := 118140960795 + 1983039 * 2 ^ 59
def prefixEnd_1983039 : Nat := 4983230072969 + 3 ^ 40 * 1983039 * 2
def baseEnd_1983039 : Nat := 226278258580304907665039

theorem tailTrace_1983039 : CollatzResearch.WordTrace tailWord_1983039 prefixEnd_1983039 226278258580304907665039 := by
  unfold tailWord_1983039
  simp only [CollatzResearch.WordTrace]
  refine ⟨72327374262795853942928171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48218249508530569295285447 72327374262795853942928171)
  ·
    refine ⟨108491061394193780914392257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72327374262795853942928171 108491061394193780914392257)
    ·
      refine ⟨81368296045645335685794193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108491061394193780914392257 81368296045645335685794193)
      ·
        refine ⟨61026222034234001764345645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81368296045645335685794193 61026222034234001764345645)
        ·
          refine ⟨22884833262837750661629617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61026222034234001764345645 22884833262837750661629617)
          ·
            refine ⟨17163624947128312996222213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22884833262837750661629617 17163624947128312996222213)
            ·
              refine ⟨3218179677586558686791665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17163624947128312996222213 3218179677586558686791665)
              ·
                refine ⟨2413634758189919015093749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3218179677586558686791665 2413634758189919015093749)
                ·
                  refine ⟨226278258580304907665039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2413634758189919015093749 226278258580304907665039)
                  ·
                    rfl

theorem cell22_1983039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 5].length) (baseStart_1983039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983039 prefixEnd_1983039 := by exact prefixLift 1983039
  have htrace : WordTrace (prefixWord ++ tailWord_1983039) baseStart_1983039 baseEnd_1983039 := by
    simpa [prefixWord, tailWord_1983039, baseEnd_1983039] using wordTrace_append hprefix tailTrace_1983039
  have hstable : (prefixWord ++ tailWord_1983039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983039).length < 2 ^ (prefixWord ++ tailWord_1983039).sum := by decide
  have hdescent : baseEnd_1983039 < baseStart_1983039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983101 : List Nat := [1, 4, 1, 1, 5, 1, 2, 1, 6]
def baseStart_1983101 : Nat := 118140960795 + 1983101 * 2 ^ 59
def prefixEnd_1983101 : Nat := 4983230072969 + 3 ^ 40 * 1983101 * 2
def baseEnd_1983101 : Nat := 226285333202655742648309

theorem tailTrace_1983101 : CollatzResearch.WordTrace tailWord_1983101 prefixEnd_1983101 226285333202655742648309 := by
  unfold tailWord_1983101
  simp only [CollatzResearch.WordTrace]
  refine ⟨72329635588571238531685157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48219757059047492354456771 72329635588571238531685157)
  ·
    refine ⟨13561806672857107224690967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72329635588571238531685157 13561806672857107224690967)
    ·
      refine ⟨20342710009285660837036451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13561806672857107224690967 20342710009285660837036451)
      ·
        refine ⟨30514065013928491255554677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20342710009285660837036451 30514065013928491255554677)
        ·
          refine ⟨2860693595055796055208251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30514065013928491255554677 2860693595055796055208251)
          ·
            refine ⟨4291040392583694082812377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2860693595055796055208251 4291040392583694082812377)
            ·
              refine ⟨3218280294437770562109283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4291040392583694082812377 3218280294437770562109283)
              ·
                refine ⟨4827420441656655843163925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3218280294437770562109283 4827420441656655843163925)
                ·
                  refine ⟨226285333202655742648309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4827420441656655843163925 226285333202655742648309)
                  ·
                    rfl

theorem cell22_1983101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_1983101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983101 prefixEnd_1983101 := by exact prefixLift 1983101
  have htrace : WordTrace (prefixWord ++ tailWord_1983101) baseStart_1983101 baseEnd_1983101 := by
    simpa [prefixWord, tailWord_1983101, baseEnd_1983101] using wordTrace_append hprefix tailTrace_1983101
  have hstable : (prefixWord ++ tailWord_1983101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983101).length < 2 ^ (prefixWord ++ tailWord_1983101).sum := by decide
  have hdescent : baseEnd_1983101 < baseStart_1983101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983208 : List Nat := [2, 1, 4, 1, 4, 1, 2, 2, 5]
def baseStart_1983208 : Nat := 118140960795 + 1983208 * 2 ^ 59
def prefixEnd_1983208 : Nat := 4983230072969 + 3 ^ 40 * 1983208 * 2
def baseEnd_1983208 : Nat := 226297542631551538506533

theorem tailTrace_1983208 : CollatzResearch.WordTrace tailWord_1983208 prefixEnd_1983208 226297542631551538506533 := by
  unfold tailWord_1983208
  simp only [CollatzResearch.WordTrace]
  refine ⟨36166769099591797902915139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48222358799455730537220185 36166769099591797902915139)
  ·
    refine ⟨54250153649387696854372709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36166769099591797902915139 54250153649387696854372709)
    ·
      refine ⟨10171903809260193160194883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54250153649387696854372709 10171903809260193160194883)
      ·
        refine ⟨15257855713890289740292325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10171903809260193160194883 15257855713890289740292325)
        ·
          refine ⟨2860847946354429326304811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15257855713890289740292325 2860847946354429326304811)
          ·
            refine ⟨4291271919531643989457217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2860847946354429326304811 4291271919531643989457217)
            ·
              refine ⟨3218453939648732992092913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4291271919531643989457217 3218453939648732992092913)
              ·
                refine ⟨2413840454736549744069685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3218453939648732992092913 2413840454736549744069685)
                ·
                  refine ⟨226297542631551538506533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2413840454736549744069685 226297542631551538506533)
                  ·
                    rfl

theorem cell22_1983208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 5].length) (baseStart_1983208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983208 prefixEnd_1983208 := by exact prefixLift 1983208
  have htrace : WordTrace (prefixWord ++ tailWord_1983208) baseStart_1983208 baseEnd_1983208 := by
    simpa [prefixWord, tailWord_1983208, baseEnd_1983208] using wordTrace_append hprefix tailTrace_1983208
  have hstable : (prefixWord ++ tailWord_1983208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983208).length < 2 ^ (prefixWord ++ tailWord_1983208).sum := by decide
  have hdescent : baseEnd_1983208 < baseStart_1983208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983219 : List Nat := [1, 1, 1, 2, 2, 3, 1, 5, 6]
def baseStart_1983219 : Nat := 118140960795 + 1983219 * 2 ^ 59
def prefixEnd_1983219 : Nat := 4983230072969 + 3 ^ 40 * 1983219 * 2
def baseEnd_1983219 : Nat := 226298797806484751164855

theorem tailTrace_1983219 : CollatzResearch.WordTrace tailWord_1983219 prefixEnd_1983219 226298797806484751164855 := by
  unfold tailWord_1983219
  simp only [CollatzResearch.WordTrace]
  refine ⟨72333939402143744684480711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48222626268095829789653807 72333939402143744684480711)
  ·
    refine ⟨108500909103215617026721067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72333939402143744684480711 108500909103215617026721067)
    ·
      refine ⟨162751363654823425540081601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108500909103215617026721067 162751363654823425540081601)
      ·
        refine ⟨122063522741117569155061201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162751363654823425540081601 122063522741117569155061201)
        ·
          refine ⟨91547642055838176866295901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122063522741117569155061201 91547642055838176866295901)
          ·
            refine ⟨34330365770939316324860963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91547642055838176866295901 34330365770939316324860963)
            ·
              refine ⟨51495548656408974487291445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34330365770939316324860963 51495548656408974487291445)
              ·
                refine ⟨4827707686538341358183573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51495548656408974487291445 4827707686538341358183573)
                ·
                  refine ⟨226298797806484751164855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4827707686538341358183573 226298797806484751164855)
                  ·
                    rfl

theorem cell22_1983219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 6].length) (baseStart_1983219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983219 prefixEnd_1983219 := by exact prefixLift 1983219
  have htrace : WordTrace (prefixWord ++ tailWord_1983219) baseStart_1983219 baseEnd_1983219 := by
    simpa [prefixWord, tailWord_1983219, baseEnd_1983219] using wordTrace_append hprefix tailTrace_1983219
  have hstable : (prefixWord ++ tailWord_1983219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983219).length < 2 ^ (prefixWord ++ tailWord_1983219).sum := by decide
  have hdescent : baseEnd_1983219 < baseStart_1983219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983236 : List Nat := [2, 3, 2, 2, 1, 1, 3, 2, 6]
def baseStart_1983236 : Nat := 118140960795 + 1983236 * 2 ^ 59
def prefixEnd_1983236 : Nat := 4983230072969 + 3 ^ 40 * 1983236 * 2
def baseEnd_1983236 : Nat := 226300737622290625273171

theorem tailTrace_1983236 : CollatzResearch.WordTrace tailWord_1983236 prefixEnd_1983236 226300737622290625273171 := by
  unfold tailWord_1983236
  simp only [CollatzResearch.WordTrace]
  refine ⟨36167279721541078293924781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48223039628721437725233041 36167279721541078293924781)
  ·
    refine ⟨13562729895577904360221793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36167279721541078293924781 13562729895577904360221793)
    ·
      refine ⟨10172047421683428270166345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13562729895577904360221793 10172047421683428270166345)
      ·
        refine ⟨7629035566262571202624759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10172047421683428270166345 7629035566262571202624759)
        ·
          refine ⟨11443553349393856803937139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7629035566262571202624759 11443553349393856803937139)
          ·
            refine ⟨17165330024090785205905709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11443553349393856803937139 17165330024090785205905709)
            ·
              refine ⟨6436998759034044452214641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17165330024090785205905709 6436998759034044452214641)
              ·
                refine ⟨4827749069275533339160981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6436998759034044452214641 4827749069275533339160981)
                ·
                  refine ⟨226300737622290625273171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4827749069275533339160981 226300737622290625273171)
                  ·
                    rfl

theorem cell22_1983236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_1983236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983236 prefixEnd_1983236 := by exact prefixLift 1983236
  have htrace : WordTrace (prefixWord ++ tailWord_1983236) baseStart_1983236 baseEnd_1983236 := by
    simpa [prefixWord, tailWord_1983236, baseEnd_1983236] using wordTrace_append hprefix tailTrace_1983236
  have hstable : (prefixWord ++ tailWord_1983236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983236).length < 2 ^ (prefixWord ++ tailWord_1983236).sum := by decide
  have hdescent : baseEnd_1983236 < baseStart_1983236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983251 : List Nat := [1, 1, 1, 2, 1, 3, 4, 2, 4, 3]
def baseStart_1983251 : Nat := 118140960795 + 1983251 * 2 ^ 59
def prefixEnd_1983251 : Nat := 4983230072969 + 3 ^ 40 * 1983251 * 2
def baseEnd_1983251 : Nat := 678907347673416836694467

theorem tailTrace_1983251 : CollatzResearch.WordTrace tailWord_1983251 prefixEnd_1983251 678907347673416836694467 := by
  unfold tailWord_1983251
  simp only [CollatzResearch.WordTrace]
  refine ⟨72335106538027814149645607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48223404358685209433097071 72335106538027814149645607)
  ·
    refine ⟨108502659807041721224468411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72335106538027814149645607 108502659807041721224468411)
    ·
      refine ⟨162753989710562581836702617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108502659807041721224468411 162753989710562581836702617)
      ·
        refine ⟨122065492282921936377526963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162753989710562581836702617 122065492282921936377526963)
        ·
          refine ⟨183098238424382904566290445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122065492282921936377526963 183098238424382904566290445)
          ·
            refine ⟨68661839409143589212358917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 183098238424382904566290445 68661839409143589212358917)
            ·
              refine ⟨12874094889214422977317297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 68661839409143589212358917 12874094889214422977317297)
              ·
                refine ⟨9655571166910817232987973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12874094889214422977317297 9655571166910817232987973)
                ·
                  refine ⟨1810419593795778231185245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9655571166910817232987973 1810419593795778231185245)
                  ·
                    refine ⟨678907347673416836694467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1810419593795778231185245 678907347673416836694467)
                    ·
                      rfl

theorem cell22_1983251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4, 3].length) (baseStart_1983251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983251 prefixEnd_1983251 := by exact prefixLift 1983251
  have htrace : WordTrace (prefixWord ++ tailWord_1983251) baseStart_1983251 baseEnd_1983251 := by
    simpa [prefixWord, tailWord_1983251, baseEnd_1983251] using wordTrace_append hprefix tailTrace_1983251
  have hstable : (prefixWord ++ tailWord_1983251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983251).length < 2 ^ (prefixWord ++ tailWord_1983251).sum := by decide
  have hdescent : baseEnd_1983251 < baseStart_1983251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983253 : List Nat := [1, 3, 2, 1, 2, 2, 4, 3, 4]
def baseStart_1983253 : Nat := 118140960795 + 1983253 * 2 ^ 59
def prefixEnd_1983253 : Nat := 4983230072969 + 3 ^ 40 * 1983253 * 2
def baseEnd_1983253 : Nat := 226302677438096499381487

theorem tailTrace_1983253 : CollatzResearch.WordTrace tailWord_1983253 prefixEnd_1983253 226302677438096499381487 := by
  unfold tailWord_1983253
  simp only [CollatzResearch.WordTrace]
  refine ⟨72335179484020568491218413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48223452989347045660812275 72335179484020568491218413)
  ·
    refine ⟨27125692306507713184206905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72335179484020568491218413 27125692306507713184206905)
    ·
      refine ⟨20344269229880784888155179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27125692306507713184206905 20344269229880784888155179)
      ·
        refine ⟨30516403844821177332232769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20344269229880784888155179 30516403844821177332232769)
        ·
          refine ⟨22887302883615882999174577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30516403844821177332232769 22887302883615882999174577)
          ·
            refine ⟨17165477162711912249380933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22887302883615882999174577 17165477162711912249380933)
            ·
              refine ⟨3218526968008483546758925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17165477162711912249380933 3218526968008483546758925)
              ·
                refine ⟨1206947613003181330034597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3218526968008483546758925 1206947613003181330034597)
                ·
                  refine ⟨226302677438096499381487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1206947613003181330034597 226302677438096499381487)
                  ·
                    rfl

theorem cell22_1983253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3, 4].length) (baseStart_1983253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983253 prefixEnd_1983253 := by exact prefixLift 1983253
  have htrace : WordTrace (prefixWord ++ tailWord_1983253) baseStart_1983253 baseEnd_1983253 := by
    simpa [prefixWord, tailWord_1983253, baseEnd_1983253] using wordTrace_append hprefix tailTrace_1983253
  have hstable : (prefixWord ++ tailWord_1983253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983253).length < 2 ^ (prefixWord ++ tailWord_1983253).sum := by decide
  have hdescent : baseEnd_1983253 < baseStart_1983253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983279 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 4, 7]
def baseStart_1983279 : Nat := 118140960795 + 1983279 * 2 ^ 59
def prefixEnd_1983279 : Nat := 4983230072969 + 3 ^ 40 * 1983279 * 2
def baseEnd_1983279 : Nat := 678916932645634096994381

theorem tailTrace_1983279 : CollatzResearch.WordTrace tailWord_1983279 prefixEnd_1983279 678916932645634096994381 := by
  unfold tailWord_1983279
  simp only [CollatzResearch.WordTrace]
  refine ⟨72336127781926374931664891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48224085187950916621109927 72336127781926374931664891)
  ·
    refine ⟨108504191672889562397497337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72336127781926374931664891 108504191672889562397497337)
    ·
      refine ⟨81378143754667171798123003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108504191672889562397497337 81378143754667171798123003)
      ·
        refine ⟨122067215632000757697184505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81378143754667171798123003 122067215632000757697184505)
        ·
          refine ⟨91550411724000568272888379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122067215632000757697184505 91550411724000568272888379)
          ·
            refine ⟨137325617586000852409332569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91550411724000568272888379 137325617586000852409332569)
            ·
              refine ⟨102994213189500639306999427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 137325617586000852409332569 102994213189500639306999427)
              ·
                refine ⟨154491319784250958960499141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 102994213189500639306999427 154491319784250958960499141)
                ·
                  refine ⟨28967122459547054805093589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154491319784250958960499141 28967122459547054805093589)
                  ·
                    refine ⟨678916932645634096994381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28967122459547054805093589 678916932645634096994381)
                    ·
                      rfl

theorem cell22_1983279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_1983279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983279 prefixEnd_1983279 := by exact prefixLift 1983279
  have htrace : WordTrace (prefixWord ++ tailWord_1983279) baseStart_1983279 baseEnd_1983279 := by
    simpa [prefixWord, tailWord_1983279, baseEnd_1983279] using wordTrace_append hprefix tailTrace_1983279
  have hstable : (prefixWord ++ tailWord_1983279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983279).length < 2 ^ (prefixWord ++ tailWord_1983279).sum := by decide
  have hdescent : baseEnd_1983279 < baseStart_1983279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983341 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_1983341 : Nat := 118140960795 + 1983341 * 2 ^ 59
def prefixEnd_1983341 : Nat := 4983230072969 + 3 ^ 40 * 1983341 * 2
def baseEnd_1983341 : Nat := 678938156512686601944191

theorem tailTrace_1983341 : CollatzResearch.WordTrace tailWord_1983341 prefixEnd_1983341 678938156512686601944191 := by
  unfold tailWord_1983341
  simp only [CollatzResearch.WordTrace]
  refine ⟨72338389107701759520421877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48225592738467839680281251 72338389107701759520421877)
  ·
    refine ⟨6781723978847039955039551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 72338389107701759520421877 6781723978847039955039551)
    ·
      refine ⟨10172585968270559932559327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6781723978847039955039551 10172585968270559932559327)
      ·
        refine ⟨15258878952405839898838991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10172585968270559932559327 15258878952405839898838991)
        ·
          refine ⟨22888318428608759848258487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15258878952405839898838991 22888318428608759848258487)
          ·
            refine ⟨34332477642913139772387731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22888318428608759848258487 34332477642913139772387731)
            ·
              refine ⟨51498716464369709658581597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34332477642913139772387731 51498716464369709658581597)
              ·
                refine ⟨19312018674138641121968099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51498716464369709658581597 19312018674138641121968099)
                ·
                  refine ⟨28968028011207961682952149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19312018674138641121968099 28968028011207961682952149)
                  ·
                    refine ⟨678938156512686601944191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28968028011207961682952149 678938156512686601944191)
                    ·
                      rfl

theorem cell22_1983341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_1983341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983341 prefixEnd_1983341 := by exact prefixLift 1983341
  have htrace : WordTrace (prefixWord ++ tailWord_1983341) baseStart_1983341 baseEnd_1983341 := by
    simpa [prefixWord, tailWord_1983341, baseEnd_1983341] using wordTrace_append hprefix tailTrace_1983341
  have hstable : (prefixWord ++ tailWord_1983341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983341).length < 2 ^ (prefixWord ++ tailWord_1983341).sum := by decide
  have hdescent : baseEnd_1983341 < baseStart_1983341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983401 : List Nat := [1, 2, 1, 1, 1, 1, 6, 2, 1, 6]
def baseStart_1983401 : Nat := 118140960795 + 1983401 * 2 ^ 59
def prefixEnd_1983401 : Nat := 4983230072969 + 3 ^ 40 * 1983401 * 2
def baseEnd_1983401 : Nat := 678958695738866445444007

theorem tailTrace_1983401 : CollatzResearch.WordTrace tailWord_1983401 prefixEnd_1983401 678958695738866445444007 := by
  unfold tailWord_1983401
  simp only [CollatzResearch.WordTrace]
  refine ⟨72340577487484389767606057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48227051658322926511737371 72340577487484389767606057)
  ·
    refine ⟨54255433115613292325704543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72340577487484389767606057 54255433115613292325704543)
    ·
      refine ⟨81383149673419938488556815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54255433115613292325704543 81383149673419938488556815)
      ·
        refine ⟨122074724510129907732835223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81383149673419938488556815 122074724510129907732835223)
        ·
          refine ⟨183112086765194861599252835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122074724510129907732835223 183112086765194861599252835)
          ·
            refine ⟨274668130147792292398879253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183112086765194861599252835 274668130147792292398879253)
            ·
              refine ⟨12875068600677763706197465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 274668130147792292398879253 12875068600677763706197465)
              ·
                refine ⟨9656301450508322779648099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12875068600677763706197465 9656301450508322779648099)
                ·
                  refine ⟨14484452175762484169472149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9656301450508322779648099 14484452175762484169472149)
                  ·
                    refine ⟨678958695738866445444007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14484452175762484169472149 678958695738866445444007)
                    ·
                      rfl

theorem cell22_1983401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 1, 6].length) (baseStart_1983401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983401 prefixEnd_1983401 := by exact prefixLift 1983401
  have htrace : WordTrace (prefixWord ++ tailWord_1983401) baseStart_1983401 baseEnd_1983401 := by
    simpa [prefixWord, tailWord_1983401, baseEnd_1983401] using wordTrace_append hprefix tailTrace_1983401
  have hstable : (prefixWord ++ tailWord_1983401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983401).length < 2 ^ (prefixWord ++ tailWord_1983401).sum := by decide
  have hdescent : baseEnd_1983401 < baseStart_1983401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983499 : List Nat := [1, 1, 1, 1, 6, 3, 3, 2, 1, 3]
def baseStart_1983499 : Nat := 118140960795 + 1983499 * 2 ^ 59
def prefixEnd_1983499 : Nat := 4983230072969 + 3 ^ 40 * 1983499 * 2
def baseEnd_1983499 : Nat := 678992243141626856493707

theorem tailTrace_1983499 : CollatzResearch.WordTrace tailWord_1983499 prefixEnd_1983499 678992243141626856493707 := by
  unfold tailWord_1983499
  simp only [CollatzResearch.WordTrace]
  refine ⟨72344151841129352504673551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48229434560752901669782367 72344151841129352504673551)
  ·
    refine ⟨108516227761694028757010327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72344151841129352504673551 108516227761694028757010327)
    ·
      refine ⟨162774341642541043135515491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108516227761694028757010327 162774341642541043135515491)
      ·
        refine ⟨244161512463811564703273237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162774341642541043135515491 244161512463811564703273237)
        ·
          refine ⟨11445070896741167095465933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 244161512463811564703273237 11445070896741167095465933)
          ·
            refine ⟨4291901586277937660799725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11445070896741167095465933 4291901586277937660799725)
            ·
              refine ⟨1609463094854226622799897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4291901586277937660799725 1609463094854226622799897)
              ·
                refine ⟨1207097321140669967099923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1609463094854226622799897 1207097321140669967099923)
                ·
                  refine ⟨1810645981711004950649885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1207097321140669967099923 1810645981711004950649885)
                  ·
                    refine ⟨678992243141626856493707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1810645981711004950649885 678992243141626856493707)
                    ·
                      rfl

theorem cell22_1983499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2, 1, 3].length) (baseStart_1983499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983499 prefixEnd_1983499 := by exact prefixLift 1983499
  have htrace : WordTrace (prefixWord ++ tailWord_1983499) baseStart_1983499 baseEnd_1983499 := by
    simpa [prefixWord, tailWord_1983499, baseEnd_1983499] using wordTrace_append hprefix tailTrace_1983499
  have hstable : (prefixWord ++ tailWord_1983499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983499).length < 2 ^ (prefixWord ++ tailWord_1983499).sum := by decide
  have hdescent : baseEnd_1983499 < baseStart_1983499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983512 : List Nat := [2, 1, 2, 3, 2, 4, 2, 1, 5]
def baseStart_1983512 : Nat := 118140960795 + 1983512 * 2 ^ 59
def prefixEnd_1983512 : Nat := 4983230072969 + 3 ^ 40 * 1983512 * 2
def baseEnd_1983512 : Nat := 226332231102433051972889

theorem tailTrace_1983512 : CollatzResearch.WordTrace tailWord_1983512 prefixEnd_1983512 226332231102433051972889 := by
  unfold tailWord_1983512
  simp only [CollatzResearch.WordTrace]
  refine ⟨36172312995041127862448395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48229750660054837149931193 36172312995041127862448395)
  ·
    refine ⟨54258469492561691793672593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36172312995041127862448395 54258469492561691793672593)
    ·
      refine ⟨40693852119421268845254445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54258469492561691793672593 40693852119421268845254445)
      ·
        refine ⟨15260194544782975816970417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40693852119421268845254445 15260194544782975816970417)
        ·
          refine ⟨11445145908587231862727813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15260194544782975816970417 11445145908587231862727813)
          ·
            refine ⟨2145964857860105974261465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11445145908587231862727813 2145964857860105974261465)
            ·
              refine ⟨1609473643395079480696099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2145964857860105974261465 1609473643395079480696099)
              ·
                refine ⟨2414210465092619221044149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1609473643395079480696099 2414210465092619221044149)
                ·
                  refine ⟨226332231102433051972889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2414210465092619221044149 226332231102433051972889)
                  ·
                    rfl

theorem cell22_1983512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 5].length) (baseStart_1983512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983512 prefixEnd_1983512 := by exact prefixLift 1983512
  have htrace : WordTrace (prefixWord ++ tailWord_1983512) baseStart_1983512 baseEnd_1983512 := by
    simpa [prefixWord, tailWord_1983512, baseEnd_1983512] using wordTrace_append hprefix tailTrace_1983512
  have hstable : (prefixWord ++ tailWord_1983512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983512).length < 2 ^ (prefixWord ++ tailWord_1983512).sum := by decide
  have hdescent : baseEnd_1983512 < baseStart_1983512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983557 : List Nat := [1, 3, 1, 1, 1, 3, 6, 2, 4]
def baseStart_1983557 : Nat := 118140960795 + 1983557 * 2 ^ 59
def prefixEnd_1983557 : Nat := 4983230072969 + 3 ^ 40 * 1983557 * 2
def baseEnd_1983557 : Nat := 226337365908978012847843

theorem tailTrace_1983557 : CollatzResearch.WordTrace tailWord_1983557 prefixEnd_1983557 226337365908978012847843 := by
  unfold tailWord_1983557
  simp only [CollatzResearch.WordTrace]
  refine ⟨72346267274919228410284925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48230844849946152273523283 72346267274919228410284925)
  ·
    refine ⟨27129850228094710653856847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72346267274919228410284925 27129850228094710653856847)
    ·
      refine ⟨40694775342142065980785271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27129850228094710653856847 40694775342142065980785271)
      ·
        refine ⟨61042163013213098971177907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40694775342142065980785271 61042163013213098971177907)
        ·
          refine ⟨91563244519819648456766861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61042163013213098971177907 91563244519819648456766861)
          ·
            refine ⟨34336216694932368171287573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91563244519819648456766861 34336216694932368171287573)
            ·
              refine ⟨1609510157574954758029105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34336216694932368171287573 1609510157574954758029105)
              ·
                refine ⟨1207132618181216068521829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1609510157574954758029105 1207132618181216068521829)
                ·
                  refine ⟨226337365908978012847843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1207132618181216068521829 226337365908978012847843)
                  ·
                    rfl

theorem cell22_1983557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2, 4].length) (baseStart_1983557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983557 prefixEnd_1983557 := by exact prefixLift 1983557
  have htrace : WordTrace (prefixWord ++ tailWord_1983557) baseStart_1983557 baseEnd_1983557 := by
    simpa [prefixWord, tailWord_1983557, baseEnd_1983557] using wordTrace_append hprefix tailTrace_1983557
  have hstable : (prefixWord ++ tailWord_1983557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983557).length < 2 ^ (prefixWord ++ tailWord_1983557).sum := by decide
  have hdescent : baseEnd_1983557 < baseStart_1983557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983572 : List Nat := [2, 4, 1, 1, 1, 1, 4, 3, 2, 3]
def baseStart_1983572 : Nat := 118140960795 + 1983572 * 2 ^ 59
def prefixEnd_1983572 : Nat := 4983230072969 + 3 ^ 40 * 1983572 * 2
def baseEnd_1983572 : Nat := 679017232533478999418483

theorem tailTrace_1983572 : CollatzResearch.WordTrace tailWord_1983572 prefixEnd_1983572 679017232533478999418483 := by
  unfold tailWord_1983572
  simp only [CollatzResearch.WordTrace]
  refine ⟨36173407184932442986040485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48231209579909923981387313 36173407184932442986040485)
  ·
    refine ⟨6782513847174833059882591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36173407184932442986040485 6782513847174833059882591)
    ·
      refine ⟨10173770770762249589823887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6782513847174833059882591 10173770770762249589823887)
      ·
        refine ⟨15260656156143374384735831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10173770770762249589823887 15260656156143374384735831)
        ·
          refine ⟨22890984234215061577103747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15260656156143374384735831 22890984234215061577103747)
          ·
            refine ⟨34336476351322592365655621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22890984234215061577103747 34336476351322592365655621)
            ·
              refine ⟨6438089315872986068560429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34336476351322592365655621 6438089315872986068560429)
              ·
                refine ⟨2414283493452369775710161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6438089315872986068560429 2414283493452369775710161)
                ·
                  refine ⟨1810712620089277331782621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2414283493452369775710161 1810712620089277331782621)
                  ·
                    refine ⟨679017232533478999418483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1810712620089277331782621 679017232533478999418483)
                    ·
                      rfl

theorem cell22_1983572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_1983572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983572 prefixEnd_1983572 := by exact prefixLift 1983572
  have htrace : WordTrace (prefixWord ++ tailWord_1983572) baseStart_1983572 baseEnd_1983572 := by
    simpa [prefixWord, tailWord_1983572, baseEnd_1983572] using wordTrace_append hprefix tailTrace_1983572
  have hstable : (prefixWord ++ tailWord_1983572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983572).length < 2 ^ (prefixWord ++ tailWord_1983572).sum := by decide
  have hdescent : baseEnd_1983572 < baseStart_1983572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983574 : List Nat := [5, 2, 2, 1, 2, 1, 1, 2, 6]
def baseStart_1983574 : Nat := 118140960795 + 1983574 * 2 ^ 59
def prefixEnd_1983574 : Nat := 4983230072969 + 3 ^ 40 * 1983574 * 2
def baseEnd_1983574 : Nat := 226339305724783886956159

theorem tailTrace_1983574 : CollatzResearch.WordTrace tailWord_1983574 prefixEnd_1983574 226339305724783886956159 := by
  unfold tailWord_1983574
  simp only [CollatzResearch.WordTrace]
  refine ⟨4521680457241102519603361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48231258210571760209102517 4521680457241102519603361)
  ·
    refine ⟨3391260342930826889702521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4521680457241102519603361 3391260342930826889702521)
    ·
      refine ⟨2543445257198120167276891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3391260342930826889702521 2543445257198120167276891)
      ·
        refine ⟨3815167885797180250915337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2543445257198120167276891 3815167885797180250915337)
        ·
          refine ⟨2861375914347885188186503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3815167885797180250915337 2861375914347885188186503)
          ·
            refine ⟨4292063871521827782279755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2861375914347885188186503 4292063871521827782279755)
            ·
              refine ⟨6438095807282741673419633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4292063871521827782279755 6438095807282741673419633)
              ·
                refine ⟨4828571855462056255064725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6438095807282741673419633 4828571855462056255064725)
                ·
                  refine ⟨226339305724783886956159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4828571855462056255064725 226339305724783886956159)
                  ·
                    rfl

theorem cell22_1983574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_1983574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983574 prefixEnd_1983574 := by exact prefixLift 1983574
  have htrace : WordTrace (prefixWord ++ tailWord_1983574) baseStart_1983574 baseEnd_1983574 := by
    simpa [prefixWord, tailWord_1983574, baseEnd_1983574] using wordTrace_append hprefix tailTrace_1983574
  have hstable : (prefixWord ++ tailWord_1983574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983574).length < 2 ^ (prefixWord ++ tailWord_1983574).sum := by decide
  have hdescent : baseEnd_1983574 < baseStart_1983574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983600 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 5, 3]
def baseStart_1983600 : Nat := 118140960795 + 1983600 * 2 ^ 59
def prefixEnd_1983600 : Nat := 4983230072969 + 3 ^ 40 * 1983600 * 2
def baseEnd_1983600 : Nat := 679026817505696259718397

theorem tailTrace_1983600 : CollatzResearch.WordTrace tailWord_1983600 prefixEnd_1983600 679026817505696259718397 := by
  unfold tailWord_1983600
  simp only [CollatzResearch.WordTrace]
  refine ⟨36173917806881723377050127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48231890409175631169400169 36173917806881723377050127)
  ·
    refine ⟨54260876710322585065575191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36173917806881723377050127 54260876710322585065575191)
    ·
      refine ⟨81391315065483877598362787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54260876710322585065575191 81391315065483877598362787)
      ·
        refine ⟨122086972598225816397544181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81391315065483877598362787 122086972598225816397544181)
        ·
          refine ⟨11445653681083670287269767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 122086972598225816397544181 11445653681083670287269767)
          ·
            refine ⟨17168480521625505430904651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11445653681083670287269767 17168480521625505430904651)
            ·
              refine ⟨25752720782438258146356977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17168480521625505430904651 25752720782438258146356977)
              ·
                refine ⟨19314540586828693609767733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25752720782438258146356977 19314540586828693609767733)
                ·
                  refine ⟨1810738180015190025915725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19314540586828693609767733 1810738180015190025915725)
                  ·
                    refine ⟨679026817505696259718397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1810738180015190025915725 679026817505696259718397)
                    ·
                      rfl

theorem cell22_1983600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 5, 3].length) (baseStart_1983600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983600 prefixEnd_1983600 := by exact prefixLift 1983600
  have htrace : WordTrace (prefixWord ++ tailWord_1983600) baseStart_1983600 baseEnd_1983600 := by
    simpa [prefixWord, tailWord_1983600, baseEnd_1983600] using wordTrace_append hprefix tailTrace_1983600
  have hstable : (prefixWord ++ tailWord_1983600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983600).length < 2 ^ (prefixWord ++ tailWord_1983600).sum := by decide
  have hdescent : baseEnd_1983600 < baseStart_1983600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983617 : List Nat := [1, 2, 4, 2, 2, 1, 1, 3, 3, 3]
def baseStart_1983617 : Nat := 118140960795 + 1983617 * 2 ^ 59
def prefixEnd_1983617 : Nat := 4983230072969 + 3 ^ 40 * 1983617 * 2
def baseEnd_1983617 : Nat := 679032636953113882043345

theorem tailTrace_1983617 : CollatzResearch.WordTrace tailWord_1983617 prefixEnd_1983617 679032636953113882043345 := by
  unfold tailWord_1983617
  simp only [CollatzResearch.WordTrace]
  refine ⟨72348455654701858657469105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48232303769801239104979403 72348455654701858657469105)
  ·
    refine ⟨54261341741026393993101829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72348455654701858657469105 54261341741026393993101829)
    ·
      refine ⟨10174001576442448873706593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54261341741026393993101829 10174001576442448873706593)
      ·
        refine ⟨7630501182331836655279945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10174001576442448873706593 7630501182331836655279945)
        ·
          refine ⟨5722875886748877491459959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7630501182331836655279945 5722875886748877491459959)
          ·
            refine ⟨8584313830123316237189939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5722875886748877491459959 8584313830123316237189939)
            ·
              refine ⟨12876470745184974355784909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8584313830123316237189939 12876470745184974355784909)
              ·
                refine ⟨4828676529444365383419341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12876470745184974355784909 4828676529444365383419341)
                ·
                  refine ⟨1810753698541637018782253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4828676529444365383419341 1810753698541637018782253)
                  ·
                    refine ⟨679032636953113882043345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1810753698541637018782253 679032636953113882043345)
                    ·
                      rfl

theorem cell22_1983617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_1983617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983617 prefixEnd_1983617 := by exact prefixLift 1983617
  have htrace : WordTrace (prefixWord ++ tailWord_1983617) baseStart_1983617 baseEnd_1983617 := by
    simpa [prefixWord, tailWord_1983617, baseEnd_1983617] using wordTrace_append hprefix tailTrace_1983617
  have hstable : (prefixWord ++ tailWord_1983617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983617).length < 2 ^ (prefixWord ++ tailWord_1983617).sum := by decide
  have hdescent : baseEnd_1983617 < baseStart_1983617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983681 : List Nat := [1, 2, 6, 1, 1, 3, 2, 1, 5]
def baseStart_1983681 : Nat := 118140960795 + 1983681 * 2 ^ 59
def prefixEnd_1983681 : Nat := 4983230072969 + 3 ^ 40 * 1983681 * 2
def baseEnd_1983681 : Nat := 226351515153679682814383

theorem tailTrace_1983681 : CollatzResearch.WordTrace tailWord_1983681 prefixEnd_1983681 226351515153679682814383 := by
  unfold tailWord_1983681
  simp only [CollatzResearch.WordTrace]
  refine ⟨72350789926469997587798897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48233859950979998391865931 72350789926469997587798897)
  ·
    refine ⟨54263092444852498190849173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72350789926469997587798897 54263092444852498190849173)
    ·
      refine ⟨2543582458352460852696055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54263092444852498190849173 2543582458352460852696055)
      ·
        refine ⟨3815373687528691279044083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2543582458352460852696055 3815373687528691279044083)
        ·
          refine ⟨5723060531293036918566125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3815373687528691279044083 5723060531293036918566125)
          ·
            refine ⟨2146147699234888844462297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5723060531293036918566125 2146147699234888844462297)
            ·
              refine ⟨1609610774426166633346723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2146147699234888844462297 1609610774426166633346723)
              ·
                refine ⟨2414416161639249950020085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1609610774426166633346723 2414416161639249950020085)
                ·
                  refine ⟨226351515153679682814383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2414416161639249950020085 226351515153679682814383)
                  ·
                    rfl

theorem cell22_1983681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 5].length) (baseStart_1983681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983681 prefixEnd_1983681 := by exact prefixLift 1983681
  have htrace : WordTrace (prefixWord ++ tailWord_1983681) baseStart_1983681 baseEnd_1983681 := by
    simpa [prefixWord, tailWord_1983681, baseEnd_1983681] using wordTrace_append hprefix tailTrace_1983681
  have hstable : (prefixWord ++ tailWord_1983681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983681).length < 2 ^ (prefixWord ++ tailWord_1983681).sum := by decide
  have hdescent : baseEnd_1983681 < baseStart_1983681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983722 : List Nat := [3, 1, 3, 1, 1, 3, 2, 2, 2, 4]
def baseStart_1983722 : Nat := 118140960795 + 1983722 * 2 ^ 59
def prefixEnd_1983722 : Nat := 4983230072969 + 3 ^ 40 * 1983722 * 2
def baseEnd_1983722 : Nat := 679068580598928608168023

theorem tailTrace_1983722 : CollatzResearch.WordTrace tailWord_1983722 prefixEnd_1983722 679068580598928608168023 := by
  unfold tailWord_1983722
  simp only [CollatzResearch.WordTrace]
  refine ⟨18088071329830365397510355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48234856879547641060027613 18088071329830365397510355)
  ·
    refine ⟨27132106994745548096265533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18088071329830365397510355 27132106994745548096265533)
    ·
      refine ⟨10174540123029580536099575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27132106994745548096265533 10174540123029580536099575)
      ·
        refine ⟨15261810184544370804149363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10174540123029580536099575 15261810184544370804149363)
        ·
          refine ⟨22892715276816556206224045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15261810184544370804149363 22892715276816556206224045)
          ·
            refine ⟨8584768228806208577334017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22892715276816556206224045 8584768228806208577334017)
            ·
              refine ⟨6438576171604656433000513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8584768228806208577334017 6438576171604656433000513)
              ·
                refine ⟨4828932128703492324750385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6438576171604656433000513 4828932128703492324750385)
                ·
                  refine ⟨3621699096527619243562789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4828932128703492324750385 3621699096527619243562789)
                  ·
                    refine ⟨679068580598928608168023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3621699096527619243562789 679068580598928608168023)
                    ·
                      rfl

theorem cell22_1983722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_1983722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983722 prefixEnd_1983722 := by exact prefixLift 1983722
  have htrace : WordTrace (prefixWord ++ tailWord_1983722) baseStart_1983722 baseEnd_1983722 := by
    simpa [prefixWord, tailWord_1983722, baseEnd_1983722] using wordTrace_append hprefix tailTrace_1983722
  have hstable : (prefixWord ++ tailWord_1983722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983722).length < 2 ^ (prefixWord ++ tailWord_1983722).sum := by decide
  have hdescent : baseEnd_1983722 < baseStart_1983722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983724 : List Nat := [2, 2, 1, 1, 2, 5, 2, 2, 2, 3]
def baseStart_1983724 : Nat := 118140960795 + 1983724 * 2 ^ 59
def prefixEnd_1983724 : Nat := 4983230072969 + 3 ^ 40 * 1983724 * 2
def baseEnd_1983724 : Nat := 679069265239801269618017

theorem tailTrace_1983724 : CollatzResearch.WordTrace tailWord_1983724 prefixEnd_1983724 679069265239801269618017 := by
  unfold tailWord_1983724
  simp only [CollatzResearch.WordTrace]
  refine ⟨36176179132657107965807113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48234905510209477287742817 36176179132657107965807113)
  ·
    refine ⟨27132134349492830974355335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36176179132657107965807113 27132134349492830974355335)
    ·
      refine ⟨40698201524239246461533003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27132134349492830974355335 40698201524239246461533003)
      ·
        refine ⟨61047302286358869692299505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40698201524239246461533003 61047302286358869692299505)
        ·
          refine ⟨45785476714769152269224629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61047302286358869692299505 45785476714769152269224629)
          ·
            refine ⟨4292388442009608025239809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45785476714769152269224629 4292388442009608025239809)
            ·
              refine ⟨3219291331507206018929857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4292388442009608025239809 3219291331507206018929857)
              ·
                refine ⟨2414468498630404514197393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3219291331507206018929857 2414468498630404514197393)
                ·
                  refine ⟨1810851373972803385648045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2414468498630404514197393 1810851373972803385648045)
                  ·
                    refine ⟨679069265239801269618017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1810851373972803385648045 679069265239801269618017)
                    ·
                      rfl

theorem cell22_1983724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 3].length) (baseStart_1983724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983724 prefixEnd_1983724 := by exact prefixLift 1983724
  have htrace : WordTrace (prefixWord ++ tailWord_1983724) baseStart_1983724 baseEnd_1983724 := by
    simpa [prefixWord, tailWord_1983724, baseEnd_1983724] using wordTrace_append hprefix tailTrace_1983724
  have hstable : (prefixWord ++ tailWord_1983724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983724).length < 2 ^ (prefixWord ++ tailWord_1983724).sum := by decide
  have hdescent : baseEnd_1983724 < baseStart_1983724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983765 : List Nat := [1, 3, 2, 1, 2, 1, 1, 4, 7]
def baseStart_1983765 : Nat := 118140960795 + 1983765 * 2 ^ 59
def prefixEnd_1983765 : Nat := 4983230072969 + 3 ^ 40 * 1983765 * 2
def baseEnd_1983765 : Nat := 226361100125896943114297

theorem tailTrace_1983765 : CollatzResearch.WordTrace tailWord_1983765 prefixEnd_1983765 226361100125896943114297 := by
  unfold tailWord_1983765
  simp only [CollatzResearch.WordTrace]
  refine ⟨72353853658165679933856749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48235902438777119955904499 72353853658165679933856749)
  ·
    refine ⟨27132695121812129975196281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72353853658165679933856749 27132695121812129975196281)
    ·
      refine ⟨20349521341359097481397211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27132695121812129975196281 20349521341359097481397211)
      ·
        refine ⟨30524282012038646222095817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20349521341359097481397211 30524282012038646222095817)
        ·
          refine ⟨22893211509028984666571863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30524282012038646222095817 22893211509028984666571863)
          ·
            refine ⟨34339817263543476999857795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22893211509028984666571863 34339817263543476999857795)
            ·
              refine ⟨51509725895315215499786693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34339817263543476999857795 51509725895315215499786693)
              ·
                refine ⟨9658073605371602906210005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51509725895315215499786693 9658073605371602906210005)
                ·
                  refine ⟨226361100125896943114297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9658073605371602906210005 226361100125896943114297)
                  ·
                    rfl

theorem cell22_1983765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_1983765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983765 prefixEnd_1983765 := by exact prefixLift 1983765
  have htrace : WordTrace (prefixWord ++ tailWord_1983765) baseStart_1983765 baseEnd_1983765 := by
    simpa [prefixWord, tailWord_1983765, baseEnd_1983765] using wordTrace_append hprefix tailTrace_1983765
  have hstable : (prefixWord ++ tailWord_1983765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983765).length < 2 ^ (prefixWord ++ tailWord_1983765).sum := by decide
  have hdescent : baseEnd_1983765 < baseStart_1983765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983786 : List Nat := [3, 1, 4, 2, 1, 2, 2, 1, 3, 3]
def baseStart_1983786 : Nat := 118140960795 + 1983786 * 2 ^ 59
def prefixEnd_1983786 : Nat := 4983230072969 + 3 ^ 40 * 1983786 * 2
def baseEnd_1983786 : Nat := 679090489106853774567827

theorem tailTrace_1983786 : CollatzResearch.WordTrace tailWord_1983786 prefixEnd_1983786 679090489106853774567827 := by
  unfold tailWord_1983786
  simp only [CollatzResearch.WordTrace]
  refine ⟨18088654897772400130092803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48236413060726400346914141 18088654897772400130092803)
  ·
    refine ⟨27132982346658600195139205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18088654897772400130092803 27132982346658600195139205)
    ·
      refine ⟨5087434189998487536588601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27132982346658600195139205 5087434189998487536588601)
      ·
        refine ⟨3815575642498865652441451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5087434189998487536588601 3815575642498865652441451)
        ·
          refine ⟨5723363463748298478662177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3815575642498865652441451 5723363463748298478662177)
          ·
            refine ⟨4292522597811223858996633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5723363463748298478662177 4292522597811223858996633)
            ·
              refine ⟨3219391948358417894247475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4292522597811223858996633 3219391948358417894247475)
              ·
                refine ⟨4829087922537626841371213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3219391948358417894247475 4829087922537626841371213)
                ·
                  refine ⟨1810907970951610065514205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4829087922537626841371213 1810907970951610065514205)
                  ·
                    refine ⟨679090489106853774567827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1810907970951610065514205 679090489106853774567827)
                    ·
                      rfl

theorem cell22_1983786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_1983786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983786 prefixEnd_1983786 := by exact prefixLift 1983786
  have htrace : WordTrace (prefixWord ++ tailWord_1983786) baseStart_1983786 baseEnd_1983786 := by
    simpa [prefixWord, tailWord_1983786, baseEnd_1983786] using wordTrace_append hprefix tailTrace_1983786
  have hstable : (prefixWord ++ tailWord_1983786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983786).length < 2 ^ (prefixWord ++ tailWord_1983786).sum := by decide
  have hdescent : baseEnd_1983786 < baseStart_1983786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983797 : List Nat := [1, 3, 3, 1, 2, 2, 2, 1, 2, 5]
def baseStart_1983797 : Nat := 118140960795 + 1983797 * 2 ^ 59
def prefixEnd_1983797 : Nat := 4983230072969 + 3 ^ 40 * 1983797 * 2
def baseEnd_1983797 : Nat := 679094254631653412542793

theorem tailTrace_1983797 : CollatzResearch.WordTrace tailWord_1983797 prefixEnd_1983797 679094254631653412542793 := by
  unfold tailWord_1983797
  simp only [CollatzResearch.WordTrace]
  refine ⟨72355020794049749399021645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48236680529366499599347763 72355020794049749399021645)
  ·
    refine ⟨27133132797768656024633117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72355020794049749399021645 27133132797768656024633117)
    ·
      refine ⟨10174924799163246009237419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27133132797768656024633117 10174924799163246009237419)
      ·
        refine ⟨15262387198744869013856129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10174924799163246009237419 15262387198744869013856129)
        ·
          refine ⟨11446790399058651760392097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15262387198744869013856129 11446790399058651760392097)
          ·
            refine ⟨8585092799293988820294073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11446790399058651760392097 8585092799293988820294073)
            ·
              refine ⟨6438819599470491615220555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8585092799293988820294073 6438819599470491615220555)
              ·
                refine ⟨9658229399205737422830833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6438819599470491615220555 9658229399205737422830833)
                ·
                  refine ⟨7243672049404303067123125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9658229399205737422830833 7243672049404303067123125)
                  ·
                    refine ⟨679094254631653412542793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7243672049404303067123125 679094254631653412542793)
                    ·
                      rfl

theorem cell22_1983797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_1983797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983797 prefixEnd_1983797 := by exact prefixLift 1983797
  have htrace : WordTrace (prefixWord ++ tailWord_1983797) baseStart_1983797 baseEnd_1983797 := by
    simpa [prefixWord, tailWord_1983797, baseEnd_1983797] using wordTrace_append hprefix tailTrace_1983797
  have hstable : (prefixWord ++ tailWord_1983797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983797).length < 2 ^ (prefixWord ++ tailWord_1983797).sum := by decide
  have hdescent : baseEnd_1983797 < baseStart_1983797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983829 : List Nat := [1, 3, 2, 2, 3, 1, 2, 3, 1, 4]
def baseStart_1983829 : Nat := 118140960795 + 1983829 * 2 ^ 59
def prefixEnd_1983829 : Nat := 4983230072969 + 3 ^ 40 * 1983829 * 2
def baseEnd_1983829 : Nat := 679105208885615995742695

theorem tailTrace_1983829 : CollatzResearch.WordTrace tailWord_1983829 prefixEnd_1983829 679105208885615995742695 := by
  unfold tailWord_1983829
  simp only [CollatzResearch.WordTrace]
  refine ⟨72356187929933818864186541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48237458619955879242791027 72356187929933818864186541)
  ·
    refine ⟨27133570473725182074069953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72356187929933818864186541 27133570473725182074069953)
    ·
      refine ⟨20350177855293886555552465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27133570473725182074069953 20350177855293886555552465)
      ·
        refine ⟨15262633391470414916664349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20350177855293886555552465 15262633391470414916664349)
        ·
          refine ⟨5723487521801405593749131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15262633391470414916664349 5723487521801405593749131)
          ·
            refine ⟨8585231282702108390623697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5723487521801405593749131 8585231282702108390623697)
            ·
              refine ⟨6438923462026581292967773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8585231282702108390623697 6438923462026581292967773)
              ·
                refine ⟨2414596298259967984862915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6438923462026581292967773 2414596298259967984862915)
                ·
                  refine ⟨3621894447389951977294373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2414596298259967984862915 3621894447389951977294373)
                  ·
                    refine ⟨679105208885615995742695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3621894447389951977294373 679105208885615995742695)
                    ·
                      rfl

theorem cell22_1983829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_1983829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983829 prefixEnd_1983829 := by exact prefixLift 1983829
  have htrace : WordTrace (prefixWord ++ tailWord_1983829) baseStart_1983829 baseEnd_1983829 := by
    simpa [prefixWord, tailWord_1983829, baseEnd_1983829] using wordTrace_append hprefix tailTrace_1983829
  have hstable : (prefixWord ++ tailWord_1983829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983829).length < 2 ^ (prefixWord ++ tailWord_1983829).sum := by decide
  have hdescent : baseEnd_1983829 < baseStart_1983829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983837 : List Nat := [1, 4, 5, 1, 2, 1, 1, 1, 3, 3]
def baseStart_1983837 : Nat := 118140960795 + 1983837 * 2 ^ 59
def prefixEnd_1983837 : Nat := 4983230072969 + 3 ^ 40 * 1983837 * 2
def baseEnd_1983837 : Nat := 679107947449106641542671

theorem tailTrace_1983837 : CollatzResearch.WordTrace tailWord_1983837 prefixEnd_1983837 679107947449106641542671 := by
  unfold tailWord_1983837
  simp only [CollatzResearch.WordTrace]
  refine ⟨72356479713904836230477765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48237653142603224153651843 72356479713904836230477765)
  ·
    refine ⟨13566839946357156793214581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72356479713904836230477765 13566839946357156793214581)
    ·
      refine ⟨1271891244970983449363867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13566839946357156793214581 1271891244970983449363867)
      ·
        refine ⟨1907836867456475174045801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1271891244970983449363867 1907836867456475174045801)
        ·
          refine ⟨1430877650592356380534351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1907836867456475174045801 1430877650592356380534351)
          ·
            refine ⟨2146316475888534570801527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1430877650592356380534351 2146316475888534570801527)
            ·
              refine ⟨3219474713832801856202291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2146316475888534570801527 3219474713832801856202291)
              ·
                refine ⟨4829212070749202784303437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3219474713832801856202291 4829212070749202784303437)
                ·
                  refine ⟨1810954526530951044113789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4829212070749202784303437 1810954526530951044113789)
                  ·
                    refine ⟨679107947449106641542671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1810954526530951044113789 679107947449106641542671)
                    ·
                      rfl

theorem cell22_1983837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_1983837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983837 prefixEnd_1983837 := by exact prefixLift 1983837
  have htrace : WordTrace (prefixWord ++ tailWord_1983837) baseStart_1983837 baseEnd_1983837 := by
    simpa [prefixWord, tailWord_1983837, baseEnd_1983837] using wordTrace_append hprefix tailTrace_1983837
  have hstable : (prefixWord ++ tailWord_1983837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983837).length < 2 ^ (prefixWord ++ tailWord_1983837).sum := by decide
  have hdescent : baseEnd_1983837 < baseStart_1983837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983844 : List Nat := [2, 3, 1, 1, 3, 4, 1, 1, 6]
def baseStart_1983844 : Nat := 118140960795 + 1983844 * 2 ^ 59
def prefixEnd_1983844 : Nat := 4983230072969 + 3 ^ 40 * 1983844 * 2
def baseEnd_1983844 : Nat := 226370114564053652205883

theorem tailTrace_1983844 : CollatzResearch.WordTrace tailWord_1983844 prefixEnd_1983844 226370114564053652205883 := by
  unfold tailWord_1983844
  simp only [CollatzResearch.WordTrace]
  refine ⟨36178367512439738212991293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48237823349919650950655057 36178367512439738212991293)
  ·
    refine ⟨13566887817164901829871735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36178367512439738212991293 13566887817164901829871735)
    ·
      refine ⟨20350331725747352744807603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13566887817164901829871735 20350331725747352744807603)
      ·
        refine ⟨30525497588621029117211405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20350331725747352744807603 30525497588621029117211405)
        ·
          refine ⟨11447061595732885918954277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30525497588621029117211405 11447061595732885918954277)
          ·
            refine ⟨2146324049199916109803927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11447061595732885918954277 2146324049199916109803927)
            ·
              refine ⟨3219486073799874164705891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2146324049199916109803927 3219486073799874164705891)
              ·
                refine ⟨4829229110699811247058837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3219486073799874164705891 4829229110699811247058837)
                ·
                  refine ⟨226370114564053652205883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4829229110699811247058837 226370114564053652205883)
                  ·
                    rfl

theorem cell22_1983844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_1983844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983844 prefixEnd_1983844 := by exact prefixLift 1983844
  have htrace : WordTrace (prefixWord ++ tailWord_1983844) baseStart_1983844 baseEnd_1983844 := by
    simpa [prefixWord, tailWord_1983844, baseEnd_1983844] using wordTrace_append hprefix tailTrace_1983844
  have hstable : (prefixWord ++ tailWord_1983844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983844).length < 2 ^ (prefixWord ++ tailWord_1983844).sum := by decide
  have hdescent : baseEnd_1983844 < baseStart_1983844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983904 : List Nat := [2, 1, 1, 4, 1, 2, 2, 3, 3, 3]
def baseStart_1983904 : Nat := 118140960795 + 1983904 * 2 ^ 59
def prefixEnd_1983904 : Nat := 4983230072969 + 3 ^ 40 * 1983904 * 2
def baseEnd_1983904 : Nat := 679130882918340800117465

theorem tailTrace_1983904 : CollatzResearch.WordTrace tailWord_1983904 prefixEnd_1983904 679130882918340800117465 := by
  unfold tailWord_1983904
  simp only [CollatzResearch.WordTrace]
  refine ⟨36179461702331053336583383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48239282269774737782111177 36179461702331053336583383)
  ·
    refine ⟨54269192553496580004875075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36179461702331053336583383 54269192553496580004875075)
    ·
      refine ⟨81403788830244870007312613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54269192553496580004875075 81403788830244870007312613)
      ·
        refine ⟨15263210405670913126371115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81403788830244870007312613 15263210405670913126371115)
        ·
          refine ⟨22894815608506369689556673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15263210405670913126371115 22894815608506369689556673)
          ·
            refine ⟨17171111706379777267167505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22894815608506369689556673 17171111706379777267167505)
            ·
              refine ⟨12878333779784832950375629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17171111706379777267167505 12878333779784832950375629)
              ·
                refine ⟨4829375167419312356390861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12878333779784832950375629 4829375167419312356390861)
                ·
                  refine ⟨1811015687782242133646573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4829375167419312356390861 1811015687782242133646573)
                  ·
                    refine ⟨679130882918340800117465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1811015687782242133646573 679130882918340800117465)
                    ·
                      rfl

theorem cell22_1983904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 3, 3].length) (baseStart_1983904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983904 prefixEnd_1983904 := by exact prefixLift 1983904
  have htrace : WordTrace (prefixWord ++ tailWord_1983904) baseStart_1983904 baseEnd_1983904 := by
    simpa [prefixWord, tailWord_1983904, baseEnd_1983904] using wordTrace_append hprefix tailTrace_1983904
  have hstable : (prefixWord ++ tailWord_1983904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983904).length < 2 ^ (prefixWord ++ tailWord_1983904).sum := by decide
  have hdescent : baseEnd_1983904 < baseStart_1983904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983994 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 6, 3]
def baseStart_1983994 : Nat := 118140960795 + 1983994 * 2 ^ 59
def prefixEnd_1983994 : Nat := 4983230072969 + 3 ^ 40 * 1983994 * 2
def baseEnd_1983994 : Nat := 679161691757610565367189

theorem tailTrace_1983994 : CollatzResearch.WordTrace tailWord_1983994 prefixEnd_1983994 679161691757610565367189 := by
  unfold tailWord_1983994
  simp only [CollatzResearch.WordTrace]
  refine ⟨18090551493584013010985759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48241470649557368029295357 18090551493584013010985759)
  ·
    refine ⟨27135827240376019516478639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18090551493584013010985759 27135827240376019516478639)
    ·
      refine ⟨40703740860564029274717959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27135827240376019516478639 40703740860564029274717959)
      ·
        refine ⟨61055611290846043912076939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40703740860564029274717959 61055611290846043912076939)
        ·
          refine ⟨91583416936269065868115409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61055611290846043912076939 91583416936269065868115409)
          ·
            refine ⟨68687562702201799401086557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91583416936269065868115409 68687562702201799401086557)
            ·
              refine ⟨25757836013325674775407459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68687562702201799401086557 25757836013325674775407459)
              ·
                refine ⟨38636754019988512163111189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25757836013325674775407459 38636754019988512163111189)
                ·
                  refine ⟨1811097844686961507645837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38636754019988512163111189 1811097844686961507645837)
                  ·
                    refine ⟨679161691757610565367189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1811097844686961507645837 679161691757610565367189)
                    ·
                      rfl

theorem cell22_1983994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 6, 3].length) (baseStart_1983994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983994 prefixEnd_1983994 := by exact prefixLift 1983994
  have htrace : WordTrace (prefixWord ++ tailWord_1983994) baseStart_1983994 baseEnd_1983994 := by
    simpa [prefixWord, tailWord_1983994, baseEnd_1983994] using wordTrace_append hprefix tailTrace_1983994
  have hstable : (prefixWord ++ tailWord_1983994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983994).length < 2 ^ (prefixWord ++ tailWord_1983994).sum := by decide
  have hdescent : baseEnd_1983994 < baseStart_1983994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1983996 : List Nat := [2, 2, 2, 1, 2, 1, 5, 3, 4]
def baseStart_1983996 : Nat := 118140960795 + 1983996 * 2 ^ 59
def prefixEnd_1983996 : Nat := 4983230072969 + 3 ^ 40 * 1983996 * 2
def baseEnd_1983996 : Nat := 226387458799494408939061

theorem tailTrace_1983996 : CollatzResearch.WordTrace tailWord_1983996 prefixEnd_1983996 226387458799494408939061 := by
  unfold tailWord_1983996
  simp only [CollatzResearch.WordTrace]
  refine ⟨36181139460164403192757921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48241519280219204257010561 36181139460164403192757921)
  ·
    refine ⟨27135854595123302394568441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36181139460164403192757921 27135854595123302394568441)
    ·
      refine ⟨20351890946342476795926331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27135854595123302394568441 20351890946342476795926331)
      ·
        refine ⟨30527836419513715193889497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20351890946342476795926331 30527836419513715193889497)
        ·
          refine ⟨22895877314635286395417123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30527836419513715193889497 22895877314635286395417123)
          ·
            refine ⟨34343815971952929593125685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22895877314635286395417123 34343815971952929593125685)
            ·
              refine ⟨3219732747370587149355533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34343815971952929593125685 3219732747370587149355533)
              ·
                refine ⟨1207399780263970181008325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3219732747370587149355533 1207399780263970181008325)
                ·
                  refine ⟨226387458799494408939061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1207399780263970181008325 226387458799494408939061)
                  ·
                    rfl

theorem cell22_1983996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3, 4].length) (baseStart_1983996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1983996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1983996 prefixEnd_1983996 := by exact prefixLift 1983996
  have htrace : WordTrace (prefixWord ++ tailWord_1983996) baseStart_1983996 baseEnd_1983996 := by
    simpa [prefixWord, tailWord_1983996, baseEnd_1983996] using wordTrace_append hprefix tailTrace_1983996
  have hstable : (prefixWord ++ tailWord_1983996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1983996).length < 2 ^ (prefixWord ++ tailWord_1983996).sum := by decide
  have hdescent : baseEnd_1983996 < baseStart_1983996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1983996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984006 : List Nat := [6, 2, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_1984006 : Nat := 118140960795 + 1984006 * 2 ^ 59
def prefixEnd_1984006 : Nat := 4983230072969 + 3 ^ 40 * 1984006 * 2
def baseEnd_1984006 : Nat := 679165799602846534067153

theorem tailTrace_1984006 : CollatzResearch.WordTrace tailWord_1984006 prefixEnd_1984006 679165799602846534067153 := by
  unfold tailWord_1984006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2261332614071643065418121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48241762433528385395586581 2261332614071643065418121)
  ·
    refine ⟨1695999460553732299063591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2261332614071643065418121 1695999460553732299063591)
    ·
      refine ⟨2543999190830598448595387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1695999460553732299063591 2543999190830598448595387)
      ·
        refine ⟨3815998786245897672893081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2543999190830598448595387 3815998786245897672893081)
        ·
          refine ⟨2861999089684423254669811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3815998786245897672893081 2861999089684423254669811)
          ·
            refine ⟨4292998634526634882004717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2861999089684423254669811 4292998634526634882004717)
            ·
              refine ⟨1609874487947488080751769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4292998634526634882004717 1609874487947488080751769)
              ·
                refine ⟨1207405865960616060563827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1609874487947488080751769 1207405865960616060563827)
                ·
                  refine ⟨1811108798940924090845741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1207405865960616060563827 1811108798940924090845741)
                  ·
                    refine ⟨679165799602846534067153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1811108798940924090845741 679165799602846534067153)
                    ·
                      rfl

theorem cell22_1984006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_1984006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984006 prefixEnd_1984006 := by exact prefixLift 1984006
  have htrace : WordTrace (prefixWord ++ tailWord_1984006) baseStart_1984006 baseEnd_1984006 := by
    simpa [prefixWord, tailWord_1984006, baseEnd_1984006] using wordTrace_append hprefix tailTrace_1984006
  have hstable : (prefixWord ++ tailWord_1984006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984006).length < 2 ^ (prefixWord ++ tailWord_1984006).sum := by decide
  have hdescent : baseEnd_1984006 < baseStart_1984006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984009 : List Nat := [1, 2, 1, 1, 3, 1, 5, 2, 2, 4]
def baseStart_1984009 : Nat := 118140960795 + 1984009 * 2 ^ 59
def prefixEnd_1984009 : Nat := 4983230072969 + 3 ^ 40 * 1984009 * 2
def baseEnd_1984009 : Nat := 679166826564155526242143

theorem tailTrace_1984009 : CollatzResearch.WordTrace tailWord_1984009 prefixEnd_1984009 679166826564155526242143 := by
  unfold tailWord_1984009
  simp only [CollatzResearch.WordTrace]
  refine ⟨72362753069281709605739081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48241835379521139737159387 72362753069281709605739081)
  ·
    refine ⟨54272064801961282204304311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72362753069281709605739081 54272064801961282204304311)
    ·
      refine ⟨81408097202941923306456467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54272064801961282204304311 81408097202941923306456467)
      ·
        refine ⟨122112145804412884959684701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81408097202941923306456467 122112145804412884959684701)
        ·
          refine ⟨45792054676654831859881763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122112145804412884959684701 45792054676654831859881763)
          ·
            refine ⟨68688082014982247789822645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45792054676654831859881763 68688082014982247789822645)
            ·
              refine ⟨6439507688904585730295873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68688082014982247789822645 6439507688904585730295873)
              ·
                refine ⟨4829630766678439297721905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6439507688904585730295873 4829630766678439297721905)
                ·
                  refine ⟨3622223075008829473291429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4829630766678439297721905 3622223075008829473291429)
                  ·
                    refine ⟨679166826564155526242143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3622223075008829473291429 679166826564155526242143)
                    ·
                      rfl

theorem cell22_1984009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 2, 4].length) (baseStart_1984009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984009 prefixEnd_1984009 := by exact prefixLift 1984009
  have htrace : WordTrace (prefixWord ++ tailWord_1984009) baseStart_1984009 baseEnd_1984009 := by
    simpa [prefixWord, tailWord_1984009, baseEnd_1984009] using wordTrace_append hprefix tailTrace_1984009
  have hstable : (prefixWord ++ tailWord_1984009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984009).length < 2 ^ (prefixWord ++ tailWord_1984009).sum := by decide
  have hdescent : baseEnd_1984009 < baseStart_1984009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984161 : List Nat := [1, 2, 3, 3, 2, 1, 2, 1, 1, 6]
def baseStart_1984161 : Nat := 118140960795 + 1984161 * 2 ^ 59
def prefixEnd_1984161 : Nat := 4983230072969 + 3 ^ 40 * 1984161 * 2
def baseEnd_1984161 : Nat := 679218859270477796441677

theorem tailTrace_1984161 : CollatzResearch.WordTrace tailWord_1984161 prefixEnd_1984161 679218859270477796441677 := by
  unfold tailWord_1984161
  simp only [CollatzResearch.WordTrace]
  refine ⟨72368296964731039565272337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48245531309820693043514891 72368296964731039565272337)
  ·
    refine ⟨54276222723548279673954253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72368296964731039565272337 54276222723548279673954253)
    ·
      refine ⟨20353583521330604877732845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54276222723548279673954253 20353583521330604877732845)
      ·
        refine ⟨7632593820498976829149817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20353583521330604877732845 7632593820498976829149817)
        ·
          refine ⟨5724445365374232621862363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7632593820498976829149817 5724445365374232621862363)
          ·
            refine ⟨8586668048061348932793545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5724445365374232621862363 8586668048061348932793545)
            ·
              refine ⟨6440001036046011699595159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8586668048061348932793545 6440001036046011699595159)
              ·
                refine ⟨9660001554069017549392739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6440001036046011699595159 9660001554069017549392739)
                ·
                  refine ⟨14490002331103526324089109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9660001554069017549392739 14490002331103526324089109)
                  ·
                    refine ⟨679218859270477796441677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14490002331103526324089109 679218859270477796441677)
                    ·
                      rfl

theorem cell22_1984161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_1984161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984161 prefixEnd_1984161 := by exact prefixLift 1984161
  have htrace : WordTrace (prefixWord ++ tailWord_1984161) baseStart_1984161 baseEnd_1984161 := by
    simpa [prefixWord, tailWord_1984161, baseEnd_1984161] using wordTrace_append hprefix tailTrace_1984161
  have hstable : (prefixWord ++ tailWord_1984161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984161).length < 2 ^ (prefixWord ++ tailWord_1984161).sum := by decide
  have hdescent : baseEnd_1984161 < baseStart_1984161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984238 : List Nat := [4, 1, 2, 1, 1, 2, 4, 2, 5]
def baseStart_1984238 : Nat := 118140960795 + 1984238 * 2 ^ 59
def prefixEnd_1984238 : Nat := 4983230072969 + 3 ^ 40 * 1984238 * 2
def baseEnd_1984238 : Nat := 226415072648025087422147

theorem tailTrace_1984238 : CollatzResearch.WordTrace tailWord_1984238 prefixEnd_1984238 226415072648025087422147 := by
  unfold tailWord_1984238
  simp only [CollatzResearch.WordTrace]
  refine ⟨9046388173181510214478171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48247403590301387810550245 9046388173181510214478171)
  ·
    refine ⟨13569582259772265321717257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9046388173181510214478171 13569582259772265321717257)
    ·
      refine ⟨10177186694829198991287943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13569582259772265321717257 10177186694829198991287943)
      ·
        refine ⟨15265780042243798486931915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10177186694829198991287943 15265780042243798486931915)
        ·
          refine ⟨22898670063365697730397873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15265780042243798486931915 22898670063365697730397873)
          ·
            refine ⟨17174002547524273297798405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22898670063365697730397873 17174002547524273297798405)
            ·
              refine ⟨3220125477660801243337201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17174002547524273297798405 3220125477660801243337201)
              ·
                refine ⟨2415094108245600932502901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3220125477660801243337201 2415094108245600932502901)
                ·
                  refine ⟨226415072648025087422147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2415094108245600932502901 226415072648025087422147)
                  ·
                    rfl

theorem cell22_1984238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_1984238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984238 prefixEnd_1984238 := by exact prefixLift 1984238
  have htrace : WordTrace (prefixWord ++ tailWord_1984238) baseStart_1984238 baseEnd_1984238 := by
    simpa [prefixWord, tailWord_1984238, baseEnd_1984238] using wordTrace_append hprefix tailTrace_1984238
  have hstable : (prefixWord ++ tailWord_1984238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984238).length < 2 ^ (prefixWord ++ tailWord_1984238).sum := by decide
  have hdescent : baseEnd_1984238 < baseStart_1984238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984266 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 8]
def baseStart_1984266 : Nat := 118140960795 + 1984266 * 2 ^ 59
def prefixEnd_1984266 : Nat := 4983230072969 + 3 ^ 40 * 1984266 * 2
def baseEnd_1984266 : Nat := 226418267638764174188785

theorem tailTrace_1984266 : CollatzResearch.WordTrace tailWord_1984266 prefixEnd_1984266 226418267638764174188785 := by
  unfold tailWord_1984266
  simp only [CollatzResearch.WordTrace]
  refine ⟨18093031657337660624461163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48248084419567094998563101 18093031657337660624461163)
  ·
    refine ⟨27139547486006490936691745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18093031657337660624461163 27139547486006490936691745)
    ·
      refine ⟨20354660614504868202518809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27139547486006490936691745 20354660614504868202518809)
      ·
        refine ⟨15265995460878651151889107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20354660614504868202518809 15265995460878651151889107)
        ·
          refine ⟨22898993191317976727833661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15265995460878651151889107 22898993191317976727833661)
          ·
            refine ⟨8587122446744241272937623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22898993191317976727833661 8587122446744241272937623)
            ·
              refine ⟨12880683670116361909406435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8587122446744241272937623 12880683670116361909406435)
              ·
                refine ⟨19321025505174542864109653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12880683670116361909406435 19321025505174542864109653)
                ·
                  refine ⟨226418267638764174188785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19321025505174542864109653 226418267638764174188785)
                  ·
                    rfl

theorem cell22_1984266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_1984266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984266 prefixEnd_1984266 := by exact prefixLift 1984266
  have htrace : WordTrace (prefixWord ++ tailWord_1984266) baseStart_1984266 baseEnd_1984266 := by
    simpa [prefixWord, tailWord_1984266, baseEnd_1984266] using wordTrace_append hprefix tailTrace_1984266
  have hstable : (prefixWord ++ tailWord_1984266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984266).length < 2 ^ (prefixWord ++ tailWord_1984266).sum := by decide
  have hdescent : baseEnd_1984266 < baseStart_1984266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984328 : List Nat := [2, 1, 3, 1, 1, 4, 4, 6]
def baseStart_1984328 : Nat := 118140960795 + 1984328 * 2 ^ 59
def prefixEnd_1984328 : Nat := 4983230072969 + 3 ^ 40 * 1984328 * 2
def baseEnd_1984328 : Nat := 75475114087038336390685

theorem tailTrace_1984328 : CollatzResearch.WordTrace tailWord_1984328 prefixEnd_1984328 75475114087038336390685 := by
  unfold tailWord_1984328
  simp only [CollatzResearch.WordTrace]
  refine ⟨36187193977563013543300819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48249591970084018057734425 36187193977563013543300819)
  ·
    refine ⟨54280790966344520314951229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36187193977563013543300819 54280790966344520314951229)
    ·
      refine ⟨20355296612379195118106711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54280790966344520314951229 20355296612379195118106711)
      ·
        refine ⟨30532944918568792677160067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20355296612379195118106711 30532944918568792677160067)
        ·
          refine ⟨45799417377853189015740101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30532944918568792677160067 45799417377853189015740101)
          ·
            refine ⟨8587390758347472940451269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45799417377853189015740101 8587390758347472940451269)
            ·
              refine ⟨1610135767190151176334613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8587390758347472940451269 1610135767190151176334613)
              ·
                refine ⟨75475114087038336390685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1610135767190151176334613 75475114087038336390685)
                ·
                  rfl

theorem cell22_1984328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 6].length) (baseStart_1984328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984328 prefixEnd_1984328 := by exact prefixLift 1984328
  have htrace : WordTrace (prefixWord ++ tailWord_1984328) baseStart_1984328 baseEnd_1984328 := by
    simpa [prefixWord, tailWord_1984328, baseEnd_1984328] using wordTrace_append hprefix tailTrace_1984328
  have hstable : (prefixWord ++ tailWord_1984328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984328).length < 2 ^ (prefixWord ++ tailWord_1984328).sum := by decide
  have hdescent : baseEnd_1984328 < baseStart_1984328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984371 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 1, 7]
def baseStart_1984371 : Nat := 118140960795 + 1984371 * 2 ^ 59
def prefixEnd_1984371 : Nat := 4983230072969 + 3 ^ 40 * 1984371 * 2
def baseEnd_1984371 : Nat := 679290746562107248691033

theorem tailTrace_1984371 : CollatzResearch.WordTrace tailWord_1984371 prefixEnd_1984371 679290746562107248691033 := by
  unfold tailWord_1984371
  simp only [CollatzResearch.WordTrace]
  refine ⟨72375956293970245430416967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48250637529313496953611311 72375956293970245430416967)
  ·
    refine ⟨108563934440955368145625451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72375956293970245430416967 108563934440955368145625451)
    ·
      refine ⟨162845901661433052218438177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108563934440955368145625451 162845901661433052218438177)
      ·
        refine ⟨122134426246074789163828633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162845901661433052218438177 122134426246074789163828633)
        ·
          refine ⟨91600819684556091872871475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122134426246074789163828633 91600819684556091872871475)
          ·
            refine ⟨137401229526834137809307213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91600819684556091872871475 137401229526834137809307213)
            ·
              refine ⟨51525461072562801678490205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 137401229526834137809307213 51525461072562801678490205)
              ·
                refine ⟨19322047902211050629433827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51525461072562801678490205 19322047902211050629433827)
                ·
                  refine ⟨28983071853316575944150741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19322047902211050629433827 28983071853316575944150741)
                  ·
                    refine ⟨679290746562107248691033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28983071853316575944150741 679290746562107248691033)
                    ·
                      rfl

theorem cell22_1984371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 7].length) (baseStart_1984371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984371 prefixEnd_1984371 := by exact prefixLift 1984371
  have htrace : WordTrace (prefixWord ++ tailWord_1984371) baseStart_1984371 baseEnd_1984371 := by
    simpa [prefixWord, tailWord_1984371, baseEnd_1984371] using wordTrace_append hprefix tailTrace_1984371
  have hstable : (prefixWord ++ tailWord_1984371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984371).length < 2 ^ (prefixWord ++ tailWord_1984371).sum := by decide
  have hdescent : baseEnd_1984371 < baseStart_1984371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984448 : List Nat := [2, 1, 1, 2, 3, 2, 3, 1, 1, 6]
def baseStart_1984448 : Nat := 118140960795 + 1984448 * 2 ^ 59
def prefixEnd_1984448 : Nat := 4983230072969 + 3 ^ 40 * 1984448 * 2
def baseEnd_1984448 : Nat := 679317105235704714515797

theorem tailTrace_1984448 : CollatzResearch.WordTrace tailWord_1984448 prefixEnd_1984448 679317105235704714515797 := by
  unfold tailWord_1984448
  simp only [CollatzResearch.WordTrace]
  refine ⟨36189382357345643790484999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48252509809794191720646665 36189382357345643790484999)
  ·
    refine ⟨54284073536018465685727499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36189382357345643790484999 54284073536018465685727499)
    ·
      refine ⟨81426110304027698528591249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54284073536018465685727499 81426110304027698528591249)
      ·
        refine ⟨61069582728020773896443437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81426110304027698528591249 61069582728020773896443437)
        ·
          refine ⟨22901093523007790211166289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61069582728020773896443437 22901093523007790211166289)
          ·
            refine ⟨17175820142255842658374717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22901093523007790211166289 17175820142255842658374717)
            ·
              refine ⟨6440932553345940996890519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17175820142255842658374717 6440932553345940996890519)
              ·
                refine ⟨9661398830018911495335779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6440932553345940996890519 9661398830018911495335779)
                ·
                  refine ⟨14492098245028367243003669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9661398830018911495335779 14492098245028367243003669)
                  ·
                    refine ⟨679317105235704714515797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14492098245028367243003669 679317105235704714515797)
                    ·
                      rfl

theorem cell22_1984448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 1, 6].length) (baseStart_1984448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984448 prefixEnd_1984448 := by exact prefixLift 1984448
  have htrace : WordTrace (prefixWord ++ tailWord_1984448) baseStart_1984448 baseEnd_1984448 := by
    simpa [prefixWord, tailWord_1984448, baseEnd_1984448] using wordTrace_append hprefix tailTrace_1984448
  have hstable : (prefixWord ++ tailWord_1984448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984448).length < 2 ^ (prefixWord ++ tailWord_1984448).sum := by decide
  have hdescent : baseEnd_1984448 < baseStart_1984448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984495 : List Nat := [1, 1, 2, 1, 4, 2, 1, 4, 3, 3]
def baseStart_1984495 : Nat := 118140960795 + 1984495 * 2 ^ 59
def prefixEnd_1984495 : Nat := 4983230072969 + 3 ^ 40 * 1984495 * 2
def baseEnd_1984495 : Nat := 679333194296212258590653

theorem tailTrace_1984495 : CollatzResearch.WordTrace tailWord_1984495 prefixEnd_1984495 679333194296212258590653 := by
  unfold tailWord_1984495
  simp only [CollatzResearch.WordTrace]
  refine ⟨72380478945521014607930939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48253652630347343071953959 72380478945521014607930939)
  ·
    refine ⟨108570718418281521911896409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72380478945521014607930939 108570718418281521911896409)
    ·
      refine ⟨81428038813711141433922307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108570718418281521911896409 81428038813711141433922307)
      ·
        refine ⟨122142058220566712150883461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81428038813711141433922307 122142058220566712150883461)
        ·
          refine ⟨22901635916356258528290649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 122142058220566712150883461 22901635916356258528290649)
          ·
            refine ⟨17176226937267193896217987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22901635916356258528290649 17176226937267193896217987)
            ·
              refine ⟨25764340405900790844326981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17176226937267193896217987 25764340405900790844326981)
              ·
                refine ⟨4830813826106398283311309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25764340405900790844326981 4830813826106398283311309)
                ·
                  refine ⟨1811555184789899356241741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4830813826106398283311309 1811555184789899356241741)
                  ·
                    refine ⟨679333194296212258590653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1811555184789899356241741 679333194296212258590653)
                    ·
                      rfl

theorem cell22_1984495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3, 3].length) (baseStart_1984495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984495 prefixEnd_1984495 := by exact prefixLift 1984495
  have htrace : WordTrace (prefixWord ++ tailWord_1984495) baseStart_1984495 baseEnd_1984495 := by
    simpa [prefixWord, tailWord_1984495, baseEnd_1984495] using wordTrace_append hprefix tailTrace_1984495
  have hstable : (prefixWord ++ tailWord_1984495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984495).length < 2 ^ (prefixWord ++ tailWord_1984495).sum := by decide
  have hdescent : baseEnd_1984495 < baseStart_1984495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984497 : List Nat := [1, 2, 2, 2, 5, 2, 2, 6]
def baseStart_1984497 : Nat := 118140960795 + 1984497 * 2 ^ 59
def prefixEnd_1984497 : Nat := 4983230072969 + 3 ^ 40 * 1984497 * 2
def baseEnd_1984497 : Nat := 75481542104120546671183

theorem tailTrace_1984497 : CollatzResearch.WordTrace tailWord_1984497 prefixEnd_1984497 75481542104120546671183 := by
  unfold tailWord_1984497
  simp only [CollatzResearch.WordTrace]
  refine ⟨72380551891513768949503745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48253701261009179299669163 72380551891513768949503745)
  ·
    refine ⟨54285413918635326712127809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72380551891513768949503745 54285413918635326712127809)
    ·
      refine ⟨40714060438976495034095857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54285413918635326712127809 40714060438976495034095857)
      ·
        refine ⟨30535545329232371275571893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40714060438976495034095857 30535545329232371275571893)
        ·
          refine ⟨2862707374615534807084865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30535545329232371275571893 2862707374615534807084865)
          ·
            refine ⟨2147030530961651105313649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2862707374615534807084865 2147030530961651105313649)
            ·
              refine ⟨1610272898221238328985237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2147030530961651105313649 1610272898221238328985237)
              ·
                refine ⟨75481542104120546671183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1610272898221238328985237 75481542104120546671183)
                ·
                  rfl

theorem cell22_1984497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 6].length) (baseStart_1984497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984497 prefixEnd_1984497 := by exact prefixLift 1984497
  have htrace : WordTrace (prefixWord ++ tailWord_1984497) baseStart_1984497 baseEnd_1984497 := by
    simpa [prefixWord, tailWord_1984497, baseEnd_1984497] using wordTrace_append hprefix tailTrace_1984497
  have hstable : (prefixWord ++ tailWord_1984497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984497).length < 2 ^ (prefixWord ++ tailWord_1984497).sum := by decide
  have hdescent : baseEnd_1984497 < baseStart_1984497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984508 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 9]
def baseStart_1984508 : Nat := 118140960795 + 1984508 * 2 ^ 59
def prefixEnd_1984508 : Nat := 4983230072969 + 3 ^ 40 * 1984508 * 2
def baseEnd_1984508 : Nat := 226445881487294852671871

theorem tailTrace_1984508 : CollatzResearch.WordTrace tailWord_1984508 prefixEnd_1984508 226445881487294852671871 := by
  unfold tailWord_1984508
  simp only [CollatzResearch.WordTrace]
  refine ⟨36190476547236958914077089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48253968729649278552102785 36190476547236958914077089)
  ·
    refine ⟨27142857410427719185557817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36190476547236958914077089 27142857410427719185557817)
    ·
      refine ⟨20357143057820789389168363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27142857410427719185557817 20357143057820789389168363)
      ·
        refine ⟨30535714586731184083752545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20357143057820789389168363 30535714586731184083752545)
        ·
          refine ⟨22901785940048388062814409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30535714586731184083752545 22901785940048388062814409)
          ·
            refine ⟨17176339455036291047110807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22901785940048388062814409 17176339455036291047110807)
            ·
              refine ⟨25764509182554436570666211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17176339455036291047110807 25764509182554436570666211)
              ·
                refine ⟨38646763773831654855999317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25764509182554436570666211 38646763773831654855999317)
                ·
                  refine ⟨226445881487294852671871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38646763773831654855999317 226445881487294852671871)
                  ·
                    rfl

theorem cell22_1984508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_1984508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984508 prefixEnd_1984508 := by exact prefixLift 1984508
  have htrace : WordTrace (prefixWord ++ tailWord_1984508) baseStart_1984508 baseEnd_1984508 := by
    simpa [prefixWord, tailWord_1984508, baseEnd_1984508] using wordTrace_append hprefix tailTrace_1984508
  have hstable : (prefixWord ++ tailWord_1984508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984508).length < 2 ^ (prefixWord ++ tailWord_1984508).sum := by decide
  have hdescent : baseEnd_1984508 < baseStart_1984508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984512 : List Nat := [2, 1, 1, 2, 1, 1, 1, 9, 1, 3]
def baseStart_1984512 : Nat := 118140960795 + 1984512 * 2 ^ 59
def prefixEnd_1984512 : Nat := 4983230072969 + 3 ^ 40 * 1984512 * 2
def baseEnd_1984512 : Nat := 679339013743629880915601

theorem tailTrace_1984512 : CollatzResearch.WordTrace tailWord_1984512 prefixEnd_1984512 679339013743629880915601 := by
  unfold tailWord_1984512
  simp only [CollatzResearch.WordTrace]
  refine ⟨36190549493229713255649895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48254065990972951007533193 36190549493229713255649895)
  ·
    refine ⟨54285824239844569883474843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36190549493229713255649895 54285824239844569883474843)
    ·
      refine ⟨81428736359766854825212265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54285824239844569883474843 81428736359766854825212265)
      ·
        refine ⟨61071552269825141118909199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81428736359766854825212265 61071552269825141118909199)
        ·
          refine ⟨91607328404737711678363799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61071552269825141118909199 91607328404737711678363799)
          ·
            refine ⟨137410992607106567517545699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91607328404737711678363799 137410992607106567517545699)
            ·
              refine ⟨206116488910659851276318549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137410992607106567517545699 206116488910659851276318549)
              ·
                refine ⟨1207713802210897566072179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 206116488910659851276318549 1207713802210897566072179)
                ·
                  refine ⟨1811570703316346349108269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1207713802210897566072179 1811570703316346349108269)
                  ·
                    refine ⟨679339013743629880915601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1811570703316346349108269 679339013743629880915601)
                    ·
                      rfl

theorem cell22_1984512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9, 1, 3].length) (baseStart_1984512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984512 prefixEnd_1984512 := by exact prefixLift 1984512
  have htrace : WordTrace (prefixWord ++ tailWord_1984512) baseStart_1984512 baseEnd_1984512 := by
    simpa [prefixWord, tailWord_1984512, baseEnd_1984512] using wordTrace_append hprefix tailTrace_1984512
  have hstable : (prefixWord ++ tailWord_1984512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984512).length < 2 ^ (prefixWord ++ tailWord_1984512).sum := by decide
  have hdescent : baseEnd_1984512 < baseStart_1984512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984555 : List Nat := [1, 1, 1, 1, 2, 1, 4, 6, 1, 4]
def baseStart_1984555 : Nat := 118140960795 + 1984555 * 2 ^ 59
def prefixEnd_1984555 : Nat := 4983230072969 + 3 ^ 40 * 1984555 * 2
def baseEnd_1984555 : Nat := 679353733522392102090469

theorem tailTrace_1984555 : CollatzResearch.WordTrace tailWord_1984555 prefixEnd_1984555 679353733522392102090469 := by
  unfold tailWord_1984555
  simp only [CollatzResearch.WordTrace]
  refine ⟨72382667325303644855115119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48255111550202429903410079 72382667325303644855115119)
  ·
    refine ⟨108574000987955467282672679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72382667325303644855115119 108574000987955467282672679)
    ·
      refine ⟨162861001481933200924009019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108574000987955467282672679 162861001481933200924009019)
      ·
        refine ⟨244291502222899801386013529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162861001481933200924009019 244291502222899801386013529)
        ·
          refine ⟨183218626667174851039510147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244291502222899801386013529 183218626667174851039510147)
          ·
            refine ⟨274827940000762276559265221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183218626667174851039510147 274827940000762276559265221)
            ·
              refine ⟨51530238750142926854862229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 274827940000762276559265221 51530238750142926854862229)
              ·
                refine ⟨2415479941412949696321667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51530238750142926854862229 2415479941412949696321667)
                ·
                  refine ⟨3623219912119424544482501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2415479941412949696321667 3623219912119424544482501)
                  ·
                    refine ⟨679353733522392102090469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3623219912119424544482501 679353733522392102090469)
                    ·
                      rfl

theorem cell22_1984555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 4].length) (baseStart_1984555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984555 prefixEnd_1984555 := by exact prefixLift 1984555
  have htrace : WordTrace (prefixWord ++ tailWord_1984555) baseStart_1984555 baseEnd_1984555 := by
    simpa [prefixWord, tailWord_1984555, baseEnd_1984555] using wordTrace_append hprefix tailTrace_1984555
  have hstable : (prefixWord ++ tailWord_1984555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984555).length < 2 ^ (prefixWord ++ tailWord_1984555).sum := by decide
  have hdescent : baseEnd_1984555 < baseStart_1984555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984602 : List Nat := [3, 1, 1, 2, 1, 1, 3, 5, 2, 3]
def baseStart_1984602 : Nat := 118140960795 + 1984602 * 2 ^ 59
def prefixEnd_1984602 : Nat := 4983230072969 + 3 ^ 40 * 1984602 * 2
def baseEnd_1984602 : Nat := 679369822582899646165325

theorem tailTrace_1984602 : CollatzResearch.WordTrace tailWord_1984602 prefixEnd_1984602 679369822582899646165325 := by
  unfold tailWord_1984602
  simp only [CollatzResearch.WordTrace]
  refine ⟨18096095389033342970519015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48256254370755581254717373 18096095389033342970519015)
  ·
    refine ⟨27144143083550014455778523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18096095389033342970519015 27144143083550014455778523)
    ·
      refine ⟨40716214625325021683667785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27144143083550014455778523 40716214625325021683667785)
      ·
        refine ⟨30537160968993766262750839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40716214625325021683667785 30537160968993766262750839)
        ·
          refine ⟨45805741453490649394126259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30537160968993766262750839 45805741453490649394126259)
          ·
            refine ⟨68708612180235974091189389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45805741453490649394126259 68708612180235974091189389)
            ·
              refine ⟨25765729567588490284196021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68708612180235974091189389 25765729567588490284196021)
              ·
                refine ⟨2415537146961420964143377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25765729567588490284196021 2415537146961420964143377)
                ·
                  refine ⟨1811652860221065723107533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2415537146961420964143377 1811652860221065723107533)
                  ·
                    refine ⟨679369822582899646165325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1811652860221065723107533 679369822582899646165325)
                    ·
                      rfl

theorem cell22_1984602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 2, 3].length) (baseStart_1984602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984602 prefixEnd_1984602 := by exact prefixLift 1984602
  have htrace : WordTrace (prefixWord ++ tailWord_1984602) baseStart_1984602 baseEnd_1984602 := by
    simpa [prefixWord, tailWord_1984602, baseEnd_1984602] using wordTrace_append hprefix tailTrace_1984602
  have hstable : (prefixWord ++ tailWord_1984602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984602).length < 2 ^ (prefixWord ++ tailWord_1984602).sum := by decide
  have hdescent : baseEnd_1984602 < baseStart_1984602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984647 : List Nat := [1, 1, 4, 2, 1, 1, 3, 3, 3, 3]
def baseStart_1984647 : Nat := 118140960795 + 1984647 * 2 ^ 59
def prefixEnd_1984647 : Nat := 4983230072969 + 3 ^ 40 * 1984647 * 2
def baseEnd_1984647 : Nat := 679385227002534528790187

theorem tailTrace_1984647 : CollatzResearch.WordTrace tailWord_1984647 prefixEnd_1984647 679385227002534528790187 := by
  unfold tailWord_1984647
  simp only [CollatzResearch.WordTrace]
  refine ⟨72386022840970344567464195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48257348560646896378309463 72386022840970344567464195)
  ·
    refine ⟨108579034261455516851196293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72386022840970344567464195 108579034261455516851196293)
    ·
      refine ⟨20358568924022909409599305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108579034261455516851196293 20358568924022909409599305)
      ·
        refine ⟨15268926693017182057199479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20358568924022909409599305 15268926693017182057199479)
        ·
          refine ⟨22903390039525773085799219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15268926693017182057199479 22903390039525773085799219)
          ·
            refine ⟨34355085059288659628698829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22903390039525773085799219 34355085059288659628698829)
            ·
              refine ⟨12883156897233247360762061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34355085059288659628698829 12883156897233247360762061)
              ·
                refine ⟨4831183836462467760285773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12883156897233247360762061 4831183836462467760285773)
                ·
                  refine ⟨1811693938673425410107165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4831183836462467760285773 1811693938673425410107165)
                  ·
                    refine ⟨679385227002534528790187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1811693938673425410107165 679385227002534528790187)
                    ·
                      rfl

theorem cell22_1984647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_1984647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984647 prefixEnd_1984647 := by exact prefixLift 1984647
  have htrace : WordTrace (prefixWord ++ tailWord_1984647) baseStart_1984647 baseEnd_1984647 := by
    simpa [prefixWord, tailWord_1984647, baseEnd_1984647] using wordTrace_append hprefix tailTrace_1984647
  have hstable : (prefixWord ++ tailWord_1984647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984647).length < 2 ^ (prefixWord ++ tailWord_1984647).sum := by decide
  have hdescent : baseEnd_1984647 < baseStart_1984647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984666 : List Nat := [3, 1, 1, 5, 3, 1, 2, 6]
def baseStart_1984666 : Nat := 118140960795 + 1984666 * 2 ^ 59
def prefixEnd_1984666 : Nat := 4983230072969 + 3 ^ 40 * 1984666 * 2
def baseEnd_1984666 : Nat := 75487970121202756951681

theorem tailTrace_1984666 : CollatzResearch.WordTrace tailWord_1984666 prefixEnd_1984666 75487970121202756951681 := by
  unfold tailWord_1984666
  simp only [CollatzResearch.WordTrace]
  refine ⟨18096678956975377703101463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48257810551934340541603901 18096678956975377703101463)
  ·
    refine ⟨27145018435463066554652195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18096678956975377703101463 27145018435463066554652195)
    ·
      refine ⟨40717527653194599831978293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27145018435463066554652195 40717527653194599831978293)
      ·
        refine ⟨3817268217486993734247965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40717527653194599831978293 3817268217486993734247965)
        ·
          refine ⟨1431475581557622650342987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3817268217486993734247965 1431475581557622650342987)
          ·
            refine ⟨2147213372336433975514481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431475581557622650342987 2147213372336433975514481)
            ·
              refine ⟨1610410029252325481635861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2147213372336433975514481 1610410029252325481635861)
              ·
                refine ⟨75487970121202756951681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1610410029252325481635861 75487970121202756951681)
                ·
                  rfl

theorem cell22_1984666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 6].length) (baseStart_1984666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984666 prefixEnd_1984666 := by exact prefixLift 1984666
  have htrace : WordTrace (prefixWord ++ tailWord_1984666) baseStart_1984666 baseEnd_1984666 := by
    simpa [prefixWord, tailWord_1984666, baseEnd_1984666] using wordTrace_append hprefix tailTrace_1984666
  have hstable : (prefixWord ++ tailWord_1984666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984666).length < 2 ^ (prefixWord ++ tailWord_1984666).sum := by decide
  have hdescent : baseEnd_1984666 < baseStart_1984666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984720 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 7, 5]
def baseStart_1984720 : Nat := 118140960795 + 1984720 * 2 ^ 59
def prefixEnd_1984720 : Nat := 4983230072969 + 3 ^ 40 * 1984720 * 2
def baseEnd_1984720 : Nat := 679410216394386671714963

theorem tailTrace_1984720 : CollatzResearch.WordTrace tailWord_1984720 prefixEnd_1984720 679410216394386671714963 := by
  unfold tailWord_1984720
  simp only [CollatzResearch.WordTrace]
  refine ⟨36194342684852939017435807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48259123579803918689914409 36194342684852939017435807)
  ·
    refine ⟨54291514027279408526153711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36194342684852939017435807 54291514027279408526153711)
    ·
      refine ⟨81437271040919112789230567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54291514027279408526153711 81437271040919112789230567)
      ·
        refine ⟨122155906561378669183845851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81437271040919112789230567 122155906561378669183845851)
        ·
          refine ⟨183233859842068003775768777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122155906561378669183845851 183233859842068003775768777)
          ·
            refine ⟨137425394881551002831826583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183233859842068003775768777 137425394881551002831826583)
            ·
              refine ⟨206138092322326504247739875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137425394881551002831826583 206138092322326504247739875)
              ·
                refine ⟨309207138483489756371609813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206138092322326504247739875 309207138483489756371609813)
                ·
                  refine ⟨7247042308206791164959605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 309207138483489756371609813 7247042308206791164959605)
                  ·
                    refine ⟨679410216394386671714963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7247042308206791164959605 679410216394386671714963)
                    ·
                      rfl

theorem cell22_1984720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 7, 5].length) (baseStart_1984720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984720 prefixEnd_1984720 := by exact prefixLift 1984720
  have htrace : WordTrace (prefixWord ++ tailWord_1984720) baseStart_1984720 baseEnd_1984720 := by
    simpa [prefixWord, tailWord_1984720, baseEnd_1984720] using wordTrace_append hprefix tailTrace_1984720
  have hstable : (prefixWord ++ tailWord_1984720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984720).length < 2 ^ (prefixWord ++ tailWord_1984720).sum := by decide
  have hdescent : baseEnd_1984720 < baseStart_1984720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984737 : List Nat := [1, 2, 3, 1, 3, 1, 3, 2, 1, 5]
def baseStart_1984737 : Nat := 118140960795 + 1984737 * 2 ^ 59
def prefixEnd_1984737 : Nat := 4983230072969 + 3 ^ 40 * 1984737 * 2
def baseEnd_1984737 : Nat := 679416035841804294039911

theorem tailTrace_1984737 : CollatzResearch.WordTrace tailWord_1984737 prefixEnd_1984737 679416035841804294039911 := by
  unfold tailWord_1984737
  simp only [CollatzResearch.WordTrace]
  refine ⟨72389305410644289938240465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48259536940429526625493643 72389305410644289938240465)
  ·
    refine ⟨54291979057983217453680349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72389305410644289938240465 54291979057983217453680349)
    ·
      refine ⟨20359492146743706545130131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54291979057983217453680349 20359492146743706545130131)
      ·
        refine ⟨30539238220115559817695197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20359492146743706545130131 30539238220115559817695197)
        ·
          refine ⟨11452214332543334931635699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30539238220115559817695197 11452214332543334931635699)
          ·
            refine ⟨17178321498815002397453549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11452214332543334931635699 17178321498815002397453549)
            ·
              refine ⟨6441870562055625899045081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17178321498815002397453549 6441870562055625899045081)
              ·
                refine ⟨4831402921541719424283811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6441870562055625899045081 4831402921541719424283811)
                ·
                  refine ⟨7247104382312579136425717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4831402921541719424283811 7247104382312579136425717)
                  ·
                    refine ⟨679416035841804294039911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7247104382312579136425717 679416035841804294039911)
                    ·
                      rfl

theorem cell22_1984737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_1984737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984737 prefixEnd_1984737 := by exact prefixLift 1984737
  have htrace : WordTrace (prefixWord ++ tailWord_1984737) baseStart_1984737 baseEnd_1984737 := by
    simpa [prefixWord, tailWord_1984737, baseEnd_1984737] using wordTrace_append hprefix tailTrace_1984737
  have hstable : (prefixWord ++ tailWord_1984737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984737).length < 2 ^ (prefixWord ++ tailWord_1984737).sum := by decide
  have hdescent : baseEnd_1984737 < baseStart_1984737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984741 : List Nat := [1, 3, 1, 4, 2, 2, 3, 1, 1, 4]
def baseStart_1984741 : Nat := 118140960795 + 1984741 * 2 ^ 59
def prefixEnd_1984741 : Nat := 4983230072969 + 3 ^ 40 * 1984741 * 2
def baseEnd_1984741 : Nat := 679417405123549616939899

theorem tailTrace_1984741 : CollatzResearch.WordTrace tailWord_1984741 prefixEnd_1984741 679417405123549616939899 := by
  unfold tailWord_1984741
  simp only [CollatzResearch.WordTrace]
  refine ⟨72389451302629798621386077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48259634201753199080924051 72389451302629798621386077)
  ·
    refine ⟨27146044238486174483019779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72389451302629798621386077 27146044238486174483019779)
    ·
      refine ⟨40719066357729261724529669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27146044238486174483019779 40719066357729261724529669)
      ·
        refine ⟨7634824942074236573349313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40719066357729261724529669 7634824942074236573349313)
        ·
          refine ⟨5726118706555677430011985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7634824942074236573349313 5726118706555677430011985)
          ·
            refine ⟨4294589029916758072508989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5726118706555677430011985 4294589029916758072508989)
            ·
              refine ⟨1610470886218784277190871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4294589029916758072508989 1610470886218784277190871)
              ·
                refine ⟨2415706329328176415786307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1610470886218784277190871 2415706329328176415786307)
                ·
                  refine ⟨3623559493992264623679461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2415706329328176415786307 3623559493992264623679461)
                  ·
                    refine ⟨679417405123549616939899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3623559493992264623679461 679417405123549616939899)
                    ·
                      rfl

theorem cell22_1984741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 1, 4].length) (baseStart_1984741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984741 prefixEnd_1984741 := by exact prefixLift 1984741
  have htrace : WordTrace (prefixWord ++ tailWord_1984741) baseStart_1984741 baseEnd_1984741 := by
    simpa [prefixWord, tailWord_1984741, baseEnd_1984741] using wordTrace_append hprefix tailTrace_1984741
  have hstable : (prefixWord ++ tailWord_1984741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984741).length < 2 ^ (prefixWord ++ tailWord_1984741).sum := by decide
  have hdescent : baseEnd_1984741 < baseStart_1984741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984887 : List Nat := [1, 1, 3, 1, 1, 2, 2, 4, 1, 6]
def baseStart_1984887 : Nat := 118140960795 + 1984887 * 2 ^ 59
def prefixEnd_1984887 : Nat := 4983230072969 + 3 ^ 40 * 1984887 * 2
def baseEnd_1984887 : Nat := 679467383907253902789451

theorem tailTrace_1984887 : CollatzResearch.WordTrace tailWord_1984887 prefixEnd_1984887 679467383907253902789451 := by
  unfold tailWord_1984887
  simp only [CollatzResearch.WordTrace]
  refine ⟨72394776360100865556200915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48263184240067243704133943 72394776360100865556200915)
  ·
    refine ⟨108592164540151298334301373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72394776360100865556200915 108592164540151298334301373)
    ·
      refine ⟨40722061702556736875363015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108592164540151298334301373 40722061702556736875363015)
      ·
        refine ⟨61083092553835105313044523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40722061702556736875363015 61083092553835105313044523)
        ·
          refine ⟨91624638830752657969566785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61083092553835105313044523 91624638830752657969566785)
          ·
            refine ⟨68718479123064493477175089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91624638830752657969566785 68718479123064493477175089)
            ·
              refine ⟨51538859342298370107881317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68718479123064493477175089 51538859342298370107881317)
              ·
                refine ⟨9663536126680944395227747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 51538859342298370107881317 9663536126680944395227747)
                ·
                  refine ⟨14495304190021416592841621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9663536126680944395227747 14495304190021416592841621)
                  ·
                    refine ⟨679467383907253902789451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14495304190021416592841621 679467383907253902789451)
                    ·
                      rfl

theorem cell22_1984887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_1984887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984887 prefixEnd_1984887 := by exact prefixLift 1984887
  have htrace : WordTrace (prefixWord ++ tailWord_1984887) baseStart_1984887 baseEnd_1984887 := by
    simpa [prefixWord, tailWord_1984887, baseEnd_1984887] using wordTrace_append hprefix tailTrace_1984887
  have hstable : (prefixWord ++ tailWord_1984887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984887).length < 2 ^ (prefixWord ++ tailWord_1984887).sum := by decide
  have hdescent : baseEnd_1984887 < baseStart_1984887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984918 : List Nat := [5, 3, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_1984918 : Nat := 118140960795 + 1984918 * 2 ^ 59
def prefixEnd_1984918 : Nat := 4983230072969 + 3 ^ 40 * 1984918 * 2
def baseEnd_1984918 : Nat := 679477995840780155264357

theorem tailTrace_1984918 : CollatzResearch.WordTrace tailWord_1984918 prefixEnd_1984918 679477995840780155264357 := by
  unfold tailWord_1984918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4524744188936784865661213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48263938015325705233719605 4524744188936784865661213)
  ·
    refine ⟨1696779070851294324622955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4524744188936784865661213 1696779070851294324622955)
    ·
      refine ⟨2545168606276941486934433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1696779070851294324622955 2545168606276941486934433)
      ·
        refine ⟨1908876454707706115200825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2545168606276941486934433 1908876454707706115200825)
        ·
          refine ⟨1431657341030779586400619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1908876454707706115200825 1431657341030779586400619)
          ·
            refine ⟨2147486011546169379600929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431657341030779586400619 2147486011546169379600929)
            ·
              refine ⟨1610614508659627034700697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2147486011546169379600929 1610614508659627034700697)
              ·
                refine ⟨1207960881494720276025523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1610614508659627034700697 1207960881494720276025523)
                ·
                  refine ⟨1811941322242080414038285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1207960881494720276025523 1811941322242080414038285)
                  ·
                    refine ⟨679477995840780155264357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1811941322242080414038285 679477995840780155264357)
                    ·
                      rfl

theorem cell22_1984918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_1984918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984918 prefixEnd_1984918 := by exact prefixLift 1984918
  have htrace : WordTrace (prefixWord ++ tailWord_1984918) baseStart_1984918 baseEnd_1984918 := by
    simpa [prefixWord, tailWord_1984918, baseEnd_1984918] using wordTrace_append hprefix tailTrace_1984918
  have hstable : (prefixWord ++ tailWord_1984918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984918).length < 2 ^ (prefixWord ++ tailWord_1984918).sum := by decide
  have hdescent : baseEnd_1984918 < baseStart_1984918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984925 : List Nat := [1, 4, 2, 1, 4, 2, 2, 2, 4]
def baseStart_1984925 : Nat := 118140960795 + 1984925 * 2 ^ 59
def prefixEnd_1984925 : Nat := 4983230072969 + 3 ^ 40 * 1984925 * 2
def baseEnd_1984925 : Nat := 226493464027944823446445

theorem tailTrace_1984925 : CollatzResearch.WordTrace tailWord_1984925 prefixEnd_1984925 226493464027944823446445 := by
  unfold tailWord_1984925
  simp only [CollatzResearch.WordTrace]
  refine ⟨72396162333963198046084229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48264108222642132030722819 72396162333963198046084229)
  ·
    refine ⟨13574280437618099633640793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72396162333963198046084229 13574280437618099633640793)
    ·
      refine ⟨10180710328213574725230595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13574280437618099633640793 10180710328213574725230595)
      ·
        refine ⟨15271065492320362087845893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10180710328213574725230595 15271065492320362087845893)
        ·
          refine ⟨2863324779810067891471105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15271065492320362087845893 2863324779810067891471105)
          ·
            refine ⟨2147493584857550918603329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2863324779810067891471105 2147493584857550918603329)
            ·
              refine ⟨1610620188643163188952497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2147493584857550918603329 1610620188643163188952497)
              ·
                refine ⟨1207965141482372391714373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1610620188643163188952497 1207965141482372391714373)
                ·
                  refine ⟨226493464027944823446445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1207965141482372391714373 226493464027944823446445)
                  ·
                    rfl

theorem cell22_1984925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_1984925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984925 prefixEnd_1984925 := by exact prefixLift 1984925
  have htrace : WordTrace (prefixWord ++ tailWord_1984925) baseStart_1984925 baseEnd_1984925 := by
    simpa [prefixWord, tailWord_1984925, baseEnd_1984925] using wordTrace_append hprefix tailTrace_1984925
  have hstable : (prefixWord ++ tailWord_1984925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984925).length < 2 ^ (prefixWord ++ tailWord_1984925).sum := by decide
  have hdescent : baseEnd_1984925 < baseStart_1984925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984936 : List Nat := [2, 1, 6, 1, 1, 1, 3, 7]
def baseStart_1984936 : Nat := 118140960795 + 1984936 * 2 ^ 59
def prefixEnd_1984936 : Nat := 4983230072969 + 3 ^ 40 * 1984936 * 2
def baseEnd_1984936 : Nat := 75498239734292678701589

theorem tailTrace_1984936 : CollatzResearch.WordTrace tailWord_1984936 prefixEnd_1984936 75498239734292678701589 := by
  unfold tailWord_1984936
  simp only [CollatzResearch.WordTrace]
  refine ⟨36198281768461673462367331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48264375691282231283156441 36198281768461673462367331)
  ·
    refine ⟨54297422652692510193550997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36198281768461673462367331 54297422652692510193550997)
    ·
      refine ⟨2545191686844961415322703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54297422652692510193550997 2545191686844961415322703)
      ·
        refine ⟨3817787530267442122984055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2545191686844961415322703 3817787530267442122984055)
        ·
          refine ⟨5726681295401163184476083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3817787530267442122984055 5726681295401163184476083)
          ·
            refine ⟨8590021943101744776714125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5726681295401163184476083 8590021943101744776714125)
            ·
              refine ⟨3221258228663154291267797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8590021943101744776714125 3221258228663154291267797)
              ·
                refine ⟨75498239734292678701589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3221258228663154291267797 75498239734292678701589)
                ·
                  rfl

theorem cell22_1984936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 7].length) (baseStart_1984936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984936 prefixEnd_1984936 := by exact prefixLift 1984936
  have htrace : WordTrace (prefixWord ++ tailWord_1984936) baseStart_1984936 baseEnd_1984936 := by
    simpa [prefixWord, tailWord_1984936, baseEnd_1984936] using wordTrace_append hprefix tailTrace_1984936
  have hstable : (prefixWord ++ tailWord_1984936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984936).length < 2 ^ (prefixWord ++ tailWord_1984936).sum := by decide
  have hdescent : baseEnd_1984936 < baseStart_1984936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984947 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 11]
def baseStart_1984947 : Nat := 118140960795 + 1984947 * 2 ^ 59
def prefixEnd_1984947 : Nat := 4983230072969 + 3 ^ 40 * 1984947 * 2
def baseEnd_1984947 : Nat := 226495974377811248763089

theorem tailTrace_1984947 : CollatzResearch.WordTrace tailWord_1984947 prefixEnd_1984947 226495974377811248763089 := by
  unfold tailWord_1984947
  simp only [CollatzResearch.WordTrace]
  refine ⟨72396964739883495803385095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48264643159922330535590063 72396964739883495803385095)
  ·
    refine ⟨108595447109825243705077643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72396964739883495803385095 108595447109825243705077643)
    ·
      refine ⟨162893170664737865557616465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108595447109825243705077643 162893170664737865557616465)
      ·
        refine ⟨122169877998553399168212349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162893170664737865557616465 122169877998553399168212349)
        ·
          refine ⟨45813704249457524688079631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122169877998553399168212349 45813704249457524688079631)
          ·
            refine ⟨68720556374186287032119447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45813704249457524688079631 68720556374186287032119447)
            ·
              refine ⟨103080834561279430548179171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68720556374186287032119447 103080834561279430548179171)
              ·
                refine ⟨154621251841919145822268757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103080834561279430548179171 154621251841919145822268757)
                ·
                  refine ⟨226495974377811248763089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 154621251841919145822268757 226495974377811248763089)
                  ·
                    rfl

theorem cell22_1984947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 11].length) (baseStart_1984947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984947 prefixEnd_1984947 := by exact prefixLift 1984947
  have htrace : WordTrace (prefixWord ++ tailWord_1984947) baseStart_1984947 baseEnd_1984947 := by
    simpa [prefixWord, tailWord_1984947, baseEnd_1984947] using wordTrace_append hprefix tailTrace_1984947
  have hstable : (prefixWord ++ tailWord_1984947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984947).length < 2 ^ (prefixWord ++ tailWord_1984947).sum := by decide
  have hdescent : baseEnd_1984947 < baseStart_1984947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984951 : List Nat := [1, 1, 3, 1, 3, 4, 1, 2, 3, 3]
def baseStart_1984951 : Nat := 118140960795 + 1984951 * 2 ^ 59
def prefixEnd_1984951 : Nat := 4983230072969 + 3 ^ 40 * 1984951 * 2
def baseEnd_1984951 : Nat := 679489292415179069189255

theorem tailTrace_1984951 : CollatzResearch.WordTrace tailWord_1984951 prefixEnd_1984951 679489292415179069189255 := by
  unfold tailWord_1984951
  simp only [CollatzResearch.WordTrace]
  refine ⟨72397110631869004486530707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48264740421246002991020471 72397110631869004486530707)
  ·
    refine ⟨108595665947803506729796061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72397110631869004486530707 108595665947803506729796061)
    ·
      refine ⟨40723374730426315023673523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108595665947803506729796061 40723374730426315023673523)
      ·
        refine ⟨61085062095639472535510285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40723374730426315023673523 61085062095639472535510285)
        ·
          refine ⟨22906898285864802200816357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61085062095639472535510285 22906898285864802200816357)
          ·
            refine ⟨4295043428599650412653067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22906898285864802200816357 4295043428599650412653067)
            ·
              refine ⟨6442565142899475618979601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4295043428599650412653067 6442565142899475618979601)
              ·
                refine ⟨4831923857174606714234701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6442565142899475618979601 4831923857174606714234701)
                ·
                  refine ⟨1811971446440477517838013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4831923857174606714234701 1811971446440477517838013)
                  ·
                    refine ⟨679489292415179069189255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1811971446440477517838013 679489292415179069189255)
                    ·
                      rfl

theorem cell22_1984951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 3, 3].length) (baseStart_1984951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984951 prefixEnd_1984951 := by exact prefixLift 1984951
  have htrace : WordTrace (prefixWord ++ tailWord_1984951) baseStart_1984951 baseEnd_1984951 := by
    simpa [prefixWord, tailWord_1984951, baseEnd_1984951] using wordTrace_append hprefix tailTrace_1984951
  have hstable : (prefixWord ++ tailWord_1984951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984951).length < 2 ^ (prefixWord ++ tailWord_1984951).sum := by decide
  have hdescent : baseEnd_1984951 < baseStart_1984951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984968 : List Nat := [2, 1, 3, 1, 3, 2, 1, 5, 1, 3]
def baseStart_1984968 : Nat := 118140960795 + 1984968 * 2 ^ 59
def prefixEnd_1984968 : Nat := 4983230072969 + 3 ^ 40 * 1984968 * 2
def baseEnd_1984968 : Nat := 679495111862596691514203

theorem tailTrace_1984968 : CollatzResearch.WordTrace tailWord_1984968 prefixEnd_1984968 679495111862596691514203 := by
  unfold tailWord_1984968
  simp only [CollatzResearch.WordTrace]
  refine ⟨36198865336403708194949779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48265153781871610926599705 36198865336403708194949779)
  ·
    refine ⟨54298298004605562292424669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36198865336403708194949779 54298298004605562292424669)
    ·
      refine ⟨20361861751727085859659251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54298298004605562292424669 20361861751727085859659251)
      ·
        refine ⟨30542792627590628789488877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20361861751727085859659251 30542792627590628789488877)
        ·
          refine ⟨11453547235346485796058329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30542792627590628789488877 11453547235346485796058329)
          ·
            refine ⟨8590160426509864347043747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11453547235346485796058329 8590160426509864347043747)
            ·
              refine ⟨12885240639764796520565621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8590160426509864347043747 12885240639764796520565621)
              ·
                refine ⟨1207991309977949673803027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12885240639764796520565621 1207991309977949673803027)
                ·
                  refine ⟨1811986964966924510704541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1207991309977949673803027 1811986964966924510704541)
                  ·
                    refine ⟨679495111862596691514203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1811986964966924510704541 679495111862596691514203)
                    ·
                      rfl

theorem cell22_1984968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5, 1, 3].length) (baseStart_1984968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984968 prefixEnd_1984968 := by exact prefixLift 1984968
  have htrace : WordTrace (prefixWord ++ tailWord_1984968) baseStart_1984968 baseEnd_1984968 := by
    simpa [prefixWord, tailWord_1984968, baseEnd_1984968] using wordTrace_append hprefix tailTrace_1984968
  have hstable : (prefixWord ++ tailWord_1984968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984968).length < 2 ^ (prefixWord ++ tailWord_1984968).sum := by decide
  have hdescent : baseEnd_1984968 < baseStart_1984968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1984981 : List Nat := [1, 3, 2, 3, 1, 2, 3, 2, 5]
def baseStart_1984981 : Nat := 118140960795 + 1984981 * 2 ^ 59
def prefixEnd_1984981 : Nat := 4983230072969 + 3 ^ 40 * 1984981 * 2
def baseEnd_1984981 : Nat := 226499854009422996979721

theorem tailTrace_1984981 : CollatzResearch.WordTrace tailWord_1984981 prefixEnd_1984981 226499854009422996979721 := by
  unfold tailWord_1984981
  simp only [CollatzResearch.WordTrace]
  refine ⟨72398204821760319610122797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48265469881173546406748531 72398204821760319610122797)
  ·
    refine ⟨27149326808160119853796049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72398204821760319610122797 27149326808160119853796049)
    ·
      refine ⟨20361995106120089890347037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27149326808160119853796049 20361995106120089890347037)
      ·
        refine ⟨7635748164795033708880139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20361995106120089890347037 7635748164795033708880139)
        ·
          refine ⟨11453622247192550563320209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7635748164795033708880139 11453622247192550563320209)
          ·
            refine ⟨8590216685394412922490157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11453622247192550563320209 8590216685394412922490157)
            ·
              refine ⟨3221331257022904845933809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8590216685394412922490157 3221331257022904845933809)
              ·
                refine ⟨2415998442767178634450357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3221331257022904845933809 2415998442767178634450357)
                ·
                  refine ⟨226499854009422996979721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2415998442767178634450357 226499854009422996979721)
                  ·
                    rfl

theorem cell22_1984981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 5].length) (baseStart_1984981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1984981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1984981 prefixEnd_1984981 := by exact prefixLift 1984981
  have htrace : WordTrace (prefixWord ++ tailWord_1984981) baseStart_1984981 baseEnd_1984981 := by
    simpa [prefixWord, tailWord_1984981, baseEnd_1984981] using wordTrace_append hprefix tailTrace_1984981
  have hstable : (prefixWord ++ tailWord_1984981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1984981).length < 2 ^ (prefixWord ++ tailWord_1984981).sum := by decide
  have hdescent : baseEnd_1984981 < baseStart_1984981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1984981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985009 : List Nat := [1, 2, 2, 2, 3, 1, 1, 4, 6]
def baseStart_1985009 : Nat := 118140960795 + 1985009 * 2 ^ 59
def prefixEnd_1985009 : Nat := 4983230072969 + 3 ^ 40 * 1985009 * 2
def baseEnd_1985009 : Nat := 226503049000162083746359

theorem tailTrace_1985009 : CollatzResearch.WordTrace tailWord_1985009 prefixEnd_1985009 226503049000162083746359 := by
  unfold tailWord_1985009
  simp only [CollatzResearch.WordTrace]
  refine ⟨72399226065658880392142081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48266150710439253594761387 72399226065658880392142081)
  ·
    refine ⟨54299419549244160294106561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72399226065658880392142081 54299419549244160294106561)
    ·
      refine ⟨40724564661933120220579921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54299419549244160294106561 40724564661933120220579921)
      ·
        refine ⟨30543423496449840165434941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40724564661933120220579921 30543423496449840165434941)
        ·
          refine ⟨11453783811168690062038103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30543423496449840165434941 11453783811168690062038103)
          ·
            refine ⟨17180675716753035093057155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11453783811168690062038103 17180675716753035093057155)
            ·
              refine ⟨25771013575129552639585733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17180675716753035093057155 25771013575129552639585733)
              ·
                refine ⟨4832065045336791119922325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25771013575129552639585733 4832065045336791119922325)
                ·
                  refine ⟨226503049000162083746359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4832065045336791119922325 226503049000162083746359)
                  ·
                    rfl

theorem cell22_1985009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 6].length) (baseStart_1985009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985009 prefixEnd_1985009 := by exact prefixLift 1985009
  have htrace : WordTrace (prefixWord ++ tailWord_1985009) baseStart_1985009 baseEnd_1985009 := by
    simpa [prefixWord, tailWord_1985009, baseEnd_1985009] using wordTrace_append hprefix tailTrace_1985009
  have hstable : (prefixWord ++ tailWord_1985009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985009).length < 2 ^ (prefixWord ++ tailWord_1985009).sum := by decide
  have hdescent : baseEnd_1985009 < baseStart_1985009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985011 : List Nat := [1, 1, 1, 2, 2, 2, 6, 2, 1, 4]
def baseStart_1985011 : Nat := 118140960795 + 1985011 * 2 ^ 59
def prefixEnd_1985011 : Nat := 4983230072969 + 3 ^ 40 * 1985011 * 2
def baseEnd_1985011 : Nat := 679509831641358912689071

theorem tailTrace_1985011 : CollatzResearch.WordTrace tailWord_1985011 prefixEnd_1985011 679509831641358912689071 := by
  unfold tailWord_1985011
  simp only [CollatzResearch.WordTrace]
  refine ⟨72399299011651634733714887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48266199341101089822476591 72399299011651634733714887)
  ·
    refine ⟨108598948517477452100572331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72399299011651634733714887 108598948517477452100572331)
    ·
      refine ⟨162898422776216178150858497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108598948517477452100572331 162898422776216178150858497)
      ·
        refine ⟨122173817082162133613143873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162898422776216178150858497 122173817082162133613143873)
        ·
          refine ⟨91630362811621600209857905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122173817082162133613143873 91630362811621600209857905)
          ·
            refine ⟨68722772108716200157393429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91630362811621600209857905 68722772108716200157393429)
            ·
              refine ⟨3221379942596071882377817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 68722772108716200157393429 3221379942596071882377817)
              ·
                refine ⟨2416034956947053911783363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3221379942596071882377817 2416034956947053911783363)
                ·
                  refine ⟨3624052435420580867675045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2416034956947053911783363 3624052435420580867675045)
                  ·
                    refine ⟨679509831641358912689071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3624052435420580867675045 679509831641358912689071)
                    ·
                      rfl

theorem cell22_1985011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 4].length) (baseStart_1985011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985011 prefixEnd_1985011 := by exact prefixLift 1985011
  have htrace : WordTrace (prefixWord ++ tailWord_1985011) baseStart_1985011 baseEnd_1985011 := by
    simpa [prefixWord, tailWord_1985011, baseEnd_1985011] using wordTrace_append hprefix tailTrace_1985011
  have hstable : (prefixWord ++ tailWord_1985011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985011).length < 2 ^ (prefixWord ++ tailWord_1985011).sum := by decide
  have hdescent : baseEnd_1985011 < baseStart_1985011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985028 : List Nat := [2, 3, 2, 3, 1, 1, 2, 3, 1, 4]
def baseStart_1985028 : Nat := 118140960795 + 1985028 * 2 ^ 59
def prefixEnd_1985028 : Nat := 4983230072969 + 3 ^ 40 * 1985028 * 2
def baseEnd_1985028 : Nat := 679515651088776535014019

theorem tailTrace_1985028 : CollatzResearch.WordTrace tailWord_1985028 prefixEnd_1985028 679515651088776535014019 := by
  unfold tailWord_1985028
  simp only [CollatzResearch.WordTrace]
  refine ⟨36199959526295023318541869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48266612701726697758055825 36199959526295023318541869)
  ·
    refine ⟨13574984822360633744453201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36199959526295023318541869 13574984822360633744453201)
    ·
      refine ⟨10181238616770475308339901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13574984822360633744453201 10181238616770475308339901)
      ·
        refine ⟨3817964481288928240627463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10181238616770475308339901 3817964481288928240627463)
        ·
          refine ⟨5726946721933392360941195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3817964481288928240627463 5726946721933392360941195)
          ·
            refine ⟨8590420082900088541411793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5726946721933392360941195 8590420082900088541411793)
            ·
              refine ⟨6442815062175066406058845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8590420082900088541411793 6442815062175066406058845)
              ·
                refine ⟨2416055648315649902272067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6442815062175066406058845 2416055648315649902272067)
                ·
                  refine ⟨3624083472473474853408101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2416055648315649902272067 3624083472473474853408101)
                  ·
                    refine ⟨679515651088776535014019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3624083472473474853408101 679515651088776535014019)
                    ·
                      rfl

theorem cell22_1985028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_1985028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985028 prefixEnd_1985028 := by exact prefixLift 1985028
  have htrace : WordTrace (prefixWord ++ tailWord_1985028) baseStart_1985028 baseEnd_1985028 := by
    simpa [prefixWord, tailWord_1985028, baseEnd_1985028] using wordTrace_append hprefix tailTrace_1985028
  have hstable : (prefixWord ++ tailWord_1985028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985028).length < 2 ^ (prefixWord ++ tailWord_1985028).sum := by decide
  have hdescent : baseEnd_1985028 < baseStart_1985028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985039 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 4, 4]
def baseStart_1985039 : Nat := 118140960795 + 1985039 * 2 ^ 59
def prefixEnd_1985039 : Nat := 4983230072969 + 3 ^ 40 * 1985039 * 2
def baseEnd_1985039 : Nat := 679519416613576172988985

theorem tailTrace_1985039 : CollatzResearch.WordTrace tailWord_1985039 prefixEnd_1985039 679519416613576172988985 := by
  unfold tailWord_1985039
  simp only [CollatzResearch.WordTrace]
  refine ⟨72400320255550195515734171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48266880170366797010489447 72400320255550195515734171)
  ·
    refine ⟨108600480383325293273601257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72400320255550195515734171 108600480383325293273601257)
    ·
      refine ⟨81450360287493969955200943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108600480383325293273601257 81450360287493969955200943)
      ·
        refine ⟨122175540431240954932801415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81450360287493969955200943 122175540431240954932801415)
        ·
          refine ⟨183263310646861432399202123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122175540431240954932801415 183263310646861432399202123)
          ·
            refine ⟨274894965970292148598803185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183263310646861432399202123 274894965970292148598803185)
            ·
              refine ⟨206171224477719111449102389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274894965970292148598803185 206171224477719111449102389)
              ·
                refine ⟨19328552294786166698353349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 206171224477719111449102389 19328552294786166698353349)
                ·
                  refine ⟨3624103555272406255941253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19328552294786166698353349 3624103555272406255941253)
                  ·
                    refine ⟨679519416613576172988985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3624103555272406255941253 679519416613576172988985)
                    ·
                      rfl

theorem cell22_1985039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 4].length) (baseStart_1985039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985039 prefixEnd_1985039 := by exact prefixLift 1985039
  have htrace : WordTrace (prefixWord ++ tailWord_1985039) baseStart_1985039 baseEnd_1985039 := by
    simpa [prefixWord, tailWord_1985039, baseEnd_1985039] using wordTrace_append hprefix tailTrace_1985039
  have hstable : (prefixWord ++ tailWord_1985039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985039).length < 2 ^ (prefixWord ++ tailWord_1985039).sum := by decide
  have hdescent : baseEnd_1985039 < baseStart_1985039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985043 : List Nat := [1, 1, 1, 2, 1, 5, 5, 2, 4]
def baseStart_1985043 : Nat := 118140960795 + 1985043 * 2 ^ 59
def prefixEnd_1985043 : Nat := 4983230072969 + 3 ^ 40 * 1985043 * 2
def baseEnd_1985043 : Nat := 226506928631773831962991

theorem tailTrace_1985043 : CollatzResearch.WordTrace tailWord_1985043 prefixEnd_1985043 226506928631773831962991 := by
  unfold tailWord_1985043
  simp only [CollatzResearch.WordTrace]
  refine ⟨72400466147535704198879783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48266977431690469465919855 72400466147535704198879783)
  ·
    refine ⟨108600699221303556298319675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72400466147535704198879783 108600699221303556298319675)
    ·
      refine ⟨162901048831955334447479513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108600699221303556298319675 162901048831955334447479513)
      ·
        refine ⟨122175786623966500835609635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162901048831955334447479513 122175786623966500835609635)
        ·
          refine ⟨183263679935949751253414453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122175786623966500835609635 183263679935949751253414453)
          ·
            refine ⟨17180969993995289180007605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 183263679935949751253414453 17180969993995289180007605)
            ·
              refine ⟨1610715936937058360625713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17180969993995289180007605 1610715936937058360625713)
              ·
                refine ⟨1208036952702793770469285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1610715936937058360625713 1208036952702793770469285)
                ·
                  refine ⟨226506928631773831962991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1208036952702793770469285 226506928631773831962991)
                  ·
                    rfl

theorem cell22_1985043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2, 4].length) (baseStart_1985043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985043 prefixEnd_1985043 := by exact prefixLift 1985043
  have htrace : WordTrace (prefixWord ++ tailWord_1985043) baseStart_1985043 baseEnd_1985043 := by
    simpa [prefixWord, tailWord_1985043, baseEnd_1985043] using wordTrace_append hprefix tailTrace_1985043
  have hstable : (prefixWord ++ tailWord_1985043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985043).length < 2 ^ (prefixWord ++ tailWord_1985043).sum := by decide
  have hdescent : baseEnd_1985043 < baseStart_1985043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985094 : List Nat := [6, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_1985094 : Nat := 118140960795 + 1985094 * 2 ^ 59
def prefixEnd_1985094 : Nat := 4983230072969 + 3 ^ 40 * 1985094 * 2
def baseEnd_1985094 : Nat := 226512748079191454287939

theorem tailTrace_1985094 : CollatzResearch.WordTrace tailWord_1985094 prefixEnd_1985094 226512748079191454287939 := by
  unfold tailWord_1985094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2262572695948466872155823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48268217513567293272657557 2262572695948466872155823)
  ·
    refine ⟨3393859043922700308233735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2262572695948466872155823 3393859043922700308233735)
    ·
      refine ⟨5090788565884050462350603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3393859043922700308233735 5090788565884050462350603)
      ·
        refine ⟨7636182848826075693525905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5090788565884050462350603 7636182848826075693525905)
        ·
          refine ⟨5727137136619556770144429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7636182848826075693525905 5727137136619556770144429)
          ·
            refine ⟨2147676426232333788804161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5727137136619556770144429 2147676426232333788804161)
            ·
              refine ⟨1610757319674250341603121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2147676426232333788804161 1610757319674250341603121)
              ·
                refine ⟨1208067989755687756202341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1610757319674250341603121 1208067989755687756202341)
                ·
                  refine ⟨226512748079191454287939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1208067989755687756202341 226512748079191454287939)
                  ·
                    rfl

theorem cell22_1985094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_1985094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985094 prefixEnd_1985094 := by exact prefixLift 1985094
  have htrace : WordTrace (prefixWord ++ tailWord_1985094) baseStart_1985094 baseEnd_1985094 := by
    simpa [prefixWord, tailWord_1985094, baseEnd_1985094] using wordTrace_append hprefix tailTrace_1985094
  have hstable : (prefixWord ++ tailWord_1985094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985094).length < 2 ^ (prefixWord ++ tailWord_1985094).sum := by decide
  have hdescent : baseEnd_1985094 < baseStart_1985094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985099 : List Nat := [1, 1, 1, 1, 3, 1, 4, 3, 7]
def baseStart_1985099 : Nat := 118140960795 + 1985099 * 2 ^ 59
def prefixEnd_1985099 : Nat := 4983230072969 + 3 ^ 40 * 1985099 * 2
def baseEnd_1985099 : Nat := 226513318613252005496267

theorem tailTrace_1985099 : CollatzResearch.WordTrace tailWord_1985099 prefixEnd_1985099 226513318613252005496267 := by
  unfold tailWord_1985099
  simp only [CollatzResearch.WordTrace]
  refine ⟨72402508635332825762918351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48268339090221883841945567 72402508635332825762918351)
  ·
    refine ⟨108603762952999238644377527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72402508635332825762918351 108603762952999238644377527)
    ·
      refine ⟨162905644429498857966566291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108603762952999238644377527 162905644429498857966566291)
      ·
        refine ⟨244358466644248286949849437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162905644429498857966566291 244358466644248286949849437)
        ·
          refine ⟨91634424991593107606193539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 244358466644248286949849437 91634424991593107606193539)
          ·
            refine ⟨137451637487389661409290309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91634424991593107606193539 137451637487389661409290309)
            ·
              refine ⟨25772182028885561514241933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 137451637487389661409290309 25772182028885561514241933)
              ·
                refine ⟨9664568260832085567840725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25772182028885561514241933 9664568260832085567840725)
                ·
                  refine ⟨226513318613252005496267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9664568260832085567840725 226513318613252005496267)
                  ·
                    rfl

theorem cell22_1985099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 7].length) (baseStart_1985099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985099 prefixEnd_1985099 := by exact prefixLift 1985099
  have htrace : WordTrace (prefixWord ++ tailWord_1985099) baseStart_1985099 baseEnd_1985099 := by
    simpa [prefixWord, tailWord_1985099, baseEnd_1985099] using wordTrace_append hprefix tailTrace_1985099
  have hstable : (prefixWord ++ tailWord_1985099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985099).length < 2 ^ (prefixWord ++ tailWord_1985099).sum := by decide
  have hdescent : baseEnd_1985099 < baseStart_1985099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985180 : List Nat := [2, 2, 3, 2, 2, 2, 2, 2, 1, 4]
def baseStart_1985180 : Nat := 118140960795 + 1985180 * 2 ^ 59
def prefixEnd_1985180 : Nat := 4983230072969 + 3 ^ 40 * 1985180 * 2
def baseEnd_1985180 : Nat := 679567683795098805213553

theorem tailTrace_1985180 : CollatzResearch.WordTrace tailWord_1985180 prefixEnd_1985180 679567683795098805213553 := by
  unfold tailWord_1985180
  simp only [CollatzResearch.WordTrace]
  refine ⟨36202731474019688298308497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48270308632026251064411329 36202731474019688298308497)
  ·
    refine ⟨27152048605514766223731373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36202731474019688298308497 27152048605514766223731373)
    ·
      refine ⟨10182018227068037333899265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27152048605514766223731373 10182018227068037333899265)
      ·
        refine ⟨7636513670301028000424449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10182018227068037333899265 7636513670301028000424449)
        ·
          refine ⟨5727385252725771000318337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7636513670301028000424449 5727385252725771000318337)
          ·
            refine ⟨4295538939544328250238753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5727385252725771000318337 4295538939544328250238753)
            ·
              refine ⟨3221654204658246187679065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4295538939544328250238753 3221654204658246187679065)
              ·
                refine ⟨2416240653493684640759299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3221654204658246187679065 2416240653493684640759299)
                ·
                  refine ⟨3624360980240526961138949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2416240653493684640759299 3624360980240526961138949)
                  ·
                    refine ⟨679567683795098805213553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3624360980240526961138949 679567683795098805213553)
                    ·
                      rfl

theorem cell22_1985180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_1985180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985180 prefixEnd_1985180 := by exact prefixLift 1985180
  have htrace : WordTrace (prefixWord ++ tailWord_1985180) baseStart_1985180 baseEnd_1985180 := by
    simpa [prefixWord, tailWord_1985180, baseEnd_1985180] using wordTrace_append hprefix tailTrace_1985180
  have hstable : (prefixWord ++ tailWord_1985180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985180).length < 2 ^ (prefixWord ++ tailWord_1985180).sum := by decide
  have hdescent : baseEnd_1985180 < baseStart_1985180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985330 : List Nat := [3, 2, 1, 1, 3, 1, 1, 6, 4]
def baseStart_1985330 : Nat := 118140960795 + 1985330 * 2 ^ 59
def prefixEnd_1985330 : Nat := 4983230072969 + 3 ^ 40 * 1985330 * 2
def baseEnd_1985330 : Nat := 226539677286849471321031

theorem tailTrace_1985330 : CollatzResearch.WordTrace tailWord_1985330 prefixEnd_1985330 226539677286849471321031 := by
  unfold tailWord_1985330
  simp only [CollatzResearch.WordTrace]
  refine ⟨18102733474373988053644361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48273955931663968143051629 18102733474373988053644361)
  ·
    refine ⟨13577050105780491040233271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18102733474373988053644361 13577050105780491040233271)
    ·
      refine ⟨20365575158670736560349907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13577050105780491040233271 20365575158670736560349907)
      ·
        refine ⟨30548362738006104840524861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20365575158670736560349907 30548362738006104840524861)
        ·
          refine ⟨11455636026752289315196823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30548362738006104840524861 11455636026752289315196823)
          ·
            refine ⟨17183454040128433972795235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11455636026752289315196823 17183454040128433972795235)
            ·
              refine ⟨25775181060192650959192853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17183454040128433972795235 25775181060192650959192853)
              ·
                refine ⟨1208211612196530513712165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25775181060192650959192853 1208211612196530513712165)
                ·
                  refine ⟨226539677286849471321031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1208211612196530513712165 226539677286849471321031)
                  ·
                    rfl

theorem cell22_1985330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_1985330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985330 prefixEnd_1985330 := by exact prefixLift 1985330
  have htrace : WordTrace (prefixWord ++ tailWord_1985330) baseStart_1985330 baseEnd_1985330 := by
    simpa [prefixWord, tailWord_1985330, baseEnd_1985330] using wordTrace_append hprefix tailTrace_1985330
  have hstable : (prefixWord ++ tailWord_1985330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985330).length < 2 ^ (prefixWord ++ tailWord_1985330).sum := by decide
  have hdescent : baseEnd_1985330 < baseStart_1985330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985343 : List Nat := [1, 1, 2, 2, 5, 1, 1, 2, 1, 6]
def baseStart_1985343 : Nat := 118140960795 + 1985343 * 2 ^ 59
def prefixEnd_1985343 : Nat := 4983230072969 + 3 ^ 40 * 1985343 * 2
def baseEnd_1985343 : Nat := 679623482026220713388053

theorem tailTrace_1985343 : CollatzResearch.WordTrace tailWord_1985343 prefixEnd_1985343 679623482026220713388053 := by
  unfold tailWord_1985343
  simp only [CollatzResearch.WordTrace]
  refine ⟨72411408046448855434800683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48274272030965903623200455 72411408046448855434800683)
  ·
    refine ⟨108617112069673283152201025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72411408046448855434800683 108617112069673283152201025)
    ·
      refine ⟨81462834052254962364150769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108617112069673283152201025 81462834052254962364150769)
      ·
        refine ⟨61097125539191221773113077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81462834052254962364150769 61097125539191221773113077)
        ·
          refine ⟨5727855519299177041229351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61097125539191221773113077 5727855519299177041229351)
          ·
            refine ⟨8591783278948765561844027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5727855519299177041229351 8591783278948765561844027)
            ·
              refine ⟨12887674918423148342766041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8591783278948765561844027 12887674918423148342766041)
              ·
                refine ⟨9665756188817361257074531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12887674918423148342766041 9665756188817361257074531)
                ·
                  refine ⟨14498634283226041885611797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9665756188817361257074531 14498634283226041885611797)
                  ·
                    refine ⟨679623482026220713388053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14498634283226041885611797 679623482026220713388053)
                    ·
                      rfl

theorem cell22_1985343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 6].length) (baseStart_1985343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985343 prefixEnd_1985343 := by exact prefixLift 1985343
  have htrace : WordTrace (prefixWord ++ tailWord_1985343) baseStart_1985343 baseEnd_1985343 := by
    simpa [prefixWord, tailWord_1985343, baseEnd_1985343] using wordTrace_append hprefix tailTrace_1985343
  have hstable : (prefixWord ++ tailWord_1985343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985343).length < 2 ^ (prefixWord ++ tailWord_1985343).sum := by decide
  have hdescent : baseEnd_1985343 < baseStart_1985343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985364 : List Nat := [2, 4, 1, 1, 4, 2, 1, 3, 4]
def baseStart_1985364 : Nat := 118140960795 + 1985364 * 2 ^ 59
def prefixEnd_1985364 : Nat := 4983230072969 + 3 ^ 40 * 1985364 * 2
def baseEnd_1985364 : Nat := 226543556918461219537663

theorem tailTrace_1985364 : CollatzResearch.WordTrace tailWord_1985364 prefixEnd_1985364 226543556918461219537663 := by
  unfold tailWord_1985364
  simp only [CollatzResearch.WordTrace]
  refine ⟨36206086989686388010657573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48274782652915184014210097 36206086989686388010657573)
  ·
    refine ⟨6788641310566197751998295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36206086989686388010657573 6788641310566197751998295)
    ·
      refine ⟨10182961965849296627997443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6788641310566197751998295 10182961965849296627997443)
      ·
        refine ⟨15274442948773944941996165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10182961965849296627997443 15274442948773944941996165)
        ·
          refine ⟨2863958052895114676624281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15274442948773944941996165 2863958052895114676624281)
          ·
            refine ⟨2147968539671336007468211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2863958052895114676624281 2147968539671336007468211)
            ·
              refine ⟨3221952809507004011202317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2147968539671336007468211 3221952809507004011202317)
              ·
                refine ⟨1208232303565126504200869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3221952809507004011202317 1208232303565126504200869)
                ·
                  refine ⟨226543556918461219537663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1208232303565126504200869 226543556918461219537663)
                  ·
                    rfl

theorem cell22_1985364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_1985364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985364 prefixEnd_1985364 := by exact prefixLift 1985364
  have htrace : WordTrace (prefixWord ++ tailWord_1985364) baseStart_1985364 baseEnd_1985364 := by
    simpa [prefixWord, tailWord_1985364, baseEnd_1985364] using wordTrace_append hprefix tailTrace_1985364
  have hstable : (prefixWord ++ tailWord_1985364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985364).length < 2 ^ (prefixWord ++ tailWord_1985364).sum := by decide
  have hdescent : baseEnd_1985364 < baseStart_1985364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985388 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 2, 6]
def baseStart_1985388 : Nat := 118140960795 + 1985388 * 2 ^ 59
def prefixEnd_1985388 : Nat := 4983230072969 + 3 ^ 40 * 1985388 * 2
def baseEnd_1985388 : Nat := 679638886445855596012915

theorem tailTrace_1985388 : CollatzResearch.WordTrace tailWord_1985388 prefixEnd_1985388 679638886445855596012915 := by
  unfold tailWord_1985388
  simp only [CollatzResearch.WordTrace]
  refine ⟨36206524665642914060094409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48275366220857218746792545 36206524665642914060094409)
  ·
    refine ⟨27154893499232185545070807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36206524665642914060094409 27154893499232185545070807)
    ·
      refine ⟨40732340248848278317606211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27154893499232185545070807 40732340248848278317606211)
      ·
        refine ⟨61098510373272417476409317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40732340248848278317606211 61098510373272417476409317)
        ·
          refine ⟨11455970694988578276826747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61098510373272417476409317 11455970694988578276826747)
          ·
            refine ⟨17183956042482867415240121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11455970694988578276826747 17183956042482867415240121)
            ·
              refine ⟨12887967031862150561430091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17183956042482867415240121 12887967031862150561430091)
              ·
                refine ⟨19331950547793225842145137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12887967031862150561430091 19331950547793225842145137)
                ·
                  refine ⟨14498962910844919381608853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19331950547793225842145137 14498962910844919381608853)
                  ·
                    refine ⟨679638886445855596012915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14498962910844919381608853 679638886445855596012915)
                    ·
                      rfl

theorem cell22_1985388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_1985388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985388 prefixEnd_1985388 := by exact prefixLift 1985388
  have htrace : WordTrace (prefixWord ++ tailWord_1985388) baseStart_1985388 baseEnd_1985388 := by
    simpa [prefixWord, tailWord_1985388, baseEnd_1985388] using wordTrace_append hprefix tailTrace_1985388
  have hstable : (prefixWord ++ tailWord_1985388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985388).length < 2 ^ (prefixWord ++ tailWord_1985388).sum := by decide
  have hdescent : baseEnd_1985388 < baseStart_1985388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985441 : List Nat := [1, 2, 3, 4, 1, 1, 4, 2, 1, 3]
def baseStart_1985441 : Nat := 118140960795 + 1985441 * 2 ^ 59
def prefixEnd_1985441 : Nat := 4983230072969 + 3 ^ 40 * 1985441 * 2
def baseEnd_1985441 : Nat := 679657029428981124437753

theorem tailTrace_1985441 : CollatzResearch.WordTrace tailWord_1985441 prefixEnd_1985441 679657029428981124437753 := by
  unfold tailWord_1985441
  simp only [CollatzResearch.WordTrace]
  refine ⟨72414982400093818171868177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48276654933395878781245451 72414982400093818171868177)
  ·
    refine ⟨54311236800070363628901133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72414982400093818171868177 54311236800070363628901133)
    ·
      refine ⟨20366713800026386360837925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54311236800070363628901133 20366713800026386360837925)
      ·
        refine ⟨3818758837504947442657111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20366713800026386360837925 3818758837504947442657111)
        ·
          refine ⟨5728138256257421163985667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3818758837504947442657111 5728138256257421163985667)
          ·
            refine ⟨8592207384386131745978501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5728138256257421163985667 8592207384386131745978501)
            ·
              refine ⟨1611038884572399702370969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8592207384386131745978501 1611038884572399702370969)
              ·
                refine ⟨1208279163429299776778227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1611038884572399702370969 1208279163429299776778227)
                ·
                  refine ⟨1812418745143949665167341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1208279163429299776778227 1812418745143949665167341)
                  ·
                    refine ⟨679657029428981124437753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1812418745143949665167341 679657029428981124437753)
                    ·
                      rfl

theorem cell22_1985441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_1985441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985441 prefixEnd_1985441 := by exact prefixLift 1985441
  have htrace : WordTrace (prefixWord ++ tailWord_1985441) baseStart_1985441 baseEnd_1985441 := by
    simpa [prefixWord, tailWord_1985441, baseEnd_1985441] using wordTrace_append hprefix tailTrace_1985441
  have hstable : (prefixWord ++ tailWord_1985441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985441).length < 2 ^ (prefixWord ++ tailWord_1985441).sum := by decide
  have hdescent : baseEnd_1985441 < baseStart_1985441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985465 : List Nat := [1, 2, 1, 4, 2, 3, 1, 2, 6]
def baseStart_1985465 : Nat := 118140960795 + 1985465 * 2 ^ 59
def prefixEnd_1985465 : Nat := 4983230072969 + 3 ^ 40 * 1985465 * 2
def baseEnd_1985465 : Nat := 226555081706484353945893

theorem tailTrace_1985465 : CollatzResearch.WordTrace tailWord_1985465 prefixEnd_1985465 226555081706484353945893 := by
  unfold tailWord_1985465
  simp only [CollatzResearch.WordTrace]
  refine ⟨72415857752006870270741849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48277238501337913513827899 72415857752006870270741849)
  ·
    refine ⟨54311893314005152703056387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72415857752006870270741849 54311893314005152703056387)
    ·
      refine ⟨81467839971007729054584581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54311893314005152703056387 81467839971007729054584581)
      ·
        refine ⟨15275219994563949197734609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81467839971007729054584581 15275219994563949197734609)
        ·
          refine ⟨11456414995922961898300957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15275219994563949197734609 11456414995922961898300957)
          ·
            refine ⟨4296155623471110711862859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11456414995922961898300957 4296155623471110711862859)
            ·
              refine ⟨6444233435206666067794289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4296155623471110711862859 6444233435206666067794289)
              ·
                refine ⟨4833175076404999550845717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6444233435206666067794289 4833175076404999550845717)
                ·
                  refine ⟨226555081706484353945893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4833175076404999550845717 226555081706484353945893)
                  ·
                    rfl

theorem cell22_1985465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 6].length) (baseStart_1985465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985465 prefixEnd_1985465 := by exact prefixLift 1985465
  have htrace : WordTrace (prefixWord ++ tailWord_1985465) baseStart_1985465 baseEnd_1985465 := by
    simpa [prefixWord, tailWord_1985465, baseEnd_1985465] using wordTrace_append hprefix tailTrace_1985465
  have hstable : (prefixWord ++ tailWord_1985465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985465).length < 2 ^ (prefixWord ++ tailWord_1985465).sum := by decide
  have hdescent : baseEnd_1985465 < baseStart_1985465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985497 : List Nat := [1, 2, 1, 2, 5, 2, 1, 1, 4, 3]
def baseStart_1985497 : Nat := 118140960795 + 1985497 * 2 ^ 59
def prefixEnd_1985497 : Nat := 4983230072969 + 3 ^ 40 * 1985497 * 2
def baseEnd_1985497 : Nat := 679676199373415645037581

theorem tailTrace_1985497 : CollatzResearch.WordTrace tailWord_1985497 prefixEnd_1985497 679676199373415645037581 := by
  unfold tailWord_1985497
  simp only [CollatzResearch.WordTrace]
  refine ⟨72417024887890939735906745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48278016591927293157271163 72417024887890939735906745)
  ·
    refine ⟨54312768665918204801930059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72417024887890939735906745 54312768665918204801930059)
    ·
      refine ⟨81469152998877307202895089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54312768665918204801930059 81469152998877307202895089)
      ·
        refine ⟨61101864749157980402171317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81469152998877307202895089 61101864749157980402171317)
        ·
          refine ⟨5728299820233560662703561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61101864749157980402171317 5728299820233560662703561)
          ·
            refine ⟨4296224865175170497027671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5728299820233560662703561 4296224865175170497027671)
            ·
              refine ⟨6444337297762755745541507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4296224865175170497027671 6444337297762755745541507)
              ·
                refine ⟨9666505946644133618312261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6444337297762755745541507 9666505946644133618312261)
                ·
                  refine ⟨1812469864995775053433549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9666505946644133618312261 1812469864995775053433549)
                  ·
                    refine ⟨679676199373415645037581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1812469864995775053433549 679676199373415645037581)
                    ·
                      rfl

theorem cell22_1985497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4, 3].length) (baseStart_1985497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985497 prefixEnd_1985497 := by exact prefixLift 1985497
  have htrace : WordTrace (prefixWord ++ tailWord_1985497) baseStart_1985497 baseEnd_1985497 := by
    simpa [prefixWord, tailWord_1985497, baseEnd_1985497] using wordTrace_append hprefix tailTrace_1985497
  have hstable : (prefixWord ++ tailWord_1985497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985497).length < 2 ^ (prefixWord ++ tailWord_1985497).sum := by decide
  have hdescent : baseEnd_1985497 < baseStart_1985497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985555 : List Nat := [1, 1, 1, 2, 1, 4, 1, 6, 5]
def baseStart_1985555 : Nat := 118140960795 + 1985555 * 2 ^ 59
def prefixEnd_1985555 : Nat := 4983230072969 + 3 ^ 40 * 1985555 * 2
def baseEnd_1985555 : Nat := 226565351319574275695801

theorem tailTrace_1985555 : CollatzResearch.WordTrace tailWord_1985555 prefixEnd_1985555 226565351319574275695801 := by
  unfold tailWord_1985555
  simp only [CollatzResearch.WordTrace]
  refine ⟨72419140321680815641518119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48279426881120543761012079 72419140321680815641518119)
  ·
    refine ⟨108628710482521223462277179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72419140321680815641518119 108628710482521223462277179)
    ·
      refine ⟨162943065723781835193415769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108628710482521223462277179 162943065723781835193415769)
      ·
        refine ⟨122207299292836376395061827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162943065723781835193415769 122207299292836376395061827)
        ·
          refine ⟨183310948939254564592592741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122207299292836376395061827 183310948939254564592592741)
          ·
            refine ⟨34370802926110230861111139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 183310948939254564592592741 34370802926110230861111139)
            ·
              refine ⟨51556204389165346291666709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34370802926110230861111139 51556204389165346291666709)
              ·
                refine ⟨2416697080742125607421877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 51556204389165346291666709 2416697080742125607421877)
                ·
                  refine ⟨226565351319574275695801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2416697080742125607421877 226565351319574275695801)
                  ·
                    rfl

theorem cell22_1985555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 5].length) (baseStart_1985555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985555 prefixEnd_1985555 := by exact prefixLift 1985555
  have htrace : WordTrace (prefixWord ++ tailWord_1985555) baseStart_1985555 baseEnd_1985555 := by
    simpa [prefixWord, tailWord_1985555, baseEnd_1985555] using wordTrace_append hprefix tailTrace_1985555
  have hstable : (prefixWord ++ tailWord_1985555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985555).length < 2 ^ (prefixWord ++ tailWord_1985555).sum := by decide
  have hdescent : baseEnd_1985555 < baseStart_1985555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985559 : List Nat := [1, 1, 3, 5, 1, 1, 3, 1, 3, 3]
def baseStart_1985559 : Nat := 118140960795 + 1985559 * 2 ^ 59
def prefixEnd_1985559 : Nat := 4983230072969 + 3 ^ 40 * 1985559 * 2
def baseEnd_1985559 : Nat := 679697423240468149987391

theorem tailTrace_1985559 : CollatzResearch.WordTrace tailWord_1985559 prefixEnd_1985559 679697423240468149987391 := by
  unfold tailWord_1985559
  simp only [CollatzResearch.WordTrace]
  refine ⟨72419286213666324324663731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48279524142444216216442487 72419286213666324324663731)
  ·
    refine ⟨108628929320499486486995597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72419286213666324324663731 108628929320499486486995597)
    ·
      refine ⟨40735848495187307432623349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108628929320499486486995597 40735848495187307432623349)
      ·
        refine ⟨3818985796423810071808439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40735848495187307432623349 3818985796423810071808439)
        ·
          refine ⟨5728478694635715107712659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3818985796423810071808439 5728478694635715107712659)
          ·
            refine ⟨8592718041953572661568989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5728478694635715107712659 8592718041953572661568989)
            ·
              refine ⟨3222269265732589748088371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8592718041953572661568989 3222269265732589748088371)
              ·
                refine ⟨4833403898598884622132557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3222269265732589748088371 4833403898598884622132557)
                ·
                  refine ⟨1812526461974581733299709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4833403898598884622132557 1812526461974581733299709)
                  ·
                    refine ⟨679697423240468149987391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1812526461974581733299709 679697423240468149987391)
                    ·
                      rfl

theorem cell22_1985559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3, 3].length) (baseStart_1985559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985559 prefixEnd_1985559 := by exact prefixLift 1985559
  have htrace : WordTrace (prefixWord ++ tailWord_1985559) baseStart_1985559 baseEnd_1985559 := by
    simpa [prefixWord, tailWord_1985559, baseEnd_1985559] using wordTrace_append hprefix tailTrace_1985559
  have hstable : (prefixWord ++ tailWord_1985559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985559).length < 2 ^ (prefixWord ++ tailWord_1985559).sum := by decide
  have hdescent : baseEnd_1985559 < baseStart_1985559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985606 : List Nat := [6, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_1985606 : Nat := 118140960795 + 1985606 * 2 ^ 59
def prefixEnd_1985606 : Nat := 4983230072969 + 3 ^ 40 * 1985606 * 2
def baseEnd_1985606 : Nat := 226571170766991898020749

theorem tailTrace_1985606 : CollatzResearch.WordTrace tailWord_1985606 prefixEnd_1985606 226571170766991898020749 := by
  unfold tailWord_1985606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2263156263890501604738271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48280666962997367567749781 2263156263890501604738271)
  ·
    refine ⟨3394734395835752407107407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2263156263890501604738271 3394734395835752407107407)
    ·
      refine ⟨5092101593753628610661111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3394734395835752407107407 5092101593753628610661111)
      ·
        refine ⟨7638152390630442915991667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5092101593753628610661111 7638152390630442915991667)
        ·
          refine ⟨11457228585945664373987501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7638152390630442915991667 11457228585945664373987501)
          ·
            refine ⟨4296460719729624140245313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11457228585945664373987501 4296460719729624140245313)
            ·
              refine ⟨3222345539797218105183985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4296460719729624140245313 3222345539797218105183985)
              ·
                refine ⟨2416759154847913578887989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3222345539797218105183985 2416759154847913578887989)
                ·
                  refine ⟨226571170766991898020749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2416759154847913578887989 226571170766991898020749)
                  ·
                    rfl

theorem cell22_1985606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_1985606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985606 prefixEnd_1985606 := by exact prefixLift 1985606
  have htrace : WordTrace (prefixWord ++ tailWord_1985606) baseStart_1985606 baseEnd_1985606 := by
    simpa [prefixWord, tailWord_1985606, baseEnd_1985606] using wordTrace_append hprefix tailTrace_1985606
  have hstable : (prefixWord ++ tailWord_1985606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985606).length < 2 ^ (prefixWord ++ tailWord_1985606).sum := by decide
  have hdescent : baseEnd_1985606 < baseStart_1985606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985632 : List Nat := [2, 1, 1, 3, 2, 2, 4, 1, 1, 5]
def baseStart_1985632 : Nat := 118140960795 + 1985632 * 2 ^ 59
def prefixEnd_1985632 : Nat := 4983230072969 + 3 ^ 40 * 1985632 * 2
def baseEnd_1985632 : Nat := 679722412632320292912167

theorem tailTrace_1985632 : CollatzResearch.WordTrace tailWord_1985632 prefixEnd_1985632 679722412632320292912167 := by
  unfold tailWord_1985632
  simp only [CollatzResearch.WordTrace]
  refine ⟨36210974371200928896035575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48281299161601238528047433 36210974371200928896035575)
  ·
    refine ⟨54316461556801393344053363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36210974371200928896035575 54316461556801393344053363)
    ·
      refine ⟨81474692335202090016080045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54316461556801393344053363 81474692335202090016080045)
      ·
        refine ⟨30553009625700783756030017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81474692335202090016080045 30553009625700783756030017)
        ·
          refine ⟨22914757219275587817022513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30553009625700783756030017 22914757219275587817022513)
          ·
            refine ⟨17186067914456690862766885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22914757219275587817022513 17186067914456690862766885)
            ·
              refine ⟨3222387733960629536768791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17186067914456690862766885 3222387733960629536768791)
              ·
                refine ⟨4833581600940944305153187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3222387733960629536768791 4833581600940944305153187)
                ·
                  refine ⟨7250372401411416457729781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4833581600940944305153187 7250372401411416457729781)
                  ·
                    refine ⟨679722412632320292912167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7250372401411416457729781 679722412632320292912167)
                    ·
                      rfl

theorem cell22_1985632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 1, 5].length) (baseStart_1985632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985632 prefixEnd_1985632 := by exact prefixLift 1985632
  have htrace : WordTrace (prefixWord ++ tailWord_1985632) baseStart_1985632 baseEnd_1985632 := by
    simpa [prefixWord, tailWord_1985632, baseEnd_1985632] using wordTrace_append hprefix tailTrace_1985632
  have hstable : (prefixWord ++ tailWord_1985632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985632).length < 2 ^ (prefixWord ++ tailWord_1985632).sum := by decide
  have hdescent : baseEnd_1985632 < baseStart_1985632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985634 : List Nat := [3, 3, 2, 2, 1, 2, 1, 2, 6]
def baseStart_1985634 : Nat := 118140960795 + 1985634 * 2 ^ 59
def prefixEnd_1985634 : Nat := 4983230072969 + 3 ^ 40 * 1985634 * 2
def baseEnd_1985634 : Nat := 226574365757730984787387

theorem tailTrace_1985634 : CollatzResearch.WordTrace tailWord_1985634 prefixEnd_1985634 226574365757730984787387 := by
  unfold tailWord_1985634
  simp only [CollatzResearch.WordTrace]
  refine ⟨18105505422098653033410989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48281347792263074755762637 18105505422098653033410989)
  ·
    refine ⟨6789564533286994887529121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18105505422098653033410989 6789564533286994887529121)
    ·
      refine ⟨5092173399965246165646841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6789564533286994887529121 5092173399965246165646841)
      ·
        refine ⟨3819130049973934624235131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5092173399965246165646841 3819130049973934624235131)
        ·
          refine ⟨5728695074960901936352697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3819130049973934624235131 5728695074960901936352697)
          ·
            refine ⟨4296521306220676452264523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5728695074960901936352697 4296521306220676452264523)
            ·
              refine ⟨6444781959331014678396785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4296521306220676452264523 6444781959331014678396785)
              ·
                refine ⟨4833586469498261008797589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6444781959331014678396785 4833586469498261008797589)
                ·
                  refine ⟨226574365757730984787387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4833586469498261008797589 226574365757730984787387)
                  ·
                    rfl

theorem cell22_1985634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_1985634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985634 prefixEnd_1985634 := by exact prefixLift 1985634
  have htrace : WordTrace (prefixWord ++ tailWord_1985634) baseStart_1985634 baseEnd_1985634 := by
    simpa [prefixWord, tailWord_1985634, baseEnd_1985634] using wordTrace_append hprefix tailTrace_1985634
  have hstable : (prefixWord ++ tailWord_1985634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985634).length < 2 ^ (prefixWord ++ tailWord_1985634).sum := by decide
  have hdescent : baseEnd_1985634 < baseStart_1985634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985675 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 1, 8]
def baseStart_1985675 : Nat := 118140960795 + 1985675 * 2 ^ 59
def prefixEnd_1985675 : Nat := 4983230072969 + 3 ^ 40 * 1985675 * 2
def baseEnd_1985675 : Nat := 679737132411082514087035

theorem tailTrace_1985675 : CollatzResearch.WordTrace tailWord_1985675 prefixEnd_1985675 679737132411082514087035 := by
  unfold tailWord_1985675
  simp only [CollatzResearch.WordTrace]
  refine ⟨72423517081246076135886479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48282344720830717423924319 72423517081246076135886479)
  ·
    refine ⟨108635275621869114203829719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72423517081246076135886479 108635275621869114203829719)
    ·
      refine ⟨162952913432803671305744579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108635275621869114203829719 162952913432803671305744579)
      ·
        refine ⟨244429370149205506958616869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162952913432803671305744579 244429370149205506958616869)
        ·
          refine ⟨45830506902976032554740663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244429370149205506958616869 45830506902976032554740663)
          ·
            refine ⟨68745760354464048832110995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45830506902976032554740663 68745760354464048832110995)
            ·
              refine ⟨103118640531696073248166493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68745760354464048832110995 103118640531696073248166493)
              ·
                refine ⟨38669490199386027468062435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103118640531696073248166493 38669490199386027468062435)
                ·
                  refine ⟨58004235299079041202093653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38669490199386027468062435 58004235299079041202093653)
                  ·
                    refine ⟨679737132411082514087035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58004235299079041202093653 679737132411082514087035)
                    ·
                      rfl

theorem cell22_1985675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 8].length) (baseStart_1985675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985675 prefixEnd_1985675 := by exact prefixLift 1985675
  have htrace : WordTrace (prefixWord ++ tailWord_1985675) baseStart_1985675 baseEnd_1985675 := by
    simpa [prefixWord, tailWord_1985675, baseEnd_1985675] using wordTrace_append hprefix tailTrace_1985675
  have hstable : (prefixWord ++ tailWord_1985675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985675).length < 2 ^ (prefixWord ++ tailWord_1985675).sum := by decide
  have hdescent : baseEnd_1985675 < baseStart_1985675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985711 : List Nat := [1, 1, 2, 1, 2, 3, 5, 3, 1, 3]
def baseStart_1985711 : Nat := 118140960795 + 1985711 * 2 ^ 59
def prefixEnd_1985711 : Nat := 4983230072969 + 3 ^ 40 * 1985711 * 2
def baseEnd_1985711 : Nat := 679749455946790420186925

theorem tailTrace_1985711 : CollatzResearch.WordTrace tailWord_1985711 prefixEnd_1985711 679749455946790420186925 := by
  unfold tailWord_1985711
  simp only [CollatzResearch.WordTrace]
  refine ⟨72424830109115654284196987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48283220072743769522797991 72424830109115654284196987)
  ·
    refine ⟨108637245163673481426295481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72424830109115654284196987 108637245163673481426295481)
    ·
      refine ⟨81477933872755111069721611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108637245163673481426295481 81477933872755111069721611)
      ·
        refine ⟨122216900809132666604582417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81477933872755111069721611 122216900809132666604582417)
        ·
          refine ⟨91662675606849499953436813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122216900809132666604582417 91662675606849499953436813)
          ·
            refine ⟨34373503352568562482538805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91662675606849499953436813 34373503352568562482538805)
            ·
              refine ⟨3222515939303302732738013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34373503352568562482538805 3222515939303302732738013)
              ·
                refine ⟨1208443477238738524776755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3222515939303302732738013 1208443477238738524776755)
                ·
                  refine ⟨1812665215858107787165133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1208443477238738524776755 1812665215858107787165133)
                  ·
                    refine ⟨679749455946790420186925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1812665215858107787165133 679749455946790420186925)
                    ·
                      rfl

theorem cell22_1985711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3, 1, 3].length) (baseStart_1985711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985711 prefixEnd_1985711 := by exact prefixLift 1985711
  have htrace : WordTrace (prefixWord ++ tailWord_1985711) baseStart_1985711 baseEnd_1985711 := by
    simpa [prefixWord, tailWord_1985711, baseEnd_1985711] using wordTrace_append hprefix tailTrace_1985711
  have hstable : (prefixWord ++ tailWord_1985711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985711).length < 2 ^ (prefixWord ++ tailWord_1985711).sum := by decide
  have hdescent : baseEnd_1985711 < baseStart_1985711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985728 : List Nat := [2, 1, 1, 2, 7, 1, 1, 1, 3, 3]
def baseStart_1985728 : Nat := 118140960795 + 1985728 * 2 ^ 59
def prefixEnd_1985728 : Nat := 4983230072969 + 3 ^ 40 * 1985728 * 2
def baseEnd_1985728 : Nat := 679755275394208042511873

theorem tailTrace_1985728 : CollatzResearch.WordTrace tailWord_1985728 prefixEnd_1985728 679755275394208042511873 := by
  unfold tailWord_1985728
  simp only [CollatzResearch.WordTrace]
  refine ⟨36212725075027033093782919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48283633433369377458377225 36212725075027033093782919)
  ·
    refine ⟨54319087612540549640674379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36212725075027033093782919 54319087612540549640674379)
    ·
      refine ⟨81478631418810824461011569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54319087612540549640674379 81478631418810824461011569)
      ·
        refine ⟨61108973564108118345758677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81478631418810824461011569 61108973564108118345758677)
        ·
          refine ⟨1432241567908784023728719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 61108973564108118345758677 1432241567908784023728719)
          ·
            refine ⟨2148362351863176035593079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1432241567908784023728719 2148362351863176035593079)
            ·
              refine ⟨3222543527794764053389619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2148362351863176035593079 3222543527794764053389619)
              ·
                refine ⟨4833815291692146080084429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3222543527794764053389619 4833815291692146080084429)
                ·
                  refine ⟨1812680734384554780031661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4833815291692146080084429 1812680734384554780031661)
                  ·
                    refine ⟨679755275394208042511873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1812680734384554780031661 679755275394208042511873)
                    ·
                      rfl

theorem cell22_1985728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 3, 3].length) (baseStart_1985728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985728 prefixEnd_1985728 := by exact prefixLift 1985728
  have htrace : WordTrace (prefixWord ++ tailWord_1985728) baseStart_1985728 baseEnd_1985728 := by
    simpa [prefixWord, tailWord_1985728, baseEnd_1985728] using wordTrace_append hprefix tailTrace_1985728
  have hstable : (prefixWord ++ tailWord_1985728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985728).length < 2 ^ (prefixWord ++ tailWord_1985728).sum := by decide
  have hdescent : baseEnd_1985728 < baseStart_1985728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985734 : List Nat := [6, 1, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_1985734 : Nat := 118140960795 + 1985734 * 2 ^ 59
def prefixEnd_1985734 : Nat := 4983230072969 + 3 ^ 40 * 1985734 * 2
def baseEnd_1985734 : Nat := 679757329316826026861855

theorem tailTrace_1985734 : CollatzResearch.WordTrace tailWord_1985734 prefixEnd_1985734 679757329316826026861855 := by
  unfold tailWord_1985734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2263302155876010287883883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48283779325354886141522837 2263302155876010287883883)
  ·
    refine ⟨3394953233814015431825825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2263302155876010287883883 3394953233814015431825825)
    ·
      refine ⟨2546214925360511573869369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3394953233814015431825825 2546214925360511573869369)
      ·
        refine ⟨1909661194020383680402027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2546214925360511573869369 1909661194020383680402027)
        ·
          refine ⟨2864491791030575520603041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1909661194020383680402027 2864491791030575520603041)
          ·
            refine ⟨2148368843272931640452281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2864491791030575520603041 2148368843272931640452281)
            ·
              refine ⟨1611276632454698730339211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2148368843272931640452281 1611276632454698730339211)
              ·
                refine ⟨2416914948682048095508817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1611276632454698730339211 2416914948682048095508817)
                ·
                  refine ⟨1812686211511536071631613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2416914948682048095508817 1812686211511536071631613)
                  ·
                    refine ⟨679757329316826026861855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1812686211511536071631613 679757329316826026861855)
                    ·
                      rfl

theorem cell22_1985734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_1985734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985734 prefixEnd_1985734 := by exact prefixLift 1985734
  have htrace : WordTrace (prefixWord ++ tailWord_1985734) baseStart_1985734 baseEnd_1985734 := by
    simpa [prefixWord, tailWord_1985734, baseEnd_1985734] using wordTrace_append hprefix tailTrace_1985734
  have hstable : (prefixWord ++ tailWord_1985734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985734).length < 2 ^ (prefixWord ++ tailWord_1985734).sum := by decide
  have hdescent : baseEnd_1985734 < baseStart_1985734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985771 : List Nat := [1, 1, 1, 1, 2, 7, 3, 1, 1, 4]
def baseStart_1985771 : Nat := 118140960795 + 1985771 * 2 ^ 59
def prefixEnd_1985771 : Nat := 4983230072969 + 3 ^ 40 * 1985771 * 2
def baseEnd_1985771 : Nat := 679769995172970263686741

theorem tailTrace_1985771 : CollatzResearch.WordTrace tailWord_1985771 prefixEnd_1985771 679769995172970263686741 := by
  unfold tailWord_1985771
  simp only [CollatzResearch.WordTrace]
  refine ⟨72427018488898284531381167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48284678992598856354254111 72427018488898284531381167)
  ·
    refine ⟨108640527733347426797071751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72427018488898284531381167 108640527733347426797071751)
    ·
      refine ⟨162960791600021140195607627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108640527733347426797071751 162960791600021140195607627)
      ·
        refine ⟨244441187400031710293411441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162960791600021140195607627 244441187400031710293411441)
        ·
          refine ⟨183330890550023782720058581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244441187400031710293411441 183330890550023782720058581)
          ·
            refine ⟨4296817747266182407501373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 183330890550023782720058581 4296817747266182407501373)
            ·
              refine ⟨1611306655224818402813015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4296817747266182407501373 1611306655224818402813015)
              ·
                refine ⟨2416959982837227604219523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1611306655224818402813015 2416959982837227604219523)
                ·
                  refine ⟨3625439974255841406329285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2416959982837227604219523 3625439974255841406329285)
                  ·
                    refine ⟨679769995172970263686741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3625439974255841406329285 679769995172970263686741)
                    ·
                      rfl

theorem cell22_1985771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 1, 4].length) (baseStart_1985771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985771 prefixEnd_1985771 := by exact prefixLift 1985771
  have htrace : WordTrace (prefixWord ++ tailWord_1985771) baseStart_1985771 baseEnd_1985771 := by
    simpa [prefixWord, tailWord_1985771, baseEnd_1985771] using wordTrace_append hprefix tailTrace_1985771
  have hstable : (prefixWord ++ tailWord_1985771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985771).length < 2 ^ (prefixWord ++ tailWord_1985771).sum := by decide
  have hdescent : baseEnd_1985771 < baseStart_1985771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985816 : List Nat := [2, 1, 2, 3, 1, 5, 1, 1, 2, 4]
def baseStart_1985816 : Nat := 118140960795 + 1985816 * 2 ^ 59
def prefixEnd_1985816 : Nat := 4983230072969 + 3 ^ 40 * 1985816 * 2
def baseEnd_1985816 : Nat := 679785399592605146311603

theorem tailTrace_1985816 : CollatzResearch.WordTrace tailWord_1985816 prefixEnd_1985816 679785399592605146311603 := by
  unfold tailWord_1985816
  simp only [CollatzResearch.WordTrace]
  refine ⟨36214329886867628608384651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48285773182490171477846201 36214329886867628608384651)
  ·
    refine ⟨54321494830301442912576977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36214329886867628608384651 54321494830301442912576977)
    ·
      refine ⟨40741121122726082184432733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54321494830301442912576977 40741121122726082184432733)
      ·
        refine ⟨15277920421022280819162275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40741121122726082184432733 15277920421022280819162275)
        ·
          refine ⟨22916880631533421228743413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15277920421022280819162275 22916880631533421228743413)
          ·
            refine ⟨2148457559206258240194695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22916880631533421228743413 2148457559206258240194695)
            ·
              refine ⟨3222686338809387360292043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2148457559206258240194695 3222686338809387360292043)
              ·
                refine ⟨4834029508214081040438065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3222686338809387360292043 4834029508214081040438065)
                ·
                  refine ⟨3625522131160560780328549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4834029508214081040438065 3625522131160560780328549)
                  ·
                    refine ⟨679785399592605146311603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3625522131160560780328549 679785399592605146311603)
                    ·
                      rfl

theorem cell22_1985816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 2, 4].length) (baseStart_1985816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985816 prefixEnd_1985816 := by exact prefixLift 1985816
  have htrace : WordTrace (prefixWord ++ tailWord_1985816) baseStart_1985816 baseEnd_1985816 := by
    simpa [prefixWord, tailWord_1985816, baseEnd_1985816] using wordTrace_append hprefix tailTrace_1985816
  have hstable : (prefixWord ++ tailWord_1985816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985816).length < 2 ^ (prefixWord ++ tailWord_1985816).sum := by decide
  have hdescent : baseEnd_1985816 < baseStart_1985816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985822 : List Nat := [4, 3, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_1985822 : Nat := 118140960795 + 1985822 * 2 ^ 59
def prefixEnd_1985822 : Nat := 4983230072969 + 3 ^ 40 * 1985822 * 2
def baseEnd_1985822 : Nat := 679787453515223130661585

theorem tailTrace_1985822 : CollatzResearch.WordTrace tailWord_1985822 prefixEnd_1985822 679787453515223130661585 := by
  unfold tailWord_1985822
  simp only [CollatzResearch.WordTrace]
  refine ⟨9053609826464190030185965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48285919074475680160991813 9053609826464190030185965)
  ·
    refine ⟨3395103684924071261319737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9053609826464190030185965 3395103684924071261319737)
    ·
      refine ⟨2546327763693053445989803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3395103684924071261319737 2546327763693053445989803)
      ·
        refine ⟨3819491645539580168984705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2546327763693053445989803 3819491645539580168984705)
        ·
          refine ⟨2864618734154685126738529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3819491645539580168984705 2864618734154685126738529)
          ·
            refine ⟨2148464050616013845053897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2864618734154685126738529 2148464050616013845053897)
            ·
              refine ⟨1611348037962010383790423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2148464050616013845053897 1611348037962010383790423)
              ·
                refine ⟨2417022056943015575685635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1611348037962010383790423 2417022056943015575685635)
                ·
                  refine ⟨3625533085414523363528453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2417022056943015575685635 3625533085414523363528453)
                  ·
                    refine ⟨679787453515223130661585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3625533085414523363528453 679787453515223130661585)
                    ·
                      rfl

theorem cell22_1985822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_1985822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985822 prefixEnd_1985822 := by exact prefixLift 1985822
  have htrace : WordTrace (prefixWord ++ tailWord_1985822) baseStart_1985822 baseEnd_1985822 := by
    simpa [prefixWord, tailWord_1985822, baseEnd_1985822] using wordTrace_append hprefix tailTrace_1985822
  have hstable : (prefixWord ++ tailWord_1985822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985822).length < 2 ^ (prefixWord ++ tailWord_1985822).sum := by decide
  have hdescent : baseEnd_1985822 < baseStart_1985822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985923 : List Nat := [1, 1, 1, 3, 5, 3, 1, 2, 1, 4]
def baseStart_1985923 : Nat := 118140960795 + 1985923 * 2 ^ 59
def prefixEnd_1985923 : Nat := 4983230072969 + 3 ^ 40 * 1985923 * 2
def baseEnd_1985923 : Nat := 679822027879292533886275

theorem tailTrace_1985923 : CollatzResearch.WordTrace tailWord_1985923 prefixEnd_1985923 679822027879292533886275 := by
  unfold tailWord_1985923
  simp only [CollatzResearch.WordTrace]
  refine ⟨72432562384347614490914423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48288374922898409660609615 72432562384347614490914423)
  ·
    refine ⟨108648843576521421736371635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72432562384347614490914423 108648843576521421736371635)
    ·
      refine ⟨162973265364782132604557453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108648843576521421736371635 162973265364782132604557453)
      ·
        refine ⟨61114974511793299726709045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 162973265364782132604557453 61114974511793299726709045)
        ·
          refine ⟨5729528860480621849378973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61114974511793299726709045 5729528860480621849378973)
          ·
            refine ⟨2148573322680233193517115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5729528860480621849378973 2148573322680233193517115)
            ·
              refine ⟨3222859984020349790275673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2148573322680233193517115 3222859984020349790275673)
              ·
                refine ⟨2417144988015262342706755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3222859984020349790275673 2417144988015262342706755)
                ·
                  refine ⟨3625717482022893514060133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2417144988015262342706755 3625717482022893514060133)
                  ·
                    refine ⟨679822027879292533886275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3625717482022893514060133 679822027879292533886275)
                    ·
                      rfl

theorem cell22_1985923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 4].length) (baseStart_1985923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985923 prefixEnd_1985923 := by exact prefixLift 1985923
  have htrace : WordTrace (prefixWord ++ tailWord_1985923) baseStart_1985923 baseEnd_1985923 := by
    simpa [prefixWord, tailWord_1985923, baseEnd_1985923] using wordTrace_append hprefix tailTrace_1985923
  have hstable : (prefixWord ++ tailWord_1985923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985923).length < 2 ^ (prefixWord ++ tailWord_1985923).sum := by decide
  have hdescent : baseEnd_1985923 < baseStart_1985923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985940 : List Nat := [2, 4, 2, 1, 2, 2, 3, 1, 1, 4]
def baseStart_1985940 : Nat := 118140960795 + 1985940 * 2 ^ 59
def prefixEnd_1985940 : Nat := 4983230072969 + 3 ^ 40 * 1985940 * 2
def baseEnd_1985940 : Nat := 679827847326710156211223

theorem tailTrace_1985940 : CollatzResearch.WordTrace tailWord_1985940 prefixEnd_1985940 679827847326710156211223 := by
  unfold tailWord_1985940
  simp only [CollatzResearch.WordTrace]
  refine ⟨36216591212643013197141637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48288788283524017596188849 36216591212643013197141637)
  ·
    refine ⟨6790610852370564974464057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36216591212643013197141637 6790610852370564974464057)
    ·
      refine ⟨5092958139277923730848043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6790610852370564974464057 5092958139277923730848043)
      ·
        refine ⟨7639437208916885596272065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5092958139277923730848043 7639437208916885596272065)
        ·
          refine ⟨5729577906687664197204049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7639437208916885596272065 5729577906687664197204049)
          ·
            refine ⟨4297183430015748147903037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5729577906687664197204049 4297183430015748147903037)
            ·
              refine ⟨1611443786255905555463639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4297183430015748147903037 1611443786255905555463639)
              ·
                refine ⟨2417165679383858333195459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1611443786255905555463639 2417165679383858333195459)
                ·
                  refine ⟨3625748519075787499793189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2417165679383858333195459 3625748519075787499793189)
                  ·
                    refine ⟨679827847326710156211223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3625748519075787499793189 679827847326710156211223)
                    ·
                      rfl

theorem cell22_1985940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_1985940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985940 prefixEnd_1985940 := by exact prefixLift 1985940
  have htrace : WordTrace (prefixWord ++ tailWord_1985940) baseStart_1985940 baseEnd_1985940 := by
    simpa [prefixWord, tailWord_1985940, baseEnd_1985940] using wordTrace_append hprefix tailTrace_1985940
  have hstable : (prefixWord ++ tailWord_1985940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985940).length < 2 ^ (prefixWord ++ tailWord_1985940).sum := by decide
  have hdescent : baseEnd_1985940 < baseStart_1985940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985949 : List Nat := [1, 4, 2, 1, 3, 11]
def baseStart_1985949 : Nat := 118140960795 + 1985949 * 2 ^ 59
def prefixEnd_1985949 : Nat := 4983230072969 + 3 ^ 40 * 1985949 * 2
def baseEnd_1985949 : Nat := 8392974422353544848595

theorem tailTrace_1985949 : CollatzResearch.WordTrace tailWord_1985949 prefixEnd_1985949 8392974422353544848595 := by
  unfold tailWord_1985949
  simp only [CollatzResearch.WordTrace]
  refine ⟨72433510682253420931360901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48289007121502280620907267 72433510682253420931360901)
  ·
    refine ⟨13581283252922516424630169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72433510682253420931360901 13581283252922516424630169)
    ·
      refine ⟨10185962439691887318472627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13581283252922516424630169 10185962439691887318472627)
      ·
        refine ⟨15278943659537830977708941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10185962439691887318472627 15278943659537830977708941)
        ·
          refine ⟨5729603872326686616640853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15278943659537830977708941 5729603872326686616640853)
          ·
            refine ⟨8392974422353544848595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5729603872326686616640853 8392974422353544848595)
            ·
              rfl

theorem cell22_1985949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 11].length) (baseStart_1985949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985949 prefixEnd_1985949 := by exact prefixLift 1985949
  have htrace : WordTrace (prefixWord ++ tailWord_1985949) baseStart_1985949 baseEnd_1985949 := by
    simpa [prefixWord, tailWord_1985949, baseEnd_1985949] using wordTrace_append hprefix tailTrace_1985949
  have hstable : (prefixWord ++ tailWord_1985949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985949).length < 2 ^ (prefixWord ++ tailWord_1985949).sum := by decide
  have hdescent : baseEnd_1985949 < baseStart_1985949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1985951 : List Nat := [1, 1, 2, 5, 1, 2, 2, 2, 2, 4]
def baseStart_1985951 : Nat := 118140960795 + 1985951 * 2 ^ 59
def prefixEnd_1985951 : Nat := 4983230072969 + 3 ^ 40 * 1985951 * 2
def baseEnd_1985951 : Nat := 679831612851509794186189

theorem tailTrace_1985951 : CollatzResearch.WordTrace tailWord_1985951 prefixEnd_1985951 679831612851509794186189 := by
  unfold tailWord_1985951
  simp only [CollatzResearch.WordTrace]
  refine ⟨72433583628246175272933707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48289055752164116848622471 72433583628246175272933707)
  ·
    refine ⟨108650375442369262909400561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72433583628246175272933707 108650375442369262909400561)
    ·
      refine ⟨81487781581776947182050421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108650375442369262909400561 81487781581776947182050421)
      ·
        refine ⟨7639479523291588798317227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 81487781581776947182050421 7639479523291588798317227)
        ·
          refine ⟨11459219284937383197475841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7639479523291588798317227 11459219284937383197475841)
          ·
            refine ⟨8594414463703037398106881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11459219284937383197475841 8594414463703037398106881)
            ·
              refine ⟨6445810847777278048580161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8594414463703037398106881 6445810847777278048580161)
              ·
                refine ⟨4834358135832958536435121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6445810847777278048580161 4834358135832958536435121)
                ·
                  refine ⟨3625768601874718902326341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4834358135832958536435121 3625768601874718902326341)
                  ·
                    refine ⟨679831612851509794186189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3625768601874718902326341 679831612851509794186189)
                    ·
                      rfl

theorem cell22_1985951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 4].length) (baseStart_1985951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1985951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1985951 prefixEnd_1985951 := by exact prefixLift 1985951
  have htrace : WordTrace (prefixWord ++ tailWord_1985951) baseStart_1985951 baseEnd_1985951 := by
    simpa [prefixWord, tailWord_1985951, baseEnd_1985951] using wordTrace_append hprefix tailTrace_1985951
  have hstable : (prefixWord ++ tailWord_1985951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1985951).length < 2 ^ (prefixWord ++ tailWord_1985951).sum := by decide
  have hdescent : baseEnd_1985951 < baseStart_1985951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1985951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986039 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 8]
def baseStart_1986039 : Nat := 118140960795 + 1986039 * 2 ^ 59
def prefixEnd_1986039 : Nat := 4983230072969 + 3 ^ 40 * 1986039 * 2
def baseEnd_1986039 : Nat := 226620579016635632661973

theorem tailTrace_1986039 : CollatzResearch.WordTrace tailWord_1986039 prefixEnd_1986039 226620579016635632661973 := by
  unfold tailWord_1986039
  simp only [CollatzResearch.WordTrace]
  refine ⟨72436793251927366302137171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48291195501284910868091447 72436793251927366302137171)
  ·
    refine ⟨108655189877891049453205757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72436793251927366302137171 108655189877891049453205757)
    ·
      refine ⟨40745696204209143544952159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108655189877891049453205757 40745696204209143544952159)
      ·
        refine ⟨61118544306313715317428239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40745696204209143544952159 61118544306313715317428239)
        ·
          refine ⟨91677816459470572976142359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61118544306313715317428239 91677816459470572976142359)
          ·
            refine ⟨137516724689205859464213539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91677816459470572976142359 137516724689205859464213539)
            ·
              refine ⟨206275087033808789196320309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137516724689205859464213539 206275087033808789196320309)
              ·
                refine ⟨19338289409419573987155029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 206275087033808789196320309 19338289409419573987155029)
                ·
                  refine ⟨226620579016635632661973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19338289409419573987155029 226620579016635632661973)
                  ·
                    rfl

theorem cell22_1986039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 8].length) (baseStart_1986039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986039 prefixEnd_1986039 := by exact prefixLift 1986039
  have htrace : WordTrace (prefixWord ++ tailWord_1986039) baseStart_1986039 baseEnd_1986039 := by
    simpa [prefixWord, tailWord_1986039, baseEnd_1986039] using wordTrace_append hprefix tailTrace_1986039
  have hstable : (prefixWord ++ tailWord_1986039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986039).length < 2 ^ (prefixWord ++ tailWord_1986039).sum := by decide
  have hdescent : baseEnd_1986039 < baseStart_1986039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986049 : List Nat := [1, 2, 4, 1, 5, 1, 1, 3, 1, 3]
def baseStart_1986049 : Nat := 118140960795 + 1986049 * 2 ^ 59
def prefixEnd_1986049 : Nat := 4983230072969 + 3 ^ 40 * 1986049 * 2
def baseEnd_1986049 : Nat := 679865160254270205235889

theorem tailTrace_1986049 : CollatzResearch.WordTrace tailWord_1986049 prefixEnd_1986049 679865160254270205235889 := by
  unfold tailWord_1986049
  simp only [CollatzResearch.WordTrace]
  refine ⟨72437157981891138010001201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48291438654594092006667467 72437157981891138010001201)
  ·
    refine ⟨54327868486418353507500901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72437157981891138010001201 54327868486418353507500901)
    ·
      refine ⟨10186475341203441282656419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54327868486418353507500901 10186475341203441282656419)
      ·
        refine ⟨15279713011805161923984629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10186475341203441282656419 15279713011805161923984629)
        ·
          refine ⟨1432473094856733930373559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15279713011805161923984629 1432473094856733930373559)
          ·
            refine ⟨2148709642285100895560339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1432473094856733930373559 2148709642285100895560339)
            ·
              refine ⟨3223064463427651343340509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2148709642285100895560339 3223064463427651343340509)
              ·
                refine ⟨1208649173785369253752691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3223064463427651343340509 1208649173785369253752691)
                ·
                  refine ⟨1812973760678053880629037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1208649173785369253752691 1812973760678053880629037)
                  ·
                    refine ⟨679865160254270205235889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1812973760678053880629037 679865160254270205235889)
                    ·
                      rfl

theorem cell22_1986049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_1986049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986049 prefixEnd_1986049 := by exact prefixLift 1986049
  have htrace : WordTrace (prefixWord ++ tailWord_1986049) baseStart_1986049 baseEnd_1986049 := by
    simpa [prefixWord, tailWord_1986049, baseEnd_1986049] using wordTrace_append hprefix tailTrace_1986049
  have hstable : (prefixWord ++ tailWord_1986049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986049).length < 2 ^ (prefixWord ++ tailWord_1986049).sum := by decide
  have hdescent : baseEnd_1986049 < baseStart_1986049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986058 : List Nat := [3, 1, 2, 2, 2, 2, 2, 3, 1, 4]
def baseStart_1986058 : Nat := 118140960795 + 1986058 * 2 ^ 59
def prefixEnd_1986058 : Nat := 4983230072969 + 3 ^ 40 * 1986058 * 2
def baseEnd_1986058 : Nat := 679868241138197181760861

theorem tailTrace_1986058 : CollatzResearch.WordTrace tailWord_1986058 prefixEnd_1986058 679868241138197181760861 := by
  unfold tailWord_1986058
  simp only [CollatzResearch.WordTrace]
  refine ⟨18109371559714633136769707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48291657492572355031385885 18109371559714633136769707)
  ·
    refine ⟨27164057339571949705154561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18109371559714633136769707 27164057339571949705154561)
    ·
      refine ⟨20373043004678962278865921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27164057339571949705154561 20373043004678962278865921)
      ·
        refine ⟨15279782253509221709149441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20373043004678962278865921 15279782253509221709149441)
        ·
          refine ⟨11459836690131916281862081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15279782253509221709149441 11459836690131916281862081)
          ·
            refine ⟨8594877517598937211396561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11459836690131916281862081 8594877517598937211396561)
            ·
              refine ⟨6446158138199202908547421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8594877517598937211396561 6446158138199202908547421)
              ·
                refine ⟨2417309301824701090705283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6446158138199202908547421 2417309301824701090705283)
                ·
                  refine ⟨3625963952737051636057925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2417309301824701090705283 3625963952737051636057925)
                  ·
                    refine ⟨679868241138197181760861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3625963952737051636057925 679868241138197181760861)
                    ·
                      rfl

theorem cell22_1986058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_1986058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986058 prefixEnd_1986058 := by exact prefixLift 1986058
  have htrace : WordTrace (prefixWord ++ tailWord_1986058) baseStart_1986058 baseEnd_1986058 := by
    simpa [prefixWord, tailWord_1986058, baseEnd_1986058] using wordTrace_append hprefix tailTrace_1986058
  have hstable : (prefixWord ++ tailWord_1986058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986058).length < 2 ^ (prefixWord ++ tailWord_1986058).sum := by decide
  have hdescent : baseEnd_1986058 < baseStart_1986058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986101 : List Nat := [1, 3, 3, 1, 1, 3, 2, 8]
def baseStart_1986101 : Nat := 118140960795 + 1986101 * 2 ^ 59
def prefixEnd_1986101 : Nat := 4983230072969 + 3 ^ 40 * 1986101 * 2
def baseEnd_1986101 : Nat := 75542551212995489215081

theorem tailTrace_1986101 : CollatzResearch.WordTrace tailWord_1986101 prefixEnd_1986101 75542551212995489215081 := by
  unfold tailWord_1986101
  simp only [CollatzResearch.WordTrace]
  refine ⟨72439054577702750890894157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48292703051801833927262771 72439054577702750890894157)
  ·
    refine ⟨27164645466638531584085309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72439054577702750890894157 27164645466638531584085309)
    ·
      refine ⟨10186742049989449344031991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27164645466638531584085309 10186742049989449344031991)
      ·
        refine ⟨15280113074984174016047987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10186742049989449344031991 15280113074984174016047987)
        ·
          refine ⟨22920169612476261024071981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15280113074984174016047987 22920169612476261024071981)
          ·
            refine ⟨8595063604678597884026993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22920169612476261024071981 8595063604678597884026993)
            ·
              refine ⟨6446297703508948413020245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8595063604678597884026993 6446297703508948413020245)
              ·
                refine ⟨75542551212995489215081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6446297703508948413020245 75542551212995489215081)
                ·
                  rfl

theorem cell22_1986101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 8].length) (baseStart_1986101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986101 prefixEnd_1986101 := by exact prefixLift 1986101
  have htrace : WordTrace (prefixWord ++ tailWord_1986101) baseStart_1986101 baseEnd_1986101 := by
    simpa [prefixWord, tailWord_1986101, baseEnd_1986101] using wordTrace_append hprefix tailTrace_1986101
  have hstable : (prefixWord ++ tailWord_1986101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986101).length < 2 ^ (prefixWord ++ tailWord_1986101).sum := by decide
  have hdescent : baseEnd_1986101 < baseStart_1986101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986103 : List Nat := [1, 1, 3, 1, 2, 5, 2, 1, 2, 4]
def baseStart_1986103 : Nat := 118140960795 + 1986103 * 2 ^ 59
def prefixEnd_1986103 : Nat := 4983230072969 + 3 ^ 40 * 1986103 * 2
def baseEnd_1986103 : Nat := 679883645557832064385723

theorem tailTrace_1986103 : CollatzResearch.WordTrace tailWord_1986103 prefixEnd_1986103 679883645557832064385723 := by
  unfold tailWord_1986103
  simp only [CollatzResearch.WordTrace]
  refine ⟨72439127523695505232466963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48292751682463670154977975 72439127523695505232466963)
  ·
    refine ⟨108658691285543257848700445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72439127523695505232466963 108658691285543257848700445)
    ·
      refine ⟨40747009232078721693262667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108658691285543257848700445 40747009232078721693262667)
      ·
        refine ⟨61120513848118082539894001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40747009232078721693262667 61120513848118082539894001)
        ·
          refine ⟨45840385386088561904920501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61120513848118082539894001 45840385386088561904920501)
          ·
            refine ⟨4297536129945802678586297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45840385386088561904920501 4297536129945802678586297)
            ·
              refine ⟨3223152097459352008939723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4297536129945802678586297 3223152097459352008939723)
              ·
                refine ⟨4834728146189028013409585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3223152097459352008939723 4834728146189028013409585)
                ·
                  refine ⟨3626046109641771010057189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4834728146189028013409585 3626046109641771010057189)
                  ·
                    refine ⟨679883645557832064385723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3626046109641771010057189 679883645557832064385723)
                    ·
                      rfl

theorem cell22_1986103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_1986103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986103 prefixEnd_1986103 := by exact prefixLift 1986103
  have htrace : WordTrace (prefixWord ++ tailWord_1986103) baseStart_1986103 baseEnd_1986103 := by
    simpa [prefixWord, tailWord_1986103, baseEnd_1986103] using wordTrace_append hprefix tailTrace_1986103
  have hstable : (prefixWord ++ tailWord_1986103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986103).length < 2 ^ (prefixWord ++ tailWord_1986103).sum := by decide
  have hdescent : baseEnd_1986103 < baseStart_1986103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986118 : List Nat := [6, 1, 1, 1, 13]
def baseStart_1986118 : Nat := 118140960795 + 1986118 * 2 ^ 59
def prefixEnd_1986118 : Nat := 4983230072969 + 3 ^ 40 * 1986118 * 2
def baseEnd_1986118 : Nat := 2797896215491263478439

theorem tailTrace_1986118 : CollatzResearch.WordTrace tailWord_1986118 prefixEnd_1986118 2797896215491263478439 := by
  unfold tailWord_1986118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2263739831832536337320719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 48293116412427441862842005 2263739831832536337320719)
  ·
    refine ⟨3395609747748804505981079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2263739831832536337320719 3395609747748804505981079)
    ·
      refine ⟨5093414621623206758971619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3395609747748804505981079 5093414621623206758971619)
      ·
        refine ⟨7640121932434810138457429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5093414621623206758971619 7640121932434810138457429)
        ·
          refine ⟨2797896215491263478439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 7640121932434810138457429 2797896215491263478439)
          ·
            rfl

theorem cell22_1986118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 13].length) (baseStart_1986118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986118 prefixEnd_1986118 := by exact prefixLift 1986118
  have htrace : WordTrace (prefixWord ++ tailWord_1986118) baseStart_1986118 baseEnd_1986118 := by
    simpa [prefixWord, tailWord_1986118, baseEnd_1986118] using wordTrace_append hprefix tailTrace_1986118
  have hstable : (prefixWord ++ tailWord_1986118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986118).length < 2 ^ (prefixWord ++ tailWord_1986118).sum := by decide
  have hdescent : baseEnd_1986118 < baseStart_1986118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986133 : List Nat := [1, 3, 2, 2, 1, 1, 1, 5, 3, 3]
def baseStart_1986133 : Nat := 118140960795 + 1986133 * 2 ^ 59
def prefixEnd_1986133 : Nat := 4983230072969 + 3 ^ 40 * 1986133 * 2
def baseEnd_1986133 : Nat := 679893915170921986135631

theorem tailTrace_1986133 : CollatzResearch.WordTrace tailWord_1986133 prefixEnd_1986133 679893915170921986135631 := by
  unfold tailWord_1986133
  simp only [CollatzResearch.WordTrace]
  refine ⟨72440221713586820356059053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48293481142391213570706035 72440221713586820356059053)
  ·
    refine ⟨27165083142595057633522145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72440221713586820356059053 27165083142595057633522145)
    ·
      refine ⟨20373812356946293225141609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27165083142595057633522145 20373812356946293225141609)
      ·
        refine ⟨15280359267709719918856207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20373812356946293225141609 15280359267709719918856207)
        ·
          refine ⟨22920538901564579878284311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15280359267709719918856207 22920538901564579878284311)
          ·
            refine ⟨34380808352346869817426467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22920538901564579878284311 34380808352346869817426467)
            ·
              refine ⟨51571212528520304726139701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34380808352346869817426467 51571212528520304726139701)
              ·
                refine ⟨4834801174548778568075597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 51571212528520304726139701 4834801174548778568075597)
                ·
                  refine ⟨1813050440455791963028349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4834801174548778568075597 1813050440455791963028349)
                  ·
                    refine ⟨679893915170921986135631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1813050440455791963028349 679893915170921986135631)
                    ·
                      rfl

theorem cell22_1986133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_1986133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986133 prefixEnd_1986133 := by exact prefixLift 1986133
  have htrace : WordTrace (prefixWord ++ tailWord_1986133) baseStart_1986133 baseEnd_1986133 := by
    simpa [prefixWord, tailWord_1986133, baseEnd_1986133] using wordTrace_append hprefix tailTrace_1986133
  have hstable : (prefixWord ++ tailWord_1986133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986133).length < 2 ^ (prefixWord ++ tailWord_1986133).sum := by decide
  have hdescent : baseEnd_1986133 < baseStart_1986133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986208 : List Nat := [2, 1, 1, 4, 3, 1, 2, 2, 6]
def baseStart_1986208 : Nat := 118140960795 + 1986208 * 2 ^ 59
def prefixEnd_1986208 : Nat := 4983230072969 + 3 ^ 40 * 1986208 * 2
def baseEnd_1986208 : Nat := 226639863067882263503467

theorem tailTrace_1986208 : CollatzResearch.WordTrace tailWord_1986208 prefixEnd_1986208 226639863067882263503467 := by
  unfold tailWord_1986208
  simp only [CollatzResearch.WordTrace]
  refine ⟨36221478594157554082519639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48295304792210072110026185 36221478594157554082519639)
  ·
    refine ⟨54332217891236331123779459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36221478594157554082519639 54332217891236331123779459)
    ·
      refine ⟨81498326836854496685669189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54332217891236331123779459 81498326836854496685669189)
      ·
        refine ⟨15280936281910218128562973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81498326836854496685669189 15280936281910218128562973)
        ·
          refine ⟨5730351105716331798211115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15280936281910218128562973 5730351105716331798211115)
          ·
            refine ⟨8595526658574497697316673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5730351105716331798211115 8595526658574497697316673)
            ·
              refine ⟨6446644993930873272987505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8595526658574497697316673 6446644993930873272987505)
              ·
                refine ⟨4834983745448154954740629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6446644993930873272987505 4834983745448154954740629)
                ·
                  refine ⟨226639863067882263503467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4834983745448154954740629 226639863067882263503467)
                  ·
                    rfl

theorem cell22_1986208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 6].length) (baseStart_1986208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986208 prefixEnd_1986208 := by exact prefixLift 1986208
  have htrace : WordTrace (prefixWord ++ tailWord_1986208) baseStart_1986208 baseEnd_1986208 := by
    simpa [prefixWord, tailWord_1986208, baseEnd_1986208] using wordTrace_append hprefix tailTrace_1986208
  have hstable : (prefixWord ++ tailWord_1986208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986208).length < 2 ^ (prefixWord ++ tailWord_1986208).sum := by decide
  have hdescent : baseEnd_1986208 < baseStart_1986208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986223 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 6, 3]
def baseStart_1986223 : Nat := 118140960795 + 1986223 * 2 ^ 59
def prefixEnd_1986223 : Nat := 4983230072969 + 3 ^ 40 * 1986223 * 2
def baseEnd_1986223 : Nat := 679924724010191751385355

theorem tailTrace_1986223 : CollatzResearch.WordTrace tailWord_1986223 prefixEnd_1986223 679924724010191751385355 := by
  unfold tailWord_1986223
  simp only [CollatzResearch.WordTrace]
  refine ⟨72443504283260765726835323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48295669522173843817890215 72443504283260765726835323)
  ·
    refine ⟨108665256424891148590252985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72443504283260765726835323 108665256424891148590252985)
    ·
      refine ⟨81498942318668361442689739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108665256424891148590252985 81498942318668361442689739)
      ·
        refine ⟨122248413478002542164034609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81498942318668361442689739 122248413478002542164034609)
        ·
          refine ⟨91686310108501906623025957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122248413478002542164034609 91686310108501906623025957)
          ·
            refine ⟨17191183145344107491817367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 91686310108501906623025957 17191183145344107491817367)
            ·
              refine ⟨25786774718016161237726051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17191183145344107491817367 25786774718016161237726051)
              ·
                refine ⟨38680162077024241856589077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25786774718016161237726051 38680162077024241856589077)
                ·
                  refine ⟨1813132597360511337027613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38680162077024241856589077 1813132597360511337027613)
                  ·
                    refine ⟨679924724010191751385355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1813132597360511337027613 679924724010191751385355)
                    ·
                      rfl

theorem cell22_1986223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6, 3].length) (baseStart_1986223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986223 prefixEnd_1986223 := by exact prefixLift 1986223
  have htrace : WordTrace (prefixWord ++ tailWord_1986223) baseStart_1986223 baseEnd_1986223 := by
    simpa [prefixWord, tailWord_1986223, baseEnd_1986223] using wordTrace_append hprefix tailTrace_1986223
  have hstable : (prefixWord ++ tailWord_1986223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986223).length < 2 ^ (prefixWord ++ tailWord_1986223).sum := by decide
  have hdescent : baseEnd_1986223 < baseStart_1986223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986240 : List Nat := [2, 1, 1, 2, 4, 1, 2, 4, 2, 3]
def baseStart_1986240 : Nat := 118140960795 + 1986240 * 2 ^ 59
def prefixEnd_1986240 : Nat := 4983230072969 + 3 ^ 40 * 1986240 * 2
def baseEnd_1986240 : Nat := 679930543457609373710303

theorem tailTrace_1986240 : CollatzResearch.WordTrace tailWord_1986240 prefixEnd_1986240 679930543457609373710303 := by
  unfold tailWord_1986240
  simp only [CollatzResearch.WordTrace]
  refine ⟨36222062162099588815102087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48296082882799451753469449 36222062162099588815102087)
  ·
    refine ⟨54333093243149383222653131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36222062162099588815102087 54333093243149383222653131)
    ·
      refine ⟨81499639864724074833979697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54333093243149383222653131 81499639864724074833979697)
      ·
        refine ⟨61124729898543056125484773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81499639864724074833979697 61124729898543056125484773)
        ·
          refine ⟨11460886855976823023528395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61124729898543056125484773 11460886855976823023528395)
          ·
            refine ⟨17191330283965234535292593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11460886855976823023528395 17191330283965234535292593)
            ·
              refine ⟨12893497712973925901469445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17191330283965234535292593 12893497712973925901469445)
              ·
                refine ⟨2417530821182611106525521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12893497712973925901469445 2417530821182611106525521)
                ·
                  refine ⟨1813148115886958329894141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2417530821182611106525521 1813148115886958329894141)
                  ·
                    refine ⟨679930543457609373710303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1813148115886958329894141 679930543457609373710303)
                    ·
                      rfl

theorem cell22_1986240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 2, 3].length) (baseStart_1986240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986240 prefixEnd_1986240 := by exact prefixLift 1986240
  have htrace : WordTrace (prefixWord ++ tailWord_1986240) baseStart_1986240 baseEnd_1986240 := by
    simpa [prefixWord, tailWord_1986240, baseEnd_1986240] using wordTrace_append hprefix tailTrace_1986240
  have hstable : (prefixWord ++ tailWord_1986240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986240).length < 2 ^ (prefixWord ++ tailWord_1986240).sum := by decide
  have hdescent : baseEnd_1986240 < baseStart_1986240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986257 : List Nat := [1, 2, 2, 1, 2, 4, 4, 1, 2, 3]
def baseStart_1986257 : Nat := 118140960795 + 1986257 * 2 ^ 59
def prefixEnd_1986257 : Nat := 4983230072969 + 3 ^ 40 * 1986257 * 2
def baseEnd_1986257 : Nat := 679936362905026996035251

theorem tailTrace_1986257 : CollatzResearch.WordTrace tailWord_1986257 prefixEnd_1986257 679936362905026996035251 := by
  unfold tailWord_1986257
  simp only [CollatzResearch.WordTrace]
  refine ⟨72444744365137589533573025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48296496243425059689048683 72444744365137589533573025)
  ·
    refine ⟨54333558273853192150179769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72444744365137589533573025 54333558273853192150179769)
    ·
      refine ⟨40750168705389894112634827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54333558273853192150179769 40750168705389894112634827)
      ·
        refine ⟨61125253058084841168952241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40750168705389894112634827 61125253058084841168952241)
        ·
          refine ⟨45843939793563630876714181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61125253058084841168952241 45843939793563630876714181)
          ·
            refine ⟨8595738711293180789383909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45843939793563630876714181 8595738711293180789383909)
            ·
              refine ⟨1611701008367471398009483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8595738711293180789383909 1611701008367471398009483)
              ·
                refine ⟨2417551512551207097014225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1611701008367471398009483 2417551512551207097014225)
                ·
                  refine ⟨1813163634413405322760669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2417551512551207097014225 1813163634413405322760669)
                  ·
                    refine ⟨679936362905026996035251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1813163634413405322760669 679936362905026996035251)
                    ·
                      rfl

theorem cell22_1986257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 2, 3].length) (baseStart_1986257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986257 prefixEnd_1986257 := by exact prefixLift 1986257
  have htrace : WordTrace (prefixWord ++ tailWord_1986257) baseStart_1986257 baseEnd_1986257 := by
    simpa [prefixWord, tailWord_1986257, baseEnd_1986257] using wordTrace_append hprefix tailTrace_1986257
  have hstable : (prefixWord ++ tailWord_1986257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986257).length < 2 ^ (prefixWord ++ tailWord_1986257).sum := by decide
  have hdescent : baseEnd_1986257 < baseStart_1986257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986360 : List Nat := [2, 1, 2, 1, 3, 4, 2, 1, 6]
def baseStart_1986360 : Nat := 118140960795 + 1986360 * 2 ^ 59
def prefixEnd_1986360 : Nat := 4983230072969 + 3 ^ 40 * 1986360 * 2
def baseEnd_1986360 : Nat := 226657207303323020236645

theorem tailTrace_1986360 : CollatzResearch.WordTrace tailWord_1986360 prefixEnd_1986360 226657207303323020236645 := by
  unfold tailWord_1986360
  simp only [CollatzResearch.WordTrace]
  refine ⟨36224250541882219062286267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48299000722509625416381689 36224250541882219062286267)
  ·
    refine ⟨54336375812823328593429401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36224250541882219062286267 54336375812823328593429401)
    ·
      refine ⟨40752281859617496445072051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54336375812823328593429401 40752281859617496445072051)
      ·
        refine ⟨61128422789426244667608077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40752281859617496445072051 61128422789426244667608077)
        ·
          refine ⟨22923158546034841750353029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61128422789426244667608077 22923158546034841750353029)
          ·
            refine ⟨4298092227381532828191193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22923158546034841750353029 4298092227381532828191193)
            ·
              refine ⟨3223569170536149621143395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4298092227381532828191193 3223569170536149621143395)
              ·
                refine ⟨4835353755804224431715093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3223569170536149621143395 4835353755804224431715093)
                ·
                  refine ⟨226657207303323020236645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4835353755804224431715093 226657207303323020236645)
                  ·
                    rfl

theorem cell22_1986360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 6].length) (baseStart_1986360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986360 prefixEnd_1986360 := by exact prefixLift 1986360
  have htrace : WordTrace (prefixWord ++ tailWord_1986360) baseStart_1986360 baseEnd_1986360 := by
    simpa [prefixWord, tailWord_1986360, baseEnd_1986360] using wordTrace_append hprefix tailTrace_1986360
  have hstable : (prefixWord ++ tailWord_1986360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986360).length < 2 ^ (prefixWord ++ tailWord_1986360).sum := by decide
  have hdescent : baseEnd_1986360 < baseStart_1986360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986373 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 3, 6]
def baseStart_1986373 : Nat := 118140960795 + 1986373 * 2 ^ 59
def prefixEnd_1986373 : Nat := 4983230072969 + 3 ^ 40 * 1986373 * 2
def baseEnd_1986373 : Nat := 679976072075641360134895

theorem tailTrace_1986373 : CollatzResearch.WordTrace tailWord_1986373 prefixEnd_1986373 679976072075641360134895 := by
  unfold tailWord_1986373
  simp only [CollatzResearch.WordTrace]
  refine ⟨72448975232717341344795773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48299316821811560896530515 72448975232717341344795773)
  ·
    refine ⟨27168365712269003004298415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72448975232717341344795773 27168365712269003004298415)
    ·
      refine ⟨40752548568403504506447623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27168365712269003004298415 40752548568403504506447623)
      ·
        refine ⟨61128822852605256759671435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40752548568403504506447623 61128822852605256759671435)
        ·
          refine ⟨91693234278907885139507153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61128822852605256759671435 91693234278907885139507153)
          ·
            refine ⟨68769925709180913854630365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91693234278907885139507153 68769925709180913854630365)
            ·
              refine ⟨25788722140942842695486387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68769925709180913854630365 25788722140942842695486387)
              ·
                refine ⟨38683083211414264043229581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25788722140942842695486387 38683083211414264043229581)
                ·
                  refine ⟨14506156204280349016211093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38683083211414264043229581 14506156204280349016211093)
                  ·
                    refine ⟨679976072075641360134895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14506156204280349016211093 679976072075641360134895)
                    ·
                      rfl

theorem cell22_1986373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_1986373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986373 prefixEnd_1986373 := by exact prefixLift 1986373
  have htrace : WordTrace (prefixWord ++ tailWord_1986373) baseStart_1986373 baseEnd_1986373 := by
    simpa [prefixWord, tailWord_1986373, baseEnd_1986373] using wordTrace_append hprefix tailTrace_1986373
  have hstable : (prefixWord ++ tailWord_1986373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986373).length < 2 ^ (prefixWord ++ tailWord_1986373).sum := by decide
  have hdescent : baseEnd_1986373 < baseStart_1986373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986375 : List Nat := [1, 1, 4, 1, 2, 1, 5, 1, 1, 5]
def baseStart_1986375 : Nat := 118140960795 + 1986375 * 2 ^ 59
def prefixEnd_1986375 : Nat := 4983230072969 + 3 ^ 40 * 1986375 * 2
def baseEnd_1986375 : Nat := 679976756716514021584889

theorem tailTrace_1986375 : CollatzResearch.WordTrace tailWord_1986375 prefixEnd_1986375 679976756716514021584889 := by
  unfold tailWord_1986375
  simp only [CollatzResearch.WordTrace]
  refine ⟨72449048178710095686368579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48299365452473397124245719 72449048178710095686368579)
  ·
    refine ⟨108673572268065143529552869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72449048178710095686368579 108673572268065143529552869)
    ·
      refine ⟨20376294800262214411791163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108673572268065143529552869 20376294800262214411791163)
      ·
        refine ⟨30564442200393321617686745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20376294800262214411791163 30564442200393321617686745)
        ·
          refine ⟨22923331650294991213265059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30564442200393321617686745 22923331650294991213265059)
          ·
            refine ⟨34384997475442486819897589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22923331650294991213265059 34384997475442486819897589)
            ·
              refine ⟨3223593513322733139365399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34384997475442486819897589 3223593513322733139365399)
              ·
                refine ⟨4835390269984099709048099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3223593513322733139365399 4835390269984099709048099)
                ·
                  refine ⟨7253085404976149563572149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4835390269984099709048099 7253085404976149563572149)
                  ·
                    refine ⟨679976756716514021584889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7253085404976149563572149 679976756716514021584889)
                    ·
                      rfl

theorem cell22_1986375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_1986375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986375 prefixEnd_1986375 := by exact prefixLift 1986375
  have htrace : WordTrace (prefixWord ++ tailWord_1986375) baseStart_1986375 baseEnd_1986375 := by
    simpa [prefixWord, tailWord_1986375, baseEnd_1986375] using wordTrace_append hprefix tailTrace_1986375
  have hstable : (prefixWord ++ tailWord_1986375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986375).length < 2 ^ (prefixWord ++ tailWord_1986375).sum := by decide
  have hdescent : baseEnd_1986375 < baseStart_1986375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986471 : List Nat := [1, 1, 6, 1, 2, 2, 1, 4, 1, 3]
def baseStart_1986471 : Nat := 118140960795 + 1986471 * 2 ^ 59
def prefixEnd_1986471 : Nat := 4983230072969 + 3 ^ 40 * 1986471 * 2
def baseEnd_1986471 : Nat := 680009619478401771184595

theorem tailTrace_1986471 : CollatzResearch.WordTrace tailWord_1986471 prefixEnd_1986471 680009619478401771184595 := by
  unfold tailWord_1986471
  simp only [CollatzResearch.WordTrace]
  refine ⟨72452549586362304081863267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48301699724241536054575511 72452549586362304081863267)
  ·
    refine ⟨108678824379543456122794901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72452549586362304081863267 108678824379543456122794901)
    ·
      refine ⟨5094319892791099505756011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 108678824379543456122794901 5094319892791099505756011)
      ·
        refine ⟨7641479839186649258634017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5094319892791099505756011 7641479839186649258634017)
        ·
          refine ⟨5731109879389986943975513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7641479839186649258634017 5731109879389986943975513)
          ·
            refine ⟨4298332409542490207981635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5731109879389986943975513 4298332409542490207981635)
            ·
              refine ⟨6447498614313735311972453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4298332409542490207981635 6447498614313735311972453)
              ·
                refine ⟨1208905990183825370994835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6447498614313735311972453 1208905990183825370994835)
                ·
                  refine ⟨1813358985275738056492253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1208905990183825370994835 1813358985275738056492253)
                  ·
                    refine ⟨680009619478401771184595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1813358985275738056492253 680009619478401771184595)
                    ·
                      rfl

theorem cell22_1986471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_1986471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986471 prefixEnd_1986471 := by exact prefixLift 1986471
  have htrace : WordTrace (prefixWord ++ tailWord_1986471) baseStart_1986471 baseEnd_1986471 := by
    simpa [prefixWord, tailWord_1986471, baseEnd_1986471] using wordTrace_append hprefix tailTrace_1986471
  have hstable : (prefixWord ++ tailWord_1986471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986471).length < 2 ^ (prefixWord ++ tailWord_1986471).sum := by decide
  have hdescent : baseEnd_1986471 < baseStart_1986471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986495 : List Nat := [1, 1, 2, 2, 2, 1, 5, 2, 6]
def baseStart_1986495 : Nat := 118140960795 + 1986495 * 2 ^ 59
def prefixEnd_1986495 : Nat := 4983230072969 + 3 ^ 40 * 1986495 * 2
def baseEnd_1986495 : Nat := 226672611722957902861507

theorem tailTrace_1986495 : CollatzResearch.WordTrace tailWord_1986495 prefixEnd_1986495 226672611722957902861507 := by
  unfold tailWord_1986495
  simp only [CollatzResearch.WordTrace]
  refine ⟨72453424938275356180736939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48302283292183570787157959 72453424938275356180736939)
  ·
    refine ⟨108680137407413034271105409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72453424938275356180736939 108680137407413034271105409)
    ·
      refine ⟨81510103055559775703329057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108680137407413034271105409 81510103055559775703329057)
      ·
        refine ⟨61132577291669831777496793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81510103055559775703329057 61132577291669831777496793)
        ·
          refine ⟨45849432968752373833122595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61132577291669831777496793 45849432968752373833122595)
          ·
            refine ⟨68774149453128560749683893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45849432968752373833122595 68774149453128560749683893)
            ·
              refine ⟨6447576511230802570282865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68774149453128560749683893 6447576511230802570282865)
              ·
                refine ⟨4835682383423101927712149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6447576511230802570282865 4835682383423101927712149)
                ·
                  refine ⟨226672611722957902861507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4835682383423101927712149 226672611722957902861507)
                  ·
                    rfl

theorem cell22_1986495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 6].length) (baseStart_1986495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986495 prefixEnd_1986495 := by exact prefixLift 1986495
  have htrace : WordTrace (prefixWord ++ tailWord_1986495) baseStart_1986495 baseEnd_1986495 := by
    simpa [prefixWord, tailWord_1986495, baseEnd_1986495] using wordTrace_append hprefix tailTrace_1986495
  have hstable : (prefixWord ++ tailWord_1986495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986495).length < 2 ^ (prefixWord ++ tailWord_1986495).sum := by decide
  have hdescent : baseEnd_1986495 < baseStart_1986495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986512 : List Nat := [2, 1, 1, 1, 1, 2, 5, 5, 4]
def baseStart_1986512 : Nat := 118140960795 + 1986512 * 2 ^ 59
def prefixEnd_1986512 : Nat := 4983230072969 + 3 ^ 40 * 1986512 * 2
def baseEnd_1986512 : Nat := 226674551538763776969823

theorem tailTrace_1986512 : CollatzResearch.WordTrace tailWord_1986512 prefixEnd_1986512 226674551538763776969823 := by
  unfold tailWord_1986512
  simp only [CollatzResearch.WordTrace]
  refine ⟨36227022489606884042052895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48302696652809178722737193 36227022489606884042052895)
  ·
    refine ⟨54340533734410326063079343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36227022489606884042052895 54340533734410326063079343)
    ·
      refine ⟨81510800601615489094619015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54340533734410326063079343 81510800601615489094619015)
      ·
        refine ⟨122266200902423233641928523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81510800601615489094619015 122266200902423233641928523)
        ·
          refine ⟨183399301353634850462892785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122266200902423233641928523 183399301353634850462892785)
          ·
            refine ⟨137549476015226137847169589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 183399301353634850462892785 137549476015226137847169589)
            ·
              refine ⟨12895263376427450423172149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 137549476015226137847169589 12895263376427450423172149)
              ·
                refine ⟨1208930941540073477172389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12895263376427450423172149 1208930941540073477172389)
                ·
                  refine ⟨226674551538763776969823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1208930941540073477172389 226674551538763776969823)
                  ·
                    rfl

theorem cell22_1986512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5, 4].length) (baseStart_1986512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986512 prefixEnd_1986512 := by exact prefixLift 1986512
  have htrace : WordTrace (prefixWord ++ tailWord_1986512) baseStart_1986512 baseEnd_1986512 := by
    simpa [prefixWord, tailWord_1986512, baseEnd_1986512] using wordTrace_append hprefix tailTrace_1986512
  have hstable : (prefixWord ++ tailWord_1986512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986512).length < 2 ^ (prefixWord ++ tailWord_1986512).sum := by decide
  have hdescent : baseEnd_1986512 < baseStart_1986512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986518 : List Nat := [5, 2, 1, 1, 4, 1, 1, 2, 5]
def baseStart_1986518 : Nat := 118140960795 + 1986518 * 2 ^ 59
def prefixEnd_1986518 : Nat := 4983230072969 + 3 ^ 40 * 1986518 * 2
def baseEnd_1986518 : Nat := 226675236179636438419817

theorem tailTrace_1986518 : CollatzResearch.WordTrace tailWord_1986518 prefixEnd_1986518 226675236179636438419817 := by
  unfold tailWord_1986518
  simp only [CollatzResearch.WordTrace]
  refine ⟨4528391488574501944301513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 48302842544794687405882805 4528391488574501944301513)
  ·
    refine ⟨3396293616430876458226135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4528391488574501944301513 3396293616430876458226135)
    ·
      refine ⟨5094440424646314687339203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3396293616430876458226135 5094440424646314687339203)
      ·
        refine ⟨7641660636969472031008805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5094440424646314687339203 7641660636969472031008805)
        ·
          refine ⟨1432811369431776005814151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7641660636969472031008805 1432811369431776005814151)
          ·
            refine ⟨2149217054147664008721227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1432811369431776005814151 2149217054147664008721227)
            ·
              refine ⟨3223825581221496013081841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2149217054147664008721227 3223825581221496013081841)
              ·
                refine ⟨2417869185916122009811381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3223825581221496013081841 2417869185916122009811381)
                ·
                  refine ⟨226675236179636438419817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2417869185916122009811381 226675236179636438419817)
                  ·
                    rfl

theorem cell22_1986518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_1986518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986518 prefixEnd_1986518 := by exact prefixLift 1986518
  have htrace : WordTrace (prefixWord ++ tailWord_1986518) baseStart_1986518 baseEnd_1986518 := by
    simpa [prefixWord, tailWord_1986518, baseEnd_1986518] using wordTrace_append hprefix tailTrace_1986518
  have hstable : (prefixWord ++ tailWord_1986518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986518).length < 2 ^ (prefixWord ++ tailWord_1986518).sum := by decide
  have hdescent : baseEnd_1986518 < baseStart_1986518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986542 : List Nat := [4, 1, 2, 1, 3, 1, 1, 2, 1, 6]
def baseStart_1986542 : Nat := 118140960795 + 1986542 * 2 ^ 59
def prefixEnd_1986542 : Nat := 4983230072969 + 3 ^ 40 * 1986542 * 2
def baseEnd_1986542 : Nat := 680033924229381252659377

theorem tailTrace_1986542 : CollatzResearch.WordTrace tailWord_1986542 prefixEnd_1986542 680033924229381252659377 := by
  unfold tailWord_1986542
  simp only [CollatzResearch.WordTrace]
  refine ⟨9056892396138135400962235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48303426112736722138465253 9056892396138135400962235)
  ·
    refine ⟨13585338594207203101443353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9056892396138135400962235 13585338594207203101443353)
    ·
      refine ⟨10189003945655402326082515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13585338594207203101443353 10189003945655402326082515)
      ·
        refine ⟨15283505918483103489123773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10189003945655402326082515 15283505918483103489123773)
        ·
          refine ⟨5731314719431163808421415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15283505918483103489123773 5731314719431163808421415)
          ·
            refine ⟨8596972079146745712632123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5731314719431163808421415 8596972079146745712632123)
            ·
              refine ⟨12895458118720118568948185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8596972079146745712632123 12895458118720118568948185)
              ·
                refine ⟨9671593589040088926711139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12895458118720118568948185 9671593589040088926711139)
                ·
                  refine ⟨14507390383560133390066709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9671593589040088926711139 14507390383560133390066709)
                  ·
                    refine ⟨680033924229381252659377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14507390383560133390066709 680033924229381252659377)
                    ·
                      rfl

theorem cell22_1986542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_1986542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986542 prefixEnd_1986542 := by exact prefixLift 1986542
  have htrace : WordTrace (prefixWord ++ tailWord_1986542) baseStart_1986542 baseEnd_1986542 := by
    simpa [prefixWord, tailWord_1986542, baseEnd_1986542] using wordTrace_append hprefix tailTrace_1986542
  have hstable : (prefixWord ++ tailWord_1986542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986542).length < 2 ^ (prefixWord ++ tailWord_1986542).sum := by decide
  have hdescent : baseEnd_1986542 < baseStart_1986542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986557 : List Nat := [1, 4, 1, 1, 1, 2, 6, 6]
def baseStart_1986557 : Nat := 118140960795 + 1986557 * 2 ^ 59
def prefixEnd_1986557 : Nat := 4983230072969 + 3 ^ 40 * 1986557 * 2
def baseEnd_1986557 : Nat := 75559895448436245948259

theorem tailTrace_1986557 : CollatzResearch.WordTrace tailWord_1986557 prefixEnd_1986557 75559895448436245948259 := by
  unfold tailWord_1986557
  simp only [CollatzResearch.WordTrace]
  refine ⟨72455686264050740769493925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48303790842700493846329283 72455686264050740769493925)
  ·
    refine ⟨13585441174509513894280111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72455686264050740769493925 13585441174509513894280111)
    ·
      refine ⟨20378161761764270841420167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13585441174509513894280111 20378161761764270841420167)
      ·
        refine ⟨30567242642646406262130251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20378161761764270841420167 30567242642646406262130251)
        ·
          refine ⟨45850863963969609393195377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30567242642646406262130251 45850863963969609393195377)
          ·
            refine ⟨34388147972977207044896533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45850863963969609393195377 34388147972977207044896533)
            ·
              refine ⟨1611944436233306580229525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34388147972977207044896533 1611944436233306580229525)
              ·
                refine ⟨75559895448436245948259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1611944436233306580229525 75559895448436245948259)
                ·
                  rfl

theorem cell22_1986557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 6].length) (baseStart_1986557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986557 prefixEnd_1986557 := by exact prefixLift 1986557
  have htrace : WordTrace (prefixWord ++ tailWord_1986557) baseStart_1986557 baseEnd_1986557 := by
    simpa [prefixWord, tailWord_1986557, baseEnd_1986557] using wordTrace_append hprefix tailTrace_1986557
  have hstable : (prefixWord ++ tailWord_1986557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986557).length < 2 ^ (prefixWord ++ tailWord_1986557).sum := by decide
  have hdescent : baseEnd_1986557 < baseStart_1986557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986580 : List Nat := [2, 4, 3, 2, 1, 1, 3, 2, 4]
def baseStart_1986580 : Nat := 118140960795 + 1986580 * 2 ^ 59
def prefixEnd_1986580 : Nat := 4983230072969 + 3 ^ 40 * 1986580 * 2
def baseEnd_1986580 : Nat := 226682310801987273403087

theorem tailTrace_1986580 : CollatzResearch.WordTrace tailWord_1986580 prefixEnd_1986580 226682310801987273403087 := by
  unfold tailWord_1986580
  simp only [CollatzResearch.WordTrace]
  refine ⟨36228262571483707848790597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48304350095311610465054129 36228262571483707848790597)
  ·
    refine ⟨6792799232153195221648237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36228262571483707848790597 6792799232153195221648237)
    ·
      refine ⟨2547299712057448208118089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6792799232153195221648237 2547299712057448208118089)
      ·
        refine ⟨1910474784043086156088567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2547299712057448208118089 1910474784043086156088567)
        ·
          refine ⟨2865712176064629234132851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1910474784043086156088567 2865712176064629234132851)
          ·
            refine ⟨4298568264096943851199277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2865712176064629234132851 4298568264096943851199277)
            ·
              refine ⟨1611963099036353944199729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4298568264096943851199277 1611963099036353944199729)
              ·
                refine ⟨1208972324277265458149797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1611963099036353944199729 1208972324277265458149797)
                ·
                  refine ⟨226682310801987273403087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1208972324277265458149797 226682310801987273403087)
                  ·
                    rfl

theorem cell22_1986580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_1986580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986580 prefixEnd_1986580 := by exact prefixLift 1986580
  have htrace : WordTrace (prefixWord ++ tailWord_1986580) baseStart_1986580 baseEnd_1986580 := by
    simpa [prefixWord, tailWord_1986580, baseEnd_1986580] using wordTrace_append hprefix tailTrace_1986580
  have hstable : (prefixWord ++ tailWord_1986580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986580).length < 2 ^ (prefixWord ++ tailWord_1986580).sum := by decide
  have hdescent : baseEnd_1986580 < baseStart_1986580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986681 : List Nat := [1, 2, 1, 3, 4, 2, 2, 3, 4]
def baseStart_1986681 : Nat := 118140960795 + 1986681 * 2 ^ 59
def prefixEnd_1986681 : Nat := 4983230072969 + 3 ^ 40 * 1986681 * 2
def baseEnd_1986681 : Nat := 226693835590010407811317

theorem tailTrace_1986681 : CollatzResearch.WordTrace tailWord_1986681 prefixEnd_1986681 226693835590010407811317 := by
  unfold tailWord_1986681
  simp only [CollatzResearch.WordTrace]
  refine ⟨72460208915601509947007897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48306805943734339964671931 72460208915601509947007897)
  ·
    refine ⟨54345156686701132460255923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72460208915601509947007897 54345156686701132460255923)
    ·
      refine ⟨81517735030051698690383885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54345156686701132460255923 81517735030051698690383885)
      ·
        refine ⟨30569150636269387008893957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81517735030051698690383885 30569150636269387008893957)
        ·
          refine ⟨5731715744300510064167617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30569150636269387008893957 5731715744300510064167617)
          ·
            refine ⟨4298786808225382548125713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5731715744300510064167617 4298786808225382548125713)
            ·
              refine ⟨3224090106169036911094285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4298786808225382548125713 3224090106169036911094285)
              ·
                refine ⟨1209033789813388841660357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3224090106169036911094285 1209033789813388841660357)
                ·
                  refine ⟨226693835590010407811317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1209033789813388841660357 226693835590010407811317)
                  ·
                    rfl

theorem cell22_1986681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3, 4].length) (baseStart_1986681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986681 prefixEnd_1986681 := by exact prefixLift 1986681
  have htrace : WordTrace (prefixWord ++ tailWord_1986681) baseStart_1986681 baseEnd_1986681 := by
    simpa [prefixWord, tailWord_1986681, baseEnd_1986681] using wordTrace_append hprefix tailTrace_1986681
  have hstable : (prefixWord ++ tailWord_1986681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986681).length < 2 ^ (prefixWord ++ tailWord_1986681).sum := by decide
  have hdescent : baseEnd_1986681 < baseStart_1986681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986692 : List Nat := [2, 3, 2, 1, 2, 1, 11]
def baseStart_1986692 : Nat := 118140960795 + 1986692 * 2 ^ 59
def prefixEnd_1986692 : Nat := 4983230072969 + 3 ^ 40 * 1986692 * 2
def baseEnd_1986692 : Nat := 25188343418327068941071

theorem tailTrace_1986692 : CollatzResearch.WordTrace tailWord_1986692 prefixEnd_1986692 25188343418327068941071 := by
  unfold tailWord_1986692
  simp only [CollatzResearch.WordTrace]
  refine ⟨36230305059280829412829165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48307073412374439217105553 36230305059280829412829165)
  ·
    refine ⟨13586364397230311029810937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36230305059280829412829165 13586364397230311029810937)
    ·
      refine ⟨10189773297922733272358203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13586364397230311029810937 10189773297922733272358203)
      ·
        refine ⟨15284659946884099908537305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10189773297922733272358203 15284659946884099908537305)
        ·
          refine ⟨11463494960163074931402979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15284659946884099908537305 11463494960163074931402979)
          ·
            refine ⟨17195242440244612397104469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11463494960163074931402979 17195242440244612397104469)
            ·
              refine ⟨25188343418327068941071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 17195242440244612397104469 25188343418327068941071)
              ·
                rfl

theorem cell22_1986692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 11].length) (baseStart_1986692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986692 prefixEnd_1986692 := by exact prefixLift 1986692
  have htrace : WordTrace (prefixWord ++ tailWord_1986692) baseStart_1986692 baseEnd_1986692 := by
    simpa [prefixWord, tailWord_1986692, baseEnd_1986692] using wordTrace_append hprefix tailTrace_1986692
  have hstable : (prefixWord ++ tailWord_1986692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986692).length < 2 ^ (prefixWord ++ tailWord_1986692).sum := by decide
  have hdescent : baseEnd_1986692 < baseStart_1986692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986696 : List Nat := [2, 1, 3, 4, 1, 2, 1, 1, 4, 3]
def baseStart_1986696 : Nat := 118140960795 + 1986696 * 2 ^ 59
def prefixEnd_1986696 : Nat := 4983230072969 + 3 ^ 40 * 1986696 * 2
def baseEnd_1986696 : Nat := 680086641576576184308905

theorem tailTrace_1986696 : CollatzResearch.WordTrace tailWord_1986696 prefixEnd_1986696 680086641576576184308905 := by
  unfold tailWord_1986696
  simp only [CollatzResearch.WordTrace]
  refine ⟨36230378005273583754401971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48307170673698111672535961 36230378005273583754401971)
  ·
    refine ⟨54345567007910375631602957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36230378005273583754401971 54345567007910375631602957)
    ·
      refine ⟨20379587627966390861851109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54345567007910375631602957 20379587627966390861851109)
      ·
        refine ⟨3821172680243698286597083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20379587627966390861851109 3821172680243698286597083)
        ·
          refine ⟨5731759020365547429895625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3821172680243698286597083 5731759020365547429895625)
          ·
            refine ⟨4298819265274160572421719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5731759020365547429895625 4298819265274160572421719)
            ·
              refine ⟨6448228897911240858632579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4298819265274160572421719 6448228897911240858632579)
              ·
                refine ⟨9672343346866861287948869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6448228897911240858632579 9672343346866861287948869)
                ·
                  refine ⟨1813564377537536491490413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9672343346866861287948869 1813564377537536491490413)
                  ·
                    refine ⟨680086641576576184308905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1813564377537536491490413 680086641576576184308905)
                    ·
                      rfl

theorem cell22_1986696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_1986696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986696 prefixEnd_1986696 := by exact prefixLift 1986696
  have htrace : WordTrace (prefixWord ++ tailWord_1986696) baseStart_1986696 baseEnd_1986696 := by
    simpa [prefixWord, tailWord_1986696, baseEnd_1986696] using wordTrace_append hprefix tailTrace_1986696
  have hstable : (prefixWord ++ tailWord_1986696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986696).length < 2 ^ (prefixWord ++ tailWord_1986696).sum := by decide
  have hdescent : baseEnd_1986696 < baseStart_1986696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986784 : List Nat := [2, 1, 1, 3, 1, 3, 3, 1, 3, 4]
def baseStart_1986784 : Nat := 118140960795 + 1986784 * 2 ^ 59
def prefixEnd_1986784 : Nat := 4983230072969 + 3 ^ 40 * 1986784 * 2
def baseEnd_1986784 : Nat := 680116765774973288108635

theorem tailTrace_1986784 : CollatzResearch.WordTrace tailWord_1986784 prefixEnd_1986784 680116765774973288108635 := by
  unfold tailWord_1986784
  simp only [CollatzResearch.WordTrace]
  refine ⟨36231982817114179269003703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48309310422818905692004937 36231982817114179269003703)
  ·
    refine ⟨54347974225671268903505555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36231982817114179269003703 54347974225671268903505555)
    ·
      refine ⟨81521961338506903355258333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54347974225671268903505555 81521961338506903355258333)
      ·
        refine ⟨30570735501940088758221875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81521961338506903355258333 30570735501940088758221875)
        ·
          refine ⟨45856103252910133137332813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30570735501940088758221875 45856103252910133137332813)
          ·
            refine ⟨17196038719841299926499805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45856103252910133137332813 17196038719841299926499805)
            ·
              refine ⟨6448514519940487472437427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17196038719841299926499805 6448514519940487472437427)
              ·
                refine ⟨9672771779910731208656141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6448514519940487472437427 9672771779910731208656141)
                ·
                  refine ⟨3627289417466524203246053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9672771779910731208656141 3627289417466524203246053)
                  ·
                    refine ⟨680116765774973288108635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3627289417466524203246053 680116765774973288108635)
                    ·
                      rfl

theorem cell22_1986784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 3, 4].length) (baseStart_1986784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986784 prefixEnd_1986784 := by exact prefixLift 1986784
  have htrace : WordTrace (prefixWord ++ tailWord_1986784) baseStart_1986784 baseEnd_1986784 := by
    simpa [prefixWord, tailWord_1986784, baseEnd_1986784] using wordTrace_append hprefix tailTrace_1986784
  have hstable : (prefixWord ++ tailWord_1986784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986784).length < 2 ^ (prefixWord ++ tailWord_1986784).sum := by decide
  have hdescent : baseEnd_1986784 < baseStart_1986784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986865 : List Nat := [1, 2, 2, 3, 4, 2, 1, 2, 2, 3]
def baseStart_1986865 : Nat := 118140960795 + 1986865 * 2 ^ 59
def prefixEnd_1986865 : Nat := 4983230072969 + 3 ^ 40 * 1986865 * 2
def baseEnd_1986865 : Nat := 680144493730316076833387

theorem tailTrace_1986865 : CollatzResearch.WordTrace tailWord_1986865 prefixEnd_1986865 680144493730316076833387 := by
  unfold tailWord_1986865
  simp only [CollatzResearch.WordTrace]
  refine ⟨72466919946934909371706049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48311279964623272914470699 72466919946934909371706049)
  ·
    refine ⟨54350189960201182028779537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72466919946934909371706049 54350189960201182028779537)
    ·
      refine ⟨40762642470150886521584653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54350189960201182028779537 40762642470150886521584653)
      ·
        refine ⟨15285990926306582445594245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40762642470150886521584653 15285990926306582445594245)
        ·
          refine ⟨2866123298682484208548921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15285990926306582445594245 2866123298682484208548921)
          ·
            refine ⟨2149592474011863156411691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2866123298682484208548921 2149592474011863156411691)
            ·
              refine ⟨3224388711017794734617537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2149592474011863156411691 3224388711017794734617537)
              ·
                refine ⟨2418291533263346050963153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3224388711017794734617537 2418291533263346050963153)
                ·
                  refine ⟨1813718649947509538222365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2418291533263346050963153 1813718649947509538222365)
                  ·
                    refine ⟨680144493730316076833387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1813718649947509538222365 680144493730316076833387)
                    ·
                      rfl

theorem cell22_1986865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2, 3].length) (baseStart_1986865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986865 prefixEnd_1986865 := by exact prefixLift 1986865
  have htrace : WordTrace (prefixWord ++ tailWord_1986865) baseStart_1986865 baseEnd_1986865 := by
    simpa [prefixWord, tailWord_1986865, baseEnd_1986865] using wordTrace_append hprefix tailTrace_1986865
  have hstable : (prefixWord ++ tailWord_1986865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986865).length < 2 ^ (prefixWord ++ tailWord_1986865).sum := by decide
  have hdescent : baseEnd_1986865 < baseStart_1986865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986904 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 4, 5]
def baseStart_1986904 : Nat := 118140960795 + 1986904 * 2 ^ 59
def prefixEnd_1986904 : Nat := 4983230072969 + 3 ^ 40 * 1986904 * 2
def baseEnd_1986904 : Nat := 680157844227332975108267

theorem tailTrace_1986904 : CollatzResearch.WordTrace tailWord_1986904 prefixEnd_1986904 680157844227332975108267 := by
  unfold tailWord_1986904
  simp only [CollatzResearch.WordTrace]
  refine ⟨36234171196896809516187883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48312228262529079354917177 36234171196896809516187883)
  ·
    refine ⟨54351256795345214274281825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36234171196896809516187883 54351256795345214274281825)
    ·
      refine ⟨40763442596508910705711369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54351256795345214274281825 40763442596508910705711369)
      ·
        refine ⟨30572581947381683029283527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40763442596508910705711369 30572581947381683029283527)
        ·
          refine ⟨45858872921072524543925291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30572581947381683029283527 45858872921072524543925291)
          ·
            refine ⟨68788309381608786815887937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45858872921072524543925291 68788309381608786815887937)
            ·
              refine ⟨51591232036206590111915953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 68788309381608786815887937 51591232036206590111915953)
              ·
                refine ⟨38693424027154942583936965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51591232036206590111915953 38693424027154942583936965)
                ·
                  refine ⟨7255017005091551734488181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38693424027154942583936965 7255017005091551734488181)
                  ·
                    refine ⟨680157844227332975108267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7255017005091551734488181 680157844227332975108267)
                    ·
                      rfl

theorem cell22_1986904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_1986904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986904 prefixEnd_1986904 := by exact prefixLift 1986904
  have htrace : WordTrace (prefixWord ++ tailWord_1986904) baseStart_1986904 baseEnd_1986904 := by
    simpa [prefixWord, tailWord_1986904, baseEnd_1986904] using wordTrace_append hprefix tailTrace_1986904
  have hstable : (prefixWord ++ tailWord_1986904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986904).length < 2 ^ (prefixWord ++ tailWord_1986904).sum := by decide
  have hdescent : baseEnd_1986904 < baseStart_1986904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986953 : List Nat := [1, 2, 1, 1, 6, 1, 3, 2, 1, 4]
def baseStart_1986953 : Nat := 118140960795 + 1986953 * 2 ^ 59
def prefixEnd_1986953 : Nat := 4983230072969 + 3 ^ 40 * 1986953 * 2
def baseEnd_1986953 : Nat := 680174617928713180633117

theorem tailTrace_1986953 : CollatzResearch.WordTrace tailWord_1986953 prefixEnd_1986953 680174617928713180633117 := by
  unfold tailWord_1986953
  simp only [CollatzResearch.WordTrace]
  refine ⟨72470129570616100400909513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48313419713744066933939675 72470129570616100400909513)
  ·
    refine ⟨54352597177962075300682135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72470129570616100400909513 54352597177962075300682135)
    ·
      refine ⟨81528895766943112951023203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54352597177962075300682135 81528895766943112951023203)
      ·
        refine ⟨122293343650414669426534805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81528895766943112951023203 122293343650414669426534805)
        ·
          refine ⟨5732500483613187629368819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 122293343650414669426534805 5732500483613187629368819)
          ·
            refine ⟨8598750725419781444053229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5732500483613187629368819 8598750725419781444053229)
            ·
              refine ⟨3224531522032418041519961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8598750725419781444053229 3224531522032418041519961)
              ·
                refine ⟨2418398641524313531139971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3224531522032418041519961 2418398641524313531139971)
                ·
                  refine ⟨3627597962286470296709957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2418398641524313531139971 3627597962286470296709957)
                  ·
                    refine ⟨680174617928713180633117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3627597962286470296709957 680174617928713180633117)
                    ·
                      rfl

theorem cell22_1986953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 4].length) (baseStart_1986953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986953 prefixEnd_1986953 := by exact prefixLift 1986953
  have htrace : WordTrace (prefixWord ++ tailWord_1986953) baseStart_1986953 baseEnd_1986953 := by
    simpa [prefixWord, tailWord_1986953, baseEnd_1986953] using wordTrace_append hprefix tailTrace_1986953
  have hstable : (prefixWord ++ tailWord_1986953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986953).length < 2 ^ (prefixWord ++ tailWord_1986953).sum := by decide
  have hdescent : baseEnd_1986953 < baseStart_1986953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986970 : List Nat := [3, 1, 1, 4, 1, 3, 3, 1, 1, 4]
def baseStart_1986970 : Nat := 118140960795 + 1986970 * 2 ^ 59
def prefixEnd_1986970 : Nat := 4983230072969 + 3 ^ 40 * 1986970 * 2
def baseEnd_1986970 : Nat := 680180437376130802958065

theorem tailTrace_1986970 : CollatzResearch.WordTrace tailWord_1986970 prefixEnd_1986970 680180437376130802958065 := by
  unfold tailWord_1986970
  simp only [CollatzResearch.WordTrace]
  refine ⟨18117687402888628076069591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48313833074369674869518909 18117687402888628076069591)
  ·
    refine ⟨27176531104332942114104387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18117687402888628076069591 27176531104332942114104387)
    ·
      refine ⟨40764796656499413171156581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27176531104332942114104387 40764796656499413171156581)
      ·
        refine ⟨7643399373093639969591859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40764796656499413171156581 7643399373093639969591859)
        ·
          refine ⟨11465099059640459954387789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7643399373093639969591859 11465099059640459954387789)
          ·
            refine ⟨4299412147365172482895421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11465099059640459954387789 4299412147365172482895421)
            ·
              refine ⟨1612279555261939681085783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4299412147365172482895421 1612279555261939681085783)
              ·
                refine ⟨2418419332892909521628675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1612279555261939681085783 2418419332892909521628675)
                ·
                  refine ⟨3627628999339364282443013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2418419332892909521628675 3627628999339364282443013)
                  ·
                    refine ⟨680180437376130802958065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3627628999339364282443013 680180437376130802958065)
                    ·
                      rfl

theorem cell22_1986970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 1, 4].length) (baseStart_1986970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986970 prefixEnd_1986970 := by exact prefixLift 1986970
  have htrace : WordTrace (prefixWord ++ tailWord_1986970) baseStart_1986970 baseEnd_1986970 := by
    simpa [prefixWord, tailWord_1986970, baseEnd_1986970] using wordTrace_append hprefix tailTrace_1986970
  have hstable : (prefixWord ++ tailWord_1986970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986970).length < 2 ^ (prefixWord ++ tailWord_1986970).sum := by decide
  have hdescent : baseEnd_1986970 < baseStart_1986970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986979 : List Nat := [1, 1, 1, 4, 1, 14]
def baseStart_1986979 : Nat := 118140960795 + 1986979 * 2 ^ 59
def prefixEnd_1986979 : Nat := 4983230072969 + 3 ^ 40 * 1986979 * 2
def baseEnd_1986979 : Nat := 8397327385926639252877

theorem tailTrace_1986979 : CollatzResearch.WordTrace tailWord_1986979 prefixEnd_1986979 8397327385926639252877 := by
  unfold tailWord_1986979
  simp only [CollatzResearch.WordTrace]
  refine ⟨72471077868521906841355991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48314051912347937894237327 72471077868521906841355991)
  ·
    refine ⟨108706616802782860262033987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72471077868521906841355991 108706616802782860262033987)
    ·
      refine ⟨163059925204174290393050981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108706616802782860262033987 163059925204174290393050981)
      ·
        refine ⟨30573735975782679448697059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 163059925204174290393050981 30573735975782679448697059)
        ·
          refine ⟨45860603963674019173045589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30573735975782679448697059 45860603963674019173045589)
          ·
            refine ⟨8397327385926639252877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 45860603963674019173045589 8397327385926639252877)
            ·
              rfl

theorem cell22_1986979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 14].length) (baseStart_1986979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986979 prefixEnd_1986979 := by exact prefixLift 1986979
  have htrace : WordTrace (prefixWord ++ tailWord_1986979) baseStart_1986979 baseEnd_1986979 := by
    simpa [prefixWord, tailWord_1986979, baseEnd_1986979] using wordTrace_append hprefix tailTrace_1986979
  have hstable : (prefixWord ++ tailWord_1986979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986979).length < 2 ^ (prefixWord ++ tailWord_1986979).sum := by decide
  have hdescent : baseEnd_1986979 < baseStart_1986979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1986981 : List Nat := [1, 3, 1, 2, 1, 1, 3, 4, 2, 4]
def baseStart_1986981 : Nat := 118140960795 + 1986981 * 2 ^ 59
def prefixEnd_1986981 : Nat := 4983230072969 + 3 ^ 40 * 1986981 * 2
def baseEnd_1986981 : Nat := 680184202900930440933031

theorem tailTrace_1986981 : CollatzResearch.WordTrace tailWord_1986981 prefixEnd_1986981 680184202900930440933031 := by
  unfold tailWord_1986981
  simp only [CollatzResearch.WordTrace]
  refine ⟨72471150814514661182928797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48314100543009774121952531 72471150814514661182928797)
  ·
    refine ⟨27176681555442997943598299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72471150814514661182928797 27176681555442997943598299)
    ·
      refine ⟨40765022333164496915397449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27176681555442997943598299 40765022333164496915397449)
      ·
        refine ⟨30573766749873372686548087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40765022333164496915397449 30573766749873372686548087)
        ·
          refine ⟨45860650124810059029822131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30573766749873372686548087 45860650124810059029822131)
          ·
            refine ⟨68790975187215088544733197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45860650124810059029822131 68790975187215088544733197)
            ·
              refine ⟨25796615695205658204274949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68790975187215088544733197 25796615695205658204274949)
              ·
                refine ⟨4836865442851060913301553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25796615695205658204274949 4836865442851060913301553)
                ·
                  refine ⟨3627649082138295684976165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4836865442851060913301553 3627649082138295684976165)
                  ·
                    refine ⟨680184202900930440933031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3627649082138295684976165 680184202900930440933031)
                    ·
                      rfl

theorem cell22_1986981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_1986981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1986981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1986981 prefixEnd_1986981 := by exact prefixLift 1986981
  have htrace : WordTrace (prefixWord ++ tailWord_1986981) baseStart_1986981 baseEnd_1986981 := by
    simpa [prefixWord, tailWord_1986981, baseEnd_1986981] using wordTrace_append hprefix tailTrace_1986981
  have hstable : (prefixWord ++ tailWord_1986981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1986981).length < 2 ^ (prefixWord ++ tailWord_1986981).sum := by decide
  have hdescent : baseEnd_1986981 < baseStart_1986981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1986981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987041 : List Nat := [1, 2, 3, 1, 2, 2, 3, 1, 7]
def baseStart_1987041 : Nat := 118140960795 + 1987041 * 2 ^ 59
def prefixEnd_1987041 : Nat := 4983230072969 + 3 ^ 40 * 1987041 * 2
def baseEnd_1987041 : Nat := 226734914042370094810949

theorem tailTrace_1987041 : CollatzResearch.WordTrace tailWord_1987041 prefixEnd_1987041 226734914042370094810949 := by
  unfold tailWord_1987041
  simp only [CollatzResearch.WordTrace]
  refine ⟨72473339194297291430112977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48315559462864860953408651 72473339194297291430112977)
  ·
    refine ⟨54355004395722968572584733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72473339194297291430112977 54355004395722968572584733)
    ·
      refine ⟨20383126648396113214719275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54355004395722968572584733 20383126648396113214719275)
      ·
        refine ⟨30574689972594169822078913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20383126648396113214719275 30574689972594169822078913)
        ·
          refine ⟨22931017479445627366559185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30574689972594169822078913 22931017479445627366559185)
          ·
            refine ⟨17198263109584220524919389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22931017479445627366559185 17198263109584220524919389)
            ·
              refine ⟨6449348666094082696844771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17198263109584220524919389 6449348666094082696844771)
              ·
                refine ⟨9674022999141124045267157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6449348666094082696844771 9674022999141124045267157)
                ·
                  refine ⟨226734914042370094810949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9674022999141124045267157 226734914042370094810949)
                  ·
                    rfl

theorem cell22_1987041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 7].length) (baseStart_1987041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987041 prefixEnd_1987041 := by exact prefixLift 1987041
  have htrace : WordTrace (prefixWord ++ tailWord_1987041) baseStart_1987041 baseEnd_1987041 := by
    simpa [prefixWord, tailWord_1987041, baseEnd_1987041] using wordTrace_append hprefix tailTrace_1987041
  have hstable : (prefixWord ++ tailWord_1987041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987041).length < 2 ^ (prefixWord ++ tailWord_1987041).sum := by decide
  have hdescent : baseEnd_1987041 < baseStart_1987041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987056 : List Nat := [2, 1, 1, 1, 3, 3, 1, 3, 2, 5]
def baseStart_1987056 : Nat := 118140960795 + 1987056 * 2 ^ 59
def prefixEnd_1987056 : Nat := 4983230072969 + 3 ^ 40 * 1987056 * 2
def baseEnd_1987056 : Nat := 680209876933655245307801

theorem tailTrace_1987056 : CollatzResearch.WordTrace tailWord_1987056 prefixEnd_1987056 680209876933655245307801 := by
  unfold tailWord_1987056
  simp only [CollatzResearch.WordTrace]
  refine ⟨36236943144621474495954511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48315924192828632661272681 36236943144621474495954511)
  ·
    refine ⟨54355414716932211743931767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36236943144621474495954511 54355414716932211743931767)
    ·
      refine ⟨81533122075398317615897651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54355414716932211743931767 81533122075398317615897651)
      ·
        refine ⟨122299683113097476423846477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81533122075398317615897651 122299683113097476423846477)
        ·
          refine ⟨45862381167411553658942429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 122299683113097476423846477 45862381167411553658942429)
          ·
            refine ⟨17198392937779332622103411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45862381167411553658942429 17198392937779332622103411)
            ·
              refine ⟨25797589406668998933155117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17198392937779332622103411 25797589406668998933155117)
              ·
                refine ⟨9674096027500874599933169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25797589406668998933155117 9674096027500874599933169)
                ·
                  refine ⟨7255572020625655949949877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9674096027500874599933169 7255572020625655949949877)
                  ·
                    refine ⟨680209876933655245307801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7255572020625655949949877 680209876933655245307801)
                    ·
                      rfl

theorem cell22_1987056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 2, 5].length) (baseStart_1987056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987056 prefixEnd_1987056 := by exact prefixLift 1987056
  have htrace : WordTrace (prefixWord ++ tailWord_1987056) baseStart_1987056 baseEnd_1987056 := by
    simpa [prefixWord, tailWord_1987056, baseEnd_1987056] using wordTrace_append hprefix tailTrace_1987056
  have hstable : (prefixWord ++ tailWord_1987056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987056).length < 2 ^ (prefixWord ++ tailWord_1987056).sum := by decide
  have hdescent : baseEnd_1987056 < baseStart_1987056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987079 : List Nat := [1, 1, 4, 3, 3, 2, 1, 3, 1, 3]
def baseStart_1987079 : Nat := 118140960795 + 1987079 * 2 ^ 59
def prefixEnd_1987079 : Nat := 4983230072969 + 3 ^ 40 * 1987079 * 2
def baseEnd_1987079 : Nat := 680217750303690851982731

theorem tailTrace_1987079 : CollatzResearch.WordTrace tailWord_1987079 prefixEnd_1987079 680217750303690851982731 := by
  unfold tailWord_1987079
  simp only [CollatzResearch.WordTrace]
  refine ⟨72474725168159623919996291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48316483445439749279997527 72474725168159623919996291)
  ·
    refine ⟨108712087752239435879994437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72474725168159623919996291 108712087752239435879994437)
    ·
      refine ⟨20383516453544894227498957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108712087752239435879994437 20383516453544894227498957)
      ·
        refine ⟨7643818670079335335312109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20383516453544894227498957 7643818670079335335312109)
        ·
          refine ⟨2866432001279750750742041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7643818670079335335312109 2866432001279750750742041)
          ·
            refine ⟨2149824000959813063056531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2866432001279750750742041 2149824000959813063056531)
            ·
              refine ⟨3224736001439719594584797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2149824000959813063056531 3224736001439719594584797)
              ·
                refine ⟨1209276000539894847969299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3224736001439719594584797 1209276000539894847969299)
                ·
                  refine ⟨1813914000809842271953949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1209276000539894847969299 1813914000809842271953949)
                  ·
                    refine ⟨680217750303690851982731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1813914000809842271953949 680217750303690851982731)
                    ·
                      rfl

theorem cell22_1987079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_1987079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987079 prefixEnd_1987079 := by exact prefixLift 1987079
  have htrace : WordTrace (prefixWord ++ tailWord_1987079) baseStart_1987079 baseEnd_1987079 := by
    simpa [prefixWord, tailWord_1987079, baseEnd_1987079] using wordTrace_append hprefix tailTrace_1987079
  have hstable : (prefixWord ++ tailWord_1987079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987079).length < 2 ^ (prefixWord ++ tailWord_1987079).sum := by decide
  have hdescent : baseEnd_1987079 < baseStart_1987079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987116 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 3, 6]
def baseStart_1987116 : Nat := 118140960795 + 1987116 * 2 ^ 59
def prefixEnd_1987116 : Nat := 4983230072969 + 3 ^ 40 * 1987116 * 2
def baseEnd_1987116 : Nat := 680230416159835088807617

theorem tailTrace_1987116 : CollatzResearch.WordTrace tailWord_1987116 prefixEnd_1987116 680230416159835088807617 := by
  unfold tailWord_1987116
  simp only [CollatzResearch.WordTrace]
  refine ⟨36238037334512789619546601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48317383112683719492728801 36238037334512789619546601)
  ·
    refine ⟨27178528000884592214659951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36238037334512789619546601 27178528000884592214659951)
    ·
      refine ⟨40767792001326888321989927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27178528000884592214659951 40767792001326888321989927)
      ·
        refine ⟨61151688001990332482984891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40767792001326888321989927 61151688001990332482984891)
        ·
          refine ⟨91727532002985498724477337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61151688001990332482984891 91727532002985498724477337)
          ·
            refine ⟨68795649002239124043358003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91727532002985498724477337 68795649002239124043358003)
            ·
              refine ⟨103193473503358686065037005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68795649002239124043358003 103193473503358686065037005)
              ·
                refine ⟨38697552563759507274388877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 103193473503358686065037005 38697552563759507274388877)
                ·
                  refine ⟨14511582211409815227895829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38697552563759507274388877 14511582211409815227895829)
                  ·
                    refine ⟨680230416159835088807617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14511582211409815227895829 680230416159835088807617)
                    ·
                      rfl

theorem cell22_1987116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_1987116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987116 prefixEnd_1987116 := by exact prefixLift 1987116
  have htrace : WordTrace (prefixWord ++ tailWord_1987116) baseStart_1987116 baseEnd_1987116 := by
    simpa [prefixWord, tailWord_1987116, baseEnd_1987116] using wordTrace_append hprefix tailTrace_1987116
  have hstable : (prefixWord ++ tailWord_1987116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987116).length < 2 ^ (prefixWord ++ tailWord_1987116).sum := by decide
  have hdescent : baseEnd_1987116 < baseStart_1987116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987178 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 2, 6]
def baseStart_1987178 : Nat := 118140960795 + 1987178 * 2 ^ 59
def prefixEnd_1987178 : Nat := 4983230072969 + 3 ^ 40 * 1987178 * 2
def baseEnd_1987178 : Nat := 680251640026887593757427

theorem tailTrace_1987178 : CollatzResearch.WordTrace tailWord_1987178 prefixEnd_1987178 680251640026887593757427 := by
  unfold tailWord_1987178
  simp only [CollatzResearch.WordTrace]
  refine ⟨18119583998700240956962547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48318890663200642551900125 18119583998700240956962547)
  ·
    refine ⟨27179375998050361435443821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18119583998700240956962547 27179375998050361435443821)
    ·
      refine ⟨10192265999268885538291433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27179375998050361435443821 10192265999268885538291433)
      ·
        refine ⟨7644199499451664153718575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10192265999268885538291433 7644199499451664153718575)
        ·
          refine ⟨11466299249177496230577863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7644199499451664153718575 11466299249177496230577863)
          ·
            refine ⟨17199448873766244345866795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11466299249177496230577863 17199448873766244345866795)
            ·
              refine ⟨25799173310649366518800193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17199448873766244345866795 25799173310649366518800193)
              ·
                refine ⟨19349379982987024889100145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25799173310649366518800193 19349379982987024889100145)
                ·
                  refine ⟨14512034987240268666825109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19349379982987024889100145 14512034987240268666825109)
                  ·
                    refine ⟨680251640026887593757427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14512034987240268666825109 680251640026887593757427)
                    ·
                      rfl

theorem cell22_1987178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_1987178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987178 prefixEnd_1987178 := by exact prefixLift 1987178
  have htrace : WordTrace (prefixWord ++ tailWord_1987178) baseStart_1987178 baseEnd_1987178 := by
    simpa [prefixWord, tailWord_1987178, baseEnd_1987178] using wordTrace_append hprefix tailTrace_1987178
  have hstable : (prefixWord ++ tailWord_1987178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987178).length < 2 ^ (prefixWord ++ tailWord_1987178).sum := by decide
  have hdescent : baseEnd_1987178 < baseStart_1987178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987210 : List Nat := [3, 1, 2, 3, 3, 1, 1, 1, 7]
def baseStart_1987210 : Nat := 118140960795 + 1987210 * 2 ^ 59
def prefixEnd_1987210 : Nat := 4983230072969 + 3 ^ 40 * 1987210 * 2
def baseEnd_1987210 : Nat := 226754198093616725652443

theorem tailTrace_1987210 : CollatzResearch.WordTrace tailWord_1987210 prefixEnd_1987210 226754198093616725652443 := by
  unfold tailWord_1987210
  simp only [CollatzResearch.WordTrace]
  refine ⟨18119875782671258323253771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48319668753790022195343389 18119875782671258323253771)
  ·
    refine ⟨27179813674006887484880657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18119875782671258323253771 27179813674006887484880657)
    ·
      refine ⟨20384860255505165613660493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27179813674006887484880657 20384860255505165613660493)
      ·
        refine ⟨7644322595814437105122685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20384860255505165613660493 7644322595814437105122685)
        ·
          refine ⟨2866620973430413914421007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7644322595814437105122685 2866620973430413914421007)
          ·
            refine ⟨4299931460145620871631511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2866620973430413914421007 4299931460145620871631511)
            ·
              refine ⟨6449897190218431307447267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4299931460145620871631511 6449897190218431307447267)
              ·
                refine ⟨9674845785327646961170901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6449897190218431307447267 9674845785327646961170901)
                ·
                  refine ⟨226754198093616725652443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9674845785327646961170901 226754198093616725652443)
                  ·
                    rfl

theorem cell22_1987210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 7].length) (baseStart_1987210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987210 prefixEnd_1987210 := by exact prefixLift 1987210
  have htrace : WordTrace (prefixWord ++ tailWord_1987210) baseStart_1987210 baseEnd_1987210 := by
    simpa [prefixWord, tailWord_1987210, baseEnd_1987210] using wordTrace_append hprefix tailTrace_1987210
  have hstable : (prefixWord ++ tailWord_1987210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987210).length < 2 ^ (prefixWord ++ tailWord_1987210).sum := by decide
  have hdescent : baseEnd_1987210 < baseStart_1987210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987287 : List Nat := [1, 1, 3, 2, 1, 5, 1, 3, 2, 3]
def baseStart_1987287 : Nat := 118140960795 + 1987287 * 2 ^ 59
def prefixEnd_1987287 : Nat := 4983230072969 + 3 ^ 40 * 1987287 * 2
def baseEnd_1987287 : Nat := 680288952954447642782093

theorem tailTrace_1987287 : CollatzResearch.WordTrace tailWord_1987287 prefixEnd_1987287 680288952954447642782093 := by
  unfold tailWord_1987287
  simp only [CollatzResearch.WordTrace]
  refine ⟨72482311551406075443568115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48321541034270716962378743 72482311551406075443568115)
  ·
    refine ⟨108723467327109113165352173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72482311551406075443568115 108723467327109113165352173)
    ·
      refine ⟨40771300247665917437007065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108723467327109113165352173 40771300247665917437007065)
      ·
        refine ⟨30578475185749438077755299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40771300247665917437007065 30578475185749438077755299)
        ·
          refine ⟨45867712778624157116632949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30578475185749438077755299 45867712778624157116632949)
          ·
            refine ⟨4300098072996014729684339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45867712778624157116632949 4300098072996014729684339)
            ·
              refine ⟨6450147109494022094526509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4300098072996014729684339 6450147109494022094526509)
              ·
                refine ⟨2418805166060258285447441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6450147109494022094526509 2418805166060258285447441)
                ·
                  refine ⟨1814103874545193714085581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2418805166060258285447441 1814103874545193714085581)
                  ·
                    refine ⟨680288952954447642782093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1814103874545193714085581 680288952954447642782093)
                    ·
                      rfl

theorem cell22_1987287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2, 3].length) (baseStart_1987287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987287 prefixEnd_1987287 := by exact prefixLift 1987287
  have htrace : WordTrace (prefixWord ++ tailWord_1987287) baseStart_1987287 baseEnd_1987287 := by
    simpa [prefixWord, tailWord_1987287, baseEnd_1987287] using wordTrace_append hprefix tailTrace_1987287
  have hstable : (prefixWord ++ tailWord_1987287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987287).length < 2 ^ (prefixWord ++ tailWord_1987287).sum := by decide
  have hdescent : baseEnd_1987287 < baseStart_1987287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987317 : List Nat := [1, 3, 6, 1, 11]
def baseStart_1987317 : Nat := 118140960795 + 1987317 * 2 ^ 59
def prefixEnd_1987317 : Nat := 4983230072969 + 3 ^ 40 * 1987317 * 2
def baseEnd_1987317 : Nat := 2799585278055710142107

theorem tailTrace_1987317 : CollatzResearch.WordTrace tailWord_1987317 prefixEnd_1987317 2799585278055710142107 := by
  unfold tailWord_1987317
  simp only [CollatzResearch.WordTrace]
  refine ⟨72483405741297390567160205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48322270494198260378106803 72483405741297390567160205)
  ·
    refine ⟨27181277152986521462685077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72483405741297390567160205 27181277152986521462685077)
    ·
      refine ⟨1274122366546243193563363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27181277152986521462685077 1274122366546243193563363)
      ·
        refine ⟨1911183549819364790345045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1274122366546243193563363 1911183549819364790345045)
        ·
          refine ⟨2799585278055710142107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1911183549819364790345045 2799585278055710142107)
          ·
            rfl

theorem cell22_1987317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 11].length) (baseStart_1987317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987317 prefixEnd_1987317 := by exact prefixLift 1987317
  have htrace : WordTrace (prefixWord ++ tailWord_1987317) baseStart_1987317 baseEnd_1987317 := by
    simpa [prefixWord, tailWord_1987317, baseEnd_1987317] using wordTrace_append hprefix tailTrace_1987317
  have hstable : (prefixWord ++ tailWord_1987317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987317).length < 2 ^ (prefixWord ++ tailWord_1987317).sum := by decide
  have hdescent : baseEnd_1987317 < baseStart_1987317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987332 : List Nat := [2, 3, 2, 2, 1, 1, 2, 3, 3, 3]
def baseStart_1987332 : Nat := 118140960795 + 1987332 * 2 ^ 59
def prefixEnd_1987332 : Nat := 4983230072969 + 3 ^ 40 * 1987332 * 2
def baseEnd_1987332 : Nat := 680304357374082525406955

theorem tailTrace_1987332 : CollatzResearch.WordTrace tailWord_1987332 prefixEnd_1987332 680304357374082525406955 := by
  unfold tailWord_1987332
  simp only [CollatzResearch.WordTrace]
  refine ⟨36241976418121524064478125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48322635224162032085970833 36241976418121524064478125)
  ·
    refine ⟨13590741156795571524179297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36241976418121524064478125 13590741156795571524179297)
    ·
      refine ⟨10193055867596678643134473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13590741156795571524179297 10193055867596678643134473)
      ·
        refine ⟨7644791900697508982350855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10193055867596678643134473 7644791900697508982350855)
        ·
          refine ⟨11467187851046263473526283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7644791900697508982350855 11467187851046263473526283)
          ·
            refine ⟨17200781776569395210289425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11467187851046263473526283 17200781776569395210289425)
            ·
              refine ⟨12900586332427046407717069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17200781776569395210289425 12900586332427046407717069)
              ·
                refine ⟨4837719874660142402893901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12900586332427046407717069 4837719874660142402893901)
                ·
                  refine ⟨1814144952997553401085213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4837719874660142402893901 1814144952997553401085213)
                  ·
                    refine ⟨680304357374082525406955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1814144952997553401085213 680304357374082525406955)
                    ·
                      rfl

theorem cell22_1987332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_1987332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987332 prefixEnd_1987332 := by exact prefixLift 1987332
  have htrace : WordTrace (prefixWord ++ tailWord_1987332) baseStart_1987332 baseEnd_1987332 := by
    simpa [prefixWord, tailWord_1987332, baseEnd_1987332] using wordTrace_append hprefix tailTrace_1987332
  have hstable : (prefixWord ++ tailWord_1987332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987332).length < 2 ^ (prefixWord ++ tailWord_1987332).sum := by decide
  have hdescent : baseEnd_1987332 < baseStart_1987332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987345 : List Nat := [1, 2, 2, 1, 1, 3, 4, 3, 5]
def baseStart_1987345 : Nat := 118140960795 + 1987345 * 2 ^ 59
def prefixEnd_1987345 : Nat := 4983230072969 + 3 ^ 40 * 1987345 * 2
def baseEnd_1987345 : Nat := 226769602513251608277305

theorem tailTrace_1987345 : CollatzResearch.WordTrace tailWord_1987345 prefixEnd_1987345 226769602513251608277305 := by
  unfold tailWord_1987345
  simp only [CollatzResearch.WordTrace]
  refine ⟨72484426985195951349179489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48322951323463967566119659 72484426985195951349179489)
  ·
    refine ⟨54363320238896963511884617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72484426985195951349179489 54363320238896963511884617)
    ·
      refine ⟨40772490179172722633913463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54363320238896963511884617 40772490179172722633913463)
      ·
        refine ⟨61158735268759083950870195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40772490179172722633913463 61158735268759083950870195)
        ·
          refine ⟨91738102903138625926305293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61158735268759083950870195 91738102903138625926305293)
          ·
            refine ⟨34401788588676984722364485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 91738102903138625926305293 34401788588676984722364485)
            ·
              refine ⟨6450335360376934635443341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34401788588676984722364485 6450335360376934635443341)
              ·
                refine ⟨2418875760141350488291253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6450335360376934635443341 2418875760141350488291253)
                ·
                  refine ⟨226769602513251608277305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2418875760141350488291253 226769602513251608277305)
                  ·
                    rfl

theorem cell22_1987345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 5].length) (baseStart_1987345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987345 prefixEnd_1987345 := by exact prefixLift 1987345
  have htrace : WordTrace (prefixWord ++ tailWord_1987345) baseStart_1987345 baseEnd_1987345 := by
    simpa [prefixWord, tailWord_1987345, baseEnd_1987345] using wordTrace_append hprefix tailTrace_1987345
  have hstable : (prefixWord ++ tailWord_1987345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987345).length < 2 ^ (prefixWord ++ tailWord_1987345).sum := by decide
  have hdescent : baseEnd_1987345 < baseStart_1987345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987409 : List Nat := [1, 2, 2, 1, 6, 1, 2, 2, 1, 4]
def baseStart_1987409 : Nat := 118140960795 + 1987409 * 2 ^ 59
def prefixEnd_1987409 : Nat := 4983230072969 + 3 ^ 40 * 1987409 * 2
def baseEnd_1987409 : Nat := 680330716047679991231719

theorem tailTrace_1987409 : CollatzResearch.WordTrace tailWord_1987409 prefixEnd_1987409 680330716047679991231719 := by
  unfold tailWord_1987409
  simp only [CollatzResearch.WordTrace]
  refine ⟨72486761256964090279509281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48324507504642726853006187 72486761256964090279509281)
  ·
    refine ⟨54365070942723067709631961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72486761256964090279509281 54365070942723067709631961)
    ·
      refine ⟨40773803207042300782223971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54365070942723067709631961 40773803207042300782223971)
      ·
        refine ⟨61160704810563451173335957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40773803207042300782223971 61160704810563451173335957)
        ·
          refine ⟨2866908037995161773750123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61160704810563451173335957 2866908037995161773750123)
          ·
            refine ⟨4300362056992742660625185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2866908037995161773750123 4300362056992742660625185)
            ·
              refine ⟨3225271542744556995468889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4300362056992742660625185 3225271542744556995468889)
              ·
                refine ⟨2418953657058417746601667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3225271542744556995468889 2418953657058417746601667)
                ·
                  refine ⟨3628430485587626619902501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2418953657058417746601667 3628430485587626619902501)
                  ·
                    refine ⟨680330716047679991231719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3628430485587626619902501 680330716047679991231719)
                    ·
                      rfl

theorem cell22_1987409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_1987409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987409 prefixEnd_1987409 := by exact prefixLift 1987409
  have htrace : WordTrace (prefixWord ++ tailWord_1987409) baseStart_1987409 baseEnd_1987409 := by
    simpa [prefixWord, tailWord_1987409, baseEnd_1987409] using wordTrace_append hprefix tailTrace_1987409
  have hstable : (prefixWord ++ tailWord_1987409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987409).length < 2 ^ (prefixWord ++ tailWord_1987409).sum := by decide
  have hdescent : baseEnd_1987409 < baseStart_1987409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987467 : List Nat := [1, 1, 1, 1, 4, 2, 2, 4, 3, 3]
def baseStart_1987467 : Nat := 118140960795 + 1987467 * 2 ^ 59
def prefixEnd_1987467 : Nat := 4983230072969 + 3 ^ 40 * 1987467 * 2
def baseEnd_1987467 : Nat := 680350570632987173281541

theorem tailTrace_1987467 : CollatzResearch.WordTrace tailWord_1987467 prefixEnd_1987467 680350570632987173281541 := by
  unfold tailWord_1987467
  simp only [CollatzResearch.WordTrace]
  refine ⟨72488876690753966185120655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48325917793835977456747103 72488876690753966185120655)
  ·
    refine ⟨108733315036130949277680983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72488876690753966185120655 108733315036130949277680983)
    ·
      refine ⟨163099972554196423916521475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108733315036130949277680983 163099972554196423916521475)
      ·
        refine ⟨244649958831294635874782213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163099972554196423916521475 244649958831294635874782213)
        ·
          refine ⟨45871867280867744226521665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 244649958831294635874782213 45871867280867744226521665)
          ·
            refine ⟨34403900460650808169891249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45871867280867744226521665 34403900460650808169891249)
            ·
              refine ⟨25802925345488106127418437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34403900460650808169891249 25802925345488106127418437)
              ·
                refine ⟨4838048502279019898890957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25802925345488106127418437 4838048502279019898890957)
                ·
                  refine ⟨1814268188354632462084109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4838048502279019898890957 1814268188354632462084109)
                  ·
                    refine ⟨680350570632987173281541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1814268188354632462084109 680350570632987173281541)
                    ·
                      rfl

theorem cell22_1987467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3, 3].length) (baseStart_1987467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987467 prefixEnd_1987467 := by exact prefixLift 1987467
  have htrace : WordTrace (prefixWord ++ tailWord_1987467) baseStart_1987467 baseEnd_1987467 := by
    simpa [prefixWord, tailWord_1987467, baseEnd_1987467] using wordTrace_append hprefix tailTrace_1987467
  have hstable : (prefixWord ++ tailWord_1987467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987467).length < 2 ^ (prefixWord ++ tailWord_1987467).sum := by decide
  have hdescent : baseEnd_1987467 < baseStart_1987467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987497 : List Nat := [1, 2, 1, 1, 1, 1, 8, 2, 5]
def baseStart_1987497 : Nat := 118140960795 + 1987497 * 2 ^ 59
def prefixEnd_1987497 : Nat := 4983230072969 + 3 ^ 40 * 1987497 * 2
def baseEnd_1987497 : Nat := 226786946748692365010483

theorem tailTrace_1987497 : CollatzResearch.WordTrace tailWord_1987497 prefixEnd_1987497 226786946748692365010483 := by
  unfold tailWord_1987497
  simp only [CollatzResearch.WordTrace]
  refine ⟨72489970880645281308712745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48326647253763520872475163 72489970880645281308712745)
  ·
    refine ⟨54367478160483960981534559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72489970880645281308712745 54367478160483960981534559)
    ·
      refine ⟨81551217240725941472301839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54367478160483960981534559 81551217240725941472301839)
      ·
        refine ⟨122326825861088912208452759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81551217240725941472301839 122326825861088912208452759)
        ·
          refine ⟨183490238791633368312679139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 122326825861088912208452759 183490238791633368312679139)
          ·
            refine ⟨275235358187450052469018709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183490238791633368312679139 275235358187450052469018709)
            ·
              refine ⟨3225414353759180302371313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 275235358187450052469018709 3225414353759180302371313)
              ·
                refine ⟨2419060765319385226778485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3225414353759180302371313 2419060765319385226778485)
                ·
                  refine ⟨226786946748692365010483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2419060765319385226778485 226786946748692365010483)
                  ·
                    rfl

theorem cell22_1987497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 5].length) (baseStart_1987497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987497 prefixEnd_1987497 := by exact prefixLift 1987497
  have htrace : WordTrace (prefixWord ++ tailWord_1987497) baseStart_1987497 baseEnd_1987497 := by
    simpa [prefixWord, tailWord_1987497, baseEnd_1987497] using wordTrace_append hprefix tailTrace_1987497
  have hstable : (prefixWord ++ tailWord_1987497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987497).length < 2 ^ (prefixWord ++ tailWord_1987497).sum := by decide
  have hdescent : baseEnd_1987497 < baseStart_1987497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987512 : List Nat := [2, 1, 2, 1, 2, 5, 1, 1, 2, 5]
def baseStart_1987512 : Nat := 118140960795 + 1987512 * 2 ^ 59
def prefixEnd_1987512 : Nat := 4983230072969 + 3 ^ 40 * 1987512 * 2
def baseEnd_1987512 : Nat := 680365975052622055906403

theorem tailTrace_1987512 : CollatzResearch.WordTrace tailWord_1987512 prefixEnd_1987512 680365975052622055906403 := by
  unfold tailWord_1987512
  simp only [CollatzResearch.WordTrace]
  refine ⟨36245258987795469435254395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48327011983727292580339193 36245258987795469435254395)
  ·
    refine ⟨54367888481693204152881593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36245258987795469435254395 54367888481693204152881593)
    ·
      refine ⟨40775916361269903114661195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54367888481693204152881593 40775916361269903114661195)
      ·
        refine ⟨61163874541904854671991793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40775916361269903114661195 61163874541904854671991793)
        ·
          refine ⟨45872905906428641003993845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61163874541904854671991793 45872905906428641003993845)
          ·
            refine ⟨4300584928727685094124423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45872905906428641003993845 4300584928727685094124423)
            ·
              refine ⟨6450877393091527641186635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4300584928727685094124423 6450877393091527641186635)
              ·
                refine ⟨9676316089637291461779953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6450877393091527641186635 9676316089637291461779953)
                ·
                  refine ⟨7257237067227968596334965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9676316089637291461779953 7257237067227968596334965)
                  ·
                    refine ⟨680365975052622055906403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7257237067227968596334965 680365975052622055906403)
                    ·
                      rfl

theorem cell22_1987512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_1987512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987512 prefixEnd_1987512 := by exact prefixLift 1987512
  have htrace : WordTrace (prefixWord ++ tailWord_1987512) baseStart_1987512 baseEnd_1987512 := by
    simpa [prefixWord, tailWord_1987512, baseEnd_1987512] using wordTrace_append hprefix tailTrace_1987512
  have hstable : (prefixWord ++ tailWord_1987512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987512).length < 2 ^ (prefixWord ++ tailWord_1987512).sum := by decide
  have hdescent : baseEnd_1987512 < baseStart_1987512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987527 : List Nat := [1, 1, 4, 1, 1, 2, 4, 1, 3, 4]
def baseStart_1987527 : Nat := 118140960795 + 1987527 * 2 ^ 59
def prefixEnd_1987527 : Nat := 4983230072969 + 3 ^ 40 * 1987527 * 2
def baseEnd_1987527 : Nat := 680371109859167016781357

theorem tailTrace_1987527 : CollatzResearch.WordTrace tailWord_1987527 prefixEnd_1987527 680371109859167016781357 := by
  unfold tailWord_1987527
  simp only [CollatzResearch.WordTrace]
  refine ⟨72491065070536596432304835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48327376713691064288203223 72491065070536596432304835)
  ·
    refine ⟨108736597605804894648457253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72491065070536596432304835 108736597605804894648457253)
    ·
      refine ⟨20388112051088417746585735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 108736597605804894648457253 20388112051088417746585735)
      ·
        refine ⟨30582168076632626619878603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20388112051088417746585735 30582168076632626619878603)
        ·
          refine ⟨45873252114948939929817905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30582168076632626619878603 45873252114948939929817905)
          ·
            refine ⟨34404939086211704947363429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45873252114948939929817905 34404939086211704947363429)
            ·
              refine ⟨6450926078664694677630643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34404939086211704947363429 6450926078664694677630643)
              ·
                refine ⟨9676389117997042016445965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6450926078664694677630643 9676389117997042016445965)
                ·
                  refine ⟨3628645919248890756167237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9676389117997042016445965 3628645919248890756167237)
                  ·
                    refine ⟨680371109859167016781357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3628645919248890756167237 680371109859167016781357)
                    ·
                      rfl

theorem cell22_1987527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_1987527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987527 prefixEnd_1987527 := by exact prefixLift 1987527
  have htrace : WordTrace (prefixWord ++ tailWord_1987527) baseStart_1987527 baseEnd_1987527 := by
    simpa [prefixWord, tailWord_1987527, baseEnd_1987527] using wordTrace_append hprefix tailTrace_1987527
  have hstable : (prefixWord ++ tailWord_1987527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987527).length < 2 ^ (prefixWord ++ tailWord_1987527).sum := by decide
  have hdescent : baseEnd_1987527 < baseStart_1987527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987544 : List Nat := [2, 1, 2, 2, 2, 4, 1, 3, 1, 4]
def baseStart_1987544 : Nat := 118140960795 + 1987544 * 2 ^ 59
def prefixEnd_1987544 : Nat := 4983230072969 + 3 ^ 40 * 1987544 * 2
def baseEnd_1987544 : Nat := 680376929306584639106305

theorem tailTrace_1987544 : CollatzResearch.WordTrace tailWord_1987544 prefixEnd_1987544 680376929306584639106305 := by
  unfold tailWord_1987544
  simp only [CollatzResearch.WordTrace]
  refine ⟨36245842555737504167836843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48327790074316672223782457 36245842555737504167836843)
  ·
    refine ⟨54368763833606256251755265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36245842555737504167836843 54368763833606256251755265)
    ·
      refine ⟨40776572875204692188816449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54368763833606256251755265 40776572875204692188816449)
      ·
        refine ⟨30582429656403519141612337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40776572875204692188816449 30582429656403519141612337)
        ·
          refine ⟨22936822242302639356209253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30582429656403519141612337 22936822242302639356209253)
          ·
            refine ⟨4300654170431744879289235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22936822242302639356209253 4300654170431744879289235)
            ·
              refine ⟨6450981255647617318933853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4300654170431744879289235 6450981255647617318933853)
              ·
                refine ⟨2419117970867856494600195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6450981255647617318933853 2419117970867856494600195)
                ·
                  refine ⟨3628676956301784741900293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2419117970867856494600195 3628676956301784741900293)
                  ·
                    refine ⟨680376929306584639106305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3628676956301784741900293 680376929306584639106305)
                    ·
                      rfl

theorem cell22_1987544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 1, 4].length) (baseStart_1987544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987544 prefixEnd_1987544 := by exact prefixLift 1987544
  have htrace : WordTrace (prefixWord ++ tailWord_1987544) baseStart_1987544 baseEnd_1987544 := by
    simpa [prefixWord, tailWord_1987544, baseEnd_1987544] using wordTrace_append hprefix tailTrace_1987544
  have hstable : (prefixWord ++ tailWord_1987544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987544).length < 2 ^ (prefixWord ++ tailWord_1987544).sum := by decide
  have hdescent : baseEnd_1987544 < baseStart_1987544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987559 : List Nat := [1, 1, 5, 2, 2, 2, 2, 1, 6]
def baseStart_1987559 : Nat := 118140960795 + 1987559 * 2 ^ 59
def prefixEnd_1987559 : Nat := 4983230072969 + 3 ^ 40 * 1987559 * 2
def baseEnd_1987559 : Nat := 226794021371043199993753

theorem tailTrace_1987559 : CollatzResearch.WordTrace tailWord_1987559 prefixEnd_1987559 226794021371043199993753 := by
  unfold tailWord_1987559
  simp only [CollatzResearch.WordTrace]
  refine ⟨72492232206420665897469731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48328154804280443931646487 72492232206420665897469731)
  ·
    refine ⟨108738348309630998846204597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72492232206420665897469731 108738348309630998846204597)
    ·
      refine ⟨10194220154027906141831681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 108738348309630998846204597 10194220154027906141831681)
      ·
        refine ⟨7645665115520929606373761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10194220154027906141831681 7645665115520929606373761)
        ·
          refine ⟨5734248836640697204780321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7645665115520929606373761 5734248836640697204780321)
          ·
            refine ⟨4300686627480522903585241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5734248836640697204780321 4300686627480522903585241)
            ·
              refine ⟨3225514970610392177688931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4300686627480522903585241 3225514970610392177688931)
              ·
                refine ⟨4838272455915588266533397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3225514970610392177688931 4838272455915588266533397)
                ·
                  refine ⟨226794021371043199993753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4838272455915588266533397 226794021371043199993753)
                  ·
                    rfl

theorem cell22_1987559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 6].length) (baseStart_1987559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987559 prefixEnd_1987559 := by exact prefixLift 1987559
  have htrace : WordTrace (prefixWord ++ tailWord_1987559) baseStart_1987559 baseEnd_1987559 := by
    simpa [prefixWord, tailWord_1987559, baseEnd_1987559] using wordTrace_append hprefix tailTrace_1987559
  have hstable : (prefixWord ++ tailWord_1987559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987559).length < 2 ^ (prefixWord ++ tailWord_1987559).sum := by decide
  have hdescent : baseEnd_1987559 < baseStart_1987559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987647 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 4, 5]
def baseStart_1987647 : Nat := 118140960795 + 1987647 * 2 ^ 59
def prefixEnd_1987647 : Nat := 4983230072969 + 3 ^ 40 * 1987647 * 2
def baseEnd_1987647 : Nat := 680412188311526703780989

theorem tailTrace_1987647 : CollatzResearch.WordTrace tailWord_1987647 prefixEnd_1987647 680412188311526703780989 := by
  unfold tailWord_1987647
  simp only [CollatzResearch.WordTrace]
  refine ⟨72495441830101856926673195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48330294553401237951115463 72495441830101856926673195)
  ·
    refine ⟨108743162745152785390009793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72495441830101856926673195 108743162745152785390009793)
    ·
      refine ⟨81557372058864589042507345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108743162745152785390009793 81557372058864589042507345)
      ·
        refine ⟨61168029044148441781880509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 81557372058864589042507345 61168029044148441781880509)
        ·
          refine ⟨22938010891555665668205191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61168029044148441781880509 22938010891555665668205191)
          ·
            refine ⟨34407016337333498502307787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22938010891555665668205191 34407016337333498502307787)
            ·
              refine ⟨51610524506000247753461681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34407016337333498502307787 51610524506000247753461681)
              ·
                refine ⟨38707893379500185815096261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51610524506000247753461681 38707893379500185815096261)
                ·
                  refine ⟨7257730008656284840330549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38707893379500185815096261 7257730008656284840330549)
                  ·
                    refine ⟨680412188311526703780989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7257730008656284840330549 680412188311526703780989)
                    ·
                      rfl

theorem cell22_1987647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 5].length) (baseStart_1987647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987647 prefixEnd_1987647 := by exact prefixLift 1987647
  have htrace : WordTrace (prefixWord ++ tailWord_1987647) baseStart_1987647 baseEnd_1987647 := by
    simpa [prefixWord, tailWord_1987647, baseEnd_1987647] using wordTrace_append hprefix tailTrace_1987647
  have hstable : (prefixWord ++ tailWord_1987647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987647).length < 2 ^ (prefixWord ++ tailWord_1987647).sum := by decide
  have hdescent : baseEnd_1987647 < baseStart_1987647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987666 : List Nat := [3, 2, 2, 1, 3, 2, 2, 2, 5]
def baseStart_1987666 : Nat := 118140960795 + 1987666 * 2 ^ 59
def prefixEnd_1987666 : Nat := 4983230072969 + 3 ^ 40 * 1987666 * 2
def baseEnd_1987666 : Nat := 226806230799938995851977

theorem tailTrace_1987666 : CollatzResearch.WordTrace tailWord_1987666 prefixEnd_1987666 226806230799938995851977 := by
  unfold tailWord_1987666
  simp only [CollatzResearch.WordTrace]
  refine ⟨18124033704258255792903713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48330756544688682114409901 18124033704258255792903713)
  ·
    refine ⟨13593025278193691844677785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18124033704258255792903713 13593025278193691844677785)
    ·
      refine ⟨10194768958645268883508339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13593025278193691844677785 10194768958645268883508339)
      ·
        refine ⟨15292153437967903325262509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10194768958645268883508339 15292153437967903325262509)
        ·
          refine ⟨5734557539237963746973441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15292153437967903325262509 5734557539237963746973441)
          ·
            refine ⟨4300918154428472810230081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5734557539237963746973441 4300918154428472810230081)
            ·
              refine ⟨3225688615821354607672561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4300918154428472810230081 3225688615821354607672561)
              ·
                refine ⟨2419266461866015955754421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3225688615821354607672561 2419266461866015955754421)
                ·
                  refine ⟨226806230799938995851977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2419266461866015955754421 226806230799938995851977)
                  ·
                    rfl

theorem cell22_1987666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_1987666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987666 prefixEnd_1987666 := by exact prefixLift 1987666
  have htrace : WordTrace (prefixWord ++ tailWord_1987666) baseStart_1987666 baseEnd_1987666 := by
    simpa [prefixWord, tailWord_1987666, baseEnd_1987666] using wordTrace_append hprefix tailTrace_1987666
  have hstable : (prefixWord ++ tailWord_1987666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987666).length < 2 ^ (prefixWord ++ tailWord_1987666).sum := by decide
  have hdescent : baseEnd_1987666 < baseStart_1987666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987694 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 8]
def baseStart_1987694 : Nat := 118140960795 + 1987694 * 2 ^ 59
def prefixEnd_1987694 : Nat := 4983230072969 + 3 ^ 40 * 1987694 * 2
def baseEnd_1987694 : Nat := 226809425790678082618615

theorem tailTrace_1987694 : CollatzResearch.WordTrace tailWord_1987694 prefixEnd_1987694 226809425790678082618615 := by
  unfold tailWord_1987694
  simp only [CollatzResearch.WordTrace]
  refine ⟨9062144507616447994204267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 48331437373954389302422757 9062144507616447994204267)
  ·
    refine ⟨13593216761424671991306401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9062144507616447994204267 13593216761424671991306401)
    ·
      refine ⟨10194912571068503993479801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13593216761424671991306401 10194912571068503993479801)
      ·
        refine ⟨7646184428301377995109851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10194912571068503993479801 7646184428301377995109851)
        ·
          refine ⟨11469276642452066992664777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7646184428301377995109851 11469276642452066992664777)
          ·
            refine ⟨8601957481839050244498583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11469276642452066992664777 8601957481839050244498583)
            ·
              refine ⟨12902936222758575366747875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8601957481839050244498583 12902936222758575366747875)
              ·
                refine ⟨19354404334137863050121813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12902936222758575366747875 19354404334137863050121813)
                ·
                  refine ⟨226809425790678082618615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19354404334137863050121813 226809425790678082618615)
                  ·
                    rfl

theorem cell22_1987694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_1987694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987694 prefixEnd_1987694 := by exact prefixLift 1987694
  have htrace : WordTrace (prefixWord ++ tailWord_1987694) baseStart_1987694 baseEnd_1987694 := by
    simpa [prefixWord, tailWord_1987694, baseEnd_1987694] using wordTrace_append hprefix tailTrace_1987694
  have hstable : (prefixWord ++ tailWord_1987694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987694).length < 2 ^ (prefixWord ++ tailWord_1987694).sum := by decide
  have hdescent : baseEnd_1987694 < baseStart_1987694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987709 : List Nat := [1, 4, 1, 1, 3, 1, 1, 4, 1, 5]
def baseStart_1987709 : Nat := 118140960795 + 1987709 * 2 ^ 59
def prefixEnd_1987709 : Nat := 4983230072969 + 3 ^ 40 * 1987709 * 2
def baseEnd_1987709 : Nat := 680433412178579208730799

theorem tailTrace_1987709 : CollatzResearch.WordTrace tailWord_1987709 prefixEnd_1987709 680433412178579208730799 := by
  unfold tailWord_1987709
  simp only [CollatzResearch.WordTrace]
  refine ⟨72497703155877241515430181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48331802103918161010286787 72497703155877241515430181)
  ·
    refine ⟨13593319341726982784143159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 72497703155877241515430181 13593319341726982784143159)
    ·
      refine ⟨20389979012590474176214739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13593319341726982784143159 20389979012590474176214739)
      ·
        refine ⟨30584968518885711264322109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20389979012590474176214739 30584968518885711264322109)
        ·
          refine ⟨11469363194582141724120791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30584968518885711264322109 11469363194582141724120791)
          ·
            refine ⟨17204044791873212586181187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11469363194582141724120791 17204044791873212586181187)
            ·
              refine ⟨25806067187809818879271781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17204044791873212586181187 25806067187809818879271781)
              ·
                refine ⟨4838637597714341039863459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25806067187809818879271781 4838637597714341039863459)
                ·
                  refine ⟨7257956396571511559795189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4838637597714341039863459 7257956396571511559795189)
                  ·
                    refine ⟨680433412178579208730799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7257956396571511559795189 680433412178579208730799)
                    ·
                      rfl

theorem cell22_1987709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_1987709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987709 prefixEnd_1987709 := by exact prefixLift 1987709
  have htrace : WordTrace (prefixWord ++ tailWord_1987709) baseStart_1987709 baseEnd_1987709 := by
    simpa [prefixWord, tailWord_1987709, baseEnd_1987709] using wordTrace_append hprefix tailTrace_1987709
  have hstable : (prefixWord ++ tailWord_1987709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987709).length < 2 ^ (prefixWord ++ tailWord_1987709).sum := by decide
  have hdescent : baseEnd_1987709 < baseStart_1987709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987713 : List Nat := [1, 2, 4, 2, 2, 1, 4, 1, 1, 4]
def baseStart_1987713 : Nat := 118140960795 + 1987713 * 2 ^ 59
def prefixEnd_1987713 : Nat := 4983230072969 + 3 ^ 40 * 1987713 * 2
def baseEnd_1987713 : Nat := 680434781460324531630787

theorem tailTrace_1987713 : CollatzResearch.WordTrace tailWord_1987713 prefixEnd_1987713 680434781460324531630787 := by
  unfold tailWord_1987713
  simp only [CollatzResearch.WordTrace]
  refine ⟨72497849047862750198575793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48331899365241833465717195 72497849047862750198575793)
  ·
    refine ⟨54373386785897062648931845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 72497849047862750198575793 54373386785897062648931845)
    ·
      refine ⟨10195010022355699246674721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54373386785897062648931845 10195010022355699246674721)
      ·
        refine ⟨7646257516766774435006041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10195010022355699246674721 7646257516766774435006041)
        ·
          refine ⟨5734693137575080826254531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7646257516766774435006041 5734693137575080826254531)
          ·
            refine ⟨8602039706362621239381797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5734693137575080826254531 8602039706362621239381797)
            ·
              refine ⟨1612882444942991482384087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8602039706362621239381797 1612882444942991482384087)
              ·
                refine ⟨2419323667414487223576131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1612882444942991482384087 2419323667414487223576131)
                ·
                  refine ⟨3628985501121730835364197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2419323667414487223576131 3628985501121730835364197)
                  ·
                    refine ⟨680434781460324531630787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3628985501121730835364197 680434781460324531630787)
                    ·
                      rfl

theorem cell22_1987713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_1987713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987713 prefixEnd_1987713 := by exact prefixLift 1987713
  have htrace : WordTrace (prefixWord ++ tailWord_1987713) baseStart_1987713 baseEnd_1987713 := by
    simpa [prefixWord, tailWord_1987713, baseEnd_1987713] using wordTrace_append hprefix tailTrace_1987713
  have hstable : (prefixWord ++ tailWord_1987713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987713).length < 2 ^ (prefixWord ++ tailWord_1987713).sum := by decide
  have hdescent : baseEnd_1987713 < baseStart_1987713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987724 : List Nat := [2, 2, 1, 2, 1, 1, 1, 6, 2, 4]
def baseStart_1987724 : Nat := 118140960795 + 1987724 * 2 ^ 59
def prefixEnd_1987724 : Nat := 4983230072969 + 3 ^ 40 * 1987724 * 2
def baseEnd_1987724 : Nat := 680438546985124169605753

theorem tailTrace_1987724 : CollatzResearch.WordTrace tailWord_1987724 prefixEnd_1987724 680438546985124169605753 := by
  unfold tailWord_1987724
  simp only [CollatzResearch.WordTrace]
  refine ⟨36249125125411449538613113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48332166833881932718150817 36249125125411449538613113)
  ·
    refine ⟨27186843844058587153959835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36249125125411449538613113 27186843844058587153959835)
    ·
      refine ⟨40780265766087880730939753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27186843844058587153959835 40780265766087880730939753)
      ·
        refine ⟨30585199324565910548204815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40780265766087880730939753 30585199324565910548204815)
        ·
          refine ⟨45877798986848865822307223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30585199324565910548204815 45877798986848865822307223)
          ·
            refine ⟨68816698480273298733460835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45877798986848865822307223 68816698480273298733460835)
            ·
              refine ⟨103225047720409948100191253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68816698480273298733460835 103225047720409948100191253)
              ·
                refine ⟨4838674111894216317196465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 103225047720409948100191253 4838674111894216317196465)
                ·
                  refine ⟨3629005583920662237897349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4838674111894216317196465 3629005583920662237897349)
                  ·
                    refine ⟨680438546985124169605753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3629005583920662237897349 680438546985124169605753)
                    ·
                      rfl

theorem cell22_1987724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_1987724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987724 prefixEnd_1987724 := by exact prefixLift 1987724
  have htrace : WordTrace (prefixWord ++ tailWord_1987724) baseStart_1987724 baseEnd_1987724 := by
    simpa [prefixWord, tailWord_1987724, baseEnd_1987724] using wordTrace_append hprefix tailTrace_1987724
  have hstable : (prefixWord ++ tailWord_1987724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987724).length < 2 ^ (prefixWord ++ tailWord_1987724).sum := by decide
  have hdescent : baseEnd_1987724 < baseStart_1987724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987743 : List Nat := [1, 1, 2, 6, 2, 2, 1, 1, 1, 5]
def baseStart_1987743 : Nat := 118140960795 + 1987743 * 2 ^ 59
def prefixEnd_1987743 : Nat := 4983230072969 + 3 ^ 40 * 1987743 * 2
def baseEnd_1987743 : Nat := 680445051073414453380695

theorem tailTrace_1987743 : CollatzResearch.WordTrace tailWord_1987743 prefixEnd_1987743 680445051073414453380695 := by
  unfold tailWord_1987743
  simp only [CollatzResearch.WordTrace]
  refine ⟨72498943237754065322167883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48332628825169376881445255 72498943237754065322167883)
  ·
    refine ⟨108748414856631097983251825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72498943237754065322167883 108748414856631097983251825)
    ·
      refine ⟨81561311142473323487438869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 108748414856631097983251825 81561311142473323487438869)
      ·
        refine ⟨3823186459803437038473697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 81561311142473323487438869 3823186459803437038473697)
        ·
          refine ⟨2867389844852577778855273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3823186459803437038473697 2867389844852577778855273)
          ·
            refine ⟨2150542383639433334141455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2867389844852577778855273 2150542383639433334141455)
            ·
              refine ⟨3225813575459150001212183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2150542383639433334141455 3225813575459150001212183)
              ·
                refine ⟨4838720363188725001818275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3225813575459150001212183 4838720363188725001818275)
                ·
                  refine ⟨7258080544783087502727413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4838720363188725001818275 7258080544783087502727413)
                  ·
                    refine ⟨680445051073414453380695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7258080544783087502727413 680445051073414453380695)
                    ·
                      rfl

theorem cell22_1987743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 5].length) (baseStart_1987743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987743 prefixEnd_1987743 := by exact prefixLift 1987743
  have htrace : WordTrace (prefixWord ++ tailWord_1987743) baseStart_1987743 baseEnd_1987743 := by
    simpa [prefixWord, tailWord_1987743, baseEnd_1987743] using wordTrace_append hprefix tailTrace_1987743
  have hstable : (prefixWord ++ tailWord_1987743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987743).length < 2 ^ (prefixWord ++ tailWord_1987743).sum := by decide
  have hdescent : baseEnd_1987743 < baseStart_1987743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987784 : List Nat := [2, 1, 3, 1, 2, 1, 4, 1, 7]
def baseStart_1987784 : Nat := 118140960795 + 1987784 * 2 ^ 59
def prefixEnd_1987784 : Nat := 4983230072969 + 3 ^ 40 * 1987784 * 2
def baseEnd_1987784 : Nat := 226819695403768004368523

theorem tailTrace_1987784 : CollatzResearch.WordTrace tailWord_1987784 prefixEnd_1987784 226819695403768004368523 := by
  unfold tailWord_1987784
  simp only [CollatzResearch.WordTrace]
  refine ⟨36250219315302764662205203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48333625753737019549606937 36250219315302764662205203)
  ·
    refine ⟨54375328972954146993307805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36250219315302764662205203 54375328972954146993307805)
    ·
      refine ⟨20390748364857805122490427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54375328972954146993307805 20390748364857805122490427)
      ·
        refine ⟨30586122547286707683735641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20390748364857805122490427 30586122547286707683735641)
        ·
          refine ⟨22939591910465030762801731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30586122547286707683735641 22939591910465030762801731)
          ·
            refine ⟨34409387865697546144202597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22939591910465030762801731 34409387865697546144202597)
            ·
              refine ⟨6451760224818289902037987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34409387865697546144202597 6451760224818289902037987)
              ·
                refine ⟨9677640337227434853056981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6451760224818289902037987 9677640337227434853056981)
                ·
                  refine ⟨226819695403768004368523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9677640337227434853056981 226819695403768004368523)
                  ·
                    rfl

theorem cell22_1987784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 7].length) (baseStart_1987784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987784 prefixEnd_1987784 := by exact prefixLift 1987784
  have htrace : WordTrace (prefixWord ++ tailWord_1987784) baseStart_1987784 baseEnd_1987784 := by
    simpa [prefixWord, tailWord_1987784, baseEnd_1987784] using wordTrace_append hprefix tailTrace_1987784
  have hstable : (prefixWord ++ tailWord_1987784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987784).length < 2 ^ (prefixWord ++ tailWord_1987784).sum := by decide
  have hdescent : baseEnd_1987784 < baseStart_1987784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987799 : List Nat := [1, 1, 3, 2, 1, 2, 2, 3, 2, 5]
def baseStart_1987799 : Nat := 118140960795 + 1987799 * 2 ^ 59
def prefixEnd_1987799 : Nat := 4983230072969 + 3 ^ 40 * 1987799 * 2
def baseEnd_1987799 : Nat := 680464221017848973980523

theorem tailTrace_1987799 : CollatzResearch.WordTrace tailWord_1987799 prefixEnd_1987799 680464221017848973980523 := by
  unfold tailWord_1987799
  simp only [CollatzResearch.WordTrace]
  refine ⟨72500985725551186886206451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48333990483700791257470967 72500985725551186886206451)
  ·
    refine ⟨108751478588326780329309677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72500985725551186886206451 108751478588326780329309677)
    ·
      refine ⟨40781804470622542623491129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108751478588326780329309677 40781804470622542623491129)
      ·
        refine ⟨30586353352966906967618347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40781804470622542623491129 30586353352966906967618347)
        ·
          refine ⟨45879530029450360451427521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30586353352966906967618347 45879530029450360451427521)
          ·
            refine ⟨34409647522087770338570641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45879530029450360451427521 34409647522087770338570641)
            ·
              refine ⟨25807235641565827753927981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34409647522087770338570641 25807235641565827753927981)
              ·
                refine ⟨9677713365587185407722993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25807235641565827753927981 9677713365587185407722993)
                ·
                  refine ⟨7258285024190389055792245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9677713365587185407722993 7258285024190389055792245)
                  ·
                    refine ⟨680464221017848973980523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7258285024190389055792245 680464221017848973980523)
                    ·
                      rfl

theorem cell22_1987799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_1987799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987799 prefixEnd_1987799 := by exact prefixLift 1987799
  have htrace : WordTrace (prefixWord ++ tailWord_1987799) baseStart_1987799 baseEnd_1987799 := by
    simpa [prefixWord, tailWord_1987799, baseEnd_1987799] using wordTrace_append hprefix tailTrace_1987799
  have hstable : (prefixWord ++ tailWord_1987799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987799).length < 2 ^ (prefixWord ++ tailWord_1987799).sum := by decide
  have hdescent : baseEnd_1987799 < baseStart_1987799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987861 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 6, 3]
def baseStart_1987861 : Nat := 118140960795 + 1987861 * 2 ^ 59
def prefixEnd_1987861 : Nat := 4983230072969 + 3 ^ 40 * 1987861 * 2
def baseEnd_1987861 : Nat := 680485444884901478930333

theorem tailTrace_1987861 : CollatzResearch.WordTrace tailWord_1987861 prefixEnd_1987861 680485444884901478930333 := by
  unfold tailWord_1987861
  simp only [CollatzResearch.WordTrace]
  refine ⟨72503247051326571474963437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48335498034217714316642291 72503247051326571474963437)
  ·
    refine ⟨27188717644247464303111289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72503247051326571474963437 27188717644247464303111289)
    ·
      refine ⟨20391538233185598227333467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27188717644247464303111289 20391538233185598227333467)
      ·
        refine ⟨30587307349778397341000201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20391538233185598227333467 30587307349778397341000201)
        ·
          refine ⟨22940480512333798005750151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30587307349778397341000201 22940480512333798005750151)
          ·
            refine ⟨34410720768500697008625227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22940480512333798005750151 34410720768500697008625227)
            ·
              refine ⟨51616081152751045512937841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34410720768500697008625227 51616081152751045512937841)
              ·
                refine ⟨38712060864563284134703381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51616081152751045512937841 38712060864563284134703381)
                ·
                  refine ⟨1814627853026403943814221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38712060864563284134703381 1814627853026403943814221)
                  ·
                    refine ⟨680485444884901478930333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1814627853026403943814221 680485444884901478930333)
                    ·
                      rfl

theorem cell22_1987861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_1987861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987861 prefixEnd_1987861 := by exact prefixLift 1987861
  have htrace : WordTrace (prefixWord ++ tailWord_1987861) baseStart_1987861 baseEnd_1987861 := by
    simpa [prefixWord, tailWord_1987861, baseEnd_1987861] using wordTrace_append hprefix tailTrace_1987861
  have hstable : (prefixWord ++ tailWord_1987861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987861).length < 2 ^ (prefixWord ++ tailWord_1987861).sum := by decide
  have hdescent : baseEnd_1987861 < baseStart_1987861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987876 : List Nat := [2, 3, 1, 3, 1, 1, 3, 1, 1, 6]
def baseStart_1987876 : Nat := 118140960795 + 1987876 * 2 ^ 59
def prefixEnd_1987876 : Nat := 4983230072969 + 3 ^ 40 * 1987876 * 2
def baseEnd_1987876 : Nat := 680490579691446439805287

theorem tailTrace_1987876 : CollatzResearch.WordTrace tailWord_1987876 prefixEnd_1987876 680490579691446439805287 := by
  unfold tailWord_1987876
  simp only [CollatzResearch.WordTrace]
  refine ⟨36251897073136114518379741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48335862764181486024506321 36251897073136114518379741)
  ·
    refine ⟨13594461402426042944392403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36251897073136114518379741 13594461402426042944392403)
    ·
      refine ⟨20391692103639064416588605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13594461402426042944392403 20391692103639064416588605)
      ·
        refine ⟨7646884538864649156220727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20391692103639064416588605 7646884538864649156220727)
        ·
          refine ⟨11470326808296973734331091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7646884538864649156220727 11470326808296973734331091)
          ·
            refine ⟨17205490212445460601496637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11470326808296973734331091 17205490212445460601496637)
            ·
              refine ⟨6452058829667047725561239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17205490212445460601496637 6452058829667047725561239)
              ·
                refine ⟨9678088244500571588341859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6452058829667047725561239 9678088244500571588341859)
                ·
                  refine ⟨14517132366750857382512789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9678088244500571588341859 14517132366750857382512789)
                  ·
                    refine ⟨680490579691446439805287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14517132366750857382512789 680490579691446439805287)
                    ·
                      rfl

theorem cell22_1987876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_1987876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987876 prefixEnd_1987876 := by exact prefixLift 1987876
  have htrace : WordTrace (prefixWord ++ tailWord_1987876) baseStart_1987876 baseEnd_1987876 := by
    simpa [prefixWord, tailWord_1987876, baseEnd_1987876] using wordTrace_append hprefix tailTrace_1987876
  have hstable : (prefixWord ++ tailWord_1987876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987876).length < 2 ^ (prefixWord ++ tailWord_1987876).sum := by decide
  have hdescent : baseEnd_1987876 < baseStart_1987876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987880 : List Nat := [2, 1, 5, 1, 2, 2, 2, 3, 4]
def baseStart_1987880 : Nat := 118140960795 + 1987880 * 2 ^ 59
def prefixEnd_1987880 : Nat := 4983230072969 + 3 ^ 40 * 1987880 * 2
def baseEnd_1987880 : Nat := 226830649657730587568425

theorem tailTrace_1987880 : CollatzResearch.WordTrace tailWord_1987880 prefixEnd_1987880 226830649657730587568425 := by
  unfold tailWord_1987880
  simp only [CollatzResearch.WordTrace]
  refine ⟨36251970019128868859952547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48335960025505158479936729 36251970019128868859952547)
  ·
    refine ⟨54377955028693303289928821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36251970019128868859952547 54377955028693303289928821)
    ·
      refine ⟨5097933283939997183430827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54377955028693303289928821 5097933283939997183430827)
      ·
        refine ⟨7646899925909995775146241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5097933283939997183430827 7646899925909995775146241)
        ·
          refine ⟨5735174944432496831359681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7646899925909995775146241 5735174944432496831359681)
          ·
            refine ⟨4301381208324372623519761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5735174944432496831359681 4301381208324372623519761)
            ·
              refine ⟨3226035906243279467639821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4301381208324372623519761 3226035906243279467639821)
              ·
                refine ⟨1209763464841229800364933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3226035906243279467639821 1209763464841229800364933)
                ·
                  refine ⟨226830649657730587568425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1209763464841229800364933 226830649657730587568425)
                  ·
                    rfl

theorem cell22_1987880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3, 4].length) (baseStart_1987880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987880 prefixEnd_1987880 := by exact prefixLift 1987880
  have htrace : WordTrace (prefixWord ++ tailWord_1987880) baseStart_1987880 baseEnd_1987880 := by
    simpa [prefixWord, tailWord_1987880, baseEnd_1987880] using wordTrace_append hprefix tailTrace_1987880
  have hstable : (prefixWord ++ tailWord_1987880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987880).length < 2 ^ (prefixWord ++ tailWord_1987880).sum := by decide
  have hdescent : baseEnd_1987880 < baseStart_1987880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987882 : List Nat := [3, 1, 4, 2, 1, 3, 2, 1, 1, 4]
def baseStart_1987882 : Nat := 118140960795 + 1987882 * 2 ^ 59
def prefixEnd_1987882 : Nat := 4983230072969 + 3 ^ 40 * 1987882 * 2
def baseEnd_1987882 : Nat := 680492633614064424155269

theorem tailTrace_1987882 : CollatzResearch.WordTrace tailWord_1987882 prefixEnd_1987882 680492633614064424155269 := by
  unfold tailWord_1987882
  simp only [CollatzResearch.WordTrace]
  refine ⟨18126003246062623015369475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 48336008656166994707651933 18126003246062623015369475)
  ·
    refine ⟨27189004869093934523054213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18126003246062623015369475 27189004869093934523054213)
    ·
      refine ⟨5097938412955112723072665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27189004869093934523054213 5097938412955112723072665)
      ·
        refine ⟨3823453809716334542304499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5097938412955112723072665 3823453809716334542304499)
        ·
          refine ⟨5735180714574501813456749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3823453809716334542304499 5735180714574501813456749)
          ·
            refine ⟨2150692767965438180046281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5735180714574501813456749 2150692767965438180046281)
            ·
              refine ⟨1613019575974078635034711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2150692767965438180046281 1613019575974078635034711)
              ·
                refine ⟨2419529363961117952552067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1613019575974078635034711 2419529363961117952552067)
                ·
                  refine ⟨3629294045941676928828101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2419529363961117952552067 3629294045941676928828101)
                  ·
                    refine ⟨680492633614064424155269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3629294045941676928828101 680492633614064424155269)
                    ·
                      rfl

theorem cell22_1987882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_1987882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987882 prefixEnd_1987882 := by exact prefixLift 1987882
  have htrace : WordTrace (prefixWord ++ tailWord_1987882) baseStart_1987882 baseEnd_1987882 := by
    simpa [prefixWord, tailWord_1987882, baseEnd_1987882] using wordTrace_append hprefix tailTrace_1987882
  have hstable : (prefixWord ++ tailWord_1987882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987882).length < 2 ^ (prefixWord ++ tailWord_1987882).sum := by decide
  have hdescent : baseEnd_1987882 < baseStart_1987882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987936 : List Nat := [2, 1, 1, 3, 4, 1, 1, 2, 7]
def baseStart_1987936 : Nat := 118140960795 + 1987936 * 2 ^ 59
def prefixEnd_1987936 : Nat := 4983230072969 + 3 ^ 40 * 1987936 * 2
def baseEnd_1987936 : Nat := 226837039639208761101701

theorem tailTrace_1987936 : CollatzResearch.WordTrace tailWord_1987936 prefixEnd_1987936 226837039639208761101701 := by
  unfold tailWord_1987936
  simp only [CollatzResearch.WordTrace]
  refine ⟨36252991263027429641971831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48337321684036572855962441 36252991263027429641971831)
  ·
    refine ⟨54379486894541144462957747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36252991263027429641971831 54379486894541144462957747)
    ·
      refine ⟨81569230341811716694436621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54379486894541144462957747 81569230341811716694436621)
      ·
        refine ⟨30588461378179393760413733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 81569230341811716694436621 30588461378179393760413733)
        ·
          refine ⟨5735336508408636330077575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30588461378179393760413733 5735336508408636330077575)
          ·
            refine ⟨8603004762612954495116363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5735336508408636330077575 8603004762612954495116363)
            ·
              refine ⟨12904507143919431742674545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8603004762612954495116363 12904507143919431742674545)
              ·
                refine ⟨9678380357939573807005909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12904507143919431742674545 9678380357939573807005909)
                ·
                  refine ⟨226837039639208761101701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9678380357939573807005909 226837039639208761101701)
                  ·
                    rfl

theorem cell22_1987936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 7].length) (baseStart_1987936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987936 prefixEnd_1987936 := by exact prefixLift 1987936
  have htrace : WordTrace (prefixWord ++ tailWord_1987936) baseStart_1987936 baseEnd_1987936 := by
    simpa [prefixWord, tailWord_1987936, baseEnd_1987936] using wordTrace_append hprefix tailTrace_1987936
  have hstable : (prefixWord ++ tailWord_1987936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987936).length < 2 ^ (prefixWord ++ tailWord_1987936).sum := by decide
  have hdescent : baseEnd_1987936 < baseStart_1987936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1987957 : List Nat := [1, 3, 4, 1, 3, 2, 1, 1, 3, 3]
def baseStart_1987957 : Nat := 118140960795 + 1987957 * 2 ^ 59
def prefixEnd_1987957 : Nat := 4983230072969 + 3 ^ 40 * 1987957 * 2
def baseEnd_1987957 : Nat := 680518307646789228530039

theorem tailTrace_1987957 : CollatzResearch.WordTrace tailWord_1987957 prefixEnd_1987957 680518307646789228530039 := by
  unfold tailWord_1987957
  simp only [CollatzResearch.WordTrace]
  refine ⟨72506748458978779870458125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48337832305985853246972083 72506748458978779870458125)
  ·
    refine ⟨27190030672117042451421797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 72506748458978779870458125 27190030672117042451421797)
    ·
      refine ⟨5098130751021945459641587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27190030672117042451421797 5098130751021945459641587)
      ·
        refine ⟨7647196126532918189462381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5098130751021945459641587 7647196126532918189462381)
        ·
          refine ⟨2867698547449844321048393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7647196126532918189462381 2867698547449844321048393)
          ·
            refine ⟨2150773910587383240786295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2867698547449844321048393 2150773910587383240786295)
            ·
              refine ⟨3226160865881074861179443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2150773910587383240786295 3226160865881074861179443)
              ·
                refine ⟨4839241298821612291769165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3226160865881074861179443 4839241298821612291769165)
                ·
                  refine ⟨1814715487058104609413437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4839241298821612291769165 1814715487058104609413437)
                  ·
                    refine ⟨680518307646789228530039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1814715487058104609413437 680518307646789228530039)
                    ·
                      rfl

theorem cell22_1987957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_1987957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1987957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1987957 prefixEnd_1987957 := by exact prefixLift 1987957
  have htrace : WordTrace (prefixWord ++ tailWord_1987957) baseStart_1987957 baseEnd_1987957 := by
    simpa [prefixWord, tailWord_1987957, baseEnd_1987957] using wordTrace_append hprefix tailTrace_1987957
  have hstable : (prefixWord ++ tailWord_1987957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1987957).length < 2 ^ (prefixWord ++ tailWord_1987957).sum := by decide
  have hdescent : baseEnd_1987957 < baseStart_1987957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1987957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988000 : List Nat := [2, 1, 1, 4, 1, 2, 5, 1, 1, 4]
def baseStart_1988000 : Nat := 118140960795 + 1988000 * 2 ^ 59
def prefixEnd_1988000 : Nat := 4983230072969 + 3 ^ 40 * 1988000 * 2
def baseEnd_1988000 : Nat := 680533027425551449704907

theorem tailTrace_1988000 : CollatzResearch.WordTrace tailWord_1988000 prefixEnd_1988000 680533027425551449704907 := by
  unfold tailWord_1988000
  simp only [CollatzResearch.WordTrace]
  refine ⟨36254158398911499107136727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48338877865215332142848969 36254158398911499107136727)
  ·
    refine ⟨54381237598367248660705091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36254158398911499107136727 54381237598367248660705091)
    ·
      refine ⟨81571856397550872991057637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54381237598367248660705091 81571856397550872991057637)
      ·
        refine ⟨15294723074540788685823307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 81571856397550872991057637 15294723074540788685823307)
        ·
          refine ⟨22942084611811183028734961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15294723074540788685823307 22942084611811183028734961)
          ·
            refine ⟨17206563458858387271551221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22942084611811183028734961 17206563458858387271551221)
            ·
              refine ⟨1613115324267973806707927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17206563458858387271551221 1613115324267973806707927)
              ·
                refine ⟨2419672986401960710061891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1613115324267973806707927 2419672986401960710061891)
                ·
                  refine ⟨3629509479602941065092837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2419672986401960710061891 3629509479602941065092837)
                  ·
                    refine ⟨680533027425551449704907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3629509479602941065092837 680533027425551449704907)
                    ·
                      rfl

theorem cell22_1988000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 1, 1, 4].length) (baseStart_1988000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988000 prefixEnd_1988000 := by exact prefixLift 1988000
  have htrace : WordTrace (prefixWord ++ tailWord_1988000) baseStart_1988000 baseEnd_1988000 := by
    simpa [prefixWord, tailWord_1988000, baseEnd_1988000] using wordTrace_append hprefix tailTrace_1988000
  have hstable : (prefixWord ++ tailWord_1988000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988000).length < 2 ^ (prefixWord ++ tailWord_1988000).sum := by decide
  have hdescent : baseEnd_1988000 < baseStart_1988000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988008 : List Nat := [2, 1, 6, 1, 3, 1, 2, 2, 1, 3]
def baseStart_1988008 : Nat := 118140960795 + 1988008 * 2 ^ 59
def prefixEnd_1988008 : Nat := 4983230072969 + 3 ^ 40 * 1988008 * 2
def baseEnd_1988008 : Nat := 680535765989042095504883

theorem tailTrace_1988008 : CollatzResearch.WordTrace tailWord_1988008 prefixEnd_1988008 680535765989042095504883 := by
  unfold tailWord_1988008
  simp only [CollatzResearch.WordTrace]
  refine ⟨36254304290897007790282339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 48339072387862677053709785 36254304290897007790282339)
  ·
    refine ⟨54381456436345511685423509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36254304290897007790282339 54381456436345511685423509)
    ·
      refine ⟨2549130770453695860254227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54381456436345511685423509 2549130770453695860254227)
      ·
        refine ⟨3823696155680543790381341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2549130770453695860254227 3823696155680543790381341)
        ·
          refine ⟨1433886058380203921393003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3823696155680543790381341 1433886058380203921393003)
          ·
            refine ⟨2150829087570305882089505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1433886058380203921393003 2150829087570305882089505)
            ·
              refine ⟨1613121815677729411567129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2150829087570305882089505 1613121815677729411567129)
              ·
                refine ⟨1209841361758297058675347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1613121815677729411567129 1209841361758297058675347)
                ·
                  refine ⟨1814762042637445588013021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1209841361758297058675347 1814762042637445588013021)
                  ·
                    refine ⟨680535765989042095504883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1814762042637445588013021 680535765989042095504883)
                    ·
                      rfl

theorem cell22_1988008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_1988008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988008 prefixEnd_1988008 := by exact prefixLift 1988008
  have htrace : WordTrace (prefixWord ++ tailWord_1988008) baseStart_1988008 baseEnd_1988008 := by
    simpa [prefixWord, tailWord_1988008, baseEnd_1988008] using wordTrace_append hprefix tailTrace_1988008
  have hstable : (prefixWord ++ tailWord_1988008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988008).length < 2 ^ (prefixWord ++ tailWord_1988008).sum := by decide
  have hdescent : baseEnd_1988008 < baseStart_1988008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1988011 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 8, 4]
def baseStart_1988011 : Nat := 118140960795 + 1988011 * 2 ^ 59
def prefixEnd_1988011 : Nat := 4983230072969 + 3 ^ 40 * 1988011 * 2
def baseEnd_1988011 : Nat := 680536792950351087679873

theorem tailTrace_1988011 : CollatzResearch.WordTrace tailWord_1988011 prefixEnd_1988011 680536792950351087679873 := by
  unfold tailWord_1988011
  simp only [CollatzResearch.WordTrace]
  refine ⟨72508718000783147092923887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 48339145333855431395282591 72508718000783147092923887)
  ·
    refine ⟨108763077001174720639385831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 72508718000783147092923887 108763077001174720639385831)
    ·
      refine ⟨163144615501762080959078747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108763077001174720639385831 163144615501762080959078747)
      ·
        refine ⟨244716923252643121438618121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163144615501762080959078747 244716923252643121438618121)
        ·
          refine ⟨183537692439482341078963591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244716923252643121438618121 183537692439482341078963591)
          ·
            refine ⟨275306538659223511618445387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183537692439482341078963591 275306538659223511618445387)
            ·
              refine ⟨412959807988835267427668081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 275306538659223511618445387 412959807988835267427668081)
              ·
                refine ⟨309719855991626450570751061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412959807988835267427668081 309719855991626450570751061)
                ·
                  refine ⟨3629529562401872467625989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 309719855991626450570751061 3629529562401872467625989)
                  ·
                    refine ⟨680536792950351087679873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3629529562401872467625989 680536792950351087679873)
                    ·
                      rfl

theorem cell22_1988011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 4].length) (baseStart_1988011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1988011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1988011 prefixEnd_1988011 := by exact prefixLift 1988011
  have htrace : WordTrace (prefixWord ++ tailWord_1988011) baseStart_1988011 baseEnd_1988011 := by
    simpa [prefixWord, tailWord_1988011, baseEnd_1988011] using wordTrace_append hprefix tailTrace_1988011
  have hstable : (prefixWord ++ tailWord_1988011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1988011).length < 2 ^ (prefixWord ++ tailWord_1988011).sum := by decide
  have hdescent : baseEnd_1988011 < baseStart_1988011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1988011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
