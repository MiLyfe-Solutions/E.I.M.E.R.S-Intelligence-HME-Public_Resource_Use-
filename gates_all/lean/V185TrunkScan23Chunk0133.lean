import V185TrunkScan23Chunk0132

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_787875 : List Nat := [1, 1, 1, 4, 1, 3, 4, 2, 2, 1, 3]
def baseStart_787875 : Nat := 118140960795 + 787875 * 2 ^ 59
def prefixEnd_787875 : Nat := 4983230072969 + 3 ^ 40 * 787875 * 2
def baseEnd_787875 : Nat := 404558570661210169139135

theorem tailTrace_787875 : CollatzResearch.WordTrace tailWord_787875 prefixEnd_787875 404558570661210169139135 := by
  unfold tailWord_787875
  simp only [CollatzResearch.WordTrace]
  refine ⟨28736162020670908182373079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19157441347113938788248719 28736162020670908182373079)
  ·
    refine ⟨43104243031006362273559619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28736162020670908182373079 43104243031006362273559619)
    ·
      refine ⟨64656364546509543410339429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43104243031006362273559619 64656364546509543410339429)
      ·
        refine ⟨12123068352470539389438643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64656364546509543410339429 12123068352470539389438643)
        ·
          refine ⟨18184602528705809084157965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12123068352470539389438643 18184602528705809084157965)
          ·
            refine ⟨6819225948264678406559237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18184602528705809084157965 6819225948264678406559237)
            ·
              refine ⟨1278604865299627201229857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6819225948264678406559237 1278604865299627201229857)
              ·
                refine ⟨958953648974720400922393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1278604865299627201229857 958953648974720400922393)
                ·
                  refine ⟨719215236731040300691795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 958953648974720400922393 719215236731040300691795)
                  ·
                    refine ⟨1078822855096560451037693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 719215236731040300691795 1078822855096560451037693)
                    ·
                      refine ⟨404558570661210169139135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1078822855096560451037693 404558570661210169139135)
                      ·
                        rfl

theorem cell23_787875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_787875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787875 prefixEnd_787875 := by exact prefixLift 787875
  have htrace : WordTrace (prefixWord ++ tailWord_787875) baseStart_787875 baseEnd_787875 := by
    simpa [prefixWord, tailWord_787875, baseEnd_787875] using wordTrace_append hprefix tailTrace_787875
  have hstable : (prefixWord ++ tailWord_787875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787875).length < 2 ^ (prefixWord ++ tailWord_787875).sum := by decide
  have hdescent : baseEnd_787875 < baseStart_787875 := by decide
  rcases family_descends (prefixWord ++ tailWord_787875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787911 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 4]
def baseStart_787911 : Nat := 118140960795 + 787911 * 2 ^ 59
def prefixEnd_787911 : Nat := 4983230072969 + 3 ^ 40 * 787911 * 2
def baseEnd_787911 : Nat := 404577055964772028288969

theorem tailTrace_787911 : CollatzResearch.WordTrace tailWord_787911 prefixEnd_787911 404577055964772028288969 := by
  unfold tailWord_787911
  simp only [CollatzResearch.WordTrace]
  refine ⟨28737475048540486330683587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19158316699026990887122391 28737475048540486330683587)
  ·
    refine ⟨43106212572810729496025381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28737475048540486330683587 43106212572810729496025381)
    ·
      refine ⟨8082414857402011780504759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43106212572810729496025381 8082414857402011780504759)
      ·
        refine ⟨12123622286103017670757139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8082414857402011780504759 12123622286103017670757139)
        ·
          refine ⟨18185433429154526506135709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12123622286103017670757139 18185433429154526506135709)
          ·
            refine ⟨6819537535932947439800891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18185433429154526506135709 6819537535932947439800891)
            ·
              refine ⟨10229306303899421159701337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6819537535932947439800891 10229306303899421159701337)
              ·
                refine ⟨7671979727924565869776003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10229306303899421159701337 7671979727924565869776003)
                ·
                  refine ⟨11507969591886848804664005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7671979727924565869776003 11507969591886848804664005)
                  ·
                    refine ⟨2157744298478784150874501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11507969591886848804664005 2157744298478784150874501)
                    ·
                      refine ⟨404577055964772028288969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2157744298478784150874501 404577055964772028288969)
                      ·
                        rfl

theorem cell23_787911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_787911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787911 prefixEnd_787911 := by exact prefixLift 787911
  have htrace : WordTrace (prefixWord ++ tailWord_787911) baseStart_787911 baseEnd_787911 := by
    simpa [prefixWord, tailWord_787911, baseEnd_787911] using wordTrace_append hprefix tailTrace_787911
  have hstable : (prefixWord ++ tailWord_787911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787911).length < 2 ^ (prefixWord ++ tailWord_787911).sum := by decide
  have hdescent : baseEnd_787911 < baseStart_787911 := by decide
  rcases family_descends (prefixWord ++ tailWord_787911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787949 : List Nat := [1, 5, 1, 3, 2, 2, 1, 1, 1, 4, 2]
def baseStart_787949 : Nat := 118140960795 + 787949 * 2 ^ 59
def prefixEnd_787949 : Nat := 4983230072969 + 3 ^ 40 * 787949 * 2
def baseEnd_787949 : Nat := 404596568229642879613795

theorem tailTrace_787949 : CollatzResearch.WordTrace tailWord_787949 prefixEnd_787949 404596568229642879613795 := by
  unfold tailWord_787949
  simp only [CollatzResearch.WordTrace]
  refine ⟨28738861022402818820566901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19159240681601879213711267 28738861022402818820566901)
  ·
    refine ⟨2694268220850264264428147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28738861022402818820566901 2694268220850264264428147)
    ·
      refine ⟨4041402331275396396642221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2694268220850264264428147 4041402331275396396642221)
      ·
        refine ⟨1515525874228273648740833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4041402331275396396642221 1515525874228273648740833)
        ·
          refine ⟨1136644405671205236555625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1515525874228273648740833 1136644405671205236555625)
          ·
            refine ⟨852483304253403927416719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1136644405671205236555625 852483304253403927416719)
            ·
              refine ⟨1278724956380105891125079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 852483304253403927416719 1278724956380105891125079)
              ·
                refine ⟨1918087434570158836687619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1278724956380105891125079 1918087434570158836687619)
                ·
                  refine ⟨2877131151855238255031429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1918087434570158836687619 2877131151855238255031429)
                  ·
                    refine ⟨539462090972857172818393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2877131151855238255031429 539462090972857172818393)
                    ·
                      refine ⟨404596568229642879613795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 539462090972857172818393 404596568229642879613795)
                      ·
                        rfl

theorem cell23_787949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_787949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787949 prefixEnd_787949 := by exact prefixLift 787949
  have htrace : WordTrace (prefixWord ++ tailWord_787949) baseStart_787949 baseEnd_787949 := by
    simpa [prefixWord, tailWord_787949, baseEnd_787949] using wordTrace_append hprefix tailTrace_787949
  have hstable : (prefixWord ++ tailWord_787949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787949).length < 2 ^ (prefixWord ++ tailWord_787949).sum := by decide
  have hdescent : baseEnd_787949 < baseStart_787949 := by decide
  rcases family_descends (prefixWord ++ tailWord_787949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787951 : List Nat := [1, 1, 2, 1, 4, 1, 3, 2, 1, 7]
def baseStart_787951 : Nat := 118140960795 + 787951 * 2 ^ 59
def prefixEnd_787951 : Nat := 4983230072969 + 3 ^ 40 * 787951 * 2
def baseEnd_787951 : Nat := 134865865063650623929595

theorem tailTrace_787951 : CollatzResearch.WordTrace tailWord_787951 prefixEnd_787951 134865865063650623929595 := by
  unfold tailWord_787951
  simp only [CollatzResearch.WordTrace]
  refine ⟨28738933968395573162139707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19159289312263715441426471 28738933968395573162139707)
  ·
    refine ⟨43108400952593359743209561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28738933968395573162139707 43108400952593359743209561)
    ·
      refine ⟨32331300714445019807407171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43108400952593359743209561 32331300714445019807407171)
      ·
        refine ⟨48496951071667529711110757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32331300714445019807407171 48496951071667529711110757)
        ·
          refine ⟨9093178325937661820833267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48496951071667529711110757 9093178325937661820833267)
          ·
            refine ⟨13639767488906492731249901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9093178325937661820833267 13639767488906492731249901)
            ·
              refine ⟨5114912808339934774218713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13639767488906492731249901 5114912808339934774218713)
              ·
                refine ⟨3836184606254951080664035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5114912808339934774218713 3836184606254951080664035)
                ·
                  refine ⟨5754276909382426620996053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3836184606254951080664035 5754276909382426620996053)
                  ·
                    refine ⟨134865865063650623929595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5754276909382426620996053 134865865063650623929595)
                    ·
                      rfl

theorem cell23_787951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 7].length) (baseStart_787951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787951 prefixEnd_787951 := by exact prefixLift 787951
  have htrace : WordTrace (prefixWord ++ tailWord_787951) baseStart_787951 baseEnd_787951 := by
    simpa [prefixWord, tailWord_787951, baseEnd_787951] using wordTrace_append hprefix tailTrace_787951
  have hstable : (prefixWord ++ tailWord_787951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787951).length < 2 ^ (prefixWord ++ tailWord_787951).sum := by decide
  have hdescent : baseEnd_787951 < baseStart_787951 := by decide
  rcases family_descends (prefixWord ++ tailWord_787951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787961 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 3, 2, 5]
def baseStart_787961 : Nat := 118140960795 + 787961 * 2 ^ 59
def prefixEnd_787961 : Nat := 4983230072969 + 3 ^ 40 * 787961 * 2
def baseEnd_787961 : Nat := 404602729997496832663739

theorem tailTrace_787961 : CollatzResearch.WordTrace tailWord_787961 prefixEnd_787961 404602729997496832663739 := by
  unfold tailWord_787961
  simp only [CollatzResearch.WordTrace]
  refine ⟨28739298698359344870003737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19159532465572896580002491 28739298698359344870003737)
  ·
    refine ⟨21554474023769508652502803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28739298698359344870003737 21554474023769508652502803)
    ·
      refine ⟨32331711035654262978754205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21554474023769508652502803 32331711035654262978754205)
      ·
        refine ⟨12124391638370348617032827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32331711035654262978754205 12124391638370348617032827)
        ·
          refine ⟨18186587457555522925549241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12124391638370348617032827 18186587457555522925549241)
          ·
            refine ⟨13639940593166642194161931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18186587457555522925549241 13639940593166642194161931)
            ·
              refine ⟨20459910889749963291242897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13639940593166642194161931 20459910889749963291242897)
              ·
                refine ⟨15344933167312472468432173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20459910889749963291242897 15344933167312472468432173)
                ·
                  refine ⟨5754349937742177175662065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15344933167312472468432173 5754349937742177175662065)
                  ·
                    refine ⟨4315762453306632881746549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5754349937742177175662065 4315762453306632881746549)
                    ·
                      refine ⟨404602729997496832663739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4315762453306632881746549 404602729997496832663739)
                      ·
                        rfl

theorem cell23_787961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_787961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_787961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_787961 prefixEnd_787961 := by exact prefixLift 787961
  have htrace : WordTrace (prefixWord ++ tailWord_787961) baseStart_787961 baseEnd_787961 := by
    simpa [prefixWord, tailWord_787961, baseEnd_787961] using wordTrace_append hprefix tailTrace_787961
  have hstable : (prefixWord ++ tailWord_787961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787961).length < 2 ^ (prefixWord ++ tailWord_787961).sum := by decide
  have hdescent : baseEnd_787961 < baseStart_787961 := by decide
  rcases family_descends (prefixWord ++ tailWord_787961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788025 : List Nat := [1, 2, 1, 5, 1, 2, 1, 3, 2, 2, 3]
def baseStart_788025 : Nat := 118140960795 + 788025 * 2 ^ 59
def prefixEnd_788025 : Nat := 4983230072969 + 3 ^ 40 * 788025 * 2
def baseEnd_788025 : Nat := 404635592759384582263445

theorem tailTrace_788025 : CollatzResearch.WordTrace tailWord_788025 prefixEnd_788025 404635592759384582263445 := by
  unfold tailWord_788025
  simp only [CollatzResearch.WordTrace]
  refine ⟨28741632970127483800333529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19161088646751655866889019 28741632970127483800333529)
  ·
    refine ⟨21556224727595612850250147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28741632970127483800333529 21556224727595612850250147)
    ·
      refine ⟨32334337091393419275375221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21556224727595612850250147 32334337091393419275375221)
      ·
        refine ⟨3031344102318133057066427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32334337091393419275375221 3031344102318133057066427)
        ·
          refine ⟨4547016153477199585599641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3031344102318133057066427 4547016153477199585599641)
          ·
            refine ⟨3410262115107899689199731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4547016153477199585599641 3410262115107899689199731)
            ·
              refine ⟨5115393172661849533799597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3410262115107899689199731 5115393172661849533799597)
              ·
                refine ⟨1918272439748193575174849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5115393172661849533799597 1918272439748193575174849)
                ·
                  refine ⟨1438704329811145181381137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1918272439748193575174849 1438704329811145181381137)
                  ·
                    refine ⟨1079028247358358886035853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1438704329811145181381137 1079028247358358886035853)
                    ·
                      refine ⟨404635592759384582263445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1079028247358358886035853 404635592759384582263445)
                      ·
                        rfl

theorem cell23_788025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_788025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788025 prefixEnd_788025 := by exact prefixLift 788025
  have htrace : WordTrace (prefixWord ++ tailWord_788025) baseStart_788025 baseEnd_788025 := by
    simpa [prefixWord, tailWord_788025, baseEnd_788025] using wordTrace_append hprefix tailTrace_788025
  have hstable : (prefixWord ++ tailWord_788025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788025).length < 2 ^ (prefixWord ++ tailWord_788025).sum := by decide
  have hdescent : baseEnd_788025 < baseStart_788025 := by decide
  rcases family_descends (prefixWord ++ tailWord_788025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788065 : List Nat := [1, 2, 3, 1, 1, 3, 2, 2, 1, 5, 2]
def baseStart_788065 : Nat := 118140960795 + 788065 * 2 ^ 59
def prefixEnd_788065 : Nat := 4983230072969 + 3 ^ 40 * 788065 * 2
def baseEnd_788065 : Nat := 404656131985564425763261

theorem tailTrace_788065 : CollatzResearch.WordTrace tailWord_788065 prefixEnd_788065 404656131985564425763261 := by
  unfold tailWord_788065
  simp only [CollatzResearch.WordTrace]
  refine ⟨28743091889982570631789649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19162061259988380421193099 28743091889982570631789649)
  ·
    refine ⟨21557318917486927973842237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28743091889982570631789649 21557318917486927973842237)
    ·
      refine ⟨8083994594057597990190839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21557318917486927973842237 8083994594057597990190839)
      ·
        refine ⟨12125991891086396985286259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8083994594057597990190839 12125991891086396985286259)
        ·
          refine ⟨18188987836629595477929389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12125991891086396985286259 18188987836629595477929389)
          ·
            refine ⟨6820870438736098304223521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18188987836629595477929389 6820870438736098304223521)
            ·
              refine ⟨5115652829052073728167641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6820870438736098304223521 5115652829052073728167641)
              ·
                refine ⟨3836739621789055296125731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5115652829052073728167641 3836739621789055296125731)
                ·
                  refine ⟨5755109432683582944188597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3836739621789055296125731 5755109432683582944188597)
                  ·
                    refine ⟨539541509314085901017681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5755109432683582944188597 539541509314085901017681)
                    ·
                      refine ⟨404656131985564425763261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 539541509314085901017681 404656131985564425763261)
                      ·
                        rfl

theorem cell23_788065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 5, 2].length) (baseStart_788065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788065 prefixEnd_788065 := by exact prefixLift 788065
  have htrace : WordTrace (prefixWord ++ tailWord_788065) baseStart_788065 baseEnd_788065 := by
    simpa [prefixWord, tailWord_788065, baseEnd_788065] using wordTrace_append hprefix tailTrace_788065
  have hstable : (prefixWord ++ tailWord_788065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788065).length < 2 ^ (prefixWord ++ tailWord_788065).sum := by decide
  have hdescent : baseEnd_788065 < baseStart_788065 := by decide
  rcases family_descends (prefixWord ++ tailWord_788065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788072 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 5, 1, 3]
def baseStart_788072 : Nat := 118140960795 + 788072 * 2 ^ 59
def prefixEnd_788072 : Nat := 4983230072969 + 3 ^ 40 * 788072 * 2
def baseEnd_788072 : Nat := 404659726350145898375729

theorem tailTrace_788072 : CollatzResearch.WordTrace tailWord_788072 prefixEnd_788072 404659726350145898375729 := by
  unfold tailWord_788072
  simp only [CollatzResearch.WordTrace]
  refine ⟨14371673600478605413647235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19162231467304807218196313 14371673600478605413647235)
  ·
    refine ⟨21557510400717908120470853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14371673600478605413647235 21557510400717908120470853)
    ·
      refine ⟨4042033200134607772588285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21557510400717908120470853 4042033200134607772588285)
      ·
        refine ⟨1515762450050477914720607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4042033200134607772588285 1515762450050477914720607)
        ·
          refine ⟨2273643675075716872080911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1515762450050477914720607 2273643675075716872080911)
          ·
            refine ⟨3410465512613575308121367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2273643675075716872080911 3410465512613575308121367)
            ·
              refine ⟨5115698268920362962182051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3410465512613575308121367 5115698268920362962182051)
              ·
                refine ⟨7673547403380544443273077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5115698268920362962182051 7673547403380544443273077)
                ·
                  refine ⟨719395069066926041556851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7673547403380544443273077 719395069066926041556851)
                  ·
                    refine ⟨1079092603600389062335277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 719395069066926041556851 1079092603600389062335277)
                    ·
                      refine ⟨404659726350145898375729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1079092603600389062335277 404659726350145898375729)
                      ·
                        rfl

theorem cell23_788072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_788072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788072 prefixEnd_788072 := by exact prefixLift 788072
  have htrace : WordTrace (prefixWord ++ tailWord_788072) baseStart_788072 baseEnd_788072 := by
    simpa [prefixWord, tailWord_788072, baseEnd_788072] using wordTrace_append hprefix tailTrace_788072
  have hstable : (prefixWord ++ tailWord_788072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788072).length < 2 ^ (prefixWord ++ tailWord_788072).sum := by decide
  have hdescent : baseEnd_788072 < baseStart_788072 := by decide
  rcases family_descends (prefixWord ++ tailWord_788072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788082 : List Nat := [3, 2, 1, 2, 3, 2, 1, 1, 1, 5, 2]
def baseStart_788082 : Nat := 118140960795 + 788082 * 2 ^ 59
def prefixEnd_788082 : Nat := 4983230072969 + 3 ^ 40 * 788082 * 2
def baseEnd_788082 : Nat := 404664861156690859250683

theorem tailTrace_788082 : CollatzResearch.WordTrace tailWord_788082 prefixEnd_788082 404664861156690859250683 := by
  unfold tailWord_788082
  simp only [CollatzResearch.WordTrace]
  refine ⟨7185927982730245633789625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19162474620613988356772333 7185927982730245633789625)
  ·
    refine ⟨5389445987047684225342219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7185927982730245633789625 5389445987047684225342219)
    ·
      refine ⟨8084168980571526338013329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5389445987047684225342219 8084168980571526338013329)
      ·
        refine ⟨6063126735428644753509997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8084168980571526338013329 6063126735428644753509997)
        ·
          refine ⟨2273672525785741782566249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6063126735428644753509997 2273672525785741782566249)
          ·
            refine ⟨1705254394339306336924687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2273672525785741782566249 1705254394339306336924687)
            ·
              refine ⟨2557881591508959505387031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1705254394339306336924687 2557881591508959505387031)
              ·
                refine ⟨3836822387263439258080547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2557881591508959505387031 3836822387263439258080547)
                ·
                  refine ⟨5755233580895158887120821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3836822387263439258080547 5755233580895158887120821)
                  ·
                    refine ⟨539553148208921145667577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5755233580895158887120821 539553148208921145667577)
                    ·
                      refine ⟨404664861156690859250683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 539553148208921145667577 404664861156690859250683)
                      ·
                        rfl

theorem cell23_788082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_788082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788082 prefixEnd_788082 := by exact prefixLift 788082
  have htrace : WordTrace (prefixWord ++ tailWord_788082) baseStart_788082 baseEnd_788082 := by
    simpa [prefixWord, tailWord_788082, baseEnd_788082] using wordTrace_append hprefix tailTrace_788082
  have hstable : (prefixWord ++ tailWord_788082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788082).length < 2 ^ (prefixWord ++ tailWord_788082).sum := by decide
  have hdescent : baseEnd_788082 < baseStart_788082 := by decide
  rcases family_descends (prefixWord ++ tailWord_788082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788089 : List Nat := [1, 2, 1, 3, 3, 1, 4, 3, 1, 1, 3]
def baseStart_788089 : Nat := 118140960795 + 788089 * 2 ^ 59
def prefixEnd_788089 : Nat := 4983230072969 + 3 ^ 40 * 788089 * 2
def baseEnd_788089 : Nat := 404668455521272331863151

theorem tailTrace_788089 : CollatzResearch.WordTrace tailWord_788089 prefixEnd_788089 404668455521272331863151 := by
  unfold tailWord_788089
  simp only [CollatzResearch.WordTrace]
  refine ⟨28743967241895622730663321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19162644827930415153775547 28743967241895622730663321)
  ·
    refine ⟨21557975431421717047997491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28743967241895622730663321 21557975431421717047997491)
    ·
      refine ⟨32336963147132575571996237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21557975431421717047997491 32336963147132575571996237)
      ·
        refine ⟨12126361180174715839498589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32336963147132575571996237 12126361180174715839498589)
        ·
          refine ⟨4547385442565518439811971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12126361180174715839498589 4547385442565518439811971)
          ·
            refine ⟨6821078163848277659717957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4547385442565518439811971 6821078163848277659717957)
            ·
              refine ⟨1278952155721552061197117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6821078163848277659717957 1278952155721552061197117)
              ·
                refine ⟨479607058395582022948919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1278952155721552061197117 479607058395582022948919)
                ·
                  refine ⟨719410587593373034423379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 479607058395582022948919 719410587593373034423379)
                  ·
                    refine ⟨1079115881390059551635069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 719410587593373034423379 1079115881390059551635069)
                    ·
                      refine ⟨404668455521272331863151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1079115881390059551635069 404668455521272331863151)
                      ·
                        rfl

theorem cell23_788089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3, 1, 1, 3].length) (baseStart_788089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788089 prefixEnd_788089 := by exact prefixLift 788089
  have htrace : WordTrace (prefixWord ++ tailWord_788089) baseStart_788089 baseEnd_788089 := by
    simpa [prefixWord, tailWord_788089, baseEnd_788089] using wordTrace_append hprefix tailTrace_788089
  have hstable : (prefixWord ++ tailWord_788089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788089).length < 2 ^ (prefixWord ++ tailWord_788089).sum := by decide
  have hdescent : baseEnd_788089 < baseStart_788089 := by decide
  rcases family_descends (prefixWord ++ tailWord_788089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788108 : List Nat := [2, 2, 1, 2, 1, 1, 4, 2, 1, 1, 6]
def baseStart_788108 : Nat := 118140960795 + 788108 * 2 ^ 59
def prefixEnd_788108 : Nat := 4983230072969 + 3 ^ 40 * 788108 * 2
def baseEnd_788108 : Nat := 404678211653707757525563

theorem tailTrace_788108 : CollatzResearch.WordTrace tailWord_788108 prefixEnd_788108 404678211653707757525563 := by
  unfold tailWord_788108
  simp only [CollatzResearch.WordTrace]
  refine ⟨14372330114413394487802489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19163106819217859317069985 14372330114413394487802489)
  ·
    refine ⟨10779247585810045865851867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14372330114413394487802489 10779247585810045865851867)
    ·
      refine ⟨16168871378715068798777801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10779247585810045865851867 16168871378715068798777801)
      ·
        refine ⟨12126653534036301599083351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16168871378715068798777801 12126653534036301599083351)
        ·
          refine ⟨18189980301054452398625027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12126653534036301599083351 18189980301054452398625027)
          ·
            refine ⟨27284970451581678597937541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18189980301054452398625027 27284970451581678597937541)
            ·
              refine ⟨5115931959671564737113289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27284970451581678597937541 5115931959671564737113289)
              ·
                refine ⟨3836948969753673552834967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5115931959671564737113289 3836948969753673552834967)
                ·
                  refine ⟨5755423454630510329252451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3836948969753673552834967 5755423454630510329252451)
                  ·
                    refine ⟨8633135181945765493878677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5755423454630510329252451 8633135181945765493878677)
                    ·
                      refine ⟨404678211653707757525563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8633135181945765493878677 404678211653707757525563)
                      ·
                        rfl

theorem cell23_788108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_788108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788108 prefixEnd_788108 := by exact prefixLift 788108
  have htrace : WordTrace (prefixWord ++ tailWord_788108) baseStart_788108 baseEnd_788108 := by
    simpa [prefixWord, tailWord_788108, baseEnd_788108] using wordTrace_append hprefix tailTrace_788108
  have hstable : (prefixWord ++ tailWord_788108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788108).length < 2 ^ (prefixWord ++ tailWord_788108).sum := by decide
  have hdescent : baseEnd_788108 < baseStart_788108 := by decide
  rcases family_descends (prefixWord ++ tailWord_788108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788129 : List Nat := [1, 2, 3, 3, 2, 1, 2, 2, 3, 2, 2]
def baseStart_788129 : Nat := 118140960795 + 788129 * 2 ^ 59
def prefixEnd_788129 : Nat := 4983230072969 + 3 ^ 40 * 788129 * 2
def baseEnd_788129 : Nat := 404688994747452175362967

theorem tailTrace_788129 : CollatzResearch.WordTrace tailWord_788129 prefixEnd_788129 404688994747452175362967 := by
  unfold tailWord_788129
  simp only [CollatzResearch.WordTrace]
  refine ⟨28745426161750709562119441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19163617441167139708079627 28745426161750709562119441)
  ·
    refine ⟨21559069621313032171589581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28745426161750709562119441 21559069621313032171589581)
    ·
      refine ⟨8084651107992387064346093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21559069621313032171589581 8084651107992387064346093)
      ·
        refine ⟨3031744165497145149129785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8084651107992387064346093 3031744165497145149129785)
        ·
          refine ⟨2273808124122858861847339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3031744165497145149129785 2273808124122858861847339)
          ·
            refine ⟨3410712186184288292771009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2273808124122858861847339 3410712186184288292771009)
            ·
              refine ⟨2558034139638216219578257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3410712186184288292771009 2558034139638216219578257)
              ·
                refine ⟨1918525604728662164683693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2558034139638216219578257 1918525604728662164683693)
                ·
                  refine ⟨719447101773248311756385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1918525604728662164683693 719447101773248311756385)
                  ·
                    refine ⟨539585326329936233817289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 719447101773248311756385 539585326329936233817289)
                    ·
                      refine ⟨404688994747452175362967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 539585326329936233817289 404688994747452175362967)
                      ·
                        rfl

theorem cell23_788129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_788129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788129 prefixEnd_788129 := by exact prefixLift 788129
  have htrace : WordTrace (prefixWord ++ tailWord_788129) baseStart_788129 baseEnd_788129 := by
    simpa [prefixWord, tailWord_788129, baseEnd_788129] using wordTrace_append hprefix tailTrace_788129
  have hstable : (prefixWord ++ tailWord_788129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788129).length < 2 ^ (prefixWord ++ tailWord_788129).sum := by decide
  have hdescent : baseEnd_788129 < baseStart_788129 := by decide
  rcases family_descends (prefixWord ++ tailWord_788129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788132 : List Nat := [2, 3, 1, 2, 2, 2, 1, 4, 1, 2, 3]
def baseStart_788132 : Nat := 118140960795 + 788132 * 2 ^ 59
def prefixEnd_788132 : Nat := 4983230072969 + 3 ^ 40 * 788132 * 2
def baseEnd_788132 : Nat := 404690535189415663625453

theorem tailTrace_788132 : CollatzResearch.WordTrace tailWord_788132 prefixEnd_788132 404690535189415663625453 := by
  unfold tailWord_788132
  simp only [CollatzResearch.WordTrace]
  refine ⟨14372767790369920537239325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19163690387159894049652433 14372767790369920537239325)
  ·
    refine ⟨5389787921388720201464747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14372767790369920537239325 5389787921388720201464747)
    ·
      refine ⟨8084681882083080302197121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5389787921388720201464747 8084681882083080302197121)
      ·
        refine ⟨6063511411562310226647841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8084681882083080302197121 6063511411562310226647841)
        ·
          refine ⟨4547633558671732669985881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6063511411562310226647841 4547633558671732669985881)
          ·
            refine ⟨3410725169003799502489411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4547633558671732669985881 3410725169003799502489411)
            ·
              refine ⟨5116087753505699253734117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3410725169003799502489411 5116087753505699253734117)
              ·
                refine ⟨959266453782318610075147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5116087753505699253734117 959266453782318610075147)
                ·
                  refine ⟨1438899680673477915112721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 959266453782318610075147 1438899680673477915112721)
                  ·
                    refine ⟨1079174760505108436334541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1438899680673477915112721 1079174760505108436334541)
                    ·
                      refine ⟨404690535189415663625453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1079174760505108436334541 404690535189415663625453)
                      ·
                        rfl

theorem cell23_788132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_788132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788132 prefixEnd_788132 := by exact prefixLift 788132
  have htrace : WordTrace (prefixWord ++ tailWord_788132) baseStart_788132 baseEnd_788132 := by
    simpa [prefixWord, tailWord_788132, baseEnd_788132] using wordTrace_append hprefix tailTrace_788132
  have hstable : (prefixWord ++ tailWord_788132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788132).length < 2 ^ (prefixWord ++ tailWord_788132).sum := by decide
  have hdescent : baseEnd_788132 < baseStart_788132 := by decide
  rcases family_descends (prefixWord ++ tailWord_788132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788146 : List Nat := [3, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2]
def baseStart_788146 : Nat := 118140960795 + 788146 * 2 ^ 59
def prefixEnd_788146 : Nat := 4983230072969 + 3 ^ 40 * 788146 * 2
def baseEnd_788146 : Nat := 404697723918578608850389

theorem tailTrace_788146 : CollatzResearch.WordTrace tailWord_788146 prefixEnd_788146 404697723918578608850389 := by
  unfold tailWord_788146
  simp only [CollatzResearch.WordTrace]
  refine ⟨7186511550672280366372073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19164030801792747643658861 7186511550672280366372073)
  ·
    refine ⟨5389883663004210274779055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7186511550672280366372073 5389883663004210274779055)
    ·
      refine ⟨8084825494506315412168583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5389883663004210274779055 8084825494506315412168583)
      ·
        refine ⟨12127238241759473118252875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8084825494506315412168583 12127238241759473118252875)
        ·
          refine ⟨18190857362639209677379313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12127238241759473118252875 18190857362639209677379313)
          ·
            refine ⟨13643143021979407258034485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18190857362639209677379313 13643143021979407258034485)
            ·
              refine ⟨1279044658310569430440733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13643143021979407258034485 1279044658310569430440733)
              ·
                refine ⟨479641746866463536415275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1279044658310569430440733 479641746866463536415275)
                ·
                  refine ⟨719462620299695304622913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 479641746866463536415275 719462620299695304622913)
                  ·
                    refine ⟨539596965224771478467185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 719462620299695304622913 539596965224771478467185)
                    ·
                      refine ⟨404697723918578608850389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 539596965224771478467185 404697723918578608850389)
                      ·
                        rfl

theorem cell23_788146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2].length) (baseStart_788146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788146 prefixEnd_788146 := by exact prefixLift 788146
  have htrace : WordTrace (prefixWord ++ tailWord_788146) baseStart_788146 baseEnd_788146 := by
    simpa [prefixWord, tailWord_788146, baseEnd_788146] using wordTrace_append hprefix tailTrace_788146
  have hstable : (prefixWord ++ tailWord_788146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788146).length < 2 ^ (prefixWord ++ tailWord_788146).sum := by decide
  have hdescent : baseEnd_788146 < baseStart_788146 := by decide
  rcases family_descends (prefixWord ++ tailWord_788146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788173 : List Nat := [1, 6, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_788173 : Nat := 118140960795 + 788173 * 2 ^ 59
def prefixEnd_788173 : Nat := 4983230072969 + 3 ^ 40 * 788173 * 2
def baseEnd_788173 : Nat := 134903862632083334404255

theorem tailTrace_788173 : CollatzResearch.WordTrace tailWord_788173 prefixEnd_788173 134903862632083334404255 := by
  unfold tailWord_788173
  simp only [CollatzResearch.WordTrace]
  refine ⟨28747030973591305076721173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19164687315727536717814115 28747030973591305076721173)
  ·
    refine ⟨1347517076887092425471305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28747030973591305076721173 1347517076887092425471305)
    ·
      refine ⟨1010637807665319319103479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1347517076887092425471305 1010637807665319319103479)
      ·
        refine ⟨1515956711497978978655219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1010637807665319319103479 1515956711497978978655219)
        ·
          refine ⟨2273935067246968467982829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1515956711497978978655219 2273935067246968467982829)
          ·
            refine ⟨852725650217613175493561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2273935067246968467982829 852725650217613175493561)
            ·
              refine ⟨639544237663209881620171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 852725650217613175493561 639544237663209881620171)
              ·
                refine ⟨959316356494814822430257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 639544237663209881620171 959316356494814822430257)
                ·
                  refine ⟨719487267371111116822693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 959316356494814822430257 719487267371111116822693)
                  ·
                    refine ⟨134903862632083334404255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 719487267371111116822693 134903862632083334404255)
                    ·
                      rfl

theorem cell23_788173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_788173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788173 prefixEnd_788173 := by exact prefixLift 788173
  have htrace : WordTrace (prefixWord ++ tailWord_788173) baseStart_788173 baseEnd_788173 := by
    simpa [prefixWord, tailWord_788173, baseEnd_788173] using wordTrace_append hprefix tailTrace_788173
  have hstable : (prefixWord ++ tailWord_788173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788173).length < 2 ^ (prefixWord ++ tailWord_788173).sum := by decide
  have hdescent : baseEnd_788173 < baseStart_788173 := by decide
  rcases family_descends (prefixWord ++ tailWord_788173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788202 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 3, 4, 2]
def baseStart_788202 : Nat := 118140960795 + 788202 * 2 ^ 59
def prefixEnd_788202 : Nat := 4983230072969 + 3 ^ 40 * 788202 * 2
def baseEnd_788202 : Nat := 404726478835230389750131

theorem tailTrace_788202 : CollatzResearch.WordTrace tailWord_788202 prefixEnd_788202 404726478835230389750131 := by
  unfold tailWord_788202
  simp only [CollatzResearch.WordTrace]
  refine ⟨7187022172621560757381715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19165392460324162019684573 7187022172621560757381715)
  ·
    refine ⟨10780533258932341136072573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7187022172621560757381715 10780533258932341136072573)
    ·
      refine ⟨4042699972099627926027215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10780533258932341136072573 4042699972099627926027215)
      ·
        refine ⟨6064049958149441889040823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4042699972099627926027215 6064049958149441889040823)
        ·
          refine ⟨9096074937224162833561235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6064049958149441889040823 9096074937224162833561235)
          ·
            refine ⟨13644112405836244250341853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9096074937224162833561235 13644112405836244250341853)
            ·
              refine ⟨5116542152188591593878195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13644112405836244250341853 5116542152188591593878195)
              ·
                refine ⟨7674813228282887390817293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5116542152188591593878195 7674813228282887390817293)
                ·
                  refine ⟨2878054960606082771556485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7674813228282887390817293 2878054960606082771556485)
                  ·
                    refine ⟨539635305113640519666841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2878054960606082771556485 539635305113640519666841)
                    ·
                      refine ⟨404726478835230389750131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 539635305113640519666841 404726478835230389750131)
                      ·
                        rfl

theorem cell23_788202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_788202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788202 prefixEnd_788202 := by exact prefixLift 788202
  have htrace : WordTrace (prefixWord ++ tailWord_788202) baseStart_788202 baseEnd_788202 := by
    simpa [prefixWord, tailWord_788202, baseEnd_788202] using wordTrace_append hprefix tailTrace_788202
  have hstable : (prefixWord ++ tailWord_788202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788202).length < 2 ^ (prefixWord ++ tailWord_788202).sum := by decide
  have hdescent : baseEnd_788202 < baseStart_788202 := by decide
  rcases family_descends (prefixWord ++ tailWord_788202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788206 : List Nat := [4, 1, 2, 1, 1, 2, 5, 1, 1, 3, 2]
def baseStart_788206 : Nat := 118140960795 + 788206 * 2 ^ 59
def prefixEnd_788206 : Nat := 4983230072969 + 3 ^ 40 * 788206 * 2
def baseEnd_788206 : Nat := 404728532757848374100113

theorem tailTrace_788206 : CollatzResearch.WordTrace tailWord_788206 prefixEnd_788206 404728532757848374100113 := by
  unfold tailWord_788206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3593529322808968964084059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19165489721647834475114981 3593529322808968964084059)
  ·
    refine ⟨5390293984213453446126089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3593529322808968964084059 5390293984213453446126089)
    ·
      refine ⟨4042720488160090084594567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5390293984213453446126089 4042720488160090084594567)
      ·
        refine ⟨6064080732240135126891851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4042720488160090084594567 6064080732240135126891851)
        ·
          refine ⟨9096121098360202690337777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6064080732240135126891851 9096121098360202690337777)
          ·
            refine ⟨6822090823770152017753333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9096121098360202690337777 6822090823770152017753333)
            ·
              refine ⟨639571014728451751664375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6822090823770152017753333 639571014728451751664375)
              ·
                refine ⟨959356522092677627496563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 639571014728451751664375 959356522092677627496563)
                ·
                  refine ⟨1439034783139016441244845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 959356522092677627496563 1439034783139016441244845)
                  ·
                    refine ⟨539638043677131165466817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1439034783139016441244845 539638043677131165466817)
                    ·
                      refine ⟨404728532757848374100113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 539638043677131165466817 404728532757848374100113)
                      ·
                        rfl

theorem cell23_788206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_788206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788206 prefixEnd_788206 := by exact prefixLift 788206
  have htrace : WordTrace (prefixWord ++ tailWord_788206) baseStart_788206 baseEnd_788206 := by
    simpa [prefixWord, tailWord_788206, baseEnd_788206] using wordTrace_append hprefix tailTrace_788206
  have hstable : (prefixWord ++ tailWord_788206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788206).length < 2 ^ (prefixWord ++ tailWord_788206).sum := by decide
  have hdescent : baseEnd_788206 < baseStart_788206 := by decide
  rcases family_descends (prefixWord ++ tailWord_788206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788208 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 11]
def baseStart_788208 : Nat := 118140960795 + 788208 * 2 ^ 59
def prefixEnd_788208 : Nat := 4983230072969 + 3 ^ 40 * 788208 * 2
def baseEnd_788208 : Nat := 44969951079906374030567

theorem tailTrace_788208 : CollatzResearch.WordTrace tailWord_788208 prefixEnd_788208 44969951079906374030567 := by
  unfold tailWord_788208
  simp only [CollatzResearch.WordTrace]
  refine ⟨14374153764232253027122639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19165538352309670702830185 14374153764232253027122639)
  ·
    refine ⟨21561230646348379540683959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14374153764232253027122639 21561230646348379540683959)
    ·
      refine ⟨32341845969522569311025939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21561230646348379540683959 32341845969522569311025939)
      ·
        refine ⟨48512768954283853966538909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32341845969522569311025939 48512768954283853966538909)
        ·
          refine ⟨18192288357856445237452091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48512768954283853966538909 18192288357856445237452091)
          ·
            refine ⟨27288432536784667856178137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18192288357856445237452091 27288432536784667856178137)
            ·
              refine ⟨20466324402588500892133603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27288432536784667856178137 20466324402588500892133603)
              ·
                refine ⟨30699486603882751338200405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20466324402588500892133603 30699486603882751338200405)
                ·
                  refine ⟨44969951079906374030567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 30699486603882751338200405 44969951079906374030567)
                  ·
                    rfl

theorem cell23_788208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 11].length) (baseStart_788208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788208 prefixEnd_788208 := by exact prefixLift 788208
  have htrace : WordTrace (prefixWord ++ tailWord_788208) baseStart_788208 baseEnd_788208 := by
    simpa [prefixWord, tailWord_788208, baseEnd_788208] using wordTrace_append hprefix tailTrace_788208
  have hstable : (prefixWord ++ tailWord_788208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788208).length < 2 ^ (prefixWord ++ tailWord_788208).sum := by decide
  have hdescent : baseEnd_788208 < baseStart_788208 := by decide
  rcases family_descends (prefixWord ++ tailWord_788208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788235 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 1, 5, 3]
def baseStart_788235 : Nat := 118140960795 + 788235 * 2 ^ 59
def prefixEnd_788235 : Nat := 4983230072969 + 3 ^ 40 * 788235 * 2
def baseEnd_788235 : Nat := 404743423696828760637479

theorem tailTrace_788235 : CollatzResearch.WordTrace tailWord_788235 prefixEnd_788235 404743423696828760637479 := by
  unfold tailWord_788235
  simp only [CollatzResearch.WordTrace]
  refine ⟨28749292299366689665478159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19166194866244459776985439 28749292299366689665478159)
  ·
    refine ⟨43123938449050034498217239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28749292299366689665478159 43123938449050034498217239)
    ·
      refine ⟨64685907673575051747325859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43123938449050034498217239 64685907673575051747325859)
      ·
        refine ⟨97028861510362577620988789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64685907673575051747325859 97028861510362577620988789)
        ·
          refine ⟨9096455766596491651967699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97028861510362577620988789 9096455766596491651967699)
          ·
            refine ⟨13644683649894737477951549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9096455766596491651967699 13644683649894737477951549)
            ·
              refine ⟨5116756368710526554231831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13644683649894737477951549 5116756368710526554231831)
              ·
                refine ⟨7675134553065789831347747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5116756368710526554231831 7675134553065789831347747)
                ·
                  refine ⟨11512701829598684747021621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7675134553065789831347747 11512701829598684747021621)
                  ·
                    refine ⟨1079315796524876695033277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11512701829598684747021621 1079315796524876695033277)
                    ·
                      refine ⟨404743423696828760637479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1079315796524876695033277 404743423696828760637479)
                      ·
                        rfl

theorem cell23_788235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5, 3].length) (baseStart_788235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788235 prefixEnd_788235 := by exact prefixLift 788235
  have htrace : WordTrace (prefixWord ++ tailWord_788235) baseStart_788235 baseEnd_788235 := by
    simpa [prefixWord, tailWord_788235, baseEnd_788235] using wordTrace_append hprefix tailTrace_788235
  have hstable : (prefixWord ++ tailWord_788235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788235).length < 2 ^ (prefixWord ++ tailWord_788235).sum := by decide
  have hdescent : baseEnd_788235 < baseStart_788235 := by decide
  rcases family_descends (prefixWord ++ tailWord_788235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788242 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 9]
def baseStart_788242 : Nat := 118140960795 + 788242 * 2 ^ 59
def prefixEnd_788242 : Nat := 4983230072969 + 3 ^ 40 * 788242 * 2
def baseEnd_788242 : Nat := 44971890895712248138883

theorem tailTrace_788242 : CollatzResearch.WordTrace tailWord_788242 prefixEnd_788242 44971890895712248138883 := by
  unfold tailWord_788242
  simp only [CollatzResearch.WordTrace]
  refine ⟨7187386902585332465245745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19166365073560886573988653 7187386902585332465245745)
  ·
    refine ⟨5390540176938999348934309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7187386902585332465245745 5390540176938999348934309)
    ·
      refine ⟨1010726283176062377925183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5390540176938999348934309 1010726283176062377925183)
      ·
        refine ⟨1516089424764093566887775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1010726283176062377925183 1516089424764093566887775)
        ·
          refine ⟨2274134137146140350331663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1516089424764093566887775 2274134137146140350331663)
          ·
            refine ⟨3411201205719210525497495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2274134137146140350331663 3411201205719210525497495)
            ·
              refine ⟨5116801808578815788246243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3411201205719210525497495 5116801808578815788246243)
              ·
                refine ⟨7675202712868223682369365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5116801808578815788246243 7675202712868223682369365)
                ·
                  refine ⟨44971890895712248138883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7675202712868223682369365 44971890895712248138883)
                  ·
                    rfl

theorem cell23_788242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 9].length) (baseStart_788242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788242 prefixEnd_788242 := by exact prefixLift 788242
  have htrace : WordTrace (prefixWord ++ tailWord_788242) baseStart_788242 baseEnd_788242 := by
    simpa [prefixWord, tailWord_788242, baseEnd_788242] using wordTrace_append hprefix tailTrace_788242
  have hstable : (prefixWord ++ tailWord_788242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788242).length < 2 ^ (prefixWord ++ tailWord_788242).sum := by decide
  have hdescent : baseEnd_788242 < baseStart_788242 := by decide
  rcases family_descends (prefixWord ++ tailWord_788242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788255 : List Nat := [1, 1, 2, 4, 2, 1, 3, 1, 1, 7]
def baseStart_788255 : Nat := 118140960795 + 788255 * 2 ^ 59
def prefixEnd_788255 : Nat := 4983230072969 + 3 ^ 40 * 788255 * 2
def baseEnd_788255 : Nat := 134917897769972894129129

theorem tailTrace_788255 : CollatzResearch.WordTrace tailWord_788255 prefixEnd_788255 134917897769972894129129 := by
  unfold tailWord_788255
  simp only [CollatzResearch.WordTrace]
  refine ⟨28750021759294233081206219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19166681172862822054137479 28750021759294233081206219)
  ·
    refine ⟨43125032638941349621809329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28750021759294233081206219 43125032638941349621809329)
    ·
      refine ⟨32343774479206012216356997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43125032638941349621809329 32343774479206012216356997)
      ·
        refine ⟨6064457714851127290566937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32343774479206012216356997 6064457714851127290566937)
        ·
          refine ⟨4548343286138345467925203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6064457714851127290566937 4548343286138345467925203)
          ·
            refine ⟨6822514929207518201887805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4548343286138345467925203 6822514929207518201887805)
            ·
              refine ⟨2558443098452819325707927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6822514929207518201887805 2558443098452819325707927)
              ·
                refine ⟨3837664647679228988561891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2558443098452819325707927 3837664647679228988561891)
                ·
                  refine ⟨5756496971518843482842837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3837664647679228988561891 5756496971518843482842837)
                  ·
                    refine ⟨134917897769972894129129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5756496971518843482842837 134917897769972894129129)
                    ·
                      rfl

theorem cell23_788255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 7].length) (baseStart_788255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788255 prefixEnd_788255 := by exact prefixLift 788255
  have htrace : WordTrace (prefixWord ++ tailWord_788255) baseStart_788255 baseEnd_788255 := by
    simpa [prefixWord, tailWord_788255, baseEnd_788255] using wordTrace_append hprefix tailTrace_788255
  have hstable : (prefixWord ++ tailWord_788255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788255).length < 2 ^ (prefixWord ++ tailWord_788255).sum := by decide
  have hdescent : baseEnd_788255 < baseStart_788255 := by decide
  rcases family_descends (prefixWord ++ tailWord_788255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788270 : List Nat := [4, 1, 3, 2, 2, 2, 1, 2, 2, 2, 2]
def baseStart_788270 : Nat := 118140960795 + 788270 * 2 ^ 59
def prefixEnd_788270 : Nat := 4983230072969 + 3 ^ 40 * 788270 * 2
def baseEnd_788270 : Nat := 404761395519736123699819

theorem tailTrace_788270 : CollatzResearch.WordTrace tailWord_788270 prefixEnd_788270 404761395519736123699819 := by
  unfold tailWord_788270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3593821106779986330375283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19167045902826593762001509 3593821106779986330375283)
  ·
    refine ⟨5390731660169979495562925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3593821106779986330375283 5390731660169979495562925)
    ·
      refine ⟨2021524372563742310836097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5390731660169979495562925 2021524372563742310836097)
      ·
        refine ⟨1516143279422806733127073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2021524372563742310836097 1516143279422806733127073)
        ·
          refine ⟨1137107459567105049845305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1516143279422806733127073 1137107459567105049845305)
          ·
            refine ⟨852830594675328787383979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1137107459567105049845305 852830594675328787383979)
            ·
              refine ⟨1279245892012993181075969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 852830594675328787383979 1279245892012993181075969)
              ·
                refine ⟨959434419009744885806977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1279245892012993181075969 959434419009744885806977)
                ·
                  refine ⟨719575814257308664355233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 959434419009744885806977 719575814257308664355233)
                  ·
                    refine ⟨539681860692981498266425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 719575814257308664355233 539681860692981498266425)
                    ·
                      refine ⟨404761395519736123699819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 539681860692981498266425 404761395519736123699819)
                      ·
                        rfl

theorem cell23_788270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_788270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788270 prefixEnd_788270 := by exact prefixLift 788270
  have htrace : WordTrace (prefixWord ++ tailWord_788270) baseStart_788270 baseEnd_788270 := by
    simpa [prefixWord, tailWord_788270, baseEnd_788270] using wordTrace_append hprefix tailTrace_788270
  have hstable : (prefixWord ++ tailWord_788270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788270).length < 2 ^ (prefixWord ++ tailWord_788270).sum := by decide
  have hdescent : baseEnd_788270 < baseStart_788270 := by decide
  rcases family_descends (prefixWord ++ tailWord_788270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788369 : List Nat := [1, 2, 2, 1, 1, 1, 5, 3, 2, 3, 2]
def baseStart_788369 : Nat := 118140960795 + 788369 * 2 ^ 59
def prefixEnd_788369 : Nat := 4983230072969 + 3 ^ 40 * 788369 * 2
def baseEnd_788369 : Nat := 404812230104531236361863

theorem tailTrace_788369 : CollatzResearch.WordTrace tailWord_788369 prefixEnd_788369 404812230104531236361863 := by
  unfold tailWord_788369
  simp only [CollatzResearch.WordTrace]
  refine ⟨28754179680881230550856161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19169453120587487033904107 28754179680881230550856161)
  ·
    refine ⟨21565634760660922913142121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28754179680881230550856161 21565634760660922913142121)
    ·
      refine ⟨16174226070495692184856591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21565634760660922913142121 16174226070495692184856591)
      ·
        refine ⟨24261339105743538277284887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16174226070495692184856591 24261339105743538277284887)
        ·
          refine ⟨36392008658615307415927331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24261339105743538277284887 36392008658615307415927331)
          ·
            refine ⟨54588012987922961123890997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36392008658615307415927331 54588012987922961123890997)
            ·
              refine ⟨5117626217617777605364781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54588012987922961123890997 5117626217617777605364781)
              ·
                refine ⟨1919109831606666602011793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5117626217617777605364781 1919109831606666602011793)
                ·
                  refine ⟨1439332373704999951508845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1919109831606666602011793 1439332373704999951508845)
                  ·
                    refine ⟨539749640139374981815817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1439332373704999951508845 539749640139374981815817)
                    ·
                      refine ⟨404812230104531236361863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 539749640139374981815817 404812230104531236361863)
                      ·
                        rfl

theorem cell23_788369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 3, 2].length) (baseStart_788369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788369 prefixEnd_788369 := by exact prefixLift 788369
  have htrace : WordTrace (prefixWord ++ tailWord_788369) baseStart_788369 baseEnd_788369 := by
    simpa [prefixWord, tailWord_788369, baseEnd_788369] using wordTrace_append hprefix tailTrace_788369
  have hstable : (prefixWord ++ tailWord_788369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788369).length < 2 ^ (prefixWord ++ tailWord_788369).sum := by decide
  have hdescent : baseEnd_788369 < baseStart_788369 := by decide
  rcases family_descends (prefixWord ++ tailWord_788369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788402 : List Nat := [3, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5]
def baseStart_788402 : Nat := 118140960795 + 788402 * 2 ^ 59
def prefixEnd_788402 : Nat := 4983230072969 + 3 ^ 40 * 788402 * 2
def baseEnd_788402 : Nat := 404829174966129607249211

theorem tailTrace_788402 : CollatzResearch.WordTrace tailWord_788402 prefixEnd_788402 404829174966129607249211 := by
  unfold tailWord_788402
  simp only [CollatzResearch.WordTrace]
  refine ⟨7188845822440419296701865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19170255526507784791204973 7188845822440419296701865)
  ·
    refine ⟨5391634366830314472526399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7188845822440419296701865 5391634366830314472526399)
    ·
      refine ⟨8087451550245471708789599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5391634366830314472526399 8087451550245471708789599)
      ·
        refine ⟨12131177325368207563184399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8087451550245471708789599 12131177325368207563184399)
        ·
          refine ⟨18196765988052311344776599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12131177325368207563184399 18196765988052311344776599)
          ·
            refine ⟨27295148982078467017164899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18196765988052311344776599 27295148982078467017164899)
            ·
              refine ⟨40942723473117700525747349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27295148982078467017164899 40942723473117700525747349)
              ·
                refine ⟨1919190162802392212144407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40942723473117700525747349 1919190162802392212144407)
                ·
                  refine ⟨2878785244203588318216611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1919190162802392212144407 2878785244203588318216611)
                  ·
                    refine ⟨4318177866305382477324917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2878785244203588318216611 4318177866305382477324917)
                    ·
                      refine ⟨404829174966129607249211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4318177866305382477324917 404829174966129607249211)
                      ·
                        rfl

theorem cell23_788402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_788402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788402 prefixEnd_788402 := by exact prefixLift 788402
  have htrace : WordTrace (prefixWord ++ tailWord_788402) baseStart_788402 baseEnd_788402 := by
    simpa [prefixWord, tailWord_788402, baseEnd_788402] using wordTrace_append hprefix tailTrace_788402
  have hstable : (prefixWord ++ tailWord_788402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788402).length < 2 ^ (prefixWord ++ tailWord_788402).sum := by decide
  have hdescent : baseEnd_788402 < baseStart_788402 := by decide
  rcases family_descends (prefixWord ++ tailWord_788402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788409 : List Nat := [1, 2, 1, 4, 2, 1, 1, 5, 2, 4]
def baseStart_788409 : Nat := 118140960795 + 788409 * 2 ^ 59
def prefixEnd_788409 : Nat := 4983230072969 + 3 ^ 40 * 788409 * 2
def baseEnd_788409 : Nat := 134944256443570359953893

theorem tailTrace_788409 : CollatzResearch.WordTrace tailWord_788409 prefixEnd_788409 134944256443570359953893 := by
  unfold tailWord_788409
  simp only [CollatzResearch.WordTrace]
  refine ⟨28755638600736317382312281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19170425733824211588208187 28755638600736317382312281)
  ·
    refine ⟨21566728950552238036734211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28755638600736317382312281 21566728950552238036734211)
    ·
      refine ⟨32350093425828357055101317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21566728950552238036734211 32350093425828357055101317)
      ·
        refine ⟨6065642517342816947831497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32350093425828357055101317 6065642517342816947831497)
        ·
          refine ⟨4549231888007112710873623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6065642517342816947831497 4549231888007112710873623)
          ·
            refine ⟨6823847832010669066310435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4549231888007112710873623 6823847832010669066310435)
            ·
              refine ⟨10235771748016003599465653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6823847832010669066310435 10235771748016003599465653)
              ·
                refine ⟨959603601376500337449905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10235771748016003599465653 959603601376500337449905)
                ·
                  refine ⟨719702701032375253087429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 959603601376500337449905 719702701032375253087429)
                  ·
                    refine ⟨134944256443570359953893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 719702701032375253087429 134944256443570359953893)
                    ·
                      rfl

theorem cell23_788409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2, 4].length) (baseStart_788409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788409 prefixEnd_788409 := by exact prefixLift 788409
  have htrace : WordTrace (prefixWord ++ tailWord_788409) baseStart_788409 baseEnd_788409 := by
    simpa [prefixWord, tailWord_788409, baseEnd_788409] using wordTrace_append hprefix tailTrace_788409
  have hstable : (prefixWord ++ tailWord_788409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788409).length < 2 ^ (prefixWord ++ tailWord_788409).sum := by decide
  have hdescent : baseEnd_788409 < baseStart_788409 := by decide
  rcases family_descends (prefixWord ++ tailWord_788409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788416 : List Nat := [2, 1, 1, 2, 3, 2, 3, 2, 3, 2, 2]
def baseStart_788416 : Nat := 118140960795 + 788416 * 2 ^ 59
def prefixEnd_788416 : Nat := 4983230072969 + 3 ^ 40 * 788416 * 2
def baseEnd_788416 : Nat := 404836363695292552474147

theorem tailTrace_788416 : CollatzResearch.WordTrace tailWord_788416 prefixEnd_788416 404836363695292552474147 := by
  unfold tailWord_788416
  simp only [CollatzResearch.WordTrace]
  refine ⟨14377946955855478788908551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19170595941140638385211401 14377946955855478788908551)
  ·
    refine ⟨21566920433783218183362827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14377946955855478788908551 21566920433783218183362827)
    ·
      refine ⟨32350380650674827275044241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21566920433783218183362827 32350380650674827275044241)
      ·
        refine ⟨24262785488006120456283181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32350380650674827275044241 24262785488006120456283181)
        ·
          refine ⟨9098544558002295171106193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24262785488006120456283181 9098544558002295171106193)
          ·
            refine ⟨6823908418501721378329645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9098544558002295171106193 6823908418501721378329645)
            ·
              refine ⟨2558965656938145516873617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6823908418501721378329645 2558965656938145516873617)
              ·
                refine ⟨1919224242703609137655213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2558965656938145516873617 1919224242703609137655213)
                ·
                  refine ⟨719709091013853426620705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1919224242703609137655213 719709091013853426620705)
                  ·
                    refine ⟨539781818260390069965529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 719709091013853426620705 539781818260390069965529)
                    ·
                      refine ⟨404836363695292552474147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 539781818260390069965529 404836363695292552474147)
                      ·
                        rfl

theorem cell23_788416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 3, 2, 2].length) (baseStart_788416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788416 prefixEnd_788416 := by exact prefixLift 788416
  have htrace : WordTrace (prefixWord ++ tailWord_788416) baseStart_788416 baseEnd_788416 := by
    simpa [prefixWord, tailWord_788416, baseEnd_788416] using wordTrace_append hprefix tailTrace_788416
  have hstable : (prefixWord ++ tailWord_788416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788416).length < 2 ^ (prefixWord ++ tailWord_788416).sum := by decide
  have hdescent : baseEnd_788416 < baseStart_788416 := by decide
  rcases family_descends (prefixWord ++ tailWord_788416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788436 : List Nat := [2, 4, 1, 2, 1, 1, 3, 3, 1, 2, 3]
def baseStart_788436 : Nat := 118140960795 + 788436 * 2 ^ 59
def prefixEnd_788436 : Nat := 4983230072969 + 3 ^ 40 * 788436 * 2
def baseEnd_788436 : Nat := 404846633308382474224055

theorem tailTrace_788436 : CollatzResearch.WordTrace tailWord_788436 prefixEnd_788436 404846633308382474224055 := by
  unfold tailWord_788436
  simp only [CollatzResearch.WordTrace]
  refine ⟨14378311685819250496772581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19171082247759000662363441 14378311685819250496772581)
  ·
    refine ⟨2695933441091109468144859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14378311685819250496772581 2695933441091109468144859)
    ·
      refine ⟨4043900161636664202217289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2695933441091109468144859 4043900161636664202217289)
      ·
        refine ⟨3032925121227498151662967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4043900161636664202217289 3032925121227498151662967)
        ·
          refine ⟨4549387681841247227494451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3032925121227498151662967 4549387681841247227494451)
          ·
            refine ⟨6824081522761870841241677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4549387681841247227494451 6824081522761870841241677)
            ·
              refine ⟨2559030571035701565465629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6824081522761870841241677 2559030571035701565465629)
              ·
                refine ⟨959636464138388087049611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2559030571035701565465629 959636464138388087049611)
                ·
                  refine ⟨1439454696207582130574417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 959636464138388087049611 1439454696207582130574417)
                  ·
                    refine ⟨1079591022155686597930813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1439454696207582130574417 1079591022155686597930813)
                    ·
                      refine ⟨404846633308382474224055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1079591022155686597930813 404846633308382474224055)
                      ·
                        rfl

theorem cell23_788436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_788436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788436 prefixEnd_788436 := by exact prefixLift 788436
  have htrace : WordTrace (prefixWord ++ tailWord_788436) baseStart_788436 baseEnd_788436 := by
    simpa [prefixWord, tailWord_788436, baseEnd_788436] using wordTrace_append hprefix tailTrace_788436
  have hstable : (prefixWord ++ tailWord_788436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788436).length < 2 ^ (prefixWord ++ tailWord_788436).sum := by decide
  have hdescent : baseEnd_788436 < baseStart_788436 := by decide
  rcases family_descends (prefixWord ++ tailWord_788436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788459 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 5, 3, 2]
def baseStart_788459 : Nat := 118140960795 + 788459 * 2 ^ 59
def prefixEnd_788459 : Nat := 4983230072969 + 3 ^ 40 * 788459 * 2
def baseEnd_788459 : Nat := 404858443363435884236449

theorem tailTrace_788459 : CollatzResearch.WordTrace tailWord_788459 prefixEnd_788459 404858443363435884236449 := by
  unfold tailWord_788459
  simp only [CollatzResearch.WordTrace]
  refine ⟨28757462250555175921632431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19171641500370117281088287 28757462250555175921632431)
  ·
    refine ⟨43136193375832763882448647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28757462250555175921632431 43136193375832763882448647)
    ·
      refine ⟨64704290063749145823672971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43136193375832763882448647 64704290063749145823672971)
      ·
        refine ⟨97056435095623718735509457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64704290063749145823672971 97056435095623718735509457)
        ·
          refine ⟨72792326321717789051632093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97056435095623718735509457 72792326321717789051632093)
          ·
            refine ⟨27297122370644170894362035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72792326321717789051632093 27297122370644170894362035)
            ·
              refine ⟨40945683555966256341543053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27297122370644170894362035 40945683555966256341543053)
              ·
                refine ⟨15354631333487346128078645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40945683555966256341543053 15354631333487346128078645)
                ·
                  refine ⟨1439496687514438699507373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15354631333487346128078645 1439496687514438699507373)
                  ·
                    refine ⟨539811257817914512315265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1439496687514438699507373 539811257817914512315265)
                    ·
                      refine ⟨404858443363435884236449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 539811257817914512315265 404858443363435884236449)
                      ·
                        rfl

theorem cell23_788459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 3, 2].length) (baseStart_788459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788459 prefixEnd_788459 := by exact prefixLift 788459
  have htrace : WordTrace (prefixWord ++ tailWord_788459) baseStart_788459 baseEnd_788459 := by
    simpa [prefixWord, tailWord_788459, baseEnd_788459] using wordTrace_append hprefix tailTrace_788459
  have hstable : (prefixWord ++ tailWord_788459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788459).length < 2 ^ (prefixWord ++ tailWord_788459).sum := by decide
  have hdescent : baseEnd_788459 < baseStart_788459 := by decide
  rcases family_descends (prefixWord ++ tailWord_788459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788472 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 2, 3, 4]
def baseStart_788472 : Nat := 118140960795 + 788472 * 2 ^ 59
def prefixEnd_788472 : Nat := 4983230072969 + 3 ^ 40 * 788472 * 2
def baseEnd_788472 : Nat := 404865118611944333373889

theorem tailTrace_788472 : CollatzResearch.WordTrace tailWord_788472 prefixEnd_788472 404865118611944333373889 := by
  unfold tailWord_788472
  simp only [CollatzResearch.WordTrace]
  refine ⟨14378968199754039570927835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19171957599672052761237113 14378968199754039570927835)
  ·
    refine ⟨21568452299631059356391753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14378968199754039570927835 21568452299631059356391753)
    ·
      refine ⟨16176339224723294517293815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21568452299631059356391753 16176339224723294517293815)
      ·
        refine ⟨24264508837084941775940723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16176339224723294517293815 24264508837084941775940723)
        ·
          refine ⟨36396763255627412663911085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24264508837084941775940723 36396763255627412663911085)
          ·
            refine ⟨13648786220860279748966657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36396763255627412663911085 13648786220860279748966657)
            ·
              refine ⟨10236589665645209811724993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13648786220860279748966657 10236589665645209811724993)
              ·
                refine ⟨7677442249233907358793745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10236589665645209811724993 7677442249233907358793745)
                ·
                  refine ⟨5758081686925430519095309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7677442249233907358793745 5758081686925430519095309)
                  ·
                    refine ⟨2159280632597036444660741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5758081686925430519095309 2159280632597036444660741)
                    ·
                      refine ⟨404865118611944333373889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2159280632597036444660741 404865118611944333373889)
                      ·
                        rfl

theorem cell23_788472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_788472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788472 prefixEnd_788472 := by exact prefixLift 788472
  have htrace : WordTrace (prefixWord ++ tailWord_788472) baseStart_788472 baseEnd_788472 := by
    simpa [prefixWord, tailWord_788472, baseEnd_788472] using wordTrace_append hprefix tailTrace_788472
  have hstable : (prefixWord ++ tailWord_788472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788472).length < 2 ^ (prefixWord ++ tailWord_788472).sum := by decide
  have hdescent : baseEnd_788472 < baseStart_788472 := by decide
  rcases family_descends (prefixWord ++ tailWord_788472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788484 : List Nat := [2, 3, 2, 4, 1, 2, 1, 3, 1, 2, 2]
def baseStart_788484 : Nat := 118140960795 + 788484 * 2 ^ 59
def prefixEnd_788484 : Nat := 4983230072969 + 3 ^ 40 * 788484 * 2
def baseEnd_788484 : Nat := 404871280379798286423835

theorem tailTrace_788484 : CollatzResearch.WordTrace tailWord_788484 prefixEnd_788484 404871280379798286423835 := by
  unfold tailWord_788484
  simp only [CollatzResearch.WordTrace]
  refine ⟨14379187037732302595646253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19172249383643070127528337 14379187037732302595646253)
  ·
    refine ⟨5392195139149613473367345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14379187037732302595646253 5392195139149613473367345)
    ·
      refine ⟨4044146354362210105025509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5392195139149613473367345 4044146354362210105025509)
      ·
        refine ⟨758277441442914394692283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4044146354362210105025509 758277441442914394692283)
        ·
          refine ⟨1137416162164371592038425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758277441442914394692283 1137416162164371592038425)
          ·
            refine ⟨853062121623278694028819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1137416162164371592038425 853062121623278694028819)
            ·
              refine ⟨1279593182434918041043229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 853062121623278694028819 1279593182434918041043229)
              ·
                refine ⟨479847443413094265391211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1279593182434918041043229 479847443413094265391211)
                ·
                  refine ⟨719771165119641398086817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 479847443413094265391211 719771165119641398086817)
                  ·
                    refine ⟨539828373839731048565113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 719771165119641398086817 539828373839731048565113)
                    ·
                      refine ⟨404871280379798286423835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 539828373839731048565113 404871280379798286423835)
                      ·
                        rfl

theorem cell23_788484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_788484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788484 prefixEnd_788484 := by exact prefixLift 788484
  have htrace : WordTrace (prefixWord ++ tailWord_788484) baseStart_788484 baseEnd_788484 := by
    simpa [prefixWord, tailWord_788484, baseEnd_788484] using wordTrace_append hprefix tailTrace_788484
  have hstable : (prefixWord ++ tailWord_788484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788484).length < 2 ^ (prefixWord ++ tailWord_788484).sum := by decide
  have hdescent : baseEnd_788484 < baseStart_788484 := by decide
  rcases family_descends (prefixWord ++ tailWord_788484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788573 : List Nat := [1, 4, 4, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_788573 : Nat := 118140960795 + 788573 * 2 ^ 59
def prefixEnd_788573 : Nat := 4983230072969 + 3 ^ 40 * 788573 * 2
def baseEnd_788573 : Nat := 404916980158048438210925

theorem tailTrace_788573 : CollatzResearch.WordTrace tailWord_788573 prefixEnd_788573 404916980158048438210925 := by
  unfold tailWord_788573
  simp only [CollatzResearch.WordTrace]
  refine ⟨28761620172142173391282373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19174413448094782260854915 28761620172142173391282373)
  ·
    refine ⟨5392803782276657510865445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28761620172142173391282373 5392803782276657510865445)
    ·
      refine ⟨1011150709176873283287271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5392803782276657510865445 1011150709176873283287271)
      ·
        refine ⟨1516726063765309924930907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1011150709176873283287271 1516726063765309924930907)
        ·
          refine ⟨2275089095647964887396361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1516726063765309924930907 2275089095647964887396361)
          ·
            refine ⟨1706316821735973665547271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2275089095647964887396361 1706316821735973665547271)
            ·
              refine ⟨2559475232603960498320907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1706316821735973665547271 2559475232603960498320907)
              ·
                refine ⟨3839212848905940747481361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2559475232603960498320907 3839212848905940747481361)
                ·
                  refine ⟨2879409636679455560611021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3839212848905940747481361 2879409636679455560611021)
                  ·
                    refine ⟨1079778613754795835229133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2879409636679455560611021 1079778613754795835229133)
                    ·
                      refine ⟨404916980158048438210925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1079778613754795835229133 404916980158048438210925)
                      ·
                        rfl

theorem cell23_788573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_788573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788573 prefixEnd_788573 := by exact prefixLift 788573
  have htrace : WordTrace (prefixWord ++ tailWord_788573) baseStart_788573 baseEnd_788573 := by
    simpa [prefixWord, tailWord_788573, baseEnd_788573] using wordTrace_append hprefix tailTrace_788573
  have hstable : (prefixWord ++ tailWord_788573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788573).length < 2 ^ (prefixWord ++ tailWord_788573).sum := by decide
  have hdescent : baseEnd_788573 < baseStart_788573 := by decide
  rcases family_descends (prefixWord ++ tailWord_788573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788579 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 4]
def baseStart_788579 : Nat := 118140960795 + 788579 * 2 ^ 59
def prefixEnd_788579 : Nat := 4983230072969 + 3 ^ 40 * 788579 * 2
def baseEnd_788579 : Nat := 404920061041975414735897

theorem tailTrace_788579 : CollatzResearch.WordTrace tailWord_788579 prefixEnd_788579 404920061041975414735897 := by
  unfold tailWord_788579
  simp only [CollatzResearch.WordTrace]
  refine ⟨28761839010120436416000791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19174559340080290944000527 28761839010120436416000791)
  ·
    refine ⟨43142758515180654624001187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28761839010120436416000791 43142758515180654624001187)
    ·
      refine ⟨64714137772770981936001781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43142758515180654624001187 64714137772770981936001781)
      ·
        refine ⟨6066950416197279556500167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64714137772770981936001781 6066950416197279556500167)
        ·
          refine ⟨9100425624295919334750251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6066950416197279556500167 9100425624295919334750251)
          ·
            refine ⟨13650638436443879002125377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9100425624295919334750251 13650638436443879002125377)
            ·
              refine ⟨10237978827332909251594033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13650638436443879002125377 10237978827332909251594033)
              ·
                refine ⟨7678484120499681938695525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10237978827332909251594033 7678484120499681938695525)
                ·
                  refine ⟨1439715772593690363505411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7678484120499681938695525 1439715772593690363505411)
                  ·
                    refine ⟨2159573658890535545258117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1439715772593690363505411 2159573658890535545258117)
                    ·
                      refine ⟨404920061041975414735897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2159573658890535545258117 404920061041975414735897)
                      ·
                        rfl

theorem cell23_788579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_788579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788579 prefixEnd_788579 := by exact prefixLift 788579
  have htrace : WordTrace (prefixWord ++ tailWord_788579) baseStart_788579 baseEnd_788579 := by
    simpa [prefixWord, tailWord_788579, baseEnd_788579] using wordTrace_append hprefix tailTrace_788579
  have hstable : (prefixWord ++ tailWord_788579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788579).length < 2 ^ (prefixWord ++ tailWord_788579).sum := by decide
  have hdescent : baseEnd_788579 < baseStart_788579 := by decide
  rcases family_descends (prefixWord ++ tailWord_788579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788657 : List Nat := [1, 2, 2, 5, 2, 2, 1, 3, 1, 4]
def baseStart_788657 : Nat := 118140960795 + 788657 * 2 ^ 59
def prefixEnd_788657 : Nat := 4983230072969 + 3 ^ 40 * 788657 * 2
def baseEnd_788657 : Nat := 134986704177675369853513

theorem tailTrace_788657 : CollatzResearch.WordTrace tailWord_788657 prefixEnd_788657 134986704177675369853513 := by
  unfold tailWord_788657
  simp only [CollatzResearch.WordTrace]
  refine ⟨28764683903837855737340225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19176455935891903824893483 28764683903837855737340225)
  ·
    refine ⟨21573512927878391803005169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28764683903837855737340225 21573512927878391803005169)
    ·
      refine ⟨16180134695908793852253877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21573512927878391803005169 16180134695908793852253877)
      ·
        refine ⟨1516887627741449423648801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16180134695908793852253877 1516887627741449423648801)
        ·
          refine ⟨1137665720806087067736601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1516887627741449423648801 1137665720806087067736601)
          ·
            refine ⟨853249290604565300802451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1137665720806087067736601 853249290604565300802451)
            ·
              refine ⟨1279873935906847951203677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 853249290604565300802451 1279873935906847951203677)
              ·
                refine ⟨479952725965067981701379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1279873935906847951203677 479952725965067981701379)
                ·
                  refine ⟨719929088947601972552069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 479952725965067981701379 719929088947601972552069)
                  ·
                    refine ⟨134986704177675369853513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 719929088947601972552069 134986704177675369853513)
                    ·
                      rfl

theorem cell23_788657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3, 1, 4].length) (baseStart_788657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788657 prefixEnd_788657 := by exact prefixLift 788657
  have htrace : WordTrace (prefixWord ++ tailWord_788657) baseStart_788657 baseEnd_788657 := by
    simpa [prefixWord, tailWord_788657, baseEnd_788657] using wordTrace_append hprefix tailTrace_788657
  have hstable : (prefixWord ++ tailWord_788657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788657).length < 2 ^ (prefixWord ++ tailWord_788657).sum := by decide
  have hdescent : baseEnd_788657 < baseStart_788657 := by decide
  rcases family_descends (prefixWord ++ tailWord_788657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788666 : List Nat := [3, 1, 1, 1, 2, 2, 4, 3, 1, 5]
def baseStart_788666 : Nat := 118140960795 + 788666 * 2 ^ 59
def prefixEnd_788666 : Nat := 4983230072969 + 3 ^ 40 * 788666 * 2
def baseEnd_788666 : Nat := 134988244619638858115999

theorem tailTrace_788666 : CollatzResearch.WordTrace tailWord_788666 prefixEnd_788666 134988244619638858115999 := by
  unfold tailWord_788666
  simp only [CollatzResearch.WordTrace]
  refine ⟨7191253040201312568604463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19176674773870166849611901 7191253040201312568604463)
  ·
    refine ⟨10786879560301968852906695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7191253040201312568604463 10786879560301968852906695)
    ·
      refine ⟨16180319340452953279360043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10786879560301968852906695 16180319340452953279360043)
      ·
        refine ⟨24270479010679429919040065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16180319340452953279360043 24270479010679429919040065)
        ·
          refine ⟨18202859258009572439280049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24270479010679429919040065 18202859258009572439280049)
          ·
            refine ⟨13652144443507179329460037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18202859258009572439280049 13652144443507179329460037)
            ·
              refine ⟨2559777083157596124273757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13652144443507179329460037 2559777083157596124273757)
              ·
                refine ⟨959916406184098546602659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2559777083157596124273757 959916406184098546602659)
                ·
                  refine ⟨1439874609276147819903989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 959916406184098546602659 1439874609276147819903989)
                  ·
                    refine ⟨134988244619638858115999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1439874609276147819903989 134988244619638858115999)
                    ·
                      rfl

theorem cell23_788666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 1, 5].length) (baseStart_788666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788666 prefixEnd_788666 := by exact prefixLift 788666
  have htrace : WordTrace (prefixWord ++ tailWord_788666) baseStart_788666 baseEnd_788666 := by
    simpa [prefixWord, tailWord_788666, baseEnd_788666] using wordTrace_append hprefix tailTrace_788666
  have hstable : (prefixWord ++ tailWord_788666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788666).length < 2 ^ (prefixWord ++ tailWord_788666).sum := by decide
  have hdescent : baseEnd_788666 < baseStart_788666 := by decide
  rcases family_descends (prefixWord ++ tailWord_788666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788700 : List Nat := [2, 2, 5, 2, 1, 1, 1, 1, 3, 5]
def baseStart_788700 : Nat := 118140960795 + 788700 * 2 ^ 59
def prefixEnd_788700 : Nat := 4983230072969 + 3 ^ 40 * 788700 * 2
def baseEnd_788700 : Nat := 134994064067056480440947

theorem tailTrace_788700 : CollatzResearch.WordTrace tailWord_788700 prefixEnd_788700 134994064067056480440947 := by
  unfold tailWord_788700
  simp only [CollatzResearch.WordTrace]
  refine ⟨14383126121341037040577777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19177501495121382720770369 14383126121341037040577777)
  ·
    refine ⟨10787344591005777780433333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14383126121341037040577777 10787344591005777780433333)
    ·
      refine ⟨1011313555406791666915625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10787344591005777780433333 1011313555406791666915625)
      ·
        refine ⟨758485166555093750186719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1011313555406791666915625 758485166555093750186719)
        ·
          refine ⟨1137727749832640625280079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758485166555093750186719 1137727749832640625280079)
          ·
            refine ⟨1706591624748960937920119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137727749832640625280079 1706591624748960937920119)
            ·
              refine ⟨2559887437123441406880179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1706591624748960937920119 2559887437123441406880179)
              ·
                refine ⟨3839831155685162110320269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2559887437123441406880179 3839831155685162110320269)
                ·
                  refine ⟨1439936683381935791370101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3839831155685162110320269 1439936683381935791370101)
                  ·
                    refine ⟨134994064067056480440947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1439936683381935791370101 134994064067056480440947)
                    ·
                      rfl

theorem cell23_788700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_788700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788700 prefixEnd_788700 := by exact prefixLift 788700
  have htrace : WordTrace (prefixWord ++ tailWord_788700) baseStart_788700 baseEnd_788700 := by
    simpa [prefixWord, tailWord_788700, baseEnd_788700] using wordTrace_append hprefix tailTrace_788700
  have hstable : (prefixWord ++ tailWord_788700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788700).length < 2 ^ (prefixWord ++ tailWord_788700).sum := by decide
  have hdescent : baseEnd_788700 < baseStart_788700 := by decide
  rcases family_descends (prefixWord ++ tailWord_788700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788703 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 5, 2, 2]
def baseStart_788703 : Nat := 118140960795 + 788703 * 2 ^ 59
def prefixEnd_788703 : Nat := 4983230072969 + 3 ^ 40 * 788703 * 2
def baseEnd_788703 : Nat := 404983732643132929585327

theorem tailTrace_788703 : CollatzResearch.WordTrace tailWord_788703 prefixEnd_788703 404983732643132929585327 := by
  unfold tailWord_788703
  simp only [CollatzResearch.WordTrace]
  refine ⟨28766361661671205593514763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19177574441114137062343175 28766361661671205593514763)
  ·
    refine ⟨43149542492506808390272145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28766361661671205593514763 43149542492506808390272145)
    ·
      refine ⟨32362156869380106292704109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43149542492506808390272145 32362156869380106292704109)
      ·
        refine ⟨12135808826017539859764041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32362156869380106292704109 12135808826017539859764041)
        ·
          refine ⟨9101856619513154894823031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12135808826017539859764041 9101856619513154894823031)
          ·
            refine ⟨13652784929269732342234547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9101856619513154894823031 13652784929269732342234547)
            ·
              refine ⟨20479177393904598513351821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13652784929269732342234547 20479177393904598513351821)
              ·
                refine ⟨7679691522714224442506933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20479177393904598513351821 7679691522714224442506933)
                ·
                  refine ⟨719971080254458541485025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7679691522714224442506933 719971080254458541485025)
                  ·
                    refine ⟨539978310190843906113769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 719971080254458541485025 539978310190843906113769)
                    ·
                      refine ⟨404983732643132929585327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 539978310190843906113769 404983732643132929585327)
                      ·
                        rfl

theorem cell23_788703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5, 2, 2].length) (baseStart_788703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788703 prefixEnd_788703 := by exact prefixLift 788703
  have htrace : WordTrace (prefixWord ++ tailWord_788703) baseStart_788703 baseEnd_788703 := by
    simpa [prefixWord, tailWord_788703, baseEnd_788703] using wordTrace_append hprefix tailTrace_788703
  have hstable : (prefixWord ++ tailWord_788703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788703).length < 2 ^ (prefixWord ++ tailWord_788703).sum := by decide
  have hdescent : baseEnd_788703 < baseStart_788703 := by decide
  rcases family_descends (prefixWord ++ tailWord_788703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788707 : List Nat := [1, 1, 1, 8, 1, 1, 2, 1, 2, 3, 2]
def baseStart_788707 : Nat := 118140960795 + 788707 * 2 ^ 59
def prefixEnd_788707 : Nat := 4983230072969 + 3 ^ 40 * 788707 * 2
def baseEnd_788707 : Nat := 404985786565750913935309

theorem tailTrace_788707 : CollatzResearch.WordTrace tailWord_788707 prefixEnd_788707 404985786565750913935309 := by
  unfold tailWord_788707
  simp only [CollatzResearch.WordTrace]
  refine ⟨28766507553656714276660375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19177671702437809517773583 28766507553656714276660375)
  ·
    refine ⟨43149761330485071414990563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28766507553656714276660375 43149761330485071414990563)
    ·
      refine ⟨64724641995727607122485845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43149761330485071414990563 64724641995727607122485845)
      ·
        refine ⟨758491898387432895966631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 64724641995727607122485845 758491898387432895966631)
        ·
          refine ⟨1137737847581149343949947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758491898387432895966631 1137737847581149343949947)
          ·
            refine ⟨1706606771371724015924921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137737847581149343949947 1706606771371724015924921)
            ·
              refine ⟨1279955078528793011943691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1706606771371724015924921 1279955078528793011943691)
              ·
                refine ⟨1919932617793189517915537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1279955078528793011943691 1919932617793189517915537)
                ·
                  refine ⟨1439949463344892138436653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1919932617793189517915537 1439949463344892138436653)
                  ·
                    refine ⟨539981048754334551913745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1439949463344892138436653 539981048754334551913745)
                    ·
                      refine ⟨404985786565750913935309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 539981048754334551913745 404985786565750913935309)
                      ·
                        rfl

theorem cell23_788707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_788707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788707 prefixEnd_788707 := by exact prefixLift 788707
  have htrace : WordTrace (prefixWord ++ tailWord_788707) baseStart_788707 baseEnd_788707 := by
    simpa [prefixWord, tailWord_788707, baseEnd_788707] using wordTrace_append hprefix tailTrace_788707
  have hstable : (prefixWord ++ tailWord_788707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788707).length < 2 ^ (prefixWord ++ tailWord_788707).sum := by decide
  have hdescent : baseEnd_788707 < baseStart_788707 := by decide
  rcases family_descends (prefixWord ++ tailWord_788707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788716 : List Nat := [2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 4]
def baseStart_788716 : Nat := 118140960795 + 788716 * 2 ^ 59
def prefixEnd_788716 : Nat := 4983230072969 + 3 ^ 40 * 788716 * 2
def baseEnd_788716 : Nat := 404990407891641378722767

theorem tailTrace_788716 : CollatzResearch.WordTrace tailWord_788716 prefixEnd_788716 404990407891641378722767 := by
  unfold tailWord_788716
  simp only [CollatzResearch.WordTrace]
  refine ⟨14383417905312054406869001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19177890540416072542492001 14383417905312054406869001)
  ·
    refine ⟨10787563428984040805151751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14383417905312054406869001 10787563428984040805151751)
    ·
      refine ⟨16181345143476061207727627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10787563428984040805151751 16181345143476061207727627)
      ·
        refine ⟨24272017715214091811591441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16181345143476061207727627 24272017715214091811591441)
        ·
          refine ⟨18204013286410568858693581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24272017715214091811591441 18204013286410568858693581)
          ·
            refine ⟨6826504982403963322010093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18204013286410568858693581 6826504982403963322010093)
            ·
              refine ⟨2559939368401486245753785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6826504982403963322010093 2559939368401486245753785)
              ·
                refine ⟨1919954526301114684315339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2559939368401486245753785 1919954526301114684315339)
                ·
                  refine ⟨2879931789451672026473009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1919954526301114684315339 2879931789451672026473009)
                  ·
                    refine ⟨2159948842088754019854757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2879931789451672026473009 2159948842088754019854757)
                    ·
                      refine ⟨404990407891641378722767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2159948842088754019854757 404990407891641378722767)
                      ·
                        rfl

theorem cell23_788716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_788716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788716 prefixEnd_788716 := by exact prefixLift 788716
  have htrace : WordTrace (prefixWord ++ tailWord_788716) baseStart_788716 baseEnd_788716 := by
    simpa [prefixWord, tailWord_788716, baseEnd_788716] using wordTrace_append hprefix tailTrace_788716
  have hstable : (prefixWord ++ tailWord_788716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788716).length < 2 ^ (prefixWord ++ tailWord_788716).sum := by decide
  have hdescent : baseEnd_788716 < baseStart_788716 := by decide
  rcases family_descends (prefixWord ++ tailWord_788716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788729 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 2, 2, 6]
def baseStart_788729 : Nat := 118140960795 + 788729 * 2 ^ 59
def prefixEnd_788729 : Nat := 4983230072969 + 3 ^ 40 * 788729 * 2
def baseEnd_788729 : Nat := 404997083140149827860207

theorem tailTrace_788729 : CollatzResearch.WordTrace tailWord_788729 prefixEnd_788729 404997083140149827860207 := by
  unfold tailWord_788729
  simp only [CollatzResearch.WordTrace]
  refine ⟨28767309959577012033961241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19178206639718008022640827 28767309959577012033961241)
  ·
    refine ⟨21575482469682759025470931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28767309959577012033961241 21575482469682759025470931)
    ·
      refine ⟨32363223704524138538206397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21575482469682759025470931 32363223704524138538206397)
      ·
        refine ⟨12136208889196551951827399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32363223704524138538206397 12136208889196551951827399)
        ·
          refine ⟨18204313333794827927741099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12136208889196551951827399 18204313333794827927741099)
          ·
            refine ⟨27306470000692241891611649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18204313333794827927741099 27306470000692241891611649)
            ·
              refine ⟨20479852500519181418708737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27306470000692241891611649 20479852500519181418708737)
              ·
                refine ⟨15359889375389386064031553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20479852500519181418708737 15359889375389386064031553)
                ·
                  refine ⟨11519917031542039548023665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15359889375389386064031553 11519917031542039548023665)
                  ·
                    refine ⟨8639937773656529661017749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11519917031542039548023665 8639937773656529661017749)
                    ·
                      refine ⟨404997083140149827860207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8639937773656529661017749 404997083140149827860207)
                      ·
                        rfl

theorem cell23_788729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_788729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788729 prefixEnd_788729 := by exact prefixLift 788729
  have htrace : WordTrace (prefixWord ++ tailWord_788729) baseStart_788729 baseEnd_788729 := by
    simpa [prefixWord, tailWord_788729, baseEnd_788729] using wordTrace_append hprefix tailTrace_788729
  have hstable : (prefixWord ++ tailWord_788729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788729).length < 2 ^ (prefixWord ++ tailWord_788729).sum := by decide
  have hdescent : baseEnd_788729 < baseStart_788729 := by decide
  rcases family_descends (prefixWord ++ tailWord_788729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788737 : List Nat := [1, 2, 4, 1, 1, 2, 3, 4, 1, 2, 2]
def baseStart_788737 : Nat := 118140960795 + 788737 * 2 ^ 59
def prefixEnd_788737 : Nat := 4983230072969 + 3 ^ 40 * 788737 * 2
def baseEnd_788737 : Nat := 405001190985385796560171

theorem tailTrace_788737 : CollatzResearch.WordTrace tailWord_788737 prefixEnd_788737 405001190985385796560171 := by
  unfold tailWord_788737
  simp only [CollatzResearch.WordTrace]
  refine ⟨28767601743548029400252465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19178401162365352933501643 28767601743548029400252465)
  ·
    refine ⟨21575701307661022050189349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28767601743548029400252465 21575701307661022050189349)
    ·
      refine ⟨4045443995186441634410503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21575701307661022050189349 4045443995186441634410503)
      ·
        refine ⟨6068165992779662451615755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4045443995186441634410503 6068165992779662451615755)
        ·
          refine ⟨9102248989169493677423633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6068165992779662451615755 9102248989169493677423633)
          ·
            refine ⟨6826686741877120258067725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9102248989169493677423633 6826686741877120258067725)
            ·
              refine ⟨2560007528203920096775397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6826686741877120258067725 2560007528203920096775397)
              ·
                refine ⟨480001411538235018145387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2560007528203920096775397 480001411538235018145387)
                ·
                  refine ⟨720002117307352527218081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 480001411538235018145387 720002117307352527218081)
                  ·
                    refine ⟨540001587980514395413561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 720002117307352527218081 540001587980514395413561)
                    ·
                      refine ⟨405001190985385796560171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 540001587980514395413561 405001190985385796560171)
                      ·
                        rfl

theorem cell23_788737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_788737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788737 prefixEnd_788737 := by exact prefixLift 788737
  have htrace : WordTrace (prefixWord ++ tailWord_788737) baseStart_788737 baseEnd_788737 := by
    simpa [prefixWord, tailWord_788737, baseEnd_788737] using wordTrace_append hprefix tailTrace_788737
  have hstable : (prefixWord ++ tailWord_788737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788737).length < 2 ^ (prefixWord ++ tailWord_788737).sum := by decide
  have hdescent : baseEnd_788737 < baseStart_788737 := by decide
  rcases family_descends (prefixWord ++ tailWord_788737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788739 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 1, 9]
def baseStart_788739 : Nat := 118140960795 + 788739 * 2 ^ 59
def prefixEnd_788739 : Nat := 4983230072969 + 3 ^ 40 * 788739 * 2
def baseEnd_788739 : Nat := 135000739315564929578387

theorem tailTrace_788739 : CollatzResearch.WordTrace tailWord_788739 prefixEnd_788739 135000739315564929578387 := by
  unfold tailWord_788739
  simp only [CollatzResearch.WordTrace]
  refine ⟨28767674689540783741825271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19178449793027189161216847 28767674689540783741825271)
  ·
    refine ⟨43151512034311175612737907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28767674689540783741825271 43151512034311175612737907)
    ·
      refine ⟨64727268051466763419106861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43151512034311175612737907 64727268051466763419106861)
      ·
        refine ⟨24272725519300036282165073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64727268051466763419106861 24272725519300036282165073)
        ·
          refine ⟨18204544139475027211623805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24272725519300036282165073 18204544139475027211623805)
          ·
            refine ⟨6826704052303135204358927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18204544139475027211623805 6826704052303135204358927)
            ·
              refine ⟨10240056078454702806538391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6826704052303135204358927 10240056078454702806538391)
              ·
                refine ⟨15360084117682054209807587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10240056078454702806538391 15360084117682054209807587)
                ·
                  refine ⟨23040126176523081314711381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15360084117682054209807587 23040126176523081314711381)
                  ·
                    refine ⟨135000739315564929578387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 23040126176523081314711381 135000739315564929578387)
                    ·
                      rfl

theorem cell23_788739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 9].length) (baseStart_788739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788739 prefixEnd_788739 := by exact prefixLift 788739
  have htrace : WordTrace (prefixWord ++ tailWord_788739) baseStart_788739 baseEnd_788739 := by
    simpa [prefixWord, tailWord_788739, baseEnd_788739] using wordTrace_append hprefix tailTrace_788739
  have hstable : (prefixWord ++ tailWord_788739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788739).length < 2 ^ (prefixWord ++ tailWord_788739).sum := by decide
  have hdescent : baseEnd_788739 < baseStart_788739 := by decide
  rcases family_descends (prefixWord ++ tailWord_788739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788753 : List Nat := [1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 3]
def baseStart_788753 : Nat := 118140960795 + 788753 * 2 ^ 59
def prefixEnd_788753 : Nat := 4983230072969 + 3 ^ 40 * 788753 * 2
def baseEnd_788753 : Nat := 405009406675857733960097

theorem tailTrace_788753 : CollatzResearch.WordTrace tailWord_788753 prefixEnd_788753 405009406675857733960097 := by
  unfold tailWord_788753
  simp only [CollatzResearch.WordTrace]
  refine ⟨28768185311490064132834913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19178790207660042755223275 28768185311490064132834913)
  ·
    refine ⟨21576138983617548099626185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28768185311490064132834913 21576138983617548099626185)
    ·
      refine ⟨16182104237713161074719639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21576138983617548099626185 16182104237713161074719639)
      ·
        refine ⟨24273156356569741612079459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16182104237713161074719639 24273156356569741612079459)
        ·
          refine ⟨36409734534854612418119189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24273156356569741612079459 36409734534854612418119189)
          ·
            refine ⟨1706706306321309957099337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 36409734534854612418119189 1706706306321309957099337)
            ·
              refine ⟨1280029729740982467824503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1706706306321309957099337 1280029729740982467824503)
              ·
                refine ⟨1920044594611473701736755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1280029729740982467824503 1920044594611473701736755)
                ·
                  refine ⟨2880066891917210552605133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920044594611473701736755 2880066891917210552605133)
                  ·
                    refine ⟨1080025084468953957226925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2880066891917210552605133 1080025084468953957226925)
                    ·
                      refine ⟨405009406675857733960097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1080025084468953957226925 405009406675857733960097)
                      ·
                        rfl

theorem cell23_788753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 3].length) (baseStart_788753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788753 prefixEnd_788753 := by exact prefixLift 788753
  have htrace : WordTrace (prefixWord ++ tailWord_788753) baseStart_788753 baseEnd_788753 := by
    simpa [prefixWord, tailWord_788753, baseEnd_788753] using wordTrace_append hprefix tailTrace_788753
  have hstable : (prefixWord ++ tailWord_788753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788753).length < 2 ^ (prefixWord ++ tailWord_788753).sum := by decide
  have hdescent : baseEnd_788753 < baseStart_788753 := by decide
  rcases family_descends (prefixWord ++ tailWord_788753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788763 : List Nat := [1, 1, 1, 1, 1, 1, 8, 1, 3, 3, 2]
def baseStart_788763 : Nat := 118140960795 + 788763 * 2 ^ 59
def prefixEnd_788763 : Nat := 4983230072969 + 3 ^ 40 * 788763 * 2
def baseEnd_788763 : Nat := 405014541482402694835051

theorem tailTrace_788763 : CollatzResearch.WordTrace tailWord_788763 prefixEnd_788763 405014541482402694835051 := by
  unfold tailWord_788763
  simp only [CollatzResearch.WordTrace]
  refine ⟨28768550041453835840698943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19179033360969223893799295 28768550041453835840698943)
  ·
    refine ⟨43152825062180753761048415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28768550041453835840698943 43152825062180753761048415)
    ·
      refine ⟨64729237593271130641572623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43152825062180753761048415 64729237593271130641572623)
      ·
        refine ⟨97093856389906695962358935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64729237593271130641572623 97093856389906695962358935)
        ·
          refine ⟨145640784584860043943538403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97093856389906695962358935 145640784584860043943538403)
          ·
            refine ⟨218461176877290065915307605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145640784584860043943538403 218461176877290065915307605)
            ·
              refine ⟨2560091916530742959945011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 218461176877290065915307605 2560091916530742959945011)
              ·
                refine ⟨3840137874796114439917517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2560091916530742959945011 3840137874796114439917517)
                ·
                  refine ⟨1440051703048542914969069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3840137874796114439917517 1440051703048542914969069)
                  ·
                    refine ⟨540019388643203593113401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1440051703048542914969069 540019388643203593113401)
                    ·
                      refine ⟨405014541482402694835051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 540019388643203593113401 405014541482402694835051)
                      ·
                        rfl

theorem cell23_788763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 3, 2].length) (baseStart_788763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788763 prefixEnd_788763 := by exact prefixLift 788763
  have htrace : WordTrace (prefixWord ++ tailWord_788763) baseStart_788763 baseEnd_788763 := by
    simpa [prefixWord, tailWord_788763, baseEnd_788763] using wordTrace_append hprefix tailTrace_788763
  have hstable : (prefixWord ++ tailWord_788763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788763).length < 2 ^ (prefixWord ++ tailWord_788763).sum := by decide
  have hdescent : baseEnd_788763 < baseStart_788763 := by decide
  rcases family_descends (prefixWord ++ tailWord_788763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788804 : List Nat := [2, 3, 4, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_788804 : Nat := 118140960795 + 788804 * 2 ^ 59
def prefixEnd_788804 : Nat := 4983230072969 + 3 ^ 40 * 788804 * 2
def baseEnd_788804 : Nat := 405035594189237034422363

theorem tailTrace_788804 : CollatzResearch.WordTrace tailWord_788804 prefixEnd_788804 405035594189237034422363 := by
  unfold tailWord_788804
  simp only [CollatzResearch.WordTrace]
  refine ⟨14385022717152649921470733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19180030289536866561960977 14385022717152649921470733)
  ·
    refine ⟨5394383518932243720551525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14385022717152649921470733 5394383518932243720551525)
    ·
      refine ⟨1011446909799795697603411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5394383518932243720551525 1011446909799795697603411)
      ·
        refine ⟨1517170364699693546405117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1011446909799795697603411 1517170364699693546405117)
        ·
          refine ⟨568938886762385079901919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1517170364699693546405117 568938886762385079901919)
          ·
            refine ⟨853408330143577619852879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568938886762385079901919 853408330143577619852879)
            ·
              refine ⟨1280112495215366429779319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 853408330143577619852879 1280112495215366429779319)
              ·
                refine ⟨1920168742823049644668979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1280112495215366429779319 1920168742823049644668979)
                ·
                  refine ⟨2880253114234574467003469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920168742823049644668979 2880253114234574467003469)
                  ·
                    refine ⟨1080094917837965425126301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2880253114234574467003469 1080094917837965425126301)
                    ·
                      refine ⟨405035594189237034422363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1080094917837965425126301 405035594189237034422363)
                      ·
                        rfl

theorem cell23_788804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_788804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788804 prefixEnd_788804 := by exact prefixLift 788804
  have htrace : WordTrace (prefixWord ++ tailWord_788804) baseStart_788804 baseEnd_788804 := by
    simpa [prefixWord, tailWord_788804, baseEnd_788804] using wordTrace_append hprefix tailTrace_788804
  have hstable : (prefixWord ++ tailWord_788804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788804).length < 2 ^ (prefixWord ++ tailWord_788804).sum := by decide
  have hdescent : baseEnd_788804 < baseStart_788804 := by decide
  rcases family_descends (prefixWord ++ tailWord_788804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788816 : List Nat := [2, 1, 1, 1, 1, 6, 2, 2, 7]
def baseStart_788816 : Nat := 118140960795 + 788816 * 2 ^ 59
def prefixEnd_788816 : Nat := 4983230072969 + 3 ^ 40 * 788816 * 2
def baseEnd_788816 : Nat := 45004639550787887496923

theorem tailTrace_788816 : CollatzResearch.WordTrace tailWord_788816 prefixEnd_788816 45004639550787887496923 := by
  unfold tailWord_788816
  simp only [CollatzResearch.WordTrace]
  refine ⟨14385241555130912946189151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19180322073507883928252201 14385241555130912946189151)
  ·
    refine ⟨21577862332696369419283727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14385241555130912946189151 21577862332696369419283727)
    ·
      refine ⟨32366793499044554128925591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21577862332696369419283727 32366793499044554128925591)
      ·
        refine ⟨48550190248566831193388387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32366793499044554128925591 48550190248566831193388387)
        ·
          refine ⟨72825285372850246790082581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48550190248566831193388387 72825285372850246790082581)
          ·
            refine ⟨3413685251852355318285121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72825285372850246790082581 3413685251852355318285121)
            ·
              refine ⟨2560263938889266488713841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3413685251852355318285121 2560263938889266488713841)
              ·
                refine ⟨1920197954166949866535381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2560263938889266488713841 1920197954166949866535381)
                ·
                  refine ⟨45004639550787887496923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1920197954166949866535381 45004639550787887496923)
                  ·
                    rfl

theorem cell23_788816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 7].length) (baseStart_788816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788816 prefixEnd_788816 := by exact prefixLift 788816
  have htrace : WordTrace (prefixWord ++ tailWord_788816) baseStart_788816 baseEnd_788816 := by
    simpa [prefixWord, tailWord_788816, baseEnd_788816] using wordTrace_append hprefix tailTrace_788816
  have hstable : (prefixWord ++ tailWord_788816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788816).length < 2 ^ (prefixWord ++ tailWord_788816).sum := by decide
  have hdescent : baseEnd_788816 < baseStart_788816 := by decide
  rcases family_descends (prefixWord ++ tailWord_788816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788917 : List Nat := [1, 3, 3, 2, 3, 1, 1, 1, 2, 4, 2]
def baseStart_788917 : Nat := 118140960795 + 788917 * 2 ^ 59
def prefixEnd_788917 : Nat := 4983230072969 + 3 ^ 40 * 788917 * 2
def baseEnd_788917 : Nat := 405093617503195092309343

theorem tailTrace_788917 : CollatzResearch.WordTrace tailWord_788917 prefixEnd_788917 405093617503195092309343 := by
  unfold tailWord_788917
  simp only [CollatzResearch.WordTrace]
  refine ⟨28774166882895920141805005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19182777921930613427870003 28774166882895920141805005)
  ·
    refine ⟨10790312581085970053176877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28774166882895920141805005 10790312581085970053176877)
    ·
      refine ⟨4046367217907238769941329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10790312581085970053176877 4046367217907238769941329)
      ·
        refine ⟨3034775413430429077455997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4046367217907238769941329 3034775413430429077455997)
        ·
          refine ⟨1138040780036410904045999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3034775413430429077455997 1138040780036410904045999)
          ·
            refine ⟨1707061170054616356068999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1138040780036410904045999 1707061170054616356068999)
            ·
              refine ⟨2560591755081924534103499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1707061170054616356068999 2560591755081924534103499)
              ·
                refine ⟨3840887632622886801155249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2560591755081924534103499 3840887632622886801155249)
                ·
                  refine ⟨2880665724467165100866437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3840887632622886801155249 2880665724467165100866437)
                  ·
                    refine ⟨540124823337593456412457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2880665724467165100866437 540124823337593456412457)
                    ·
                      refine ⟨405093617503195092309343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 540124823337593456412457 405093617503195092309343)
                      ·
                        rfl

theorem cell23_788917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_788917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788917 prefixEnd_788917 := by exact prefixLift 788917
  have htrace : WordTrace (prefixWord ++ tailWord_788917) baseStart_788917 baseEnd_788917 := by
    simpa [prefixWord, tailWord_788917, baseEnd_788917] using wordTrace_append hprefix tailTrace_788917
  have hstable : (prefixWord ++ tailWord_788917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788917).length < 2 ^ (prefixWord ++ tailWord_788917).sum := by decide
  have hdescent : baseEnd_788917 < baseStart_788917 := by decide
  rcases family_descends (prefixWord ++ tailWord_788917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788960 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 4, 3, 2]
def baseStart_788960 : Nat := 118140960795 + 788960 * 2 ^ 59
def prefixEnd_788960 : Nat := 4983230072969 + 3 ^ 40 * 788960 * 2
def baseEnd_788960 : Nat := 405115697171338424071645

theorem tailTrace_788960 : CollatzResearch.WordTrace tailWord_788960 prefixEnd_788960 405115697171338424071645 := by
  unfold tailWord_788960
  simp only [CollatzResearch.WordTrace]
  refine ⟨14387867610870069242810167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19183823481160092323746889 14387867610870069242810167)
  ·
    refine ⟨21581801416305103864215251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14387867610870069242810167 21581801416305103864215251)
    ·
      refine ⟨32372702124457655796322877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21581801416305103864215251 32372702124457655796322877)
      ·
        refine ⟨12139763296671620923621079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32372702124457655796322877 12139763296671620923621079)
        ·
          refine ⟨18209644945007431385431619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12139763296671620923621079 18209644945007431385431619)
          ·
            refine ⟨27314467417511147078147429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18209644945007431385431619 27314467417511147078147429)
            ·
              refine ⟨5121462640783340077152643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27314467417511147078147429 5121462640783340077152643)
              ·
                refine ⟨7682193961175010115728965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5121462640783340077152643 7682193961175010115728965)
                ·
                  refine ⟨1440411367720314396699181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7682193961175010115728965 1440411367720314396699181)
                  ·
                    refine ⟨540154262895117898762193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1440411367720314396699181 540154262895117898762193)
                    ·
                      refine ⟨405115697171338424071645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 540154262895117898762193 405115697171338424071645)
                      ·
                        rfl

theorem cell23_788960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 4, 3, 2].length) (baseStart_788960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788960 prefixEnd_788960 := by exact prefixLift 788960
  have htrace : WordTrace (prefixWord ++ tailWord_788960) baseStart_788960 baseEnd_788960 := by
    simpa [prefixWord, tailWord_788960, baseEnd_788960] using wordTrace_append hprefix tailTrace_788960
  have hstable : (prefixWord ++ tailWord_788960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788960).length < 2 ^ (prefixWord ++ tailWord_788960).sum := by decide
  have hdescent : baseEnd_788960 < baseStart_788960 := by decide
  rcases family_descends (prefixWord ++ tailWord_788960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788967 : List Nat := [1, 1, 5, 2, 1, 1, 4, 1, 3, 1, 3]
def baseStart_788967 : Nat := 118140960795 + 788967 * 2 ^ 59
def prefixEnd_788967 : Nat := 4983230072969 + 3 ^ 40 * 788967 * 2
def baseEnd_788967 : Nat := 405119291535919896684113

theorem tailTrace_788967 : CollatzResearch.WordTrace tailWord_788967 prefixEnd_788967 405119291535919896684113 := by
  unfold tailWord_788967
  simp only [CollatzResearch.WordTrace]
  refine ⟨28775990532714778681125155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19183993688476519120750103 28775990532714778681125155)
  ·
    refine ⟨43163985799072168021687733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28775990532714778681125155 43163985799072168021687733)
    ·
      refine ⟨4046623668663015752033225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43163985799072168021687733 4046623668663015752033225)
      ·
        refine ⟨3034967751497261814024919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4046623668663015752033225 3034967751497261814024919)
        ·
          refine ⟨4552451627245892721037379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3034967751497261814024919 4552451627245892721037379)
          ·
            refine ⟨6828677440868839081556069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4552451627245892721037379 6828677440868839081556069)
            ·
              refine ⟨1280377020162907327791763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6828677440868839081556069 1280377020162907327791763)
              ·
                refine ⟨1920565530244360991687645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1280377020162907327791763 1920565530244360991687645)
                ·
                  refine ⟨720212073841635371882867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1920565530244360991687645 720212073841635371882867)
                  ·
                    refine ⟨1080318110762453057824301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 720212073841635371882867 1080318110762453057824301)
                    ·
                      refine ⟨405119291535919896684113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1080318110762453057824301 405119291535919896684113)
                      ·
                        rfl

theorem cell23_788967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_788967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_788967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_788967 prefixEnd_788967 := by exact prefixLift 788967
  have htrace : WordTrace (prefixWord ++ tailWord_788967) baseStart_788967 baseEnd_788967 := by
    simpa [prefixWord, tailWord_788967, baseEnd_788967] using wordTrace_append hprefix tailTrace_788967
  have hstable : (prefixWord ++ tailWord_788967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788967).length < 2 ^ (prefixWord ++ tailWord_788967).sum := by decide
  have hdescent : baseEnd_788967 < baseStart_788967 := by decide
  rcases family_descends (prefixWord ++ tailWord_788967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789034 : List Nat := [3, 1, 4, 1, 1, 2, 4, 1, 2, 4]
def baseStart_789034 : Nat := 118140960795 + 789034 * 2 ^ 59
def prefixEnd_789034 : Nat := 4983230072969 + 3 ^ 40 * 789034 * 2
def baseEnd_789034 : Nat := 135051231579923711515435

theorem tailTrace_789034 : CollatzResearch.WordTrace tailWord_789034 prefixEnd_789034 135051231579923711515435 := by
  unfold tailWord_789034
  simp only [CollatzResearch.WordTrace]
  refine ⟨7194608555868012280953539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19185622815648032749209437 7194608555868012280953539)
  ·
    refine ⟨10791912833802018421430309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7194608555868012280953539 10791912833802018421430309)
    ·
      refine ⟨2023483656337878454018183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10791912833802018421430309 2023483656337878454018183)
      ·
        refine ⟨3035225484506817681027275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2023483656337878454018183 3035225484506817681027275)
        ·
          refine ⟨4552838226760226521540913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3035225484506817681027275 4552838226760226521540913)
          ·
            refine ⟨3414628670070169891155685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4552838226760226521540913 3414628670070169891155685)
            ·
              refine ⟨640242875638156854591691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3414628670070169891155685 640242875638156854591691)
              ·
                refine ⟨960364313457235281887537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 640242875638156854591691 960364313457235281887537)
                ·
                  refine ⟨720273235092926461415653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 960364313457235281887537 720273235092926461415653)
                  ·
                    refine ⟨135051231579923711515435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 720273235092926461415653 135051231579923711515435)
                    ·
                      rfl

theorem cell23_789034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_789034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789034 prefixEnd_789034 := by exact prefixLift 789034
  have htrace : WordTrace (prefixWord ++ tailWord_789034) baseStart_789034 baseEnd_789034 := by
    simpa [prefixWord, tailWord_789034, baseEnd_789034] using wordTrace_append hprefix tailTrace_789034
  have hstable : (prefixWord ++ tailWord_789034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789034).length < 2 ^ (prefixWord ++ tailWord_789034).sum := by decide
  have hdescent : baseEnd_789034 < baseStart_789034 := by decide
  rcases family_descends (prefixWord ++ tailWord_789034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789054 : List Nat := [4, 2, 1, 4, 1, 1, 1, 2, 1, 2, 4]
def baseStart_789054 : Nat := 118140960795 + 789054 * 2 ^ 59
def prefixEnd_789054 : Nat := 4983230072969 + 3 ^ 40 * 789054 * 2
def baseEnd_789054 : Nat := 405163964352861056296213

theorem tailTrace_789054 : CollatzResearch.WordTrace tailWord_789054 prefixEnd_789054 405163964352861056296213 := by
  unfold tailWord_789054
  simp only [CollatzResearch.WordTrace]
  refine ⟨3597395460424949067442777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19186109122266395026361477 3597395460424949067442777)
  ·
    refine ⟨2698046595318711800582083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3597395460424949067442777 2698046595318711800582083)
    ·
      refine ⟨4047069892978067700873125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2698046595318711800582083 4047069892978067700873125)
      ·
        refine ⟨758825604933387693913711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4047069892978067700873125 758825604933387693913711)
        ·
          refine ⟨1138238407400081540870567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758825604933387693913711 1138238407400081540870567)
          ·
            refine ⟨1707357611100122311305851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1138238407400081540870567 1707357611100122311305851)
            ·
              refine ⟨2561036416650183466958777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1707357611100122311305851 2561036416650183466958777)
              ·
                refine ⟨1920777312487637600219083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2561036416650183466958777 1920777312487637600219083)
                ·
                  refine ⟨2881165968731456400328625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920777312487637600219083 2881165968731456400328625)
                  ·
                    refine ⟨2160874476548592300246469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2881165968731456400328625 2160874476548592300246469)
                    ·
                      refine ⟨405163964352861056296213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2160874476548592300246469 405163964352861056296213)
                      ·
                        rfl

theorem cell23_789054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_789054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789054 prefixEnd_789054 := by exact prefixLift 789054
  have htrace : WordTrace (prefixWord ++ tailWord_789054) baseStart_789054 baseEnd_789054 := by
    simpa [prefixWord, tailWord_789054, baseEnd_789054] using wordTrace_append hprefix tailTrace_789054
  have hstable : (prefixWord ++ tailWord_789054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789054).length < 2 ^ (prefixWord ++ tailWord_789054).sum := by decide
  have hdescent : baseEnd_789054 < baseStart_789054 := by decide
  rcases family_descends (prefixWord ++ tailWord_789054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789057 : List Nat := [1, 2, 5, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_789057 : Nat := 118140960795 + 789057 * 2 ^ 59
def prefixEnd_789057 : Nat := 4983230072969 + 3 ^ 40 * 789057 * 2
def baseEnd_789057 : Nat := 405165504794824544558699

theorem tailTrace_789057 : CollatzResearch.WordTrace tailWord_789057 prefixEnd_789057 405165504794824544558699 := by
  unfold tailWord_789057
  simp only [CollatzResearch.WordTrace]
  refine ⟨28779273102388724051901425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19186182068259149367934283 28779273102388724051901425)
  ·
    refine ⟨21584454826791543038926069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28779273102388724051901425 21584454826791543038926069)
    ·
      refine ⟨2023542640011707159899319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21584454826791543038926069 2023542640011707159899319)
      ·
        refine ⟨3035313960017560739848979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2023542640011707159899319 3035313960017560739848979)
        ·
          refine ⟨4552970940026341109773469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3035313960017560739848979 4552970940026341109773469)
          ·
            refine ⟨1707364102509877916165051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4552970940026341109773469 1707364102509877916165051)
            ·
              refine ⟨2561046153764816874247577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1707364102509877916165051 2561046153764816874247577)
              ·
                refine ⟨1920784615323612655685683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2561046153764816874247577 1920784615323612655685683)
                ·
                  refine ⟨2881176922985418983528525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1920784615323612655685683 2881176922985418983528525)
                  ·
                    refine ⟨1080441346119532118823197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2881176922985418983528525 1080441346119532118823197)
                    ·
                      refine ⟨405165504794824544558699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1080441346119532118823197 405165504794824544558699)
                      ·
                        rfl

theorem cell23_789057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_789057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789057 prefixEnd_789057 := by exact prefixLift 789057
  have htrace : WordTrace (prefixWord ++ tailWord_789057) baseStart_789057 baseEnd_789057 := by
    simpa [prefixWord, tailWord_789057, baseEnd_789057] using wordTrace_append hprefix tailTrace_789057
  have hstable : (prefixWord ++ tailWord_789057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789057).length < 2 ^ (prefixWord ++ tailWord_789057).sum := by decide
  have hdescent : baseEnd_789057 < baseStart_789057 := by decide
  rcases family_descends (prefixWord ++ tailWord_789057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789067 : List Nat := [1, 1, 1, 1, 3, 1, 4, 5, 1, 3, 2]
def baseStart_789067 : Nat := 118140960795 + 789067 * 2 ^ 59
def prefixEnd_789067 : Nat := 4983230072969 + 3 ^ 40 * 789067 * 2
def baseEnd_789067 : Nat := 405170639601369505433653

theorem tailTrace_789067 : CollatzResearch.WordTrace tailWord_789067 prefixEnd_789067 405170639601369505433653 := by
  unfold tailWord_789067
  simp only [CollatzResearch.WordTrace]
  refine ⟨28779637832352495759765455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19186425221568330506510303 28779637832352495759765455)
  ·
    refine ⟨43169456748528743639648183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28779637832352495759765455 43169456748528743639648183)
    ·
      refine ⟨64754185122793115459472275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43169456748528743639648183 64754185122793115459472275)
      ·
        refine ⟨97131277684189673189208413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64754185122793115459472275 97131277684189673189208413)
        ·
          refine ⟨36424229131571127445953155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97131277684189673189208413 36424229131571127445953155)
          ·
            refine ⟨54636343697356691168929733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36424229131571127445953155 54636343697356691168929733)
            ·
              refine ⟨10244314443254379594174325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54636343697356691168929733 10244314443254379594174325)
              ·
                refine ⟨960404479055098086953843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10244314443254379594174325 960404479055098086953843)
                ·
                  refine ⟨1440606718582647130430765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 960404479055098086953843 1440606718582647130430765)
                  ·
                    refine ⟨540227519468492673911537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1440606718582647130430765 540227519468492673911537)
                    ·
                      refine ⟨405170639601369505433653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 540227519468492673911537 405170639601369505433653)
                      ·
                        rfl

theorem cell23_789067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 3, 2].length) (baseStart_789067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789067 prefixEnd_789067 := by exact prefixLift 789067
  have htrace : WordTrace (prefixWord ++ tailWord_789067) baseStart_789067 baseEnd_789067 := by
    simpa [prefixWord, tailWord_789067, baseEnd_789067] using wordTrace_append hprefix tailTrace_789067
  have hstable : (prefixWord ++ tailWord_789067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789067).length < 2 ^ (prefixWord ++ tailWord_789067).sum := by decide
  have hdescent : baseEnd_789067 < baseStart_789067 := by decide
  rcases family_descends (prefixWord ++ tailWord_789067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789074 : List Nat := [3, 2, 2, 1, 2, 1, 4, 2, 2, 1, 3]
def baseStart_789074 : Nat := 118140960795 + 789074 * 2 ^ 59
def prefixEnd_789074 : Nat := 4983230072969 + 3 ^ 40 * 789074 * 2
def baseEnd_789074 : Nat := 405174233965950978046121

theorem tailTrace_789074 : CollatzResearch.WordTrace tailWord_789074 prefixEnd_789074 405174233965950978046121 := by
  unfold tailWord_789074
  simp only [CollatzResearch.WordTrace]
  refine ⟨7194973285831783988817569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19186595428884757303513517 7194973285831783988817569)
  ·
    refine ⟨5396229964373837991613177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7194973285831783988817569 5396229964373837991613177)
    ·
      refine ⟨4047172473280378493709883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5396229964373837991613177 4047172473280378493709883)
      ·
        refine ⟨6070758709920567740564825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4047172473280378493709883 6070758709920567740564825)
        ·
          refine ⟨4553069032440425805423619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6070758709920567740564825 4553069032440425805423619)
          ·
            refine ⟨6829603548660638708135429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4553069032440425805423619 6829603548660638708135429)
            ·
              refine ⟨1280550665373869757775393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6829603548660638708135429 1280550665373869757775393)
              ·
                refine ⟨960412999030402318331545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1280550665373869757775393 960412999030402318331545)
                ·
                  refine ⟨720309749272801738748659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 960412999030402318331545 720309749272801738748659)
                  ·
                    refine ⟨1080464623909202608122989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 720309749272801738748659 1080464623909202608122989)
                    ·
                      refine ⟨405174233965950978046121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1080464623909202608122989 405174233965950978046121)
                      ·
                        rfl

theorem cell23_789074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_789074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789074 prefixEnd_789074 := by exact prefixLift 789074
  have htrace : WordTrace (prefixWord ++ tailWord_789074) baseStart_789074 baseEnd_789074 := by
    simpa [prefixWord, tailWord_789074, baseEnd_789074] using wordTrace_append hprefix tailTrace_789074
  have hstable : (prefixWord ++ tailWord_789074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789074).length < 2 ^ (prefixWord ++ tailWord_789074).sum := by decide
  have hdescent : baseEnd_789074 < baseStart_789074 := by decide
  rcases family_descends (prefixWord ++ tailWord_789074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789097 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 6, 2, 2]
def baseStart_789097 : Nat := 118140960795 + 789097 * 2 ^ 59
def prefixEnd_789097 : Nat := 4983230072969 + 3 ^ 40 * 789097 * 2
def baseEnd_789097 : Nat := 405186044021004388058515

theorem tailTrace_789097 : CollatzResearch.WordTrace tailWord_789097 prefixEnd_789097 405186044021004388058515 := by
  unfold tailWord_789097
  simp only [CollatzResearch.WordTrace]
  refine ⟨28780732022243810883357545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19187154681495873922238363 28780732022243810883357545)
  ·
    refine ⟨21585549016682858162518159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28780732022243810883357545 21585549016682858162518159)
    ·
      refine ⟨32378323525024287243777239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21585549016682858162518159 32378323525024287243777239)
      ·
        refine ⟨48567485287536430865665859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32378323525024287243777239 48567485287536430865665859)
        ·
          refine ⟨72851227931304646298498789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48567485287536430865665859 72851227931304646298498789)
          ·
            refine ⟨13659605237119621180968523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72851227931304646298498789 13659605237119621180968523)
            ·
              refine ⟨20489407855679431771452785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13659605237119621180968523 20489407855679431771452785)
              ·
                refine ⟨15367055891759573828589589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20489407855679431771452785 15367055891759573828589589)
                ·
                  refine ⟨720330744926230023215137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15367055891759573828589589 720330744926230023215137)
                  ·
                    refine ⟨540248058694672517411353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 720330744926230023215137 540248058694672517411353)
                    ·
                      refine ⟨405186044021004388058515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 540248058694672517411353 405186044021004388058515)
                      ·
                        rfl

theorem cell23_789097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6, 2, 2].length) (baseStart_789097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789097 prefixEnd_789097 := by exact prefixLift 789097
  have htrace : WordTrace (prefixWord ++ tailWord_789097) baseStart_789097 baseEnd_789097 := by
    simpa [prefixWord, tailWord_789097, baseEnd_789097] using wordTrace_append hprefix tailTrace_789097
  have hstable : (prefixWord ++ tailWord_789097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789097).length < 2 ^ (prefixWord ++ tailWord_789097).sum := by decide
  have hdescent : baseEnd_789097 < baseStart_789097 := by decide
  rcases family_descends (prefixWord ++ tailWord_789097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789103 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 9]
def baseStart_789103 : Nat := 118140960795 + 789103 * 2 ^ 59
def prefixEnd_789103 : Nat := 4983230072969 + 3 ^ 40 * 789103 * 2
def baseEnd_789103 : Nat := 45021013878325707175943

theorem tailTrace_789103 : CollatzResearch.WordTrace tailWord_789103 prefixEnd_789103 45021013878325707175943 := by
  unfold tailWord_789103
  simp only [CollatzResearch.WordTrace]
  refine ⟨28780950860222073908075963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19187300573481382605383975 28780950860222073908075963)
  ·
    refine ⟨43171426290333110862113945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28780950860222073908075963 43171426290333110862113945)
    ·
      refine ⟨32378569717749833146585459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43171426290333110862113945 32378569717749833146585459)
      ·
        refine ⟨48567854576624749719878189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32378569717749833146585459 48567854576624749719878189)
        ·
          refine ⟨18212945466234281144954321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48567854576624749719878189 18212945466234281144954321)
          ·
            refine ⟨13659709099675710858715741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18212945466234281144954321 13659709099675710858715741)
            ·
              refine ⟨5122390912378391572018403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13659709099675710858715741 5122390912378391572018403)
              ·
                refine ⟨7683586368567587358027605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5122390912378391572018403 7683586368567587358027605)
                ·
                  refine ⟨45021013878325707175943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7683586368567587358027605 45021013878325707175943)
                  ·
                    rfl

theorem cell23_789103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 9].length) (baseStart_789103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789103 prefixEnd_789103 := by exact prefixLift 789103
  have htrace : WordTrace (prefixWord ++ tailWord_789103) baseStart_789103 baseEnd_789103 := by
    simpa [prefixWord, tailWord_789103, baseEnd_789103] using wordTrace_append hprefix tailTrace_789103
  have hstable : (prefixWord ++ tailWord_789103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789103).length < 2 ^ (prefixWord ++ tailWord_789103).sum := by decide
  have hdescent : baseEnd_789103 < baseStart_789103 := by decide
  rcases family_descends (prefixWord ++ tailWord_789103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789148 : List Nat := [2, 2, 3, 2, 2, 2, 3, 1, 2, 2, 2]
def baseStart_789148 : Nat := 118140960795 + 789148 * 2 ^ 59
def prefixEnd_789148 : Nat := 4983230072969 + 3 ^ 40 * 789148 * 2
def baseEnd_789148 : Nat := 405212231534383688520781

theorem tailTrace_789148 : CollatzResearch.WordTrace tailWord_789148 prefixEnd_789148 405212231534383688520781 := by
  unfold tailWord_789148
  simp only [CollatzResearch.WordTrace]
  refine ⟨14391296072529523296732049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19188394763372697728976065 14391296072529523296732049)
  ·
    refine ⟨10793472054397142472549037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14391296072529523296732049 10793472054397142472549037)
    ·
      refine ⟨4047552020398928427205889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10793472054397142472549037 4047552020398928427205889)
      ·
        refine ⟨3035664015299196320404417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4047552020398928427205889 3035664015299196320404417)
        ·
          refine ⟨2276748011474397240303313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3035664015299196320404417 2276748011474397240303313)
          ·
            refine ⟨1707561008605797930227485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2276748011474397240303313 1707561008605797930227485)
            ·
              refine ⟨640335378227174223835307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1707561008605797930227485 640335378227174223835307)
              ·
                refine ⟨960503067340761335752961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 640335378227174223835307 960503067340761335752961)
                ·
                  refine ⟨720377300505571001814721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 960503067340761335752961 720377300505571001814721)
                  ·
                    refine ⟨540282975379178251361041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 720377300505571001814721 540282975379178251361041)
                    ·
                      refine ⟨405212231534383688520781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 540282975379178251361041 405212231534383688520781)
                      ·
                        rfl

theorem cell23_789148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_789148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789148 prefixEnd_789148 := by exact prefixLift 789148
  have htrace : WordTrace (prefixWord ++ tailWord_789148) baseStart_789148 baseEnd_789148 := by
    simpa [prefixWord, tailWord_789148, baseEnd_789148] using wordTrace_append hprefix tailTrace_789148
  have hstable : (prefixWord ++ tailWord_789148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789148).length < 2 ^ (prefixWord ++ tailWord_789148).sum := by decide
  have hdescent : baseEnd_789148 < baseStart_789148 := by decide
  rcases family_descends (prefixWord ++ tailWord_789148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789247 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 3, 5, 2]
def baseStart_789247 : Nat := 118140960795 + 789247 * 2 ^ 59
def prefixEnd_789247 : Nat := 4983230072969 + 3 ^ 40 * 789247 * 2
def baseEnd_789247 : Nat := 405263066119178801182825

theorem tailTrace_789247 : CollatzResearch.WordTrace tailWord_789247 prefixEnd_789247 405263066119178801182825 := by
  unfold tailWord_789247
  simp only [CollatzResearch.WordTrace]
  refine ⟨28786202971700386501317995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19190801981133591000878663 28786202971700386501317995)
  ·
    refine ⟨43179304457550579751976993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28786202971700386501317995 43179304457550579751976993)
    ·
      refine ⟨32384478343162934813982745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43179304457550579751976993 32384478343162934813982745)
      ·
        refine ⟨24288358757372201110487059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32384478343162934813982745 24288358757372201110487059)
        ·
          refine ⟨36432538136058301665730589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24288358757372201110487059 36432538136058301665730589)
          ·
            refine ⟨13662201801021863124648971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36432538136058301665730589 13662201801021863124648971)
            ·
              refine ⟨20493302701532794686973457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13662201801021863124648971 20493302701532794686973457)
              ·
                refine ⟨15369977026149596015230093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20493302701532794686973457 15369977026149596015230093)
                ·
                  refine ⟨5763741384806098505711285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15369977026149596015230093 5763741384806098505711285)
                  ·
                    refine ⟨540350754825571734910433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5763741384806098505711285 540350754825571734910433)
                    ·
                      refine ⟨405263066119178801182825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 540350754825571734910433 405263066119178801182825)
                      ·
                        rfl

theorem cell23_789247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 5, 2].length) (baseStart_789247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789247 prefixEnd_789247 := by exact prefixLift 789247
  have htrace : WordTrace (prefixWord ++ tailWord_789247) baseStart_789247 baseEnd_789247 := by
    simpa [prefixWord, tailWord_789247, baseEnd_789247] using wordTrace_append hprefix tailTrace_789247
  have hstable : (prefixWord ++ tailWord_789247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789247).length < 2 ^ (prefixWord ++ tailWord_789247).sum := by decide
  have hdescent : baseEnd_789247 < baseStart_789247 := by decide
  rcases family_descends (prefixWord ++ tailWord_789247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789271 : List Nat := [1, 1, 3, 4, 3, 1, 1, 2, 3, 1, 3]
def baseStart_789271 : Nat := 118140960795 + 789271 * 2 ^ 59
def prefixEnd_789271 : Nat := 4983230072969 + 3 ^ 40 * 789271 * 2
def baseEnd_789271 : Nat := 405275389654886707282715

theorem tailTrace_789271 : CollatzResearch.WordTrace tailWord_789271 prefixEnd_789271 405275389654886707282715 := by
  unfold tailWord_789271
  simp only [CollatzResearch.WordTrace]
  refine ⟨28787078323613438600191667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19191385549075625733461111 28787078323613438600191667)
  ·
    refine ⟨43180617485420157900287501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28787078323613438600191667 43180617485420157900287501)
    ·
      refine ⟨16192731557032559212607813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43180617485420157900287501 16192731557032559212607813)
      ·
        refine ⟨3036137166943604852363965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16192731557032559212607813 3036137166943604852363965)
        ·
          refine ⟨1138551437603851819636487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3036137166943604852363965 1138551437603851819636487)
          ·
            refine ⟨1707827156405777729454731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1138551437603851819636487 1707827156405777729454731)
            ·
              refine ⟨2561740734608666594182097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1707827156405777729454731 2561740734608666594182097)
              ·
                refine ⟨1921305550956499945636573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2561740734608666594182097 1921305550956499945636573)
                ·
                  refine ⟨720489581608687479613715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1921305550956499945636573 720489581608687479613715)
                  ·
                    refine ⟨1080734372413031219420573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 720489581608687479613715 1080734372413031219420573)
                    ·
                      refine ⟨405275389654886707282715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1080734372413031219420573 405275389654886707282715)
                      ·
                        rfl

theorem cell23_789271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_789271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789271 prefixEnd_789271 := by exact prefixLift 789271
  have htrace : WordTrace (prefixWord ++ tailWord_789271) baseStart_789271 baseEnd_789271 := by
    simpa [prefixWord, tailWord_789271, baseEnd_789271] using wordTrace_append hprefix tailTrace_789271
  have hstable : (prefixWord ++ tailWord_789271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789271).length < 2 ^ (prefixWord ++ tailWord_789271).sum := by decide
  have hdescent : baseEnd_789271 < baseStart_789271 := by decide
  rcases family_descends (prefixWord ++ tailWord_789271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789288 : List Nat := [2, 1, 5, 1, 1, 1, 4, 3, 1, 1, 3]
def baseStart_789288 : Nat := 118140960795 + 789288 * 2 ^ 59
def prefixEnd_789288 : Nat := 4983230072969 + 3 ^ 40 * 789288 * 2
def baseEnd_789288 : Nat := 405284118826013140770137

theorem tailTrace_789288 : CollatzResearch.WordTrace tailWord_789288 prefixEnd_789288 405284118826013140770137 := by
  unfold tailWord_789288
  simp only [CollatzResearch.WordTrace]
  refine ⟨14393849182275925251780259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19191798909701233669040345 14393849182275925251780259)
  ·
    refine ⟨21590773773413887877670389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14393849182275925251780259 21590773773413887877670389)
    ·
      refine ⟨2024135041257551988531599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21590773773413887877670389 2024135041257551988531599)
      ·
        refine ⟨3036202561886327982797399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2024135041257551988531599 3036202561886327982797399)
        ·
          refine ⟨4554303842829491974196099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3036202561886327982797399 4554303842829491974196099)
          ·
            refine ⟨6831455764244237961294149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4554303842829491974196099 6831455764244237961294149)
            ·
              refine ⟨1280897955795794617742653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6831455764244237961294149 1280897955795794617742653)
              ·
                refine ⟨480336733423422981653495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1280897955795794617742653 480336733423422981653495)
                ·
                  refine ⟨720505100135134472480243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 480336733423422981653495 720505100135134472480243)
                  ·
                    refine ⟨1080757650202701708720365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 720505100135134472480243 1080757650202701708720365)
                    ·
                      refine ⟨405284118826013140770137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1080757650202701708720365 405284118826013140770137)
                      ·
                        rfl

theorem cell23_789288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_789288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789288 prefixEnd_789288 := by exact prefixLift 789288
  have htrace : WordTrace (prefixWord ++ tailWord_789288) baseStart_789288 baseEnd_789288 := by
    simpa [prefixWord, tailWord_789288, baseEnd_789288] using wordTrace_append hprefix tailTrace_789288
  have hstable : (prefixWord ++ tailWord_789288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789288).length < 2 ^ (prefixWord ++ tailWord_789288).sum := by decide
  have hdescent : baseEnd_789288 < baseStart_789288 := by decide
  rcases family_descends (prefixWord ++ tailWord_789288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789297 : List Nat := [1, 2, 2, 3, 2, 1, 2, 3, 1, 1, 5]
def baseStart_789297 : Nat := 118140960795 + 789297 * 2 ^ 59
def prefixEnd_789297 : Nat := 4983230072969 + 3 ^ 40 * 789297 * 2
def baseEnd_789297 : Nat := 405288740151903605557595

theorem tailTrace_789297 : CollatzResearch.WordTrace tailWord_789297 prefixEnd_789297 405288740151903605557595 := by
  unfold tailWord_789297
  simp only [CollatzResearch.WordTrace]
  refine ⟨28788026621519245040638145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19192017747679496693758763 28788026621519245040638145)
  ·
    refine ⟨21591019966139433780478609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28788026621519245040638145 21591019966139433780478609)
    ·
      refine ⟨16193264974604575335358957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21591019966139433780478609 16193264974604575335358957)
      ·
        refine ⟨6072474365476715750759609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16193264974604575335358957 6072474365476715750759609)
        ·
          refine ⟨4554355774107536813069707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6072474365476715750759609 4554355774107536813069707)
          ·
            refine ⟨6831533661161305219604561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4554355774107536813069707 6831533661161305219604561)
            ·
              refine ⟨5123650245870978914703421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6831533661161305219604561 5123650245870978914703421)
              ·
                refine ⟨1921368842201617093013783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5123650245870978914703421 1921368842201617093013783)
                ·
                  refine ⟨2882053263302425639520675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1921368842201617093013783 2882053263302425639520675)
                  ·
                    refine ⟨4323079894953638459281013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2882053263302425639520675 4323079894953638459281013)
                    ·
                      refine ⟨405288740151903605557595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4323079894953638459281013 405288740151903605557595)
                      ·
                        rfl

theorem cell23_789297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_789297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789297 prefixEnd_789297 := by exact prefixLift 789297
  have htrace : WordTrace (prefixWord ++ tailWord_789297) baseStart_789297 baseEnd_789297 := by
    simpa [prefixWord, tailWord_789297, baseEnd_789297] using wordTrace_append hprefix tailTrace_789297
  have hstable : (prefixWord ++ tailWord_789297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789297).length < 2 ^ (prefixWord ++ tailWord_789297).sum := by decide
  have hdescent : baseEnd_789297 < baseStart_789297 := by decide
  rcases family_descends (prefixWord ++ tailWord_789297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789311 : List Nat := [1, 1, 2, 2, 5, 1, 1, 3, 3, 2, 2]
def baseStart_789311 : Nat := 118140960795 + 789311 * 2 ^ 59
def prefixEnd_789311 : Nat := 4983230072969 + 3 ^ 40 * 789311 * 2
def baseEnd_789311 : Nat := 405295928881066550782531

theorem tailTrace_789311 : CollatzResearch.WordTrace tailWord_789311 prefixEnd_789311 405295928881066550782531 := by
  unfold tailWord_789311
  simp only [CollatzResearch.WordTrace]
  refine ⟨28788537243468525431647787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19192358162312350287765191 28788537243468525431647787)
  ·
    refine ⟨43182805865202788147471681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28788537243468525431647787 43182805865202788147471681)
    ·
      refine ⟨32387104398902091110603761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43182805865202788147471681 32387104398902091110603761)
      ·
        refine ⟨24290328299176568332952821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32387104398902091110603761 24290328299176568332952821)
        ·
          refine ⟨2277218278047803281214327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24290328299176568332952821 2277218278047803281214327)
          ·
            refine ⟨3415827417071704921821491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2277218278047803281214327 3415827417071704921821491)
            ·
              refine ⟨5123741125607557382732237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3415827417071704921821491 5123741125607557382732237)
              ·
                refine ⟨1921402922102834018524589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5123741125607557382732237 1921402922102834018524589)
                ·
                  refine ⟨720526095788562756946721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1921402922102834018524589 720526095788562756946721)
                  ·
                    refine ⟨540394571841422067710041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 720526095788562756946721 540394571841422067710041)
                    ·
                      refine ⟨405295928881066550782531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 540394571841422067710041 405295928881066550782531)
                      ·
                        rfl

theorem cell23_789311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3, 2, 2].length) (baseStart_789311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789311 prefixEnd_789311 := by exact prefixLift 789311
  have htrace : WordTrace (prefixWord ++ tailWord_789311) baseStart_789311 baseEnd_789311 := by
    simpa [prefixWord, tailWord_789311, baseEnd_789311] using wordTrace_append hprefix tailTrace_789311
  have hstable : (prefixWord ++ tailWord_789311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789311).length < 2 ^ (prefixWord ++ tailWord_789311).sum := by decide
  have hdescent : baseEnd_789311 < baseStart_789311 := by decide
  rcases family_descends (prefixWord ++ tailWord_789311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789321 : List Nat := [1, 2, 1, 1, 2, 6, 3, 1, 2, 4]
def baseStart_789321 : Nat := 118140960795 + 789321 * 2 ^ 59
def prefixEnd_789321 : Nat := 4983230072969 + 3 ^ 40 * 789321 * 2
def baseEnd_789321 : Nat := 135100354562537170552495

theorem tailTrace_789321 : CollatzResearch.WordTrace tailWord_789321 prefixEnd_789321 135100354562537170552495 := by
  unfold tailWord_789321
  simp only [CollatzResearch.WordTrace]
  refine ⟨28788901973432297139511817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19192601315621531426341211 28788901973432297139511817)
  ·
    refine ⟨21591676480074222854633863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28788901973432297139511817 21591676480074222854633863)
    ·
      refine ⟨32387514720111334281950795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21591676480074222854633863 32387514720111334281950795)
      ·
        refine ⟨48581272080167001422926193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32387514720111334281950795 48581272080167001422926193)
        ·
          refine ⟨36435954060125251067194645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48581272080167001422926193 36435954060125251067194645)
          ·
            refine ⟨1707935346568371143774749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 36435954060125251067194645 1707935346568371143774749)
            ·
              refine ⟨640475754963139178915531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1707935346568371143774749 640475754963139178915531)
              ·
                refine ⟨960713632444708768373297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 640475754963139178915531 960713632444708768373297)
                ·
                  refine ⟨720535224333531576279973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 960713632444708768373297 720535224333531576279973)
                  ·
                    refine ⟨135100354562537170552495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 720535224333531576279973 135100354562537170552495)
                    ·
                      rfl

theorem cell23_789321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 2, 4].length) (baseStart_789321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789321 prefixEnd_789321 := by exact prefixLift 789321
  have htrace : WordTrace (prefixWord ++ tailWord_789321) baseStart_789321 baseEnd_789321 := by
    simpa [prefixWord, tailWord_789321, baseEnd_789321] using wordTrace_append hprefix tailTrace_789321
  have hstable : (prefixWord ++ tailWord_789321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789321).length < 2 ^ (prefixWord ++ tailWord_789321).sum := by decide
  have hdescent : baseEnd_789321 < baseStart_789321 := by decide
  rcases family_descends (prefixWord ++ tailWord_789321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789324 : List Nat := [2, 2, 1, 3, 3, 1, 3, 1, 1, 2, 4]
def baseStart_789324 : Nat := 118140960795 + 789324 * 2 ^ 59
def prefixEnd_789324 : Nat := 4983230072969 + 3 ^ 40 * 789324 * 2
def baseEnd_789324 : Nat := 405302604129574999919971

theorem tailTrace_789324 : CollatzResearch.WordTrace tailWord_789324 prefixEnd_789324 405302604129574999919971 := by
  unfold tailWord_789324
  simp only [CollatzResearch.WordTrace]
  refine ⟨14394505696210714325935513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19192674261614285767914017 14394505696210714325935513)
  ·
    refine ⟨10795879272158035744451635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14394505696210714325935513 10795879272158035744451635)
    ·
      refine ⟨16193818908237053616677453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10795879272158035744451635 16193818908237053616677453)
      ·
        refine ⟨6072682090588895106254045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16193818908237053616677453 6072682090588895106254045)
        ·
          refine ⟨2277255783970835664845267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6072682090588895106254045 2277255783970835664845267)
          ·
            refine ⟨3415883675956253497267901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2277255783970835664845267 3415883675956253497267901)
            ·
              refine ⟨1280956378483595061475463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3415883675956253497267901 1280956378483595061475463)
              ·
                refine ⟨1921434567725392592213195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1280956378483595061475463 1921434567725392592213195)
                ·
                  refine ⟨2882151851588088888319793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1921434567725392592213195 2882151851588088888319793)
                  ·
                    refine ⟨2161613888691066666239845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2882151851588088888319793 2161613888691066666239845)
                    ·
                      refine ⟨405302604129574999919971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2161613888691066666239845 405302604129574999919971)
                      ·
                        rfl

theorem cell23_789324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_789324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789324 prefixEnd_789324 := by exact prefixLift 789324
  have htrace : WordTrace (prefixWord ++ tailWord_789324) baseStart_789324 baseEnd_789324 := by
    simpa [prefixWord, tailWord_789324, baseEnd_789324] using wordTrace_append hprefix tailTrace_789324
  have hstable : (prefixWord ++ tailWord_789324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789324).length < 2 ^ (prefixWord ++ tailWord_789324).sum := by decide
  have hdescent : baseEnd_789324 < baseStart_789324 := by decide
  rcases family_descends (prefixWord ++ tailWord_789324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789344 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 6, 1, 3]
def baseStart_789344 : Nat := 118140960795 + 789344 * 2 ^ 59
def prefixEnd_789344 : Nat := 4983230072969 + 3 ^ 40 * 789344 * 2
def baseEnd_789344 : Nat := 405312873742664921669879

theorem tailTrace_789344 : CollatzResearch.WordTrace tailWord_789344 prefixEnd_789344 405312873742664921669879 := by
  unfold tailWord_789344
  simp only [CollatzResearch.WordTrace]
  refine ⟨14394870426174486033799543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19193160568232648045066057 14394870426174486033799543)
  ·
    refine ⟨21592305639261729050699315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14394870426174486033799543 21592305639261729050699315)
    ·
      refine ⟨32388458458892593576048973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21592305639261729050699315 32388458458892593576048973)
      ·
        refine ⟨12145671922084722591018365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32388458458892593576048973 12145671922084722591018365)
        ·
          refine ⟨4554626970781770971631887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12145671922084722591018365 4554626970781770971631887)
          ·
            refine ⟨6831940456172656457447831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4554626970781770971631887 6831940456172656457447831)
            ·
              refine ⟨10247910684258984686171747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6831940456172656457447831 10247910684258984686171747)
              ·
                refine ⟨15371866026388477029257621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10247910684258984686171747 15371866026388477029257621)
                ·
                  refine ⟨720556219986959860746451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15371866026388477029257621 720556219986959860746451)
                  ·
                    refine ⟨1080834329980439791119677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 720556219986959860746451 1080834329980439791119677)
                    ·
                      refine ⟨405312873742664921669879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1080834329980439791119677 405312873742664921669879)
                      ·
                        rfl

theorem cell23_789344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_789344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789344 prefixEnd_789344 := by exact prefixLift 789344
  have htrace : WordTrace (prefixWord ++ tailWord_789344) baseStart_789344 baseEnd_789344 := by
    simpa [prefixWord, tailWord_789344, baseEnd_789344] using wordTrace_append hprefix tailTrace_789344
  have hstable : (prefixWord ++ tailWord_789344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789344).length < 2 ^ (prefixWord ++ tailWord_789344).sum := by decide
  have hdescent : baseEnd_789344 < baseStart_789344 := by decide
  rcases family_descends (prefixWord ++ tailWord_789344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789357 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_789357 : Nat := 118140960795 + 789357 * 2 ^ 59
def prefixEnd_789357 : Nat := 4983230072969 + 3 ^ 40 * 789357 * 2
def baseEnd_789357 : Nat := 405319548991173370807319

theorem tailTrace_789357 : CollatzResearch.WordTrace tailWord_789357 prefixEnd_789357 405319548991173370807319 := by
  unfold tailWord_789357
  simp only [CollatzResearch.WordTrace]
  refine ⟨28790215001301875287822325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19193476667534583525214883 28790215001301875287822325)
  ·
    refine ⟨2699082656372050808233343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28790215001301875287822325 2699082656372050808233343)
    ·
      refine ⟨4048623984558076212350015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2699082656372050808233343 4048623984558076212350015)
      ·
        refine ⟨6072935976837114318525023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4048623984558076212350015 6072935976837114318525023)
        ·
          refine ⟨9109403965255671477787535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6072935976837114318525023 9109403965255671477787535)
          ·
            refine ⟨13664105947883507216681303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9109403965255671477787535 13664105947883507216681303)
            ·
              refine ⟨20496158921825260825021955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13664105947883507216681303 20496158921825260825021955)
              ·
                refine ⟨30744238382737891237532933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20496158921825260825021955 30744238382737891237532933)
                ·
                  refine ⟨5764544696763354607037425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30744238382737891237532933 5764544696763354607037425)
                  ·
                    refine ⟨4323408522572515955278069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5764544696763354607037425 4323408522572515955278069)
                    ·
                      refine ⟨405319548991173370807319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4323408522572515955278069 405319548991173370807319)
                      ·
                        rfl

theorem cell23_789357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_789357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789357 prefixEnd_789357 := by exact prefixLift 789357
  have htrace : WordTrace (prefixWord ++ tailWord_789357) baseStart_789357 baseEnd_789357 := by
    simpa [prefixWord, tailWord_789357, baseEnd_789357] using wordTrace_append hprefix tailTrace_789357
  have hstable : (prefixWord ++ tailWord_789357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789357).length < 2 ^ (prefixWord ++ tailWord_789357).sum := by decide
  have hdescent : baseEnd_789357 < baseStart_789357 := by decide
  rcases family_descends (prefixWord ++ tailWord_789357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789387 : List Nat := [1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 5]
def baseStart_789387 : Nat := 118140960795 + 789387 * 2 ^ 59
def prefixEnd_789387 : Nat := 4983230072969 + 3 ^ 40 * 789387 * 2
def baseEnd_789387 : Nat := 405334953410808253432181

theorem tailTrace_789387 : CollatzResearch.WordTrace tailWord_789387 prefixEnd_789387 405334953410808253432181 := by
  unfold tailWord_789387
  simp only [CollatzResearch.WordTrace]
  refine ⟨28791309191193190411414415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19194206127462126940942943 28791309191193190411414415)
  ·
    refine ⟨43186963786789785617121623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28791309191193190411414415 43186963786789785617121623)
    ·
      refine ⟨64780445680184678425682435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43186963786789785617121623 64780445680184678425682435)
      ·
        refine ⟨97170668520277017638523653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64780445680184678425682435 97170668520277017638523653)
        ·
          refine ⟨18219500347551940807223185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97170668520277017638523653 18219500347551940807223185)
          ·
            refine ⟨13664625260663955605417389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18219500347551940807223185 13664625260663955605417389)
            ·
              refine ⟨5124234472748983352031521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13664625260663955605417389 5124234472748983352031521)
              ·
                refine ⟨3843175854561737514023641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5124234472748983352031521 3843175854561737514023641)
                ·
                  refine ⟨2882381890921303135517731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3843175854561737514023641 2882381890921303135517731)
                  ·
                    refine ⟨4323572836381954703276597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2882381890921303135517731 4323572836381954703276597)
                    ·
                      refine ⟨405334953410808253432181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4323572836381954703276597 405334953410808253432181)
                      ·
                        rfl

theorem cell23_789387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 5].length) (baseStart_789387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789387 prefixEnd_789387 := by exact prefixLift 789387
  have htrace : WordTrace (prefixWord ++ tailWord_789387) baseStart_789387 baseEnd_789387 := by
    simpa [prefixWord, tailWord_789387, baseEnd_789387] using wordTrace_append hprefix tailTrace_789387
  have hstable : (prefixWord ++ tailWord_789387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789387).length < 2 ^ (prefixWord ++ tailWord_789387).sum := by decide
  have hdescent : baseEnd_789387 < baseStart_789387 := by decide
  rcases family_descends (prefixWord ++ tailWord_789387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789434 : List Nat := [3, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3]
def baseStart_789434 : Nat := 118140960795 + 789434 * 2 ^ 59
def prefixEnd_789434 : Nat := 4983230072969 + 3 ^ 40 * 789434 * 2
def baseEnd_789434 : Nat := 405359087001569569544465

theorem tailTrace_789434 : CollatzResearch.WordTrace tailWord_789434 prefixEnd_789434 405359087001569569544465 := by
  unfold tailWord_789434
  simp only [CollatzResearch.WordTrace]
  refine ⟨7198255855505729359593839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19195348948015278292250237 7198255855505729359593839)
  ·
    refine ⟨10797383783258594039390759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7198255855505729359593839 10797383783258594039390759)
    ·
      refine ⟨16196075674887891059086139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10797383783258594039390759 16196075674887891059086139)
      ·
        refine ⟨24294113512331836588629209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16196075674887891059086139 24294113512331836588629209)
        ·
          refine ⟨18220585134248877441471907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24294113512331836588629209 18220585134248877441471907)
          ·
            refine ⟨27330877701373316162207861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18220585134248877441471907 27330877701373316162207861)
            ·
              refine ⟨2562269784503748390206987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27330877701373316162207861 2562269784503748390206987)
              ·
                refine ⟨3843404676755622585310481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2562269784503748390206987 3843404676755622585310481)
                ·
                  refine ⟨2882553507566716938982861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3843404676755622585310481 2882553507566716938982861)
                  ·
                    refine ⟨1080957565337518852118573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2882553507566716938982861 1080957565337518852118573)
                    ·
                      refine ⟨405359087001569569544465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1080957565337518852118573 405359087001569569544465)
                      ·
                        rfl

theorem cell23_789434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3].length) (baseStart_789434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789434 prefixEnd_789434 := by exact prefixLift 789434
  have htrace : WordTrace (prefixWord ++ tailWord_789434) baseStart_789434 baseEnd_789434 := by
    simpa [prefixWord, tailWord_789434, baseEnd_789434] using wordTrace_append hprefix tailTrace_789434
  have hstable : (prefixWord ++ tailWord_789434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789434).length < 2 ^ (prefixWord ++ tailWord_789434).sum := by decide
  have hdescent : baseEnd_789434 < baseStart_789434 := by decide
  rcases family_descends (prefixWord ++ tailWord_789434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789447 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 7]
def baseStart_789447 : Nat := 118140960795 + 789447 * 2 ^ 59
def prefixEnd_789447 : Nat := 4983230072969 + 3 ^ 40 * 789447 * 2
def baseEnd_789447 : Nat := 405365762250078018681905

theorem tailTrace_789447 : CollatzResearch.WordTrace tailWord_789447 prefixEnd_789447 405365762250078018681905 := by
  unfold tailWord_789447
  simp only [CollatzResearch.WordTrace]
  refine ⟨28793497570975820658598595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19195665047317213772399063 28793497570975820658598595)
  ·
    refine ⟨43190246356463730987897893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28793497570975820658598595 43190246356463730987897893)
    ·
      refine ⟨8098171191836949560230855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43190246356463730987897893 8098171191836949560230855)
      ·
        refine ⟨12147256787755424340346283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8098171191836949560230855 12147256787755424340346283)
        ·
          refine ⟨18220885181633136510519425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12147256787755424340346283 18220885181633136510519425)
          ·
            refine ⟨13665663886224852382889569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18220885181633136510519425 13665663886224852382889569)
            ·
              refine ⟨10249247914668639287167177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13665663886224852382889569 10249247914668639287167177)
              ·
                refine ⟨7686935936001479465375383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10249247914668639287167177 7686935936001479465375383)
                ·
                  refine ⟨11530403904002219198063075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7686935936001479465375383 11530403904002219198063075)
                  ·
                    refine ⟨17295605856003328797094613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11530403904002219198063075 17295605856003328797094613)
                    ·
                      refine ⟨405365762250078018681905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 17295605856003328797094613 405365762250078018681905)
                      ·
                        rfl

theorem cell23_789447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_789447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789447 prefixEnd_789447 := by exact prefixLift 789447
  have htrace : WordTrace (prefixWord ++ tailWord_789447) baseStart_789447 baseEnd_789447 := by
    simpa [prefixWord, tailWord_789447, baseEnd_789447] using wordTrace_append hprefix tailTrace_789447
  have hstable : (prefixWord ++ tailWord_789447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789447).length < 2 ^ (prefixWord ++ tailWord_789447).sum := by decide
  have hdescent : baseEnd_789447 < baseStart_789447 := by decide
  rcases family_descends (prefixWord ++ tailWord_789447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789454 : List Nat := [4, 1, 1, 1, 2, 4, 1, 1, 1, 7]
def baseStart_789454 : Nat := 118140960795 + 789454 * 2 ^ 59
def prefixEnd_789454 : Nat := 4983230072969 + 3 ^ 40 * 789454 * 2
def baseEnd_789454 : Nat := 135123118871553163764791

theorem tailTrace_789454 : CollatzResearch.WordTrace tailWord_789454 prefixEnd_789454 135123118871553163764791 := by
  unfold tailWord_789454
  simp only [CollatzResearch.WordTrace]
  refine ⟨3599219110243807606762927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19195835254633640569402277 3599219110243807606762927)
  ·
    refine ⟨5398828665365711410144391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3599219110243807606762927 5398828665365711410144391)
    ·
      refine ⟨8098242998048567115216587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5398828665365711410144391 8098242998048567115216587)
      ·
        refine ⟨12147364497072850672824881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8098242998048567115216587 12147364497072850672824881)
        ·
          refine ⟨9110523372804638004618661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12147364497072850672824881 9110523372804638004618661)
          ·
            refine ⟨1708223132400869625865999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9110523372804638004618661 1708223132400869625865999)
            ·
              refine ⟨2562334698601304438798999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1708223132400869625865999 2562334698601304438798999)
              ·
                refine ⟨3843502047901956658198499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2562334698601304438798999 3843502047901956658198499)
                ·
                  refine ⟨5765253071852934987297749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3843502047901956658198499 5765253071852934987297749)
                  ·
                    refine ⟨135123118871553163764791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5765253071852934987297749 135123118871553163764791)
                    ·
                      rfl

theorem cell23_789454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_789454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789454 prefixEnd_789454 := by exact prefixLift 789454
  have htrace : WordTrace (prefixWord ++ tailWord_789454) baseStart_789454 baseEnd_789454 := by
    simpa [prefixWord, tailWord_789454, baseEnd_789454] using wordTrace_append hprefix tailTrace_789454
  have hstable : (prefixWord ++ tailWord_789454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789454).length < 2 ^ (prefixWord ++ tailWord_789454).sum := by decide
  have hdescent : baseEnd_789454 < baseStart_789454 := by decide
  rcases family_descends (prefixWord ++ tailWord_789454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789458 : List Nat := [3, 2, 2, 3, 1, 2, 2, 3, 5]
def baseStart_789458 : Nat := 118140960795 + 789458 * 2 ^ 59
def prefixEnd_789458 : Nat := 4983230072969 + 3 ^ 40 * 789458 * 2
def baseEnd_789458 : Nat := 45041267837475275071595

theorem tailTrace_789458 : CollatzResearch.WordTrace tailWord_789458 prefixEnd_789458 45041267837475275071595 := by
  unfold tailWord_789458
  simp only [CollatzResearch.WordTrace]
  refine ⟨7198474693483992384312257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19195932515957313024832685 7198474693483992384312257)
  ·
    refine ⟨5398856020112994288234193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7198474693483992384312257 5398856020112994288234193)
    ·
      refine ⟨4049142015084745716175645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5398856020112994288234193 4049142015084745716175645)
      ·
        refine ⟨1518428255656779643565867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4049142015084745716175645 1518428255656779643565867)
        ·
          refine ⟨2277642383485169465348801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1518428255656779643565867 2277642383485169465348801)
          ·
            refine ⟨1708231787613877099011601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2277642383485169465348801 1708231787613877099011601)
            ·
              refine ⟨1281173840710407824258701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1708231787613877099011601 1281173840710407824258701)
              ·
                refine ⟨480440190266402934097013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1281173840710407824258701 480440190266402934097013)
                ·
                  refine ⟨45041267837475275071595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 480440190266402934097013 45041267837475275071595)
                  ·
                    rfl

theorem cell23_789458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3, 5].length) (baseStart_789458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789458 prefixEnd_789458 := by exact prefixLift 789458
  have htrace : WordTrace (prefixWord ++ tailWord_789458) baseStart_789458 baseEnd_789458 := by
    simpa [prefixWord, tailWord_789458, baseEnd_789458] using wordTrace_append hprefix tailTrace_789458
  have hstable : (prefixWord ++ tailWord_789458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789458).length < 2 ^ (prefixWord ++ tailWord_789458).sum := by decide
  have hdescent : baseEnd_789458 < baseStart_789458 := by decide
  rcases family_descends (prefixWord ++ tailWord_789458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789507 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 9]
def baseStart_789507 : Nat := 118140960795 + 789507 * 2 ^ 59
def prefixEnd_789507 : Nat := 4983230072969 + 3 ^ 40 * 789507 * 2
def baseEnd_789507 : Nat := 405396571089347783931629

theorem tailTrace_789507 : CollatzResearch.WordTrace tailWord_789507 prefixEnd_789507 405396571089347783931629 := by
  unfold tailWord_789507
  simp only [CollatzResearch.WordTrace]
  refine ⟨28795685950758450905782775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19197123967172300603855183 28795685950758450905782775)
  ·
    refine ⟨43193528926137676358674163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28795685950758450905782775 43193528926137676358674163)
    ·
      refine ⟨64790293389206514538011245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43193528926137676358674163 64790293389206514538011245)
      ·
        refine ⟨24296360020952442951754217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64790293389206514538011245 24296360020952442951754217)
        ·
          refine ⟨18222270015714332213815663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24296360020952442951754217 18222270015714332213815663)
          ·
            refine ⟨27333405023571498320723495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18222270015714332213815663 27333405023571498320723495)
            ·
              refine ⟨41000107535357247481085243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27333405023571498320723495 41000107535357247481085243)
              ·
                refine ⟨61500161303035871221627865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41000107535357247481085243 61500161303035871221627865)
                ·
                  refine ⟨46125120977276903416220899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61500161303035871221627865 46125120977276903416220899)
                  ·
                    refine ⟨69187681465915355124331349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46125120977276903416220899 69187681465915355124331349)
                    ·
                      refine ⟨405396571089347783931629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 69187681465915355124331349 405396571089347783931629)
                      ·
                        rfl

theorem cell23_789507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_789507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789507 prefixEnd_789507 := by exact prefixLift 789507
  have htrace : WordTrace (prefixWord ++ tailWord_789507) baseStart_789507 baseEnd_789507 := by
    simpa [prefixWord, tailWord_789507, baseEnd_789507] using wordTrace_append hprefix tailTrace_789507
  have hstable : (prefixWord ++ tailWord_789507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789507).length < 2 ^ (prefixWord ++ tailWord_789507).sum := by decide
  have hdescent : baseEnd_789507 < baseStart_789507 := by decide
  rcases family_descends (prefixWord ++ tailWord_789507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789511 : List Nat := [1, 1, 4, 3, 1, 1, 2, 3, 2, 2, 3]
def baseStart_789511 : Nat := 118140960795 + 789511 * 2 ^ 59
def prefixEnd_789511 : Nat := 4983230072969 + 3 ^ 40 * 789511 * 2
def baseEnd_789511 : Nat := 405398625011965768281611

theorem tailTrace_789511 : CollatzResearch.WordTrace tailWord_789511 prefixEnd_789511 405398625011965768281611 := by
  unfold tailWord_789511
  simp only [CollatzResearch.WordTrace]
  refine ⟨28795831842743959588928387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19197221228495973059285591 28795831842743959588928387)
  ·
    refine ⟨43193747764115939383392581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28795831842743959588928387 43193747764115939383392581)
    ·
      refine ⟨8098827705771738634386109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43193747764115939383392581 8098827705771738634386109)
      ·
        refine ⟨3037060389664401987894791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8098827705771738634386109 3037060389664401987894791)
        ·
          refine ⟨4555590584496602981842187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3037060389664401987894791 4555590584496602981842187)
          ·
            refine ⟨6833385876744904472763281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4555590584496602981842187 6833385876744904472763281)
            ·
              refine ⟨5125039407558678354572461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6833385876744904472763281 5125039407558678354572461)
              ·
                refine ⟨1921889777834504382964673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5125039407558678354572461 1921889777834504382964673)
                ·
                  refine ⟨1441417333375878287223505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1921889777834504382964673 1441417333375878287223505)
                  ·
                    refine ⟨1081063000031908715417629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1441417333375878287223505 1081063000031908715417629)
                    ·
                      refine ⟨405398625011965768281611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1081063000031908715417629 405398625011965768281611)
                      ·
                        rfl

theorem cell23_789511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_789511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789511 prefixEnd_789511 := by exact prefixLift 789511
  have htrace : WordTrace (prefixWord ++ tailWord_789511) baseStart_789511 baseEnd_789511 := by
    simpa [prefixWord, tailWord_789511, baseEnd_789511] using wordTrace_append hprefix tailTrace_789511
  have hstable : (prefixWord ++ tailWord_789511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789511).length < 2 ^ (prefixWord ++ tailWord_789511).sum := by decide
  have hdescent : baseEnd_789511 < baseStart_789511 := by decide
  rcases family_descends (prefixWord ++ tailWord_789511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789514 : List Nat := [3, 1, 2, 2, 3, 1, 1, 2, 8]
def baseStart_789514 : Nat := 118140960795 + 789514 * 2 ^ 59
def prefixEnd_789514 : Nat := 4983230072969 + 3 ^ 40 * 789514 * 2
def baseEnd_789514 : Nat := 45044462828214361838233

theorem tailTrace_789514 : CollatzResearch.WordTrace tailWord_789514 prefixEnd_789514 45044462828214361838233 := by
  unfold tailWord_789514
  simp only [CollatzResearch.WordTrace]
  refine ⟨7198985315433272775321899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19197294174488727400858397 7198985315433272775321899)
  ·
    refine ⟨10798477973149909162982849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7198985315433272775321899 10798477973149909162982849)
    ·
      refine ⟨8098858479862431872237137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10798477973149909162982849 8098858479862431872237137)
      ·
        refine ⟨6074143859896823904177853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8098858479862431872237137 6074143859896823904177853)
        ·
          refine ⟨2277803947461308964066695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6074143859896823904177853 2277803947461308964066695)
          ·
            refine ⟨3416705921191963446100043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2277803947461308964066695 3416705921191963446100043)
            ·
              refine ⟨5125058881787945169150065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3416705921191963446100043 5125058881787945169150065)
              ·
                refine ⟨3843794161340958876862549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5125058881787945169150065 3843794161340958876862549)
                ·
                  refine ⟨45044462828214361838233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3843794161340958876862549 45044462828214361838233)
                  ·
                    rfl

theorem cell23_789514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 8].length) (baseStart_789514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789514 prefixEnd_789514 := by exact prefixLift 789514
  have htrace : WordTrace (prefixWord ++ tailWord_789514) baseStart_789514 baseEnd_789514 := by
    simpa [prefixWord, tailWord_789514, baseEnd_789514] using wordTrace_append hprefix tailTrace_789514
  have hstable : (prefixWord ++ tailWord_789514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789514).length < 2 ^ (prefixWord ++ tailWord_789514).sum := by decide
  have hdescent : baseEnd_789514 < baseStart_789514 := by decide
  rcases family_descends (prefixWord ++ tailWord_789514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789535 : List Nat := [1, 1, 2, 4, 1, 4, 3, 2, 1, 4]
def baseStart_789535 : Nat := 118140960795 + 789535 * 2 ^ 59
def prefixEnd_789535 : Nat := 4983230072969 + 3 ^ 40 * 789535 * 2
def baseEnd_789535 : Nat := 135136982849224558127167

theorem tailTrace_789535 : CollatzResearch.WordTrace tailWord_789535 prefixEnd_789535 135136982849224558127167 := by
  unfold tailWord_789535
  simp only [CollatzResearch.WordTrace]
  refine ⟨28796707194657011687802059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19197804796438007791868039 28796707194657011687802059)
  ·
    refine ⟨43195060791985517531703089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28796707194657011687802059 43195060791985517531703089)
    ·
      refine ⟨32396295593989138148777317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43195060791985517531703089 32396295593989138148777317)
      ·
        refine ⟨6074305423872963402895747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32396295593989138148777317 6074305423872963402895747)
        ·
          refine ⟨9111458135809445104343621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6074305423872963402895747 9111458135809445104343621)
          ·
            refine ⟨1708398400464270957064429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9111458135809445104343621 1708398400464270957064429)
            ·
              refine ⟨640649400174101608899161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1708398400464270957064429 640649400174101608899161)
              ·
                refine ⟨480487050130576206674371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640649400174101608899161 480487050130576206674371)
                ·
                  refine ⟨720730575195864310011557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 480487050130576206674371 720730575195864310011557)
                  ·
                    refine ⟨135136982849224558127167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 720730575195864310011557 135136982849224558127167)
                    ·
                      rfl

theorem cell23_789535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2, 1, 4].length) (baseStart_789535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789535 prefixEnd_789535 := by exact prefixLift 789535
  have htrace : WordTrace (prefixWord ++ tailWord_789535) baseStart_789535 baseEnd_789535 := by
    simpa [prefixWord, tailWord_789535, baseEnd_789535] using wordTrace_append hprefix tailTrace_789535
  have hstable : (prefixWord ++ tailWord_789535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789535).length < 2 ^ (prefixWord ++ tailWord_789535).sum := by decide
  have hdescent : baseEnd_789535 < baseStart_789535 := by decide
  rcases family_descends (prefixWord ++ tailWord_789535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789561 : List Nat := [1, 2, 1, 5, 2, 2, 1, 1, 3, 5]
def baseStart_789561 : Nat := 118140960795 + 789561 * 2 ^ 59
def prefixEnd_789561 : Nat := 4983230072969 + 3 ^ 40 * 789561 * 2
def baseEnd_789561 : Nat := 135141433014896857552127

theorem tailTrace_789561 : CollatzResearch.WordTrace tailWord_789561 prefixEnd_789561 135141433014896857552127 := by
  unfold tailWord_789561
  simp only [CollatzResearch.WordTrace]
  refine ⟨28797655492562818128248537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19198436995041878752165691 28797655492562818128248537)
  ·
    refine ⟨21598241619422113596186403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28797655492562818128248537 21598241619422113596186403)
    ·
      refine ⟨32397362429133170394279605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21598241619422113596186403 32397362429133170394279605)
      ·
        refine ⟨3037252727731234724463713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32397362429133170394279605 3037252727731234724463713)
        ·
          refine ⟨2277939545798426043347785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3037252727731234724463713 2277939545798426043347785)
          ·
            refine ⟨1708454659348819532510839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2277939545798426043347785 1708454659348819532510839)
            ·
              refine ⟨2562681989023229298766259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1708454659348819532510839 2562681989023229298766259)
              ·
                refine ⟨3844022983534843948149389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2562681989023229298766259 3844022983534843948149389)
                ·
                  refine ⟨1441508618825566480556021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3844022983534843948149389 1441508618825566480556021)
                  ·
                    refine ⟨135141433014896857552127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1441508618825566480556021 135141433014896857552127)
                    ·
                      rfl

theorem cell23_789561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 5].length) (baseStart_789561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789561 prefixEnd_789561 := by exact prefixLift 789561
  have htrace : WordTrace (prefixWord ++ tailWord_789561) baseStart_789561 baseEnd_789561 := by
    simpa [prefixWord, tailWord_789561, baseEnd_789561] using wordTrace_append hprefix tailTrace_789561
  have hstable : (prefixWord ++ tailWord_789561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789561).length < 2 ^ (prefixWord ++ tailWord_789561).sum := by decide
  have hdescent : baseEnd_789561 < baseStart_789561 := by decide
  rcases family_descends (prefixWord ++ tailWord_789561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789568 : List Nat := [2, 1, 1, 2, 2, 3, 4, 1, 2, 3, 2]
def baseStart_789568 : Nat := 118140960795 + 789568 * 2 ^ 59
def prefixEnd_789568 : Nat := 4983230072969 + 3 ^ 40 * 789568 * 2
def baseEnd_789568 : Nat := 405427893409272045268849

theorem tailTrace_789568 : CollatzResearch.WordTrace tailWord_789568 prefixEnd_789568 405427893409272045268849 := by
  unfold tailWord_789568
  simp only [CollatzResearch.WordTrace]
  refine ⟨14398955401768729161876679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19198607202358305549168905 14398955401768729161876679)
  ·
    refine ⟨21598433102653093742815019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14398955401768729161876679 21598433102653093742815019)
    ·
      refine ⟨32397649653979640614222529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21598433102653093742815019 32397649653979640614222529)
      ·
        refine ⟨24298237240484730460666897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32397649653979640614222529 24298237240484730460666897)
        ·
          refine ⟨18223677930363547845500173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24298237240484730460666897 18223677930363547845500173)
          ·
            refine ⟨6833879223886330442062565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18223677930363547845500173 6833879223886330442062565)
            ·
              refine ⟨1281352354478686957886731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6833879223886330442062565 1281352354478686957886731)
              ·
                refine ⟨1922028531718030436830097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1281352354478686957886731 1922028531718030436830097)
                ·
                  refine ⟨1441521398788522827622573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1922028531718030436830097 1441521398788522827622573)
                  ·
                    refine ⟨540570524545696060358465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1441521398788522827622573 540570524545696060358465)
                    ·
                      refine ⟨405427893409272045268849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 540570524545696060358465 405427893409272045268849)
                      ·
                        rfl

theorem cell23_789568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 2, 3, 2].length) (baseStart_789568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789568 prefixEnd_789568 := by exact prefixLift 789568
  have htrace : WordTrace (prefixWord ++ tailWord_789568) baseStart_789568 baseEnd_789568 := by
    simpa [prefixWord, tailWord_789568, baseEnd_789568] using wordTrace_append hprefix tailTrace_789568
  have hstable : (prefixWord ++ tailWord_789568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789568).length < 2 ^ (prefixWord ++ tailWord_789568).sum := by decide
  have hdescent : baseEnd_789568 < baseStart_789568 := by decide
  rcases family_descends (prefixWord ++ tailWord_789568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789594 : List Nat := [3, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6]
def baseStart_789594 : Nat := 118140960795 + 789594 * 2 ^ 59
def prefixEnd_789594 : Nat := 4983230072969 + 3 ^ 40 * 789594 * 2
def baseEnd_789594 : Nat := 405441243906288943543729

theorem tailTrace_789594 : CollatzResearch.WordTrace tailWord_789594 prefixEnd_789594 405441243906288943543729 := by
  unfold tailWord_789594
  simp only [CollatzResearch.WordTrace]
  refine ⟨7199714775360816191049959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19199239400962176509466557 7199714775360816191049959)
  ·
    refine ⟨10799572163041224286574939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7199714775360816191049959 10799572163041224286574939)
    ·
      refine ⟨16199358244561836429862409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10799572163041224286574939 16199358244561836429862409)
      ·
        refine ⟨12149518683421377322396807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16199358244561836429862409 12149518683421377322396807)
        ·
          refine ⟨18224278025132065983595211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12149518683421377322396807 18224278025132065983595211)
          ·
            refine ⟨27336417037698098975392817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18224278025132065983595211 27336417037698098975392817)
            ·
              refine ⟨20502312778273574231544613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27336417037698098975392817 20502312778273574231544613)
              ·
                refine ⟨3844183645926295168414615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20502312778273574231544613 3844183645926295168414615)
                ·
                  refine ⟨5766275468889442752621923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3844183645926295168414615 5766275468889442752621923)
                  ·
                    refine ⟨8649413203334164128932885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5766275468889442752621923 8649413203334164128932885)
                    ·
                      refine ⟨405441243906288943543729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8649413203334164128932885 405441243906288943543729)
                      ·
                        rfl

theorem cell23_789594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_789594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789594 prefixEnd_789594 := by exact prefixLift 789594
  have htrace : WordTrace (prefixWord ++ tailWord_789594) baseStart_789594 baseEnd_789594 := by
    simpa [prefixWord, tailWord_789594, baseEnd_789594] using wordTrace_append hprefix tailTrace_789594
  have hstable : (prefixWord ++ tailWord_789594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789594).length < 2 ^ (prefixWord ++ tailWord_789594).sum := by decide
  have hdescent : baseEnd_789594 < baseStart_789594 := by decide
  rcases family_descends (prefixWord ++ tailWord_789594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789601 : List Nat := [1, 2, 3, 1, 1, 2, 3, 2, 3, 2, 3]
def baseStart_789601 : Nat := 118140960795 + 789601 * 2 ^ 59
def prefixEnd_789601 : Nat := 4983230072969 + 3 ^ 40 * 789601 * 2
def baseEnd_789601 : Nat := 405444838270870416156197

theorem tailTrace_789601 : CollatzResearch.WordTrace tailWord_789601 prefixEnd_789601 405444838270870416156197 := by
  unfold tailWord_789601
  simp only [CollatzResearch.WordTrace]
  refine ⟨28799114412417904959704657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19199409608278603306469771 28799114412417904959704657)
  ·
    refine ⟨21599335809313428719778493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28799114412417904959704657 21599335809313428719778493)
    ·
      refine ⟨8099750928492535769916935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21599335809313428719778493 8099750928492535769916935)
      ·
        refine ⟨12149626392738803654875403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8099750928492535769916935 12149626392738803654875403)
        ·
          refine ⟨18224439589108205482313105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12149626392738803654875403 18224439589108205482313105)
          ·
            refine ⟨13668329691831154111734829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18224439589108205482313105 13668329691831154111734829)
            ·
              refine ⟨5125623634436682791900561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13668329691831154111734829 5125623634436682791900561)
              ·
                refine ⟨3844217725827512093925421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5125623634436682791900561 3844217725827512093925421)
                ·
                  refine ⟨1441581647185317035222033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3844217725827512093925421 1441581647185317035222033)
                  ·
                    refine ⟨1081186235388987776416525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1441581647185317035222033 1081186235388987776416525)
                    ·
                      refine ⟨405444838270870416156197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1081186235388987776416525 405444838270870416156197)
                      ·
                        rfl

theorem cell23_789601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_789601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789601 prefixEnd_789601 := by exact prefixLift 789601
  have htrace : WordTrace (prefixWord ++ tailWord_789601) baseStart_789601 baseEnd_789601 := by
    simpa [prefixWord, tailWord_789601, baseEnd_789601] using wordTrace_append hprefix tailTrace_789601
  have hstable : (prefixWord ++ tailWord_789601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789601).length < 2 ^ (prefixWord ++ tailWord_789601).sum := by decide
  have hdescent : baseEnd_789601 < baseStart_789601 := by decide
  rcases family_descends (prefixWord ++ tailWord_789601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789618 : List Nat := [3, 2, 1, 2, 2, 1, 2, 4, 1, 2, 3]
def baseStart_789618 : Nat := 118140960795 + 789618 * 2 ^ 59
def prefixEnd_789618 : Nat := 4983230072969 + 3 ^ 40 * 789618 * 2
def baseEnd_789618 : Nat := 405453567441996849643619

theorem tailTrace_789618 : CollatzResearch.WordTrace tailWord_789618 prefixEnd_789618 405453567441996849643619 := by
  unfold tailWord_789618
  simp only [CollatzResearch.WordTrace]
  refine ⟨7199933613339079215768377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19199822968904211242049005 7199933613339079215768377)
  ·
    refine ⟨5399950210004309411826283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7199933613339079215768377 5399950210004309411826283)
    ·
      refine ⟨8099925315006464117739425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5399950210004309411826283 8099925315006464117739425)
      ·
        refine ⟨6074943986254848088304569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8099925315006464117739425 6074943986254848088304569)
        ·
          refine ⟨4556207989691136066228427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6074943986254848088304569 4556207989691136066228427)
          ·
            refine ⟨6834311984536704099342641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4556207989691136066228427 6834311984536704099342641)
            ·
              refine ⟨5125733988402528074506981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6834311984536704099342641 5125733988402528074506981)
              ·
                refine ⟨961075122825474013970059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5125733988402528074506981 961075122825474013970059)
                ·
                  refine ⟨1441612684238211020955089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 961075122825474013970059 1441612684238211020955089)
                  ·
                    refine ⟨1081209513178658265716317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1441612684238211020955089 1081209513178658265716317)
                    ·
                      refine ⟨405453567441996849643619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1081209513178658265716317 405453567441996849643619)
                      ·
                        rfl

theorem cell23_789618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_789618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789618 prefixEnd_789618 := by exact prefixLift 789618
  have htrace : WordTrace (prefixWord ++ tailWord_789618) baseStart_789618 baseEnd_789618 := by
    simpa [prefixWord, tailWord_789618, baseEnd_789618] using wordTrace_append hprefix tailTrace_789618
  have hstable : (prefixWord ++ tailWord_789618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789618).length < 2 ^ (prefixWord ++ tailWord_789618).sum := by decide
  have hdescent : baseEnd_789618 < baseStart_789618 := by decide
  rcases family_descends (prefixWord ++ tailWord_789618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789648 : List Nat := [2, 1, 1, 1, 1, 1, 4, 6, 2, 1, 3]
def baseStart_789648 : Nat := 118140960795 + 789648 * 2 ^ 59
def prefixEnd_789648 : Nat := 4983230072969 + 3 ^ 40 * 789648 * 2
def baseEnd_789648 : Nat := 405468971861631732268481

theorem tailTrace_789648 : CollatzResearch.WordTrace tailWord_789648 prefixEnd_789648 405468971861631732268481 := by
  unfold tailWord_789648
  simp only [CollatzResearch.WordTrace]
  refine ⟨14400414321623815993332799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19200552428831754657777065 14400414321623815993332799)
  ·
    refine ⟨21600621482435723989999199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14400414321623815993332799 21600621482435723989999199)
    ·
      refine ⟨32400932223653585984998799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21600621482435723989999199 32400932223653585984998799)
      ·
        refine ⟨48601398335480378977498199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32400932223653585984998799 48601398335480378977498199)
        ·
          refine ⟨72902097503220568466247299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48601398335480378977498199 72902097503220568466247299)
          ·
            refine ⟨109353146254830852699370949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72902097503220568466247299 109353146254830852699370949)
            ·
              refine ⟨20503714922780784881132053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109353146254830852699370949 20503714922780784881132053)
              ·
                refine ⟨961111637005349291303065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20503714922780784881132053 961111637005349291303065)
                ·
                  refine ⟨720833727754011968477299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 961111637005349291303065 720833727754011968477299)
                  ·
                    refine ⟨1081250591631017952715949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 720833727754011968477299 1081250591631017952715949)
                    ·
                      refine ⟨405468971861631732268481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1081250591631017952715949 405468971861631732268481)
                      ·
                        rfl

theorem cell23_789648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 2, 1, 3].length) (baseStart_789648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789648 prefixEnd_789648 := by exact prefixLift 789648
  have htrace : WordTrace (prefixWord ++ tailWord_789648) baseStart_789648 baseEnd_789648 := by
    simpa [prefixWord, tailWord_789648, baseEnd_789648] using wordTrace_append hprefix tailTrace_789648
  have hstable : (prefixWord ++ tailWord_789648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789648).length < 2 ^ (prefixWord ++ tailWord_789648).sum := by decide
  have hdescent : baseEnd_789648 < baseStart_789648 := by decide
  rcases family_descends (prefixWord ++ tailWord_789648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789716 : List Nat := [2, 4, 1, 4, 1, 2, 2, 1, 2, 1, 3]
def baseStart_789716 : Nat := 118140960795 + 789716 * 2 ^ 59
def prefixEnd_789716 : Nat := 4983230072969 + 3 ^ 40 * 789716 * 2
def baseEnd_789716 : Nat := 405503888546137466218169

theorem tailTrace_789716 : CollatzResearch.WordTrace tailWord_789716 prefixEnd_789716 405503888546137466218169 := by
  unfold tailWord_789716
  simp only [CollatzResearch.WordTrace]
  refine ⟨14401654403500639800070501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19202205871334186400094001 14401654403500639800070501)
  ·
    refine ⟨2700310200656369962513219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14401654403500639800070501 2700310200656369962513219)
    ·
      refine ⟨4050465300984554943769829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2700310200656369962513219 4050465300984554943769829)
      ·
        refine ⟨759462243934604051956843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4050465300984554943769829 759462243934604051956843)
        ·
          refine ⟨1139193365901906077935265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759462243934604051956843 1139193365901906077935265)
          ·
            refine ⟨854395024426429558451449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1139193365901906077935265 854395024426429558451449)
            ·
              refine ⟨640796268319822168838587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 854395024426429558451449 640796268319822168838587)
              ·
                refine ⟨961194402479733253257881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 640796268319822168838587 961194402479733253257881)
                ·
                  refine ⟨720895801859799939943411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 961194402479733253257881 720895801859799939943411)
                  ·
                    refine ⟨1081343702789699909915117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 720895801859799939943411 1081343702789699909915117)
                    ·
                      refine ⟨405503888546137466218169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1081343702789699909915117 405503888546137466218169)
                      ·
                        rfl

theorem cell23_789716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_789716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789716 prefixEnd_789716 := by exact prefixLift 789716
  have htrace : WordTrace (prefixWord ++ tailWord_789716) baseStart_789716 baseEnd_789716 := by
    simpa [prefixWord, tailWord_789716, baseEnd_789716] using wordTrace_append hprefix tailTrace_789716
  have hstable : (prefixWord ++ tailWord_789716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789716).length < 2 ^ (prefixWord ++ tailWord_789716).sum := by decide
  have hdescent : baseEnd_789716 < baseStart_789716 := by decide
  rcases family_descends (prefixWord ++ tailWord_789716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789721 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 1, 5, 3]
def baseStart_789721 : Nat := 118140960795 + 789721 * 2 ^ 59
def prefixEnd_789721 : Nat := 4983230072969 + 3 ^ 40 * 789721 * 2
def baseEnd_789721 : Nat := 405506455949409946655645

theorem tailTrace_789721 : CollatzResearch.WordTrace tailWord_789721 prefixEnd_789721 405506455949409946655645 := by
  unfold tailWord_789721
  simp only [CollatzResearch.WordTrace]
  refine ⟨28803491171983165454073017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19202327447988776969382011 28803491171983165454073017)
  ·
    refine ⟨21602618378987374090554763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28803491171983165454073017 21602618378987374090554763)
    ·
      refine ⟨32403927568481061135832145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21602618378987374090554763 32403927568481061135832145)
      ·
        refine ⟨24302945676360795851874109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32403927568481061135832145 24302945676360795851874109)
        ·
          refine ⟨9113604628635298444452791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24302945676360795851874109 9113604628635298444452791)
          ·
            refine ⟨13670406942952947666679187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9113604628635298444452791 13670406942952947666679187)
            ·
              refine ⟨20505610414429421500018781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13670406942952947666679187 20505610414429421500018781)
              ·
                refine ⟨7689603905411033062507043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20505610414429421500018781 7689603905411033062507043)
                ·
                  refine ⟨11534405858116549593760565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7689603905411033062507043 11534405858116549593760565)
                  ·
                    refine ⟨1081350549198426524415053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11534405858116549593760565 1081350549198426524415053)
                    ·
                      refine ⟨405506455949409946655645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1081350549198426524415053 405506455949409946655645)
                      ·
                        rfl

theorem cell23_789721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 5, 3].length) (baseStart_789721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789721 prefixEnd_789721 := by exact prefixLift 789721
  have htrace : WordTrace (prefixWord ++ tailWord_789721) baseStart_789721 baseEnd_789721 := by
    simpa [prefixWord, tailWord_789721, baseEnd_789721] using wordTrace_append hprefix tailTrace_789721
  have hstable : (prefixWord ++ tailWord_789721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789721).length < 2 ^ (prefixWord ++ tailWord_789721).sum := by decide
  have hdescent : baseEnd_789721 < baseStart_789721 := by decide
  rcases family_descends (prefixWord ++ tailWord_789721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789762 : List Nat := [3, 4, 1, 1, 3, 1, 1, 4, 5]
def baseStart_789762 : Nat := 118140960795 + 789762 * 2 ^ 59
def prefixEnd_789762 : Nat := 4983230072969 + 3 ^ 40 * 789762 * 2
def baseEnd_789762 : Nat := 45058612072916031804773

theorem tailTrace_789762 : CollatzResearch.WordTrace tailWord_789762 prefixEnd_789762 45058612072916031804773 := by
  unfold tailWord_789762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7201246641208657364078885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19203324376556419637543693 7201246641208657364078885)
  ·
    refine ⟨1350233745226623255764791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7201246641208657364078885 1350233745226623255764791)
    ·
      refine ⟨2025350617839934883647187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1350233745226623255764791 2025350617839934883647187)
      ·
        refine ⟨3038025926759902325470781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2025350617839934883647187 3038025926759902325470781)
        ·
          refine ⟨1139259722534963372051543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3038025926759902325470781 1139259722534963372051543)
          ·
            refine ⟨1708889583802445058077315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139259722534963372051543 1708889583802445058077315)
            ·
              refine ⟨2563334375703667587115973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1708889583802445058077315 2563334375703667587115973)
              ·
                refine ⟨480625195444437672584245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2563334375703667587115973 480625195444437672584245)
                ·
                  refine ⟨45058612072916031804773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 480625195444437672584245 45058612072916031804773)
                  ·
                    rfl

theorem cell23_789762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_789762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789762 prefixEnd_789762 := by exact prefixLift 789762
  have htrace : WordTrace (prefixWord ++ tailWord_789762) baseStart_789762 baseEnd_789762 := by
    simpa [prefixWord, tailWord_789762, baseEnd_789762] using wordTrace_append hprefix tailTrace_789762
  have hstable : (prefixWord ++ tailWord_789762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789762).length < 2 ^ (prefixWord ++ tailWord_789762).sum := by decide
  have hdescent : baseEnd_789762 < baseStart_789762 := by decide
  rcases family_descends (prefixWord ++ tailWord_789762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789788 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 5, 4]
def baseStart_789788 : Nat := 118140960795 + 789788 * 2 ^ 59
def prefixEnd_789788 : Nat := 4983230072969 + 3 ^ 40 * 789788 * 2
def baseEnd_789788 : Nat := 135180286384420394839279

theorem tailTrace_789788 : CollatzResearch.WordTrace tailWord_789788 prefixEnd_789788 135180286384420394839279 := by
  unfold tailWord_789788
  simp only [CollatzResearch.WordTrace]
  refine ⟨14402967431370217948381009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19203956575160290597841345 14402967431370217948381009)
  ·
    refine ⟨10802225573527663461285757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14402967431370217948381009 10802225573527663461285757)
    ·
      refine ⟨4050834590072873797982159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10802225573527663461285757 4050834590072873797982159)
      ·
        refine ⟨6076251885109310696973239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4050834590072873797982159 6076251885109310696973239)
        ·
          refine ⟨9114377827663966045459859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6076251885109310696973239 9114377827663966045459859)
          ·
            refine ⟨13671566741495949068189789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9114377827663966045459859 13671566741495949068189789)
            ·
              refine ⟨5126837528060980900571171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13671566741495949068189789 5126837528060980900571171)
              ·
                refine ⟨7690256292091471350856757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5126837528060980900571171 7690256292091471350856757)
                ·
                  refine ⟨720961527383575439142821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7690256292091471350856757 720961527383575439142821)
                  ·
                    refine ⟨135180286384420394839279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 720961527383575439142821 135180286384420394839279)
                    ·
                      rfl

theorem cell23_789788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_789788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789788 prefixEnd_789788 := by exact prefixLift 789788
  have htrace : WordTrace (prefixWord ++ tailWord_789788) baseStart_789788 baseEnd_789788 := by
    simpa [prefixWord, tailWord_789788, baseEnd_789788] using wordTrace_append hprefix tailTrace_789788
  have hstable : (prefixWord ++ tailWord_789788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789788).length < 2 ^ (prefixWord ++ tailWord_789788).sum := by decide
  have hdescent : baseEnd_789788 < baseStart_789788 := by decide
  rcases family_descends (prefixWord ++ tailWord_789788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789792 : List Nat := [2, 1, 1, 5, 4, 1, 1, 1, 2, 5]
def baseStart_789792 : Nat := 118140960795 + 789792 * 2 ^ 59
def prefixEnd_789792 : Nat := 4983230072969 + 3 ^ 40 * 789792 * 2
def baseEnd_789792 : Nat := 135180971025293056289273

theorem tailTrace_789792 : CollatzResearch.WordTrace tailWord_789792 prefixEnd_789792 135180971025293056289273 := by
  unfold tailWord_789792
  simp only [CollatzResearch.WordTrace]
  refine ⟨14403040377362972289953815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19204053836483963053271753 14403040377362972289953815)
  ·
    refine ⟨21604560566044458434930723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14403040377362972289953815 21604560566044458434930723)
    ·
      refine ⟨32406840849066687652396085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21604560566044458434930723 32406840849066687652396085)
      ·
        refine ⟨3038141329600001967412133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32406840849066687652396085 3038141329600001967412133)
        ·
          refine ⟨569651499300000368889775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3038141329600001967412133 569651499300000368889775)
          ·
            refine ⟨854477248950000553334663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569651499300000368889775 854477248950000553334663)
            ·
              refine ⟨1281715873425000830001995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 854477248950000553334663 1281715873425000830001995)
              ·
                refine ⟨1922573810137501245002993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1281715873425000830001995 1922573810137501245002993)
                ·
                  refine ⟨1441930357603125933752245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1922573810137501245002993 1441930357603125933752245)
                  ·
                    refine ⟨135180971025293056289273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1441930357603125933752245 135180971025293056289273)
                    ·
                      rfl

theorem cell23_789792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 2, 5].length) (baseStart_789792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789792 prefixEnd_789792 := by exact prefixLift 789792
  have htrace : WordTrace (prefixWord ++ tailWord_789792) baseStart_789792 baseEnd_789792 := by
    simpa [prefixWord, tailWord_789792, baseEnd_789792] using wordTrace_append hprefix tailTrace_789792
  have hstable : (prefixWord ++ tailWord_789792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789792).length < 2 ^ (prefixWord ++ tailWord_789792).sum := by decide
  have hdescent : baseEnd_789792 < baseStart_789792 := by decide
  rcases family_descends (prefixWord ++ tailWord_789792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789795 : List Nat := [1, 1, 1, 4, 2, 5, 1, 1, 2, 1, 4]
def baseStart_789795 : Nat := 118140960795 + 789795 * 2 ^ 59
def prefixEnd_789795 : Nat := 4983230072969 + 3 ^ 40 * 789795 * 2
def baseEnd_789795 : Nat := 405544453517842657130305

theorem tailTrace_789795 : CollatzResearch.WordTrace tailWord_789795 prefixEnd_789795 405544453517842657130305 := by
  unfold tailWord_789795
  simp only [CollatzResearch.WordTrace]
  refine ⟨28806190173715076092266839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19204126782476717394844559 28806190173715076092266839)
  ·
    refine ⟨43209285260572614138400259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28806190173715076092266839 43209285260572614138400259)
    ·
      refine ⟨64813927890858921207600389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43209285260572614138400259 64813927890858921207600389)
      ·
        refine ⟨12152611479536047726425073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64813927890858921207600389 12152611479536047726425073)
        ·
          refine ⟨9114458609652035794818805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12152611479536047726425073 9114458609652035794818805)
          ·
            refine ⟨854480494654878355764263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9114458609652035794818805 854480494654878355764263)
            ·
              refine ⟨1281720741982317533646395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 854480494654878355764263 1281720741982317533646395)
              ·
                refine ⟨1922581112973476300469593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1281720741982317533646395 1922581112973476300469593)
                ·
                  refine ⟨1441935834730107225352195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1922581112973476300469593 1441935834730107225352195)
                  ·
                    refine ⟨2162903752095160838028293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1441935834730107225352195 2162903752095160838028293)
                    ·
                      refine ⟨405544453517842657130305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2162903752095160838028293 405544453517842657130305)
                      ·
                        rfl

theorem cell23_789795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_789795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789795 prefixEnd_789795 := by exact prefixLift 789795
  have htrace : WordTrace (prefixWord ++ tailWord_789795) baseStart_789795 baseEnd_789795 := by
    simpa [prefixWord, tailWord_789795, baseEnd_789795] using wordTrace_append hprefix tailTrace_789795
  have hstable : (prefixWord ++ tailWord_789795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789795).length < 2 ^ (prefixWord ++ tailWord_789795).sum := by decide
  have hdescent : baseEnd_789795 < baseStart_789795 := by decide
  rcases family_descends (prefixWord ++ tailWord_789795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789822 : List Nat := [4, 2, 1, 2, 1, 1, 1, 6, 1, 4]
def baseStart_789822 : Nat := 118140960795 + 789822 * 2 ^ 59
def prefixEnd_789822 : Nat := 4983230072969 + 3 ^ 40 * 789822 * 2
def baseEnd_789822 : Nat := 135186105831838017164227

theorem tailTrace_789822 : CollatzResearch.WordTrace tailWord_789822 prefixEnd_789822 135186105831838017164227 := by
  unfold tailWord_789822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3600896868077157462937465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19204783296411506468999813 3600896868077157462937465)
  ·
    refine ⟨2700672651057868097203099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3600896868077157462937465 2700672651057868097203099)
    ·
      refine ⟨4051008976586802145804649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2700672651057868097203099 4051008976586802145804649)
      ·
        refine ⟨3038256732440101609353487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4051008976586802145804649 3038256732440101609353487)
        ·
          refine ⟨4557385098660152414030231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3038256732440101609353487 4557385098660152414030231)
          ·
            refine ⟨6836077647990228621045347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4557385098660152414030231 6836077647990228621045347)
            ·
              refine ⟨10254116471985342931568021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6836077647990228621045347 10254116471985342931568021)
              ·
                refine ⟨480661709624312949917251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10254116471985342931568021 480661709624312949917251)
                ·
                  refine ⟨720992564436469424875877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 480661709624312949917251 720992564436469424875877)
                  ·
                    refine ⟨135186105831838017164227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 720992564436469424875877 135186105831838017164227)
                    ·
                      rfl

theorem cell23_789822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_789822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789822 prefixEnd_789822 := by exact prefixLift 789822
  have htrace : WordTrace (prefixWord ++ tailWord_789822) baseStart_789822 baseEnd_789822 := by
    simpa [prefixWord, tailWord_789822, baseEnd_789822] using wordTrace_append hprefix tailTrace_789822
  have hstable : (prefixWord ++ tailWord_789822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789822).length < 2 ^ (prefixWord ++ tailWord_789822).sum := by decide
  have hdescent : baseEnd_789822 < baseStart_789822 := by decide
  rcases family_descends (prefixWord ++ tailWord_789822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789855 : List Nat := [1, 1, 2, 3, 1, 2, 1, 5, 2, 3, 2]
def baseStart_789855 : Nat := 118140960795 + 789855 * 2 ^ 59
def prefixEnd_789855 : Nat := 4983230072969 + 3 ^ 40 * 789855 * 2
def baseEnd_789855 : Nat := 405575262357112422380029

theorem tailTrace_789855 : CollatzResearch.WordTrace tailWord_789855 prefixEnd_789855 405575262357112422380029 := by
  unfold tailWord_789855
  simp only [CollatzResearch.WordTrace]
  refine ⟨28808378553497706339451019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19205585702331804226300679 28808378553497706339451019)
  ·
    refine ⟨43212567830246559509176529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28808378553497706339451019 43212567830246559509176529)
    ·
      refine ⟨32409425872684919631882397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43212567830246559509176529 32409425872684919631882397)
      ·
        refine ⟨12153534702256844861955899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32409425872684919631882397 12153534702256844861955899)
        ·
          refine ⟨18230302053385267292933849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12153534702256844861955899 18230302053385267292933849)
          ·
            refine ⟨13672726540038950469700387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18230302053385267292933849 13672726540038950469700387)
            ·
              refine ⟨20509089810058425704550581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13672726540038950469700387 20509089810058425704550581)
              ·
                refine ⟨1922727169692977409801617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20509089810058425704550581 1922727169692977409801617)
                ·
                  refine ⟨1442045377269733057351213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1922727169692977409801617 1442045377269733057351213)
                  ·
                    refine ⟨540767016476149896506705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1442045377269733057351213 540767016476149896506705)
                    ·
                      refine ⟨405575262357112422380029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 540767016476149896506705 405575262357112422380029)
                      ·
                        rfl

theorem cell23_789855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 3, 2].length) (baseStart_789855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789855 prefixEnd_789855 := by exact prefixLift 789855
  have htrace : WordTrace (prefixWord ++ tailWord_789855) baseStart_789855 baseEnd_789855 := by
    simpa [prefixWord, tailWord_789855, baseEnd_789855] using wordTrace_append hprefix tailTrace_789855
  have hstable : (prefixWord ++ tailWord_789855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789855).length < 2 ^ (prefixWord ++ tailWord_789855).sum := by decide
  have hdescent : baseEnd_789855 < baseStart_789855 := by decide
  rcases family_descends (prefixWord ++ tailWord_789855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789879 : List Nat := [1, 1, 3, 1, 1, 2, 7, 2, 1, 1, 3]
def baseStart_789879 : Nat := 118140960795 + 789879 * 2 ^ 59
def prefixEnd_789879 : Nat := 4983230072969 + 3 ^ 40 * 789879 * 2
def baseEnd_789879 : Nat := 405587585892820328479919

theorem tailTrace_789879 : CollatzResearch.WordTrace tailWord_789879 prefixEnd_789879 405587585892820328479919 := by
  unfold tailWord_789879
  simp only [CollatzResearch.WordTrace]
  refine ⟨28809253905410758438324691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19206169270273838958883127 28809253905410758438324691)
  ·
    refine ⟨43213880858116137657487037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28809253905410758438324691 43213880858116137657487037)
    ·
      refine ⟨16205205321793551621557639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43213880858116137657487037 16205205321793551621557639)
      ·
        refine ⟨24307807982690327432336459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16205205321793551621557639 24307807982690327432336459)
        ·
          refine ⟨36461711974035491148504689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24307807982690327432336459 36461711974035491148504689)
          ·
            refine ⟨27346283980526618361378517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36461711974035491148504689 27346283980526618361378517)
            ·
              refine ⟨640928530793592617844809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 27346283980526618361378517 640928530793592617844809)
              ·
                refine ⟨480696398095194463383607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640928530793592617844809 480696398095194463383607)
                ·
                  refine ⟨721044597142791695075411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 480696398095194463383607 721044597142791695075411)
                  ·
                    refine ⟨1081566895714187542613117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 721044597142791695075411 1081566895714187542613117)
                    ·
                      refine ⟨405587585892820328479919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1081566895714187542613117 405587585892820328479919)
                      ·
                        rfl

theorem cell23_789879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2, 1, 1, 3].length) (baseStart_789879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789879 prefixEnd_789879 := by exact prefixLift 789879
  have htrace : WordTrace (prefixWord ++ tailWord_789879) baseStart_789879 baseEnd_789879 := by
    simpa [prefixWord, tailWord_789879, baseEnd_789879] using wordTrace_append hprefix tailTrace_789879
  have hstable : (prefixWord ++ tailWord_789879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789879).length < 2 ^ (prefixWord ++ tailWord_789879).sum := by decide
  have hdescent : baseEnd_789879 < baseStart_789879 := by decide
  rcases family_descends (prefixWord ++ tailWord_789879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789886 : List Nat := [4, 2, 3, 2, 1, 2, 2, 1, 6]
def baseStart_789886 : Nat := 118140960795 + 789886 * 2 ^ 59
def prefixEnd_789886 : Nat := 4983230072969 + 3 ^ 40 * 789886 * 2
def baseEnd_789886 : Nat := 45065686695266866788043

theorem tailTrace_789886 : CollatzResearch.WordTrace tailWord_789886 prefixEnd_789886 45065686695266866788043 := by
  unfold tailWord_789886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3601188652048174829228689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19206339477590265755886341 3601188652048174829228689)
  ·
    refine ⟨2700891489036131121921517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3601188652048174829228689 2700891489036131121921517)
    ·
      refine ⟨1012834308388549170720569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2700891489036131121921517 1012834308388549170720569)
      ·
        refine ⟨759625731291411878040427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1012834308388549170720569 759625731291411878040427)
        ·
          refine ⟨1139438596937117817060641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759625731291411878040427 1139438596937117817060641)
          ·
            refine ⟨854578947702838362795481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1139438596937117817060641 854578947702838362795481)
            ·
              refine ⟨640934210777128772096611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 854578947702838362795481 640934210777128772096611)
              ·
                refine ⟨961401316165693158144917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 640934210777128772096611 961401316165693158144917)
                ·
                  refine ⟨45065686695266866788043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 961401316165693158144917 45065686695266866788043)
                  ·
                    rfl

theorem cell23_789886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_789886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789886 prefixEnd_789886 := by exact prefixLift 789886
  have htrace : WordTrace (prefixWord ++ tailWord_789886) baseStart_789886 baseEnd_789886 := by
    simpa [prefixWord, tailWord_789886, baseEnd_789886] using wordTrace_append hprefix tailTrace_789886
  have hstable : (prefixWord ++ tailWord_789886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789886).length < 2 ^ (prefixWord ++ tailWord_789886).sum := by decide
  have hdescent : baseEnd_789886 < baseStart_789886 := by decide
  rcases family_descends (prefixWord ++ tailWord_789886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789902 : List Nat := [4, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4]
def baseStart_789902 : Nat := 118140960795 + 789902 * 2 ^ 59
def prefixEnd_789902 : Nat := 4983230072969 + 3 ^ 40 * 789902 * 2
def baseEnd_789902 : Nat := 405599395947873738492313

theorem tailTrace_789902 : CollatzResearch.WordTrace tailWord_789902 prefixEnd_789902 405599395947873738492313 := by
  unfold tailWord_789902
  simp only [CollatzResearch.WordTrace]
  refine ⟨3601261598040929170801495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19206728522884955577607973 3601261598040929170801495)
  ·
    refine ⟨5401892397061393756202243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3601261598040929170801495 5401892397061393756202243)
    ·
      refine ⟨8102838595592090634303365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5401892397061393756202243 8102838595592090634303365)
      ·
        refine ⟨1519282236673516993931881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8102838595592090634303365 1519282236673516993931881)
        ·
          refine ⟨1139461677505137745448911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1519282236673516993931881 1139461677505137745448911)
          ·
            refine ⟨1709192516257706618173367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139461677505137745448911 1709192516257706618173367)
            ·
              refine ⟨2563788774386559927260051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709192516257706618173367 2563788774386559927260051)
              ·
                refine ⟨3845683161579839890890077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2563788774386559927260051 3845683161579839890890077)
                ·
                  refine ⟨1442131185592439959083779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3845683161579839890890077 1442131185592439959083779)
                  ·
                    refine ⟨2163196778388659938625669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1442131185592439959083779 2163196778388659938625669)
                    ·
                      refine ⟨405599395947873738492313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2163196778388659938625669 405599395947873738492313)
                      ·
                        rfl

theorem cell23_789902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_789902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789902 prefixEnd_789902 := by exact prefixLift 789902
  have htrace : WordTrace (prefixWord ++ tailWord_789902) baseStart_789902 baseEnd_789902 := by
    simpa [prefixWord, tailWord_789902, baseEnd_789902] using wordTrace_append hprefix tailTrace_789902
  have hstable : (prefixWord ++ tailWord_789902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789902).length < 2 ^ (prefixWord ++ tailWord_789902).sum := by decide
  have hdescent : baseEnd_789902 < baseStart_789902 := by decide
  rcases family_descends (prefixWord ++ tailWord_789902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789906 : List Nat := [3, 2, 3, 3, 1, 1, 2, 1, 2, 3, 2]
def baseStart_789906 : Nat := 118140960795 + 789906 * 2 ^ 59
def prefixEnd_789906 : Nat := 4983230072969 + 3 ^ 40 * 789906 * 2
def baseEnd_789906 : Nat := 405601449870491722842295

theorem tailTrace_789906 : CollatzResearch.WordTrace tailWord_789906 prefixEnd_789906 405601449870491722842295 := by
  unfold tailWord_789906
  simp only [CollatzResearch.WordTrace]
  refine ⟨7202559669078235512389393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19206825784208628033038381 7202559669078235512389393)
  ·
    refine ⟨5401919751808676634292045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7202559669078235512389393 5401919751808676634292045)
    ·
      refine ⟨2025719906928253737859517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5401919751808676634292045 2025719906928253737859517)
      ·
        refine ⟨759644965098095151697319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2025719906928253737859517 759644965098095151697319)
        ·
          refine ⟨1139467447647142727545979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759644965098095151697319 1139467447647142727545979)
          ·
            refine ⟨1709201171470714091318969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139467447647142727545979 1709201171470714091318969)
            ·
              refine ⟨1281900878603035568489227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1709201171470714091318969 1281900878603035568489227)
              ·
                refine ⟨1922851317904553352733841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1281900878603035568489227 1922851317904553352733841)
                ·
                  refine ⟨1442138488428415014550381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1922851317904553352733841 1442138488428415014550381)
                  ·
                    refine ⟨540801933160655630456393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1442138488428415014550381 540801933160655630456393)
                    ·
                      refine ⟨405601449870491722842295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 540801933160655630456393 405601449870491722842295)
                      ·
                        rfl

theorem cell23_789906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_789906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789906 prefixEnd_789906 := by exact prefixLift 789906
  have htrace : WordTrace (prefixWord ++ tailWord_789906) baseStart_789906 baseEnd_789906 := by
    simpa [prefixWord, tailWord_789906, baseEnd_789906] using wordTrace_append hprefix tailTrace_789906
  have hstable : (prefixWord ++ tailWord_789906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789906).length < 2 ^ (prefixWord ++ tailWord_789906).sum := by decide
  have hdescent : baseEnd_789906 < baseStart_789906 := by decide
  rcases family_descends (prefixWord ++ tailWord_789906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789922 : List Nat := [3, 3, 1, 2, 1, 4, 1, 1, 1, 1, 5]
def baseStart_789922 : Nat := 118140960795 + 789922 * 2 ^ 59
def prefixEnd_789922 : Nat := 4983230072969 + 3 ^ 40 * 789922 * 2
def baseEnd_789922 : Nat := 405609665560963660242221

theorem tailTrace_789922 : CollatzResearch.WordTrace tailWord_789922 prefixEnd_789922 405609665560963660242221 := by
  unfold tailWord_789922
  simp only [CollatzResearch.WordTrace]
  refine ⟨7202705561063744195535005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19207214829503317854760013 7202705561063744195535005)
  ·
    refine ⟨2701014585398904073325627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7202705561063744195535005 2701014585398904073325627)
    ·
      refine ⟨4051521878098356109988441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2701014585398904073325627 4051521878098356109988441)
      ·
        refine ⟨3038641408573767082491331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4051521878098356109988441 3038641408573767082491331)
        ·
          refine ⟨4557962112860650623736997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3038641408573767082491331 4557962112860650623736997)
          ·
            refine ⟨854617896161371991950687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4557962112860650623736997 854617896161371991950687)
            ·
              refine ⟨1281926844242057987926031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 854617896161371991950687 1281926844242057987926031)
              ·
                refine ⟨1922890266363086981889047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1281926844242057987926031 1922890266363086981889047)
                ·
                  refine ⟨2884335399544630472833571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1922890266363086981889047 2884335399544630472833571)
                  ·
                    refine ⟨4326503099316945709250357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2884335399544630472833571 4326503099316945709250357)
                    ·
                      refine ⟨405609665560963660242221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4326503099316945709250357 405609665560963660242221)
                      ·
                        rfl

theorem cell23_789922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_789922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789922 prefixEnd_789922 := by exact prefixLift 789922
  have htrace : WordTrace (prefixWord ++ tailWord_789922) baseStart_789922 baseEnd_789922 := by
    simpa [prefixWord, tailWord_789922, baseEnd_789922] using wordTrace_append hprefix tailTrace_789922
  have hstable : (prefixWord ++ tailWord_789922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789922).length < 2 ^ (prefixWord ++ tailWord_789922).sum := by decide
  have hdescent : baseEnd_789922 < baseStart_789922 := by decide
  rcases family_descends (prefixWord ++ tailWord_789922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789935 : List Nat := [1, 1, 2, 1, 2, 2, 1, 5, 4, 1, 3]
def baseStart_789935 : Nat := 118140960795 + 789935 * 2 ^ 59
def prefixEnd_789935 : Nat := 4983230072969 + 3 ^ 40 * 789935 * 2
def baseEnd_789935 : Nat := 405616340809472109379661

theorem tailTrace_789935 : CollatzResearch.WordTrace tailWord_789935 prefixEnd_789935 405616340809472109379661 := by
  unfold tailWord_789935
  simp only [CollatzResearch.WordTrace]
  refine ⟨28811296393207880002363259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19207530928805253334908839 28811296393207880002363259)
  ·
    refine ⟨43216944589811820003544889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28811296393207880002363259 43216944589811820003544889)
    ·
      refine ⟨32412708442358865002658667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43216944589811820003544889 32412708442358865002658667)
      ·
        refine ⟨48619062663538297503988001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32412708442358865002658667 48619062663538297503988001)
        ·
          refine ⟨36464296997653723127991001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48619062663538297503988001 36464296997653723127991001)
          ·
            refine ⟨27348222748240292345993251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36464296997653723127991001 27348222748240292345993251)
            ·
              refine ⟨41022334122360438518989877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27348222748240292345993251 41022334122360438518989877)
              ·
                refine ⟨3845843823971291111155301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41022334122360438518989877 3845843823971291111155301)
                ·
                  refine ⟨721095716994617083341619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3845843823971291111155301 721095716994617083341619)
                  ·
                    refine ⟨1081643575491925625012429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 721095716994617083341619 1081643575491925625012429)
                    ·
                      refine ⟨405616340809472109379661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1081643575491925625012429 405616340809472109379661)
                      ·
                        rfl

theorem cell23_789935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4, 1, 3].length) (baseStart_789935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789935 prefixEnd_789935 := by exact prefixLift 789935
  have htrace : WordTrace (prefixWord ++ tailWord_789935) baseStart_789935 baseEnd_789935 := by
    simpa [prefixWord, tailWord_789935, baseEnd_789935] using wordTrace_append hprefix tailTrace_789935
  have hstable : (prefixWord ++ tailWord_789935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789935).length < 2 ^ (prefixWord ++ tailWord_789935).sum := by decide
  have hdescent : baseEnd_789935 < baseStart_789935 := by decide
  rcases family_descends (prefixWord ++ tailWord_789935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789952 : List Nat := [2, 1, 1, 2, 3, 1, 4, 3, 2, 1, 3]
def baseStart_789952 : Nat := 118140960795 + 789952 * 2 ^ 59
def prefixEnd_789952 : Nat := 4983230072969 + 3 ^ 40 * 789952 * 2
def baseEnd_789952 : Nat := 405625069980598542867083

theorem tailTrace_789952 : CollatzResearch.WordTrace tailWord_789952 prefixEnd_789952 405625069980598542867083 := by
  unfold tailWord_789952
  simp only [CollatzResearch.WordTrace]
  refine ⟨14405958217073145952866055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19207944289430861270488073 14405958217073145952866055)
  ·
    refine ⟨21608937325609718929299083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14405958217073145952866055 21608937325609718929299083)
    ·
      refine ⟨32413405988414578393948625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21608937325609718929299083 32413405988414578393948625)
      ·
        refine ⟨24310054491310933795461469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32413405988414578393948625 24310054491310933795461469)
        ·
          refine ⟨9116270434241600173298051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24310054491310933795461469 9116270434241600173298051)
          ·
            refine ⟨13674405651362400259947077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9116270434241600173298051 13674405651362400259947077)
            ·
              refine ⟨2563951059630450048740077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13674405651362400259947077 2563951059630450048740077)
              ·
                refine ⟨961481647361418768277529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2563951059630450048740077 961481647361418768277529)
                ·
                  refine ⟨721111235521064076208147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 961481647361418768277529 721111235521064076208147)
                  ·
                    refine ⟨1081666853281596114312221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 721111235521064076208147 1081666853281596114312221)
                    ·
                      refine ⟨405625069980598542867083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1081666853281596114312221 405625069980598542867083)
                      ·
                        rfl

theorem cell23_789952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 2, 1, 3].length) (baseStart_789952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789952 prefixEnd_789952 := by exact prefixLift 789952
  have htrace : WordTrace (prefixWord ++ tailWord_789952) baseStart_789952 baseEnd_789952 := by
    simpa [prefixWord, tailWord_789952, baseEnd_789952] using wordTrace_append hprefix tailTrace_789952
  have hstable : (prefixWord ++ tailWord_789952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789952).length < 2 ^ (prefixWord ++ tailWord_789952).sum := by decide
  have hdescent : baseEnd_789952 < baseStart_789952 := by decide
  rcases family_descends (prefixWord ++ tailWord_789952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789962 : List Nat := [3, 1, 2, 1, 2, 3, 2, 1, 3, 3, 2]
def baseStart_789962 : Nat := 118140960795 + 789962 * 2 ^ 59
def prefixEnd_789962 : Nat := 4983230072969 + 3 ^ 40 * 789962 * 2
def baseEnd_789962 : Nat := 405630204787143503742037

theorem tailTrace_789962 : CollatzResearch.WordTrace tailWord_789962 prefixEnd_789962 405630204787143503742037 := by
  unfold tailWord_789962
  simp only [CollatzResearch.WordTrace]
  refine ⟨7203070291027515903399035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19208187442740042409064093 7203070291027515903399035)
  ·
    refine ⟨10804605436541273855098553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7203070291027515903399035 10804605436541273855098553)
    ·
      refine ⟨8103454077405955391323915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10804605436541273855098553 8103454077405955391323915)
      ·
        refine ⟨12155181116108933086985873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8103454077405955391323915 12155181116108933086985873)
        ·
          refine ⟨9116385837081699815239405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12155181116108933086985873 9116385837081699815239405)
          ·
            refine ⟨3418644688905637430714777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9116385837081699815239405 3418644688905637430714777)
            ·
              refine ⟨2563983516679228073036083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3418644688905637430714777 2563983516679228073036083)
              ·
                refine ⟨3845975275018842109554125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2563983516679228073036083 3845975275018842109554125)
                ·
                  refine ⟨1442240728132065791082797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3845975275018842109554125 1442240728132065791082797)
                  ·
                    refine ⟨540840273049524671656049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1442240728132065791082797 540840273049524671656049)
                    ·
                      refine ⟨405630204787143503742037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 540840273049524671656049 405630204787143503742037)
                      ·
                        rfl

theorem cell23_789962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 3, 3, 2].length) (baseStart_789962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_789962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_789962 prefixEnd_789962 := by exact prefixLift 789962
  have htrace : WordTrace (prefixWord ++ tailWord_789962) baseStart_789962 baseEnd_789962 := by
    simpa [prefixWord, tailWord_789962, baseEnd_789962] using wordTrace_append hprefix tailTrace_789962
  have hstable : (prefixWord ++ tailWord_789962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789962).length < 2 ^ (prefixWord ++ tailWord_789962).sum := by decide
  have hdescent : baseEnd_789962 < baseStart_789962 := by decide
  rcases family_descends (prefixWord ++ tailWord_789962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790049 : List Nat := [1, 2, 3, 2, 2, 3, 3, 2, 5]
def baseStart_790049 : Nat := 118140960795 + 790049 * 2 ^ 59
def prefixEnd_790049 : Nat := 4983230072969 + 3 ^ 40 * 790049 * 2
def baseEnd_790049 : Nat := 45074986400453851483793

theorem tailTrace_790049 : CollatzResearch.WordTrace tailWord_790049 prefixEnd_790049 45074986400453851483793 := by
  unfold tailWord_790049
  simp only [CollatzResearch.WordTrace]
  refine ⟨28815454314794877472013201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19210302876529918314675467 28815454314794877472013201)
  ·
    refine ⟨21611590736096158104009901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28815454314794877472013201 21611590736096158104009901)
    ·
      refine ⟨8104346526036059289003713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21611590736096158104009901 8104346526036059289003713)
      ·
        refine ⟨6078259894527044466752785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8104346526036059289003713 6078259894527044466752785)
        ·
          refine ⟨4558694920895283350064589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6078259894527044466752785 4558694920895283350064589)
          ·
            refine ⟨1709510595335731256274221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4558694920895283350064589 1709510595335731256274221)
            ·
              refine ⟨641066473250899221102833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1709510595335731256274221 641066473250899221102833)
              ·
                refine ⟨480799854938174415827125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 641066473250899221102833 480799854938174415827125)
                ·
                  refine ⟨45074986400453851483793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 480799854938174415827125 45074986400453851483793)
                  ·
                    rfl

theorem cell23_790049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2, 5].length) (baseStart_790049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790049 prefixEnd_790049 := by exact prefixLift 790049
  have htrace : WordTrace (prefixWord ++ tailWord_790049) baseStart_790049 baseEnd_790049 := by
    simpa [prefixWord, tailWord_790049, baseEnd_790049] using wordTrace_append hprefix tailTrace_790049
  have hstable : (prefixWord ++ tailWord_790049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790049).length < 2 ^ (prefixWord ++ tailWord_790049).sum := by decide
  have hdescent : baseEnd_790049 < baseStart_790049 := by decide
  rcases family_descends (prefixWord ++ tailWord_790049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790065 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 6, 1, 4]
def baseStart_790065 : Nat := 118140960795 + 790065 * 2 ^ 59
def prefixEnd_790065 : Nat := 4983230072969 + 3 ^ 40 * 790065 * 2
def baseEnd_790065 : Nat := 405683093294556600754063

theorem tailTrace_790065 : CollatzResearch.WordTrace tailWord_790065 prefixEnd_790065 405683093294556600754063 := by
  unfold tailWord_790065
  simp only [CollatzResearch.WordTrace]
  refine ⟨28816037882736912204595649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19210691921824608136397099 28816037882736912204595649)
  ·
    refine ⟨21612028412052684153446737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28816037882736912204595649 21612028412052684153446737)
    ·
      refine ⟨16209021309039513115085053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21612028412052684153446737 16209021309039513115085053)
      ·
        refine ⟨6078382990889817418156895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16209021309039513115085053 6078382990889817418156895)
        ·
          refine ⟨9117574486334726127235343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6078382990889817418156895 9117574486334726127235343)
          ·
            refine ⟨13676361729502089190853015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9117574486334726127235343 13676361729502089190853015)
            ·
              refine ⟨20514542594253133786279523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13676361729502089190853015 20514542594253133786279523)
              ·
                refine ⟨30771813891379700679419285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20514542594253133786279523 30771813891379700679419285)
                ·
                  refine ⟨1442428776158423469347779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30771813891379700679419285 1442428776158423469347779)
                  ·
                    refine ⟨2163643164237635204021669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1442428776158423469347779 2163643164237635204021669)
                    ·
                      refine ⟨405683093294556600754063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2163643164237635204021669 405683093294556600754063)
                      ·
                        rfl

theorem cell23_790065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_790065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790065 prefixEnd_790065 := by exact prefixLift 790065
  have htrace : WordTrace (prefixWord ++ tailWord_790065) baseStart_790065 baseEnd_790065 := by
    simpa [prefixWord, tailWord_790065, baseEnd_790065] using wordTrace_append hprefix tailTrace_790065
  have hstable : (prefixWord ++ tailWord_790065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790065).length < 2 ^ (prefixWord ++ tailWord_790065).sum := by decide
  have hdescent : baseEnd_790065 < baseStart_790065 := by decide
  rcases family_descends (prefixWord ++ tailWord_790065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790122 : List Nat := [3, 1, 3, 2, 1, 2, 2, 3, 6]
def baseStart_790122 : Nat := 118140960795 + 790122 * 2 ^ 59
def prefixEnd_790122 : Nat := 4983230072969 + 3 ^ 40 * 790122 * 2
def baseEnd_790122 : Nat := 45079151299095875304589

theorem tailTrace_790122 : CollatzResearch.WordTrace tailWord_790122 prefixEnd_790122 45079151299095875304589 := by
  unfold tailWord_790122
  simp only [CollatzResearch.WordTrace]
  refine ⟨7204529210882602734855155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19212077895686940626280413 7204529210882602734855155)
  ·
    refine ⟨10806793816323904102282733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7204529210882602734855155 10806793816323904102282733)
    ·
      refine ⟨4052547681121464038356025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10806793816323904102282733 4052547681121464038356025)
      ·
        refine ⟨3039410760841098028767019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4052547681121464038356025 3039410760841098028767019)
        ·
          refine ⟨4559116141261647043150529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3039410760841098028767019 4559116141261647043150529)
          ·
            refine ⟨3419337105946235282362897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4559116141261647043150529 3419337105946235282362897)
            ·
              refine ⟨2564502829459676461772173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3419337105946235282362897 2564502829459676461772173)
              ·
                refine ⟨961688561047378673164565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2564502829459676461772173 961688561047378673164565)
                ·
                  refine ⟨45079151299095875304589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 961688561047378673164565 45079151299095875304589)
                  ·
                    rfl

theorem cell23_790122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 6].length) (baseStart_790122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790122 prefixEnd_790122 := by exact prefixLift 790122
  have htrace : WordTrace (prefixWord ++ tailWord_790122) baseStart_790122 baseEnd_790122 := by
    simpa [prefixWord, tailWord_790122, baseEnd_790122] using wordTrace_append hprefix tailTrace_790122
  have hstable : (prefixWord ++ tailWord_790122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790122).length < 2 ^ (prefixWord ++ tailWord_790122).sum := by decide
  have hdescent : baseEnd_790122 < baseStart_790122 := by decide
  rcases family_descends (prefixWord ++ tailWord_790122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790165 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 3, 6]
def baseStart_790165 : Nat := 118140960795 + 790165 * 2 ^ 59
def prefixEnd_790165 : Nat := 4983230072969 + 3 ^ 40 * 790165 * 2
def baseEnd_790165 : Nat := 135244813786668736501201

theorem tailTrace_790165 : CollatzResearch.WordTrace tailWord_790165 prefixEnd_790165 135244813786668736501201 := by
  unfold tailWord_790165
  simp only [CollatzResearch.WordTrace]
  refine ⟨28819685182374629283235949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19213123454916419522157299 28819685182374629283235949)
  ·
    refine ⟨10807381943390485981213481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28819685182374629283235949 10807381943390485981213481)
    ·
      refine ⟨8105536457542864485910111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10807381943390485981213481 8105536457542864485910111)
      ·
        refine ⟨12158304686314296728865167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8105536457542864485910111 12158304686314296728865167)
        ·
          refine ⟨18237457029471445093297751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12158304686314296728865167 18237457029471445093297751)
          ·
            refine ⟨27356185544207167639946627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18237457029471445093297751 27356185544207167639946627)
            ·
              refine ⟨41034278316310751459919941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27356185544207167639946627 41034278316310751459919941)
              ·
                refine ⟨7693927184308265898734989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41034278316310751459919941 7693927184308265898734989)
                ·
                  refine ⟨2885222694115599712025621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7693927184308265898734989 2885222694115599712025621)
                  ·
                    refine ⟨135244813786668736501201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2885222694115599712025621 135244813786668736501201)
                    ·
                      rfl

theorem cell23_790165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_790165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790165 prefixEnd_790165 := by exact prefixLift 790165
  have htrace : WordTrace (prefixWord ++ tailWord_790165) baseStart_790165 baseEnd_790165 := by
    simpa [prefixWord, tailWord_790165, baseEnd_790165] using wordTrace_append hprefix tailTrace_790165
  have hstable : (prefixWord ++ tailWord_790165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790165).length < 2 ^ (prefixWord ++ tailWord_790165).sum := by decide
  have hdescent : baseEnd_790165 < baseStart_790165 := by decide
  rcases family_descends (prefixWord ++ tailWord_790165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790189 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 2, 6, 2]
def baseStart_790189 : Nat := 118140960795 + 790189 * 2 ^ 59
def prefixEnd_790189 : Nat := 4983230072969 + 3 ^ 40 * 790189 * 2
def baseEnd_790189 : Nat := 405746764895714115603493

theorem tailTrace_790189 : CollatzResearch.WordTrace tailWord_790189 prefixEnd_790189 405746764895714115603493 := by
  unfold tailWord_790189
  simp only [CollatzResearch.WordTrace]
  refine ⟨28820560534287681382109621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19213707022858454254739747 28820560534287681382109621)
  ·
    refine ⟨2701927550089470129572777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28820560534287681382109621 2701927550089470129572777)
    ·
      refine ⟨2026445662567102597179583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2701927550089470129572777 2026445662567102597179583)
      ·
        refine ⟨3039668493850653895769375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2026445662567102597179583 3039668493850653895769375)
        ·
          refine ⟨4559502740775980843654063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3039668493850653895769375 4559502740775980843654063)
          ·
            refine ⟨6839254111163971265481095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4559502740775980843654063 6839254111163971265481095)
            ·
              refine ⟨10258881166745956898221643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6839254111163971265481095 10258881166745956898221643)
              ·
                refine ⟨15388321750118935347332465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10258881166745956898221643 15388321750118935347332465)
                ·
                  refine ⟨11541241312589201510499349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15388321750118935347332465 11541241312589201510499349)
                  ·
                    refine ⟨540995686527618820804657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11541241312589201510499349 540995686527618820804657)
                    ·
                      refine ⟨405746764895714115603493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 540995686527618820804657 405746764895714115603493)
                      ·
                        rfl

theorem cell23_790189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_790189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790189 prefixEnd_790189 := by exact prefixLift 790189
  have htrace : WordTrace (prefixWord ++ tailWord_790189) baseStart_790189 baseEnd_790189 := by
    simpa [prefixWord, tailWord_790189, baseEnd_790189] using wordTrace_append hprefix tailTrace_790189
  have hstable : (prefixWord ++ tailWord_790189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790189).length < 2 ^ (prefixWord ++ tailWord_790189).sum := by decide
  have hdescent : baseEnd_790189 < baseStart_790189 := by decide
  rcases family_descends (prefixWord ++ tailWord_790189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790192 : List Nat := [2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 3]
def baseStart_790192 : Nat := 118140960795 + 790192 * 2 ^ 59
def prefixEnd_790192 : Nat := 4983230072969 + 3 ^ 40 * 790192 * 2
def baseEnd_790192 : Nat := 405748305337677603865979

theorem tailTrace_790192 : CollatzResearch.WordTrace tailWord_790192 prefixEnd_790192 405748305337677603865979 := by
  unfold tailWord_790192
  simp only [CollatzResearch.WordTrace]
  refine ⟨14410334976638406447234415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19213779968851208596312553 14410334976638406447234415)
  ·
    refine ⟨21615502464957609670851623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14410334976638406447234415 21615502464957609670851623)
    ·
      refine ⟨32423253697436414506277435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21615502464957609670851623 32423253697436414506277435)
      ·
        refine ⟨48634880546154621759416153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32423253697436414506277435 48634880546154621759416153)
        ·
          refine ⟨36476160409615966319562115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48634880546154621759416153 36476160409615966319562115)
          ·
            refine ⟨54714240614423949479343173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36476160409615966319562115 54714240614423949479343173)
            ·
              refine ⟨10258920115204490527376845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54714240614423949479343173 10258920115204490527376845)
              ·
                refine ⟨3847095043201683947766317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10258920115204490527376845 3847095043201683947766317)
                ·
                  refine ⟨1442660641200631480412369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3847095043201683947766317 1442660641200631480412369)
                  ·
                    refine ⟨1081995480900473610309277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1442660641200631480412369 1081995480900473610309277)
                    ·
                      refine ⟨405748305337677603865979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1081995480900473610309277 405748305337677603865979)
                      ·
                        rfl

theorem cell23_790192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 3].length) (baseStart_790192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790192 prefixEnd_790192 := by exact prefixLift 790192
  have htrace : WordTrace (prefixWord ++ tailWord_790192) baseStart_790192 baseEnd_790192 := by
    simpa [prefixWord, tailWord_790192, baseEnd_790192] using wordTrace_append hprefix tailTrace_790192
  have hstable : (prefixWord ++ tailWord_790192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790192).length < 2 ^ (prefixWord ++ tailWord_790192).sum := by decide
  have hdescent : baseEnd_790192 < baseStart_790192 := by decide
  rcases family_descends (prefixWord ++ tailWord_790192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790195 : List Nat := [1, 1, 1, 2, 3, 3, 3, 9]
def baseStart_790195 : Nat := 118140960795 + 790195 * 2 ^ 59
def prefixEnd_790195 : Nat := 4983230072969 + 3 ^ 40 * 790195 * 2
def baseEnd_790195 : Nat := 15027772065912633041795

theorem tailTrace_790195 : CollatzResearch.WordTrace tailWord_790195 prefixEnd_790195 15027772065912633041795 := by
  unfold tailWord_790195
  simp only [CollatzResearch.WordTrace]
  refine ⟨28820779372265944406828039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19213852914843962937885359 28820779372265944406828039)
  ·
    refine ⟨43231169058398916610242059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28820779372265944406828039 43231169058398916610242059)
    ·
      refine ⟨64846753587598374915363089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43231169058398916610242059 64846753587598374915363089)
      ·
        refine ⟨48635065190698781186522317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64846753587598374915363089 48635065190698781186522317)
        ·
          refine ⟨18238149446512042944945869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48635065190698781186522317 18238149446512042944945869)
          ·
            refine ⟨6839306042442016104354701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18238149446512042944945869 6839306042442016104354701)
            ·
              refine ⟨2564739765915756039133013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6839306042442016104354701 2564739765915756039133013)
              ·
                refine ⟨15027772065912633041795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2564739765915756039133013 15027772065912633041795)
                ·
                  rfl

theorem cell23_790195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 9].length) (baseStart_790195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790195 prefixEnd_790195 := by exact prefixLift 790195
  have htrace : WordTrace (prefixWord ++ tailWord_790195) baseStart_790195 baseEnd_790195 := by
    simpa [prefixWord, tailWord_790195, baseEnd_790195] using wordTrace_append hprefix tailTrace_790195
  have hstable : (prefixWord ++ tailWord_790195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790195).length < 2 ^ (prefixWord ++ tailWord_790195).sum := by decide
  have hdescent : baseEnd_790195 < baseStart_790195 := by decide
  rcases family_descends (prefixWord ++ tailWord_790195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790243 : List Nat := [1, 1, 1, 7, 2, 2, 1, 2, 1, 2, 3]
def baseStart_790243 : Nat := 118140960795 + 790243 * 2 ^ 59
def prefixEnd_790243 : Nat := 4983230072969 + 3 ^ 40 * 790243 * 2
def baseEnd_790243 : Nat := 405774492851056904328245

theorem tailTrace_790243 : CollatzResearch.WordTrace tailWord_790243 prefixEnd_790243 405774492851056904328245 := by
  unfold tailWord_790243
  simp only [CollatzResearch.WordTrace]
  refine ⟨28822530076092048604575383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19215020050728032403050255 28822530076092048604575383)
  ·
    refine ⟨43233795114138072906863075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28822530076092048604575383 43233795114138072906863075)
    ·
      refine ⟨64850692671207109360294613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43233795114138072906863075 64850692671207109360294613)
      ·
        refine ⟨1519938109481416625631905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 64850692671207109360294613 1519938109481416625631905)
        ·
          refine ⟨1139953582111062469223929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1519938109481416625631905 1139953582111062469223929)
          ·
            refine ⟨854965186583296851917947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1139953582111062469223929 854965186583296851917947)
            ·
              refine ⟨1282447779874945277876921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 854965186583296851917947 1282447779874945277876921)
              ·
                refine ⟨961835834906208958407691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1282447779874945277876921 961835834906208958407691)
                ·
                  refine ⟨1442753752359313437611537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 961835834906208958407691 1442753752359313437611537)
                  ·
                    refine ⟨1082065314269485078208653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1442753752359313437611537 1082065314269485078208653)
                    ·
                      refine ⟨405774492851056904328245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1082065314269485078208653 405774492851056904328245)
                      ·
                        rfl

theorem cell23_790243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_790243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790243 prefixEnd_790243 := by exact prefixLift 790243
  have htrace : WordTrace (prefixWord ++ tailWord_790243) baseStart_790243 baseEnd_790243 := by
    simpa [prefixWord, tailWord_790243, baseEnd_790243] using wordTrace_append hprefix tailTrace_790243
  have hstable : (prefixWord ++ tailWord_790243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790243).length < 2 ^ (prefixWord ++ tailWord_790243).sum := by decide
  have hdescent : baseEnd_790243 < baseStart_790243 := by decide
  rcases family_descends (prefixWord ++ tailWord_790243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790326 : List Nat := [5, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_790326 : Nat := 118140960795 + 790326 * 2 ^ 59
def prefixEnd_790326 : Nat := 4983230072969 + 3 ^ 40 * 790326 * 2
def baseEnd_790326 : Nat := 405817111745380079590363

theorem tailTrace_790326 : CollatzResearch.WordTrace tailWord_790326 prefixEnd_790326 405817111745380079590363 := by
  unfold tailWord_790326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1801597333424459611240427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19217038223194235853231221 1801597333424459611240427)
  ·
    refine ⟨2702396000136689416860641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1801597333424459611240427 2702396000136689416860641)
    ·
      refine ⟨2026797000102517062645481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2702396000136689416860641 2026797000102517062645481)
      ·
        refine ⟨1520097750076887796984111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2026797000102517062645481 1520097750076887796984111)
        ·
          refine ⟨2280146625115331695476167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1520097750076887796984111 2280146625115331695476167)
          ·
            refine ⟨3420219937672997543214251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2280146625115331695476167 3420219937672997543214251)
            ·
              refine ⟨5130329906509496314821377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3420219937672997543214251 5130329906509496314821377)
              ·
                refine ⟨3847747429882122236116033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5130329906509496314821377 3847747429882122236116033)
                ·
                  refine ⟨2885810572411591677087025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3847747429882122236116033 2885810572411591677087025)
                  ·
                    refine ⟨2164357929308693757815269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2885810572411591677087025 2164357929308693757815269)
                    ·
                      refine ⟨405817111745380079590363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2164357929308693757815269 405817111745380079590363)
                      ·
                        rfl

theorem cell23_790326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_790326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790326 prefixEnd_790326 := by exact prefixLift 790326
  have htrace : WordTrace (prefixWord ++ tailWord_790326) baseStart_790326 baseEnd_790326 := by
    simpa [prefixWord, tailWord_790326, baseEnd_790326] using wordTrace_append hprefix tailTrace_790326
  have hstable : (prefixWord ++ tailWord_790326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790326).length < 2 ^ (prefixWord ++ tailWord_790326).sum := by decide
  have hdescent : baseEnd_790326 < baseStart_790326 := by decide
  rcases family_descends (prefixWord ++ tailWord_790326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790330 : List Nat := [3, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2]
def baseStart_790330 : Nat := 118140960795 + 790330 * 2 ^ 59
def prefixEnd_790330 : Nat := 4983230072969 + 3 ^ 40 * 790330 * 2
def baseEnd_790330 : Nat := 405819165667998063940345

theorem tailTrace_790330 : CollatzResearch.WordTrace tailWord_790330 prefixEnd_790330 405819165667998063940345 := by
  unfold tailWord_790330
  simp only [CollatzResearch.WordTrace]
  refine ⟨7206425806694215615748111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19217135484517908308661629 7206425806694215615748111)
  ·
    refine ⟨10809638710041323423622167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7206425806694215615748111 10809638710041323423622167)
    ·
      refine ⟨16214458065061985135433251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10809638710041323423622167 16214458065061985135433251)
      ·
        refine ⟨24321687097592977703149877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16214458065061985135433251 24321687097592977703149877)
        ·
          refine ⟨2280158165399341659670301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24321687097592977703149877 2280158165399341659670301)
          ·
            refine ⟨855059312024753122376363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2280158165399341659670301 855059312024753122376363)
            ·
              refine ⟨1282588968037129683564545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 855059312024753122376363 1282588968037129683564545)
              ·
                refine ⟨961941726027847262673409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1282588968037129683564545 961941726027847262673409)
                ·
                  refine ⟨721456294520885447005057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 961941726027847262673409 721456294520885447005057)
                  ·
                    refine ⟨541092220890664085253793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 721456294520885447005057 541092220890664085253793)
                    ·
                      refine ⟨405819165667998063940345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 541092220890664085253793 405819165667998063940345)
                      ·
                        rfl

theorem cell23_790330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2].length) (baseStart_790330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790330 prefixEnd_790330 := by exact prefixLift 790330
  have htrace : WordTrace (prefixWord ++ tailWord_790330) baseStart_790330 baseEnd_790330 := by
    simpa [prefixWord, tailWord_790330, baseEnd_790330] using wordTrace_append hprefix tailTrace_790330
  have hstable : (prefixWord ++ tailWord_790330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790330).length < 2 ^ (prefixWord ++ tailWord_790330).sum := by decide
  have hdescent : baseEnd_790330 < baseStart_790330 := by decide
  rcases family_descends (prefixWord ++ tailWord_790330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790362 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 2, 8]
def baseStart_790362 : Nat := 118140960795 + 790362 * 2 ^ 59
def prefixEnd_790362 : Nat := 4983230072969 + 3 ^ 40 * 790362 * 2
def baseEnd_790362 : Nat := 135278532349647312913399

theorem tailTrace_790362 : CollatzResearch.WordTrace tailWord_790362 prefixEnd_790362 135278532349647312913399 := by
  unfold tailWord_790362
  simp only [CollatzResearch.WordTrace]
  refine ⟨7206717590665232982039335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19217913575107287952104893 7206717590665232982039335)
  ·
    refine ⟨10810076385997849473059003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7206717590665232982039335 10810076385997849473059003)
    ·
      refine ⟨16215114578996774209588505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10810076385997849473059003 16215114578996774209588505)
      ·
        refine ⟨12161335934247580657191379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16215114578996774209588505 12161335934247580657191379)
        ·
          refine ⟨18242003901371370985787069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12161335934247580657191379 18242003901371370985787069)
          ·
            refine ⟨6840751463014264119670151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18242003901371370985787069 6840751463014264119670151)
            ·
              refine ⟨10261127194521396179505227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6840751463014264119670151 10261127194521396179505227)
              ·
                refine ⟨15391690791782094269257841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10261127194521396179505227 15391690791782094269257841)
                ·
                  refine ⟨11543768093836570701943381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15391690791782094269257841 11543768093836570701943381)
                  ·
                    refine ⟨135278532349647312913399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11543768093836570701943381 135278532349647312913399)
                    ·
                      rfl

theorem cell23_790362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_790362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790362 prefixEnd_790362 := by exact prefixLift 790362
  have htrace : WordTrace (prefixWord ++ tailWord_790362) baseStart_790362 baseEnd_790362 := by
    simpa [prefixWord, tailWord_790362, baseEnd_790362] using wordTrace_append hprefix tailTrace_790362
  have hstable : (prefixWord ++ tailWord_790362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790362).length < 2 ^ (prefixWord ++ tailWord_790362).sum := by decide
  have hdescent : baseEnd_790362 < baseStart_790362 := by decide
  rcases family_descends (prefixWord ++ tailWord_790362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790369 : List Nat := [1, 2, 3, 1, 1, 1, 4, 3, 2, 1, 4]
def baseStart_790369 : Nat := 118140960795 + 790369 * 2 ^ 59
def prefixEnd_790369 : Nat := 4983230072969 + 3 ^ 40 * 790369 * 2
def baseEnd_790369 : Nat := 405839191413523411352665

theorem tailTrace_790369 : CollatzResearch.WordTrace tailWord_790369 prefixEnd_790369 405839191413523411352665 := by
  unfold tailWord_790369
  simp only [CollatzResearch.WordTrace]
  refine ⟨28827125673635572123662161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19218083782423714749108107 28827125673635572123662161)
  ·
    refine ⟨21620344255226679092746621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28827125673635572123662161 21620344255226679092746621)
    ·
      refine ⟨8107629095710004659779983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21620344255226679092746621 8107629095710004659779983)
      ·
        refine ⟨12161443643565006989669975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8107629095710004659779983 12161443643565006989669975)
        ·
          refine ⟨18242165465347510484504963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12161443643565006989669975 18242165465347510484504963)
          ·
            refine ⟨27363248198021265726757445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18242165465347510484504963 27363248198021265726757445)
            ·
              refine ⟨5130609037128987323767021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27363248198021265726757445 5130609037128987323767021)
              ·
                refine ⟨1923978388923370246412633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5130609037128987323767021 1923978388923370246412633)
                ·
                  refine ⟨1442983791692527684809475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1923978388923370246412633 1442983791692527684809475)
                  ·
                    refine ⟨2164475687538791527214213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1442983791692527684809475 2164475687538791527214213)
                    ·
                      refine ⟨405839191413523411352665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2164475687538791527214213 405839191413523411352665)
                      ·
                        rfl

theorem cell23_790369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_790369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790369 prefixEnd_790369 := by exact prefixLift 790369
  have htrace : WordTrace (prefixWord ++ tailWord_790369) baseStart_790369 baseEnd_790369 := by
    simpa [prefixWord, tailWord_790369, baseEnd_790369] using wordTrace_append hprefix tailTrace_790369
  have hstable : (prefixWord ++ tailWord_790369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790369).length < 2 ^ (prefixWord ++ tailWord_790369).sum := by decide
  have hdescent : baseEnd_790369 < baseStart_790369 := by decide
  rcases family_descends (prefixWord ++ tailWord_790369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790409 : List Nat := [1, 2, 1, 1, 5, 1, 3, 3, 6]
def baseStart_790409 : Nat := 118140960795 + 790409 * 2 ^ 59
def prefixEnd_790409 : Nat := 4983230072969 + 3 ^ 40 * 790409 * 2
def baseEnd_790409 : Nat := 45095525626633694983609

theorem tailTrace_790409 : CollatzResearch.WordTrace tailWord_790409 prefixEnd_790409 45095525626633694983609 := by
  unfold tailWord_790409
  simp only [CollatzResearch.WordTrace]
  refine ⟨28828584593490658955118281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19219056395660439303412187 28828584593490658955118281)
  ·
    refine ⟨21621438445117994216338711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28828584593490658955118281 21621438445117994216338711)
    ·
      refine ⟨32432157667676991324508067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21621438445117994216338711 32432157667676991324508067)
      ·
        refine ⟨48648236501515486986762101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32432157667676991324508067 48648236501515486986762101)
        ·
          refine ⟨4560772172017076905008947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48648236501515486986762101 4560772172017076905008947)
          ·
            refine ⟨6841158258025615357513421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4560772172017076905008947 6841158258025615357513421)
            ·
              refine ⟨2565434346759605759067533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6841158258025615357513421 2565434346759605759067533)
              ·
                refine ⟨962037880034852159650325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2565434346759605759067533 962037880034852159650325)
                ·
                  refine ⟨45095525626633694983609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 962037880034852159650325 45095525626633694983609)
                  ·
                    rfl

theorem cell23_790409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 6].length) (baseStart_790409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790409 prefixEnd_790409 := by exact prefixLift 790409
  have htrace : WordTrace (prefixWord ++ tailWord_790409) baseStart_790409 baseEnd_790409 := by
    simpa [prefixWord, tailWord_790409, baseEnd_790409] using wordTrace_append hprefix tailTrace_790409
  have hstable : (prefixWord ++ tailWord_790409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790409).length < 2 ^ (prefixWord ++ tailWord_790409).sum := by decide
  have hdescent : baseEnd_790409 < baseStart_790409 := by decide
  rcases family_descends (prefixWord ++ tailWord_790409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790459 : List Nat := [1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 4]
def baseStart_790459 : Nat := 118140960795 + 790459 * 2 ^ 59
def prefixEnd_790459 : Nat := 4983230072969 + 3 ^ 40 * 790459 * 2
def baseEnd_790459 : Nat := 405885404672428059227251

theorem tailTrace_790459 : CollatzResearch.WordTrace tailWord_790459 prefixEnd_790459 405885404672428059227251 := by
  unfold tailWord_790459
  simp only [CollatzResearch.WordTrace]
  refine ⟨28830408243309517494438431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19220272162206344996292287 28830408243309517494438431)
  ·
    refine ⟨43245612364964276241657647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28830408243309517494438431 43245612364964276241657647)
    ·
      refine ⟨64868418547446414362486471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43245612364964276241657647 64868418547446414362486471)
      ·
        refine ⟨97302627821169621543729707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64868418547446414362486471 97302627821169621543729707)
        ·
          refine ⟨145953941731754432315594561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97302627821169621543729707 145953941731754432315594561)
          ·
            refine ⟨109465456298815824236695921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145953941731754432315594561 109465456298815824236695921)
            ·
              refine ⟨82099092224111868177521941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109465456298815824236695921 82099092224111868177521941)
              ·
                refine ⟨3848394948005243820821341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82099092224111868177521941 3848394948005243820821341)
                ·
                  refine ⟨1443148105501966432808003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3848394948005243820821341 1443148105501966432808003)
                  ·
                    refine ⟨2164722158252949649212005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1443148105501966432808003 2164722158252949649212005)
                    ·
                      refine ⟨405885404672428059227251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2164722158252949649212005 405885404672428059227251)
                      ·
                        rfl

theorem cell23_790459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 4].length) (baseStart_790459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790459 prefixEnd_790459 := by exact prefixLift 790459
  have htrace : WordTrace (prefixWord ++ tailWord_790459) baseStart_790459 baseEnd_790459 := by
    simpa [prefixWord, tailWord_790459, baseEnd_790459] using wordTrace_append hprefix tailTrace_790459
  have hstable : (prefixWord ++ tailWord_790459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790459).length < 2 ^ (prefixWord ++ tailWord_790459).sum := by decide
  have hdescent : baseEnd_790459 < baseStart_790459 := by decide
  rcases family_descends (prefixWord ++ tailWord_790459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790476 : List Nat := [2, 2, 1, 4, 1, 2, 2, 1, 3, 1, 4]
def baseStart_790476 : Nat := 118140960795 + 790476 * 2 ^ 59
def prefixEnd_790476 : Nat := 4983230072969 + 3 ^ 40 * 790476 * 2
def baseEnd_790476 : Nat := 405894133843554492714673

theorem tailTrace_790476 : CollatzResearch.WordTrace tailWord_790476 prefixEnd_790476 405894133843554492714673 := by
  unfold tailWord_790476
  simp only [CollatzResearch.WordTrace]
  refine ⟨14415514142123964698903641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19220685522831952931871521 14415514142123964698903641)
  ·
    refine ⟨10811635606592973524177731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14415514142123964698903641 10811635606592973524177731)
    ·
      refine ⟨16217453409889460286266597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10811635606592973524177731 16217453409889460286266597)
      ·
        refine ⟨3040772514354273803674987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16217453409889460286266597 3040772514354273803674987)
        ·
          refine ⟨4561158771531410705512481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3040772514354273803674987 4561158771531410705512481)
          ·
            refine ⟨3420869078648558029134361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4561158771531410705512481 3420869078648558029134361)
            ·
              refine ⟨2565651808986418521850771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3420869078648558029134361 2565651808986418521850771)
              ·
                refine ⟨3848477713479627782776157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2565651808986418521850771 3848477713479627782776157)
                ·
                  refine ⟨1443179142554860418541059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3848477713479627782776157 1443179142554860418541059)
                  ·
                    refine ⟨2164768713832290627811589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1443179142554860418541059 2164768713832290627811589)
                    ·
                      refine ⟨405894133843554492714673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2164768713832290627811589 405894133843554492714673)
                      ·
                        rfl

theorem cell23_790476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_790476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790476 prefixEnd_790476 := by exact prefixLift 790476
  have htrace : WordTrace (prefixWord ++ tailWord_790476) baseStart_790476 baseEnd_790476 := by
    simpa [prefixWord, tailWord_790476, baseEnd_790476] using wordTrace_append hprefix tailTrace_790476
  have hstable : (prefixWord ++ tailWord_790476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790476).length < 2 ^ (prefixWord ++ tailWord_790476).sum := by decide
  have hdescent : baseEnd_790476 < baseStart_790476 := by decide
  rcases family_descends (prefixWord ++ tailWord_790476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790490 : List Nat := [3, 1, 1, 2, 5, 2, 2, 1, 1, 5]
def baseStart_790490 : Nat := 118140960795 + 790490 * 2 ^ 59
def prefixEnd_790490 : Nat := 4983230072969 + 3 ^ 40 * 790490 * 2
def baseEnd_790490 : Nat := 135300440857572479313203

theorem tailTrace_790490 : CollatzResearch.WordTrace tailWord_790490 prefixEnd_790490 135300440857572479313203 := by
  unfold tailWord_790490
  simp only [CollatzResearch.WordTrace]
  refine ⟨7207884726549302447204231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19221025937464806525877949 7207884726549302447204231)
  ·
    refine ⟨10811827089823953670806347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7207884726549302447204231 10811827089823953670806347)
    ·
      refine ⟨16217740634735930506209521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10811827089823953670806347 16217740634735930506209521)
      ·
        refine ⟨12163305476051947879657141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16217740634735930506209521 12163305476051947879657141)
        ·
          refine ⟨1140309888379870113717857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12163305476051947879657141 1140309888379870113717857)
          ·
            refine ⟨855232416284902585288393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1140309888379870113717857 855232416284902585288393)
            ·
              refine ⟨641424312213676938966295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 855232416284902585288393 641424312213676938966295)
              ·
                refine ⟨962136468320515408449443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641424312213676938966295 962136468320515408449443)
                ·
                  refine ⟨1443204702480773112674165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 962136468320515408449443 1443204702480773112674165)
                  ·
                    refine ⟨135300440857572479313203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1443204702480773112674165 135300440857572479313203)
                    ·
                      rfl

theorem cell23_790490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 1, 5].length) (baseStart_790490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790490 prefixEnd_790490 := by exact prefixLift 790490
  have htrace : WordTrace (prefixWord ++ tailWord_790490) baseStart_790490 baseEnd_790490 := by
    simpa [prefixWord, tailWord_790490, baseEnd_790490] using wordTrace_append hprefix tailTrace_790490
  have hstable : (prefixWord ++ tailWord_790490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790490).length < 2 ^ (prefixWord ++ tailWord_790490).sum := by decide
  have hdescent : baseEnd_790490 < baseStart_790490 := by decide
  rcases family_descends (prefixWord ++ tailWord_790490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790499 : List Nat := [1, 1, 1, 6, 1, 3, 10]
def baseStart_790499 : Nat := 118140960795 + 790499 * 2 ^ 59
def prefixEnd_790499 : Nat := 4983230072969 + 3 ^ 40 * 790499 * 2
def baseEnd_790499 : Nat := 5011184492575406206507

theorem tailTrace_790499 : CollatzResearch.WordTrace tailWord_790499 prefixEnd_790499 5011184492575406206507 := by
  unfold tailWord_790499
  simp only [CollatzResearch.WordTrace]
  refine ⟨28831867163164604325894551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19221244775443069550596367 28831867163164604325894551)
  ·
    refine ⟨43247800744746906488841827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28831867163164604325894551 43247800744746906488841827)
    ·
      refine ⟨64871701117120359733262741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43247800744746906488841827 64871701117120359733262741)
      ·
        refine ⟨3040860989865016862496691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64871701117120359733262741 3040860989865016862496691)
        ·
          refine ⟨4561291484797525293745037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3040860989865016862496691 4561291484797525293745037)
          ·
            refine ⟨1710484306799071985154389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4561291484797525293745037 1710484306799071985154389)
            ·
              refine ⟨5011184492575406206507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1710484306799071985154389 5011184492575406206507)
              ·
                rfl

theorem cell23_790499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 10].length) (baseStart_790499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790499 prefixEnd_790499 := by exact prefixLift 790499
  have htrace : WordTrace (prefixWord ++ tailWord_790499) baseStart_790499 baseEnd_790499 := by
    simpa [prefixWord, tailWord_790499, baseEnd_790499] using wordTrace_append hprefix tailTrace_790499
  have hstable : (prefixWord ++ tailWord_790499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790499).length < 2 ^ (prefixWord ++ tailWord_790499).sum := by decide
  have hdescent : baseEnd_790499 < baseStart_790499 := by decide
  rcases family_descends (prefixWord ++ tailWord_790499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790503 : List Nat := [1, 1, 5, 2, 3, 1, 1, 1, 4, 4]
def baseStart_790503 : Nat := 118140960795 + 790503 * 2 ^ 59
def prefixEnd_790503 : Nat := 4983230072969 + 3 ^ 40 * 790503 * 2
def baseEnd_790503 : Nat := 135302665940408629025683

theorem tailTrace_790503 : CollatzResearch.WordTrace tailWord_790503 prefixEnd_790503 135302665940408629025683 := by
  unfold tailWord_790503
  simp only [CollatzResearch.WordTrace]
  refine ⟨28832013055150113009040163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19221342036766742006026775 28832013055150113009040163)
  ·
    refine ⟨43248019582725169513560245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28832013055150113009040163 43248019582725169513560245)
    ·
      refine ⟨4054501835880484641896273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43248019582725169513560245 4054501835880484641896273)
      ·
        refine ⟨3040876376910363481422205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4054501835880484641896273 3040876376910363481422205)
        ·
          refine ⟨1140328641341386305533327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3040876376910363481422205 1140328641341386305533327)
          ·
            refine ⟨1710492962012079458299991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1140328641341386305533327 1710492962012079458299991)
            ·
              refine ⟨2565739443018119187449987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1710492962012079458299991 2565739443018119187449987)
              ·
                refine ⟨3848609164527178781174981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2565739443018119187449987 3848609164527178781174981)
                ·
                  refine ⟨721614218348846021470309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3848609164527178781174981 721614218348846021470309)
                  ·
                    refine ⟨135302665940408629025683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 721614218348846021470309 135302665940408629025683)
                    ·
                      rfl

theorem cell23_790503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_790503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790503 prefixEnd_790503 := by exact prefixLift 790503
  have htrace : WordTrace (prefixWord ++ tailWord_790503) baseStart_790503 baseEnd_790503 := by
    simpa [prefixWord, tailWord_790503, baseEnd_790503] using wordTrace_append hprefix tailTrace_790503
  have hstable : (prefixWord ++ tailWord_790503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790503).length < 2 ^ (prefixWord ++ tailWord_790503).sum := by decide
  have hdescent : baseEnd_790503 < baseStart_790503 := by decide
  rcases family_descends (prefixWord ++ tailWord_790503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790510 : List Nat := [4, 1, 2, 1, 3, 1, 1, 3, 3, 2, 2]
def baseStart_790510 : Nat := 118140960795 + 790510 * 2 ^ 59
def prefixEnd_790510 : Nat := 4983230072969 + 3 ^ 40 * 790510 * 2
def baseEnd_790510 : Nat := 405911592185807359689517

theorem tailTrace_790510 : CollatzResearch.WordTrace tailWord_790510 prefixEnd_790510 405911592185807359689517 := by
  unfold tailWord_790510
  simp only [CollatzResearch.WordTrace]
  refine ⟨3604033545765594150568123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19221512244083168803029989 3604033545765594150568123)
  ·
    refine ⟨5406050318648391225852185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3604033545765594150568123 5406050318648391225852185)
    ·
      refine ⟨4054537738986293419389139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5406050318648391225852185 4054537738986293419389139)
      ·
        refine ⟨6081806608479440129083709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4054537738986293419389139 6081806608479440129083709)
        ·
          refine ⟨2280677478179790048406391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6081806608479440129083709 2280677478179790048406391)
          ·
            refine ⟨3421016217269685072609587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2280677478179790048406391 3421016217269685072609587)
            ·
              refine ⟨5131524325904527608914381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3421016217269685072609587 5131524325904527608914381)
              ·
                refine ⟨1924321622214197853342893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5131524325904527608914381 1924321622214197853342893)
                ·
                  refine ⟨721620608330324195003585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1924321622214197853342893 721620608330324195003585)
                  ·
                    refine ⟨541215456247743146252689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 721620608330324195003585 541215456247743146252689)
                    ·
                      refine ⟨405911592185807359689517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 541215456247743146252689 405911592185807359689517)
                      ·
                        rfl

theorem cell23_790510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_790510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790510 prefixEnd_790510 := by exact prefixLift 790510
  have htrace : WordTrace (prefixWord ++ tailWord_790510) baseStart_790510 baseEnd_790510 := by
    simpa [prefixWord, tailWord_790510, baseEnd_790510] using wordTrace_append hprefix tailTrace_790510
  have hstable : (prefixWord ++ tailWord_790510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790510).length < 2 ^ (prefixWord ++ tailWord_790510).sum := by decide
  have hdescent : baseEnd_790510 < baseStart_790510 := by decide
  rcases family_descends (prefixWord ++ tailWord_790510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790539 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 5]
def baseStart_790539 : Nat := 118140960795 + 790539 * 2 ^ 59
def prefixEnd_790539 : Nat := 4983230072969 + 3 ^ 40 * 790539 * 2
def baseEnd_790539 : Nat := 405926483124787746226883

theorem tailTrace_790539 : CollatzResearch.WordTrace tailWord_790539 prefixEnd_790539 405926483124787746226883 := by
  unfold tailWord_790539
  simp only [CollatzResearch.WordTrace]
  refine ⟨28833326083019691157350671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19222217388679794104900447 28833326083019691157350671)
  ·
    refine ⟨43249989124529536736026007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28833326083019691157350671 43249989124529536736026007)
    ·
      refine ⟨64874983686794305104039011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43249989124529536736026007 64874983686794305104039011)
      ·
        refine ⟨97312475530191457656058517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64874983686794305104039011 97312475530191457656058517)
        ·
          refine ⟨4561522290477724577627743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 97312475530191457656058517 4561522290477724577627743)
          ·
            refine ⟨6842283435716586866441615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4561522290477724577627743 6842283435716586866441615)
            ·
              refine ⟨10263425153574880299662423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6842283435716586866441615 10263425153574880299662423)
              ·
                refine ⟨15395137730362320449493635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10263425153574880299662423 15395137730362320449493635)
                ·
                  refine ⟨23092706595543480674240453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15395137730362320449493635 23092706595543480674240453)
                  ·
                    refine ⟨4329882486664402626420085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23092706595543480674240453 4329882486664402626420085)
                    ·
                      refine ⟨405926483124787746226883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4329882486664402626420085 405926483124787746226883)
                      ·
                        rfl

theorem cell23_790539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 5].length) (baseStart_790539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790539 prefixEnd_790539 := by exact prefixLift 790539
  have htrace : WordTrace (prefixWord ++ tailWord_790539) baseStart_790539 baseEnd_790539 := by
    simpa [prefixWord, tailWord_790539, baseEnd_790539] using wordTrace_append hprefix tailTrace_790539
  have hstable : (prefixWord ++ tailWord_790539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790539).length < 2 ^ (prefixWord ++ tailWord_790539).sum := by decide
  have hdescent : baseEnd_790539 < baseStart_790539 := by decide
  rcases family_descends (prefixWord ++ tailWord_790539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790577 : List Nat := [1, 2, 2, 3, 1, 5, 2, 1, 2, 1, 3]
def baseStart_790577 : Nat := 118140960795 + 790577 * 2 ^ 59
def prefixEnd_790577 : Nat := 4983230072969 + 3 ^ 40 * 790577 * 2
def baseEnd_790577 : Nat := 405945995389658597551709

theorem tailTrace_790577 : CollatzResearch.WordTrace tailWord_790577 prefixEnd_790577 405945995389658597551709 := by
  unfold tailWord_790577
  simp only [CollatzResearch.WordTrace]
  refine ⟨28834712056882023647233985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19223141371254682431489323 28834712056882023647233985)
  ·
    refine ⟨21626034042661517735425489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28834712056882023647233985 21626034042661517735425489)
    ·
      refine ⟨16219525531996138301569117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21626034042661517735425489 16219525531996138301569117)
      ·
        refine ⟨6082322074498551863088419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16219525531996138301569117 6082322074498551863088419)
        ·
          refine ⟨9123483111747827794632629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6082322074498551863088419 9123483111747827794632629)
          ·
            refine ⟨855326541726358855746809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9123483111747827794632629 855326541726358855746809)
            ·
              refine ⟨641494906294769141810107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 855326541726358855746809 641494906294769141810107)
              ·
                refine ⟨962242359442153712715161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641494906294769141810107 962242359442153712715161)
                ·
                  refine ⟨721681769581615284536371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 962242359442153712715161 721681769581615284536371)
                  ·
                    refine ⟨1082522654372422926804557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 721681769581615284536371 1082522654372422926804557)
                    ·
                      refine ⟨405945995389658597551709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1082522654372422926804557 405945995389658597551709)
                      ·
                        rfl

theorem cell23_790577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_790577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790577 prefixEnd_790577 := by exact prefixLift 790577
  have htrace : WordTrace (prefixWord ++ tailWord_790577) baseStart_790577 baseEnd_790577 := by
    simpa [prefixWord, tailWord_790577, baseEnd_790577] using wordTrace_append hprefix tailTrace_790577
  have hstable : (prefixWord ++ tailWord_790577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790577).length < 2 ^ (prefixWord ++ tailWord_790577).sum := by decide
  have hdescent : baseEnd_790577 < baseStart_790577 := by decide
  rcases family_descends (prefixWord ++ tailWord_790577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790653 : List Nat := [1, 4, 1, 1, 3, 2, 3, 1, 2, 5]
def baseStart_790653 : Nat := 118140960795 + 790653 * 2 ^ 59
def prefixEnd_790653 : Nat := 4983230072969 + 3 ^ 40 * 790653 * 2
def baseEnd_790653 : Nat := 135328339973133433400453

theorem tailTrace_790653 : CollatzResearch.WordTrace tailWord_790653 prefixEnd_790653 135328339973133433400453 := by
  unfold tailWord_790653
  simp only [CollatzResearch.WordTrace]
  refine ⟨28837484004606688627000613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19224989336404459084667075 28837484004606688627000613)
  ·
    refine ⟨5407028250863754117562615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28837484004606688627000613 5407028250863754117562615)
    ·
      refine ⟨8110542376295631176343923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5407028250863754117562615 8110542376295631176343923)
      ·
        refine ⟨12165813564443446764515885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8110542376295631176343923 12165813564443446764515885)
        ·
          refine ⟨4562180086666292536693457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12165813564443446764515885 4562180086666292536693457)
          ·
            refine ⟨3421635064999719402520093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4562180086666292536693457 3421635064999719402520093)
            ·
              refine ⟨1283113149374894775945035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3421635064999719402520093 1283113149374894775945035)
              ·
                refine ⟨1924669724062342163917553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1283113149374894775945035 1924669724062342163917553)
                ·
                  refine ⟨1443502293046756622938165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1924669724062342163917553 1443502293046756622938165)
                  ·
                    refine ⟨135328339973133433400453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1443502293046756622938165 135328339973133433400453)
                    ·
                      rfl

theorem cell23_790653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_790653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790653 prefixEnd_790653 := by exact prefixLift 790653
  have htrace : WordTrace (prefixWord ++ tailWord_790653) baseStart_790653 baseEnd_790653 := by
    simpa [prefixWord, tailWord_790653, baseEnd_790653] using wordTrace_append hprefix tailTrace_790653
  have hstable : (prefixWord ++ tailWord_790653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790653).length < 2 ^ (prefixWord ++ tailWord_790653).sum := by decide
  have hdescent : baseEnd_790653 < baseStart_790653 := by decide
  rcases family_descends (prefixWord ++ tailWord_790653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790708 : List Nat := [2, 5, 3, 1, 2, 1, 1, 3, 5]
def baseStart_790708 : Nat := 118140960795 + 790708 * 2 ^ 59
def prefixEnd_790708 : Nat := 4983230072969 + 3 ^ 40 * 790708 * 2
def baseEnd_790708 : Nat := 45112584595044176112623

theorem tailTrace_790708 : CollatzResearch.WordTrace tailWord_790708 prefixEnd_790708 45112584595044176112623 := by
  unfold tailWord_790708
  simp only [CollatzResearch.WordTrace]
  refine ⟨14419745009703716510126389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19226326679604955346835185 14419745009703716510126389)
  ·
    refine ⟨1351851094659723422824349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14419745009703716510126389 1351851094659723422824349)
    ·
      refine ⟨506944160497396283559131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1351851094659723422824349 506944160497396283559131)
      ·
        refine ⟨760416240746094425338697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506944160497396283559131 760416240746094425338697)
        ·
          refine ⟨570312180559570819004023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 760416240746094425338697 570312180559570819004023)
          ·
            refine ⟨855468270839356228506035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570312180559570819004023 855468270839356228506035)
            ·
              refine ⟨1283202406259034342759053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 855468270839356228506035 1283202406259034342759053)
              ·
                refine ⟨481200902347137878534645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1283202406259034342759053 481200902347137878534645)
                ·
                  refine ⟨45112584595044176112623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 481200902347137878534645 45112584595044176112623)
                  ·
                    rfl

theorem cell23_790708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_790708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790708 prefixEnd_790708 := by exact prefixLift 790708
  have htrace : WordTrace (prefixWord ++ tailWord_790708) baseStart_790708 baseEnd_790708 := by
    simpa [prefixWord, tailWord_790708, baseEnd_790708] using wordTrace_append hprefix tailTrace_790708
  have hstable : (prefixWord ++ tailWord_790708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790708).length < 2 ^ (prefixWord ++ tailWord_790708).sum := by decide
  have hdescent : baseEnd_790708 < baseStart_790708 := by decide
  rcases family_descends (prefixWord ++ tailWord_790708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790734 : List Nat := [4, 1, 1, 1, 4, 2, 3, 2, 1, 4]
def baseStart_790734 : Nat := 118140960795 + 790734 * 2 ^ 59
def prefixEnd_790734 : Nat := 4983230072969 + 3 ^ 40 * 790734 * 2
def baseEnd_790734 : Nat := 135342203950804827762829

theorem tailTrace_790734 : CollatzResearch.WordTrace tailWord_790734 prefixEnd_790734 135342203950804827762829 := by
  unfold tailWord_790734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3605054789664154932587407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19226958878208826307132837 3605054789664154932587407)
  ·
    refine ⟨5407582184496232398881111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3605054789664154932587407 5407582184496232398881111)
    ·
      refine ⟨8111373276744348598321667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5407582184496232398881111 8111373276744348598321667)
      ·
        refine ⟨12167059915116522897482501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8111373276744348598321667 12167059915116522897482501)
        ·
          refine ⟨2281323734084348043277969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12167059915116522897482501 2281323734084348043277969)
          ·
            refine ⟨1710992800563261032458477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2281323734084348043277969 1710992800563261032458477)
            ·
              refine ⟨641622300211222887171929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1710992800563261032458477 641622300211222887171929)
              ·
                refine ⟨481216725158417165378947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 641622300211222887171929 481216725158417165378947)
                ·
                  refine ⟨721825087737625748068421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 481216725158417165378947 721825087737625748068421)
                  ·
                    refine ⟨135342203950804827762829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 721825087737625748068421 135342203950804827762829)
                    ·
                      rfl

theorem cell23_790734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_790734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790734 prefixEnd_790734 := by exact prefixLift 790734
  have htrace : WordTrace (prefixWord ++ tailWord_790734) baseStart_790734 baseEnd_790734 := by
    simpa [prefixWord, tailWord_790734, baseEnd_790734] using wordTrace_append hprefix tailTrace_790734
  have hstable : (prefixWord ++ tailWord_790734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790734).length < 2 ^ (prefixWord ++ tailWord_790734).sum := by decide
  have hdescent : baseEnd_790734 < baseStart_790734 := by decide
  rcases family_descends (prefixWord ++ tailWord_790734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790760 : List Nat := [2, 1, 4, 1, 2, 2, 3, 2, 1, 5]
def baseStart_790760 : Nat := 118140960795 + 790760 * 2 ^ 59
def prefixEnd_790760 : Nat := 4983230072969 + 3 ^ 40 * 790760 * 2
def baseEnd_790760 : Nat := 135346654116477127187789

theorem tailTrace_790760 : CollatzResearch.WordTrace tailWord_790760 prefixEnd_790760 135346654116477127187789 := by
  unfold tailWord_790760
  simp only [CollatzResearch.WordTrace]
  refine ⟨14420693307609522950572867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19227591076812697267430489 14420693307609522950572867)
  ·
    refine ⟨21631039961414284425859301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14420693307609522950572867 21631039961414284425859301)
    ·
      refine ⟨4055819992765178329848619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21631039961414284425859301 4055819992765178329848619)
      ·
        refine ⟨6083729989147767494772929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4055819992765178329848619 6083729989147767494772929)
        ·
          refine ⟨4562797491860825621079697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6083729989147767494772929 4562797491860825621079697)
          ·
            refine ⟨3422098118895619215809773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4562797491860825621079697 3422098118895619215809773)
            ·
              refine ⟨1283286794585857205928665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3422098118895619215809773 1283286794585857205928665)
              ·
                refine ⟨962465095939392904446499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1283286794585857205928665 962465095939392904446499)
                ·
                  refine ⟨1443697643909089356669749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 962465095939392904446499 1443697643909089356669749)
                  ·
                    refine ⟨135346654116477127187789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1443697643909089356669749 135346654116477127187789)
                    ·
                      rfl

theorem cell23_790760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_790760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790760 prefixEnd_790760 := by exact prefixLift 790760
  have htrace : WordTrace (prefixWord ++ tailWord_790760) baseStart_790760 baseEnd_790760 := by
    simpa [prefixWord, tailWord_790760, baseEnd_790760] using wordTrace_append hprefix tailTrace_790760
  have hstable : (prefixWord ++ tailWord_790760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790760).length < 2 ^ (prefixWord ++ tailWord_790760).sum := by decide
  have hdescent : baseEnd_790760 < baseStart_790760 := by decide
  rcases family_descends (prefixWord ++ tailWord_790760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790763 : List Nat := [1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 4]
def baseStart_790763 : Nat := 118140960795 + 790763 * 2 ^ 59
def prefixEnd_790763 : Nat := 4983230072969 + 3 ^ 40 * 790763 * 2
def baseEnd_790763 : Nat := 406041502791394869825853

theorem tailTrace_790763 : CollatzResearch.WordTrace tailWord_790763 prefixEnd_790763 406041502791394869825853 := by
  unfold tailWord_790763
  simp only [CollatzResearch.WordTrace]
  refine ⟨28841496034208177413504943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19227664022805451609003295 28841496034208177413504943)
  ·
    refine ⟨43262244051312266120257415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28841496034208177413504943 43262244051312266120257415)
    ·
      refine ⟨64893366076968399180386123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43262244051312266120257415 64893366076968399180386123)
      ·
        refine ⟨97340049115452598770579185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64893366076968399180386123 97340049115452598770579185)
        ·
          refine ⟨73005036836589449077934389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97340049115452598770579185 73005036836589449077934389)
          ·
            refine ⟨6844222203430260851056349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73005036836589449077934389 6844222203430260851056349)
            ·
              refine ⟨2566583326286347819146131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6844222203430260851056349 2566583326286347819146131)
              ·
                refine ⟨3849874989429521728719197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2566583326286347819146131 3849874989429521728719197)
                ·
                  refine ⟨1443703121036070648269699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3849874989429521728719197 1443703121036070648269699)
                  ·
                    refine ⟨2165554681554105972404549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1443703121036070648269699 2165554681554105972404549)
                    ·
                      refine ⟨406041502791394869825853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2165554681554105972404549 406041502791394869825853)
                      ·
                        rfl

theorem cell23_790763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 4].length) (baseStart_790763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790763 prefixEnd_790763 := by exact prefixLift 790763
  have htrace : WordTrace (prefixWord ++ tailWord_790763) baseStart_790763 baseEnd_790763 := by
    simpa [prefixWord, tailWord_790763, baseEnd_790763] using wordTrace_append hprefix tailTrace_790763
  have hstable : (prefixWord ++ tailWord_790763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790763).length < 2 ^ (prefixWord ++ tailWord_790763).sum := by decide
  have hdescent : baseEnd_790763 < baseStart_790763 := by decide
  rcases family_descends (prefixWord ++ tailWord_790763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790767 : List Nat := [1, 1, 2, 1, 6, 2, 2, 1, 2, 3, 2]
def baseStart_790767 : Nat := 118140960795 + 790767 * 2 ^ 59
def prefixEnd_790767 : Nat := 4983230072969 + 3 ^ 40 * 790767 * 2
def baseEnd_790767 : Nat := 406043556714012854175835

theorem tailTrace_790767 : CollatzResearch.WordTrace tailWord_790767 prefixEnd_790767 406043556714012854175835 := by
  unfold tailWord_790767
  simp only [CollatzResearch.WordTrace]
  refine ⟨28841641926193686096650555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19227761284129124064433703 28841641926193686096650555)
  ·
    refine ⟨43262462889290529144975833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28841641926193686096650555 43262462889290529144975833)
    ·
      refine ⟨32446847166967896858731875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43262462889290529144975833 32446847166967896858731875)
      ·
        refine ⟨48670270750451845288097813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32446847166967896858731875 48670270750451845288097813)
        ·
          refine ⟨2281418941427430247879585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48670270750451845288097813 2281418941427430247879585)
          ·
            refine ⟨1711064206070572685909689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2281418941427430247879585 1711064206070572685909689)
            ·
              refine ⟨1283298154552929514432267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1711064206070572685909689 1283298154552929514432267)
              ·
                refine ⟨1924947231829394271648401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1283298154552929514432267 1924947231829394271648401)
                ·
                  refine ⟨1443710423872045703736301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1924947231829394271648401 1443710423872045703736301)
                  ·
                    refine ⟨541391408952017138901113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1443710423872045703736301 541391408952017138901113)
                    ·
                      refine ⟨406043556714012854175835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 541391408952017138901113 406043556714012854175835)
                      ·
                        rfl

theorem cell23_790767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 3, 2].length) (baseStart_790767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790767 prefixEnd_790767 := by exact prefixLift 790767
  have htrace : WordTrace (prefixWord ++ tailWord_790767) baseStart_790767 baseEnd_790767 := by
    simpa [prefixWord, tailWord_790767, baseEnd_790767] using wordTrace_append hprefix tailTrace_790767
  have hstable : (prefixWord ++ tailWord_790767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790767).length < 2 ^ (prefixWord ++ tailWord_790767).sum := by decide
  have hdescent : baseEnd_790767 < baseStart_790767 := by decide
  rcases family_descends (prefixWord ++ tailWord_790767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790791 : List Nat := [1, 1, 4, 5, 1, 1, 1, 4, 1, 1, 3]
def baseStart_790791 : Nat := 118140960795 + 790791 * 2 ^ 59
def prefixEnd_790791 : Nat := 4983230072969 + 3 ^ 40 * 790791 * 2
def baseEnd_790791 : Nat := 406055880249720760275725

theorem tailTrace_790791 : CollatzResearch.WordTrace tailWord_790791 prefixEnd_790791 406055880249720760275725 := by
  unfold tailWord_790791
  simp only [CollatzResearch.WordTrace]
  refine ⟨28842517278106738195524227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19228344852071158797016151 28842517278106738195524227)
  ·
    refine ⟨43263775917160107293286341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28842517278106738195524227 43263775917160107293286341)
    ·
      refine ⟨8111957984467520117491189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43263775917160107293286341 8111957984467520117491189)
      ·
        refine ⟨760496061043830011014799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8111957984467520117491189 760496061043830011014799)
        ·
          refine ⟨1140744091565745016522199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 760496061043830011014799 1140744091565745016522199)
          ·
            refine ⟨1711116137348617524783299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1140744091565745016522199 1711116137348617524783299)
            ·
              refine ⟨2566674206022926287174949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1711116137348617524783299 2566674206022926287174949)
              ·
                refine ⟨481251413629298678845303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2566674206022926287174949 481251413629298678845303)
                ·
                  refine ⟨721877120443948018267955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 481251413629298678845303 721877120443948018267955)
                  ·
                    refine ⟨1082815680665922027401933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 721877120443948018267955 1082815680665922027401933)
                    ·
                      refine ⟨406055880249720760275725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1082815680665922027401933 406055880249720760275725)
                      ·
                        rfl

theorem cell23_790791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_790791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790791 prefixEnd_790791 := by exact prefixLift 790791
  have htrace : WordTrace (prefixWord ++ tailWord_790791) baseStart_790791 baseEnd_790791 := by
    simpa [prefixWord, tailWord_790791, baseEnd_790791] using wordTrace_append hprefix tailTrace_790791
  have hstable : (prefixWord ++ tailWord_790791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790791).length < 2 ^ (prefixWord ++ tailWord_790791).sum := by decide
  have hdescent : baseEnd_790791 < baseStart_790791 := by decide
  rcases family_descends (prefixWord ++ tailWord_790791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790820 : List Nat := [2, 3, 1, 3, 1, 3, 3, 7]
def baseStart_790820 : Nat := 118140960795 + 790820 * 2 ^ 59
def prefixEnd_790820 : Nat := 4983230072969 + 3 ^ 40 * 790820 * 2
def baseEnd_790820 : Nat := 15039658192174116548633

theorem tailTrace_790820 : CollatzResearch.WordTrace tailWord_790820 prefixEnd_790820 15039658192174116548633 := by
  unfold tailWord_790820
  simp only [CollatzResearch.WordTrace]
  refine ⟨14421787497500838074164957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19229049996667784098886609 14421787497500838074164957)
  ·
    refine ⟨5408170311562814277811859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14421787497500838074164957 5408170311562814277811859)
    ·
      refine ⟨8112255467344221416717789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5408170311562814277811859 8112255467344221416717789)
      ·
        refine ⟨3042095800254083031269171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8112255467344221416717789 3042095800254083031269171)
        ·
          refine ⟨4563143700381124546903757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3042095800254083031269171 4563143700381124546903757)
          ·
            refine ⟨1711178887642921705088909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4563143700381124546903757 1711178887642921705088909)
            ·
              refine ⟨641692082866095639408341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1711178887642921705088909 641692082866095639408341)
              ·
                refine ⟨15039658192174116548633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 641692082866095639408341 15039658192174116548633)
                ·
                  rfl

theorem cell23_790820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 7].length) (baseStart_790820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790820 prefixEnd_790820 := by exact prefixLift 790820
  have htrace : WordTrace (prefixWord ++ tailWord_790820) baseStart_790820 baseEnd_790820 := by
    simpa [prefixWord, tailWord_790820, baseEnd_790820] using wordTrace_append hprefix tailTrace_790820
  have hstable : (prefixWord ++ tailWord_790820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790820).length < 2 ^ (prefixWord ++ tailWord_790820).sum := by decide
  have hdescent : baseEnd_790820 < baseStart_790820 := by decide
  rcases family_descends (prefixWord ++ tailWord_790820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790864 : List Nat := [2, 1, 1, 1, 1, 7, 3, 1, 2, 1, 3]
def baseStart_790864 : Nat := 118140960795 + 790864 * 2 ^ 59
def prefixEnd_790864 : Nat := 4983230072969 + 3 ^ 40 * 790864 * 2
def baseEnd_790864 : Nat := 406093364337498974662889

theorem tailTrace_790864 : CollatzResearch.WordTrace tailWord_790864 prefixEnd_790864 406093364337498974662889 := by
  unfold tailWord_790864
  simp only [CollatzResearch.WordTrace]
  refine ⟨14422589903421135831465823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19230119871228181108621097 14422589903421135831465823)
  ·
    refine ⟨21633884855131703747198735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14422589903421135831465823 21633884855131703747198735)
    ·
      refine ⟨32450827282697555620798103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21633884855131703747198735 32450827282697555620798103)
      ·
        refine ⟨48676240924046333431197155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32450827282697555620798103 48676240924046333431197155)
        ·
          refine ⟨73014361386069500146795733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48676240924046333431197155 73014361386069500146795733)
          ·
            refine ⟨1711274094986003909690525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 73014361386069500146795733 1711274094986003909690525)
            ·
              refine ⟨641727785619751466133947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1711274094986003909690525 641727785619751466133947)
              ·
                refine ⟨962591678429627199200921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641727785619751466133947 962591678429627199200921)
                ·
                  refine ⟨721943758822220399400691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 962591678429627199200921 721943758822220399400691)
                  ·
                    refine ⟨1082915638233330599101037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 721943758822220399400691 1082915638233330599101037)
                    ·
                      refine ⟨406093364337498974662889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1082915638233330599101037 406093364337498974662889)
                      ·
                        rfl

theorem cell23_790864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 2, 1, 3].length) (baseStart_790864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790864 prefixEnd_790864 := by exact prefixLift 790864
  have htrace : WordTrace (prefixWord ++ tailWord_790864) baseStart_790864 baseEnd_790864 := by
    simpa [prefixWord, tailWord_790864, baseEnd_790864] using wordTrace_append hprefix tailTrace_790864
  have hstable : (prefixWord ++ tailWord_790864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790864).length < 2 ^ (prefixWord ++ tailWord_790864).sum := by decide
  have hdescent : baseEnd_790864 < baseStart_790864 := by decide
  rcases family_descends (prefixWord ++ tailWord_790864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790873 : List Nat := [1, 2, 1, 2, 2, 2, 1, 4, 2, 1, 5]
def baseStart_790873 : Nat := 118140960795 + 790873 * 2 ^ 59
def prefixEnd_790873 : Nat := 4983230072969 + 3 ^ 40 * 790873 * 2
def baseEnd_790873 : Nat := 406097985663389439450347

theorem tailTrace_790873 : CollatzResearch.WordTrace tailWord_790873 prefixEnd_790873 406097985663389439450347 := by
  unfold tailWord_790873
  simp only [CollatzResearch.WordTrace]
  refine ⟨28845508063809666200009273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19230338709206444133339515 28845508063809666200009273)
  ·
    refine ⟨21634131047857249650006955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28845508063809666200009273 21634131047857249650006955)
    ·
      refine ⟨32451196571785874475010433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21634131047857249650006955 32451196571785874475010433)
      ·
        refine ⟨24338397428839405856257825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32451196571785874475010433 24338397428839405856257825)
        ·
          refine ⟨18253798071629554392193369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24338397428839405856257825 18253798071629554392193369)
          ·
            refine ⟨13690348553722165794145027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18253798071629554392193369 13690348553722165794145027)
            ·
              refine ⟨20535522830583248691217541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13690348553722165794145027 20535522830583248691217541)
              ·
                refine ⟨3850410530734359129603289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20535522830583248691217541 3850410530734359129603289)
                ·
                  refine ⟨2887807898050769347202467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3850410530734359129603289 2887807898050769347202467)
                  ·
                    refine ⟨4331711847076154020803701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2887807898050769347202467 4331711847076154020803701)
                    ·
                      refine ⟨406097985663389439450347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4331711847076154020803701 406097985663389439450347)
                      ·
                        rfl

theorem cell23_790873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_790873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790873 prefixEnd_790873 := by exact prefixLift 790873
  have htrace : WordTrace (prefixWord ++ tailWord_790873) baseStart_790873 baseEnd_790873 := by
    simpa [prefixWord, tailWord_790873, baseEnd_790873] using wordTrace_append hprefix tailTrace_790873
  have hstable : (prefixWord ++ tailWord_790873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790873).length < 2 ^ (prefixWord ++ tailWord_790873).sum := by decide
  have hdescent : baseEnd_790873 < baseStart_790873 := by decide
  rcases family_descends (prefixWord ++ tailWord_790873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790890 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_790890 : Nat := 118140960795 + 790890 * 2 ^ 59
def prefixEnd_790890 : Nat := 4983230072969 + 3 ^ 40 * 790890 * 2
def baseEnd_790890 : Nat := 406106714834515872937769

theorem tailTrace_790890 : CollatzResearch.WordTrace tailWord_790890 prefixEnd_790890 406106714834515872937769 := by
  unfold tailWord_790890
  simp only [CollatzResearch.WordTrace]
  refine ⟨7211532026187019525844531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19230752069832052068918749 7211532026187019525844531)
  ·
    refine ⟨10817298039280529288766797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7211532026187019525844531 10817298039280529288766797)
    ·
      refine ⟨4056486764730198483287549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10817298039280529288766797 4056486764730198483287549)
      ·
        refine ⟨1521182536773824431232831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4056486764730198483287549 1521182536773824431232831)
        ·
          refine ⟨2281773805160736646849247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1521182536773824431232831 2281773805160736646849247)
          ·
            refine ⟨3422660707741104970273871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2281773805160736646849247 3422660707741104970273871)
            ·
              refine ⟨5133991061611657455410807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3422660707741104970273871 5133991061611657455410807)
              ·
                refine ⟨7700986592417486183116211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5133991061611657455410807 7700986592417486183116211)
                ·
                  refine ⟨11551479888626229274674317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7700986592417486183116211 11551479888626229274674317)
                  ·
                    refine ⟨4331804958234835978002869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11551479888626229274674317 4331804958234835978002869)
                    ·
                      refine ⟨406106714834515872937769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4331804958234835978002869 406106714834515872937769)
                      ·
                        rfl

theorem cell23_790890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_790890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790890 prefixEnd_790890 := by exact prefixLift 790890
  have htrace : WordTrace (prefixWord ++ tailWord_790890) baseStart_790890 baseEnd_790890 := by
    simpa [prefixWord, tailWord_790890, baseEnd_790890] using wordTrace_append hprefix tailTrace_790890
  have hstable : (prefixWord ++ tailWord_790890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790890).length < 2 ^ (prefixWord ++ tailWord_790890).sum := by decide
  have hdescent : baseEnd_790890 < baseStart_790890 := by decide
  rcases family_descends (prefixWord ++ tailWord_790890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790920 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 1, 5, 3]
def baseStart_790920 : Nat := 118140960795 + 790920 * 2 ^ 59
def prefixEnd_790920 : Nat := 4983230072969 + 3 ^ 40 * 790920 * 2
def baseEnd_790920 : Nat := 406122119254150755562631

theorem tailTrace_790920 : CollatzResearch.WordTrace tailWord_790920 prefixEnd_790920 406122119254150755562631 := by
  unfold tailWord_790920
  simp only [CollatzResearch.WordTrace]
  refine ⟨14423611147319696613485107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19231481529759595484646809 14423611147319696613485107)
  ·
    refine ⟨21635416720979544920227661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14423611147319696613485107 21635416720979544920227661)
    ·
      refine ⟨8113281270367329345085373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21635416720979544920227661 8113281270367329345085373)
      ·
        refine ⟨3042480476387748504407015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8113281270367329345085373 3042480476387748504407015)
        ·
          refine ⟨4563720714581622756610523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3042480476387748504407015 4563720714581622756610523)
          ·
            refine ⟨6845581071872434134915785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4563720714581622756610523 6845581071872434134915785)
            ·
              refine ⟨5134185803904325601186839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6845581071872434134915785 5134185803904325601186839)
              ·
                refine ⟨7701278705856488401780259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5134185803904325601186839 7701278705856488401780259)
                ·
                  refine ⟨11551918058784732602670389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7701278705856488401780259 11551918058784732602670389)
                  ·
                    refine ⟨1082992318011068681500349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11551918058784732602670389 1082992318011068681500349)
                    ·
                      refine ⟨406122119254150755562631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1082992318011068681500349 406122119254150755562631)
                      ·
                        rfl

theorem cell23_790920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_790920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790920 prefixEnd_790920 := by exact prefixLift 790920
  have htrace : WordTrace (prefixWord ++ tailWord_790920) baseStart_790920 baseEnd_790920 := by
    simpa [prefixWord, tailWord_790920, baseEnd_790920] using wordTrace_append hprefix tailTrace_790920
  have hstable : (prefixWord ++ tailWord_790920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790920).length < 2 ^ (prefixWord ++ tailWord_790920).sum := by decide
  have hdescent : baseEnd_790920 < baseStart_790920 := by decide
  rcases family_descends (prefixWord ++ tailWord_790920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790921 : List Nat := [1, 2, 1, 1, 6, 1, 4, 1, 2, 2, 2]
def baseStart_790921 : Nat := 118140960795 + 790921 * 2 ^ 59
def prefixEnd_790921 : Nat := 4983230072969 + 3 ^ 40 * 790921 * 2
def baseEnd_790921 : Nat := 406122632734805251650127

theorem tailTrace_790921 : CollatzResearch.WordTrace tailWord_790921 prefixEnd_790921 406122632734805251650127 := by
  unfold tailWord_790921
  simp only [CollatzResearch.WordTrace]
  refine ⟨28847258767635770397756617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19231505845090513598504411 28847258767635770397756617)
  ·
    refine ⟨21635444075726827798317463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28847258767635770397756617 21635444075726827798317463)
    ·
      refine ⟨32453166113590241697476195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21635444075726827798317463 32453166113590241697476195)
      ·
        refine ⟨48679749170385362546214293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32453166113590241697476195 48679749170385362546214293)
        ·
          refine ⟨2281863242361813869353795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48679749170385362546214293 2281863242361813869353795)
          ·
            refine ⟨3422794863542720804030693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2281863242361813869353795 3422794863542720804030693)
            ·
              refine ⟨641774036914260150755755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3422794863542720804030693 641774036914260150755755)
              ·
                refine ⟨962661055371390226133633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641774036914260150755755 962661055371390226133633)
                ·
                  refine ⟨721995791528542669600225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 962661055371390226133633 721995791528542669600225)
                  ·
                    refine ⟨541496843646407002200169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 721995791528542669600225 541496843646407002200169)
                    ·
                      refine ⟨406122632734805251650127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 541496843646407002200169 406122632734805251650127)
                      ·
                        rfl

theorem cell23_790921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 2, 2, 2].length) (baseStart_790921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790921 prefixEnd_790921 := by exact prefixLift 790921
  have htrace : WordTrace (prefixWord ++ tailWord_790921) baseStart_790921 baseEnd_790921 := by
    simpa [prefixWord, tailWord_790921, baseEnd_790921] using wordTrace_append hprefix tailTrace_790921
  have hstable : (prefixWord ++ tailWord_790921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790921).length < 2 ^ (prefixWord ++ tailWord_790921).sum := by decide
  have hdescent : baseEnd_790921 < baseStart_790921 := by decide
  rcases family_descends (prefixWord ++ tailWord_790921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790933 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 3, 1, 7]
def baseStart_790933 : Nat := 118140960795 + 790933 * 2 ^ 59
def prefixEnd_790933 : Nat := 4983230072969 + 3 ^ 40 * 790933 * 2
def baseEnd_790933 : Nat := 406128794502659204700071

theorem tailTrace_790933 : CollatzResearch.WordTrace tailWord_790933 prefixEnd_790933 406128794502659204700071 := by
  unfold tailWord_790933
  simp only [CollatzResearch.WordTrace]
  refine ⟨28847696443592296447193453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19231797629061530964795635 28847696443592296447193453)
  ·
    refine ⟨10817886166347111167697545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28847696443592296447193453 10817886166347111167697545)
    ·
      refine ⟨8113414624760333375773159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10817886166347111167697545 8113414624760333375773159)
      ·
        refine ⟨12170121937140500063659739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8113414624760333375773159 12170121937140500063659739)
        ·
          refine ⟨18255182905710750095489609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12170121937140500063659739 18255182905710750095489609)
          ·
            refine ⟨13691387179283062571617207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18255182905710750095489609 13691387179283062571617207)
            ·
              refine ⟨20537080768924593857425811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13691387179283062571617207 20537080768924593857425811)
              ·
                refine ⟨30805621153386890786138717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20537080768924593857425811 30805621153386890786138717)
                ·
                  refine ⟨11552107932520084044802019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30805621153386890786138717 11552107932520084044802019)
                  ·
                    refine ⟨17328161898780126067203029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11552107932520084044802019 17328161898780126067203029)
                    ·
                      refine ⟨406128794502659204700071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 17328161898780126067203029 406128794502659204700071)
                      ·
                        rfl

theorem cell23_790933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_790933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790933 prefixEnd_790933 := by exact prefixLift 790933
  have htrace : WordTrace (prefixWord ++ tailWord_790933) baseStart_790933 baseEnd_790933 := by
    simpa [prefixWord, tailWord_790933, baseEnd_790933] using wordTrace_append hprefix tailTrace_790933
  have hstable : (prefixWord ++ tailWord_790933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790933).length < 2 ^ (prefixWord ++ tailWord_790933).sum := by decide
  have hdescent : baseEnd_790933 < baseStart_790933 := by decide
  rcases family_descends (prefixWord ++ tailWord_790933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790970 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 7, 4]
def baseStart_790970 : Nat := 118140960795 + 790970 * 2 ^ 59
def prefixEnd_790970 : Nat := 4983230072969 + 3 ^ 40 * 790970 * 2
def baseEnd_790970 : Nat := 135382597762291853312467

theorem tailTrace_790970 : CollatzResearch.WordTrace tailWord_790970 prefixEnd_790970 135382597762291853312467 := by
  unfold tailWord_790970
  simp only [CollatzResearch.WordTrace]
  refine ⟨7212261486114562941572591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19232697296305501177526909 7212261486114562941572591)
  ·
    refine ⟨10818392229171844412358887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7212261486114562941572591 10818392229171844412358887)
    ·
      refine ⟨16227588343757766618538331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10818392229171844412358887 16227588343757766618538331)
      ·
        refine ⟨24341382515636649927807497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16227588343757766618538331 24341382515636649927807497)
        ·
          refine ⟨18256036886727487445855623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24341382515636649927807497 18256036886727487445855623)
          ·
            refine ⟨27384055330091231168783435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18256036886727487445855623 27384055330091231168783435)
            ·
              refine ⟨41076082995136846753175153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27384055330091231168783435 41076082995136846753175153)
              ·
                refine ⟨30807062246352635064881365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41076082995136846753175153 30807062246352635064881365)
                ·
                  refine ⟨722040521398889884333157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 30807062246352635064881365 722040521398889884333157)
                  ·
                    refine ⟨135382597762291853312467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 722040521398889884333157 135382597762291853312467)
                    ·
                      rfl

theorem cell23_790970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 7, 4].length) (baseStart_790970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790970 prefixEnd_790970 := by exact prefixLift 790970
  have htrace : WordTrace (prefixWord ++ tailWord_790970) baseStart_790970 baseEnd_790970 := by
    simpa [prefixWord, tailWord_790970, baseEnd_790970] using wordTrace_append hprefix tailTrace_790970
  have hstable : (prefixWord ++ tailWord_790970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790970).length < 2 ^ (prefixWord ++ tailWord_790970).sum := by decide
  have hdescent : baseEnd_790970 < baseStart_790970 := by decide
  rcases family_descends (prefixWord ++ tailWord_790970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790994 : List Nat := [3, 2, 2, 4, 1, 1, 1, 1, 1, 3, 4]
def baseStart_790994 : Nat := 118140960795 + 790994 * 2 ^ 59
def prefixEnd_790994 : Nat := 4983230072969 + 3 ^ 40 * 790994 * 2
def baseEnd_790994 : Nat := 406160116822583466037291

theorem tailTrace_790994 : CollatzResearch.WordTrace tailWord_790994 prefixEnd_790994 406160116822583466037291 := by
  unfold tailWord_790994
  simp only [CollatzResearch.WordTrace]
  refine ⟨7212480324092825966291009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19233280864247535910109357 7212480324092825966291009)
  ·
    refine ⟨5409360243069619474718257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7212480324092825966291009 5409360243069619474718257)
    ·
      refine ⟨4057020182302214606038693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5409360243069619474718257 4057020182302214606038693)
      ·
        refine ⟨760691284181665238632255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4057020182302214606038693 760691284181665238632255)
        ·
          refine ⟨1141036926272497857948383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 760691284181665238632255 1141036926272497857948383)
          ·
            refine ⟨1711555389408746786922575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1141036926272497857948383 1711555389408746786922575)
            ·
              refine ⟨2567333084113120180383863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1711555389408746786922575 2567333084113120180383863)
              ·
                refine ⟨3850999626169680270575795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2567333084113120180383863 3850999626169680270575795)
                ·
                  refine ⟨5776499439254520405863693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3850999626169680270575795 5776499439254520405863693)
                  ·
                    refine ⟨2166187289720445152198885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5776499439254520405863693 2166187289720445152198885)
                    ·
                      refine ⟨406160116822583466037291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2166187289720445152198885 406160116822583466037291)
                      ·
                        rfl

theorem cell23_790994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_790994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790994 prefixEnd_790994 := by exact prefixLift 790994
  have htrace : WordTrace (prefixWord ++ tailWord_790994) baseStart_790994 baseEnd_790994 := by
    simpa [prefixWord, tailWord_790994, baseEnd_790994] using wordTrace_append hprefix tailTrace_790994
  have hstable : (prefixWord ++ tailWord_790994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790994).length < 2 ^ (prefixWord ++ tailWord_790994).sum := by decide
  have hdescent : baseEnd_790994 < baseStart_790994 := by decide
  rcases family_descends (prefixWord ++ tailWord_790994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790997 : List Nat := [1, 3, 2, 3, 1, 3, 1, 1, 1, 4, 3]
def baseStart_790997 : Nat := 118140960795 + 790997 * 2 ^ 59
def prefixEnd_790997 : Nat := 4983230072969 + 3 ^ 40 * 790997 * 2
def baseEnd_790997 : Nat := 406161657264546954299777

theorem tailTrace_790997 : CollatzResearch.WordTrace tailWord_790997 prefixEnd_790997 406161657264546954299777 := by
  unfold tailWord_790997
  simp only [CollatzResearch.WordTrace]
  refine ⟨28850030715360435377523245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19233353810240290251682163 28850030715360435377523245)
  ·
    refine ⟨10818761518260163266571217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28850030715360435377523245 10818761518260163266571217)
    ·
      refine ⟨8114071138695122449928413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10818761518260163266571217 8114071138695122449928413)
      ·
        refine ⟨3042776677010670918723155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8114071138695122449928413 3042776677010670918723155)
        ·
          refine ⟨4564165015516006378084733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3042776677010670918723155 4564165015516006378084733)
          ·
            refine ⟨1711561880818502391781775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4564165015516006378084733 1711561880818502391781775)
            ·
              refine ⟨2567342821227753587672663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1711561880818502391781775 2567342821227753587672663)
              ·
                refine ⟨3851014231841630381508995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2567342821227753587672663 3851014231841630381508995)
                ·
                  refine ⟨5776521347762445572263493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3851014231841630381508995 5776521347762445572263493)
                  ·
                    refine ⟨1083097752705458544799405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5776521347762445572263493 1083097752705458544799405)
                    ·
                      refine ⟨406161657264546954299777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1083097752705458544799405 406161657264546954299777)
                      ·
                        rfl

theorem cell23_790997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_790997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_790997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_790997 prefixEnd_790997 := by exact prefixLift 790997
  have htrace : WordTrace (prefixWord ++ tailWord_790997) baseStart_790997 baseEnd_790997 := by
    simpa [prefixWord, tailWord_790997, baseEnd_790997] using wordTrace_append hprefix tailTrace_790997
  have hstable : (prefixWord ++ tailWord_790997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790997).length < 2 ^ (prefixWord ++ tailWord_790997).sum := by decide
  have hdescent : baseEnd_790997 < baseStart_790997 := by decide
  rcases family_descends (prefixWord ++ tailWord_790997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791021 : List Nat := [1, 5, 1, 3, 1, 1, 2, 4, 1, 4]
def baseStart_791021 : Nat := 118140960795 + 791021 * 2 ^ 59
def prefixEnd_791021 : Nat := 4983230072969 + 3 ^ 40 * 791021 * 2
def baseEnd_791021 : Nat := 135391326933418286799889

theorem tailTrace_791021 : CollatzResearch.WordTrace tailWord_791021 prefixEnd_791021 135391326933418286799889 := by
  unfold tailWord_791021
  simp only [CollatzResearch.WordTrace]
  refine ⟨28850906067273487476396917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19233937378182324984264611 28850906067273487476396917)
  ·
    refine ⟨2704772443806889450912211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28850906067273487476396917 2704772443806889450912211)
    ·
      refine ⟨4057158665710334176368317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2704772443806889450912211 4057158665710334176368317)
      ·
        refine ⟨1521434499641375316138119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4057158665710334176368317 1521434499641375316138119)
        ·
          refine ⟨2282151749462062974207179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1521434499641375316138119 2282151749462062974207179)
          ·
            refine ⟨3423227624193094461310769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2282151749462062974207179 3423227624193094461310769)
            ·
              refine ⟨2567420718144820845983077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3423227624193094461310769 2567420718144820845983077)
              ·
                refine ⟨481391384652153908621827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2567420718144820845983077 481391384652153908621827)
                ·
                  refine ⟨722087076978230862932741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 481391384652153908621827 722087076978230862932741)
                  ·
                    refine ⟨135391326933418286799889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 722087076978230862932741 135391326933418286799889)
                    ·
                      rfl

theorem cell23_791021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_791021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791021 prefixEnd_791021 := by exact prefixLift 791021
  have htrace : WordTrace (prefixWord ++ tailWord_791021) baseStart_791021 baseEnd_791021 := by
    simpa [prefixWord, tailWord_791021, baseEnd_791021] using wordTrace_append hprefix tailTrace_791021
  have hstable : (prefixWord ++ tailWord_791021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791021).length < 2 ^ (prefixWord ++ tailWord_791021).sum := by decide
  have hdescent : baseEnd_791021 < baseStart_791021 := by decide
  rcases family_descends (prefixWord ++ tailWord_791021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791037 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 3, 5, 2]
def baseStart_791037 : Nat := 118140960795 + 791037 * 2 ^ 59
def prefixEnd_791037 : Nat := 4983230072969 + 3 ^ 40 * 791037 * 2
def baseEnd_791037 : Nat := 406182196490726797799593

theorem tailTrace_791037 : CollatzResearch.WordTrace tailWord_791037 prefixEnd_791037 406182196490726797799593 := by
  unfold tailWord_791037
  simp only [CollatzResearch.WordTrace]
  refine ⟨28851489635215522208979365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19234326423477014805986243 28851489635215522208979365)
  ·
    refine ⟨5409654306602910414183631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28851489635215522208979365 5409654306602910414183631)
    ·
      refine ⟨8114481459904365621275447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5409654306602910414183631 8114481459904365621275447)
      ·
        refine ⟨12171722189856548431913171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8114481459904365621275447 12171722189856548431913171)
        ·
          refine ⟨18257583284784822647869757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12171722189856548431913171 18257583284784822647869757)
          ·
            refine ⟨6846593731794308492951159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18257583284784822647869757 6846593731794308492951159)
            ·
              refine ⟨10269890597691462739426739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6846593731794308492951159 10269890597691462739426739)
              ·
                refine ⟨15404835896537194109140109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10269890597691462739426739 15404835896537194109140109)
                ·
                  refine ⟨5776813461201447790927541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15404835896537194109140109 5776813461201447790927541)
                  ·
                    refine ⟨541576261987635730399457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5776813461201447790927541 541576261987635730399457)
                    ·
                      refine ⟨406182196490726797799593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 541576261987635730399457 406182196490726797799593)
                      ·
                        rfl

theorem cell23_791037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 5, 2].length) (baseStart_791037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791037 prefixEnd_791037 := by exact prefixLift 791037
  have htrace : WordTrace (prefixWord ++ tailWord_791037) baseStart_791037 baseEnd_791037 := by
    simpa [prefixWord, tailWord_791037, baseEnd_791037] using wordTrace_append hprefix tailTrace_791037
  have hstable : (prefixWord ++ tailWord_791037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791037).length < 2 ^ (prefixWord ++ tailWord_791037).sum := by decide
  have hdescent : baseEnd_791037 < baseStart_791037 := by decide
  rcases family_descends (prefixWord ++ tailWord_791037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791054 : List Nat := [4, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2]
def baseStart_791054 : Nat := 118140960795 + 791054 * 2 ^ 59
def prefixEnd_791054 : Nat := 4983230072969 + 3 ^ 40 * 791054 * 2
def baseEnd_791054 : Nat := 406190925661853231287015

theorem tailTrace_791054 : CollatzResearch.WordTrace tailWord_791054 prefixEnd_791054 406190925661853231287015 := by
  unfold tailWord_791054
  simp only [CollatzResearch.WordTrace]
  refine ⟨3606513709519241764043527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19234739784102622741565477 3606513709519241764043527)
  ·
    refine ⟨5409770564278862646065291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3606513709519241764043527 5409770564278862646065291)
    ·
      refine ⟨8114655846418293969097937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5409770564278862646065291 8114655846418293969097937)
      ·
        refine ⟨6085991884813720476823453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8114655846418293969097937 6085991884813720476823453)
        ·
          refine ⟨2282246956805145178808795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6085991884813720476823453 2282246956805145178808795)
          ·
            refine ⟨3423370435207717768213193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2282246956805145178808795 3423370435207717768213193)
            ·
              refine ⟨2567527826405788326159895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3423370435207717768213193 2567527826405788326159895)
              ·
                refine ⟨3851291739608682489239843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2567527826405788326159895 3851291739608682489239843)
                ·
                  refine ⟨5776937609413023733859765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3851291739608682489239843 5776937609413023733859765)
                  ·
                    refine ⟨541587900882470975049353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5776937609413023733859765 541587900882470975049353)
                    ·
                      refine ⟨406190925661853231287015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 541587900882470975049353 406190925661853231287015)
                      ·
                        rfl

theorem cell23_791054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_791054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791054 prefixEnd_791054 := by exact prefixLift 791054
  have htrace : WordTrace (prefixWord ++ tailWord_791054) baseStart_791054 baseEnd_791054 := by
    simpa [prefixWord, tailWord_791054, baseEnd_791054] using wordTrace_append hprefix tailTrace_791054
  have hstable : (prefixWord ++ tailWord_791054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791054).length < 2 ^ (prefixWord ++ tailWord_791054).sum := by decide
  have hdescent : baseEnd_791054 < baseStart_791054 := by decide
  rcases family_descends (prefixWord ++ tailWord_791054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791077 : List Nat := [1, 3, 1, 2, 2, 1, 4, 1, 4, 4]
def baseStart_791077 : Nat := 118140960795 + 791077 * 2 ^ 59
def prefixEnd_791077 : Nat := 4983230072969 + 3 ^ 40 * 791077 * 2
def baseEnd_791077 : Nat := 135400911905635547099803

theorem tailTrace_791077 : CollatzResearch.WordTrace tailWord_791077 prefixEnd_791077 135400911905635547099803 := by
  unfold tailWord_791077
  simp only [CollatzResearch.WordTrace]
  refine ⟨28852948555070609040435485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19235299036713739360290323 28852948555070609040435485)
  ·
    refine ⟨10819855708151478390163307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28852948555070609040435485 10819855708151478390163307)
    ·
      refine ⟨16229783562227217585244961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10819855708151478390163307 16229783562227217585244961)
      ·
        refine ⟨12172337671670413188933721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16229783562227217585244961 12172337671670413188933721)
        ·
          refine ⟨9129253253752809891700291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12172337671670413188933721 9129253253752809891700291)
          ·
            refine ⟨13693879880629214837550437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9129253253752809891700291 13693879880629214837550437)
            ·
              refine ⟨2567602477617977782040707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13693879880629214837550437 2567602477617977782040707)
              ·
                refine ⟨3851403716426966673061061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2567602477617977782040707 3851403716426966673061061)
                ·
                  refine ⟨722138196830056251198949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3851403716426966673061061 722138196830056251198949)
                  ·
                    refine ⟨135400911905635547099803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 722138196830056251198949 135400911905635547099803)
                    ·
                      rfl

theorem cell23_791077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4, 4].length) (baseStart_791077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791077 prefixEnd_791077 := by exact prefixLift 791077
  have htrace : WordTrace (prefixWord ++ tailWord_791077) baseStart_791077 baseEnd_791077 := by
    simpa [prefixWord, tailWord_791077, baseEnd_791077] using wordTrace_append hprefix tailTrace_791077
  have hstable : (prefixWord ++ tailWord_791077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791077).length < 2 ^ (prefixWord ++ tailWord_791077).sum := by decide
  have hdescent : baseEnd_791077 < baseStart_791077 := by decide
  rcases family_descends (prefixWord ++ tailWord_791077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791085 : List Nat := [1, 5, 4, 1, 1, 2, 2, 1, 6]
def baseStart_791085 : Nat := 118140960795 + 791085 * 2 ^ 59
def prefixEnd_791085 : Nat := 4983230072969 + 3 ^ 40 * 791085 * 2
def baseEnd_791085 : Nat := 45134093729126956666597

theorem tailTrace_791085 : CollatzResearch.WordTrace tailWord_791085 prefixEnd_791085 45134093729126956666597 := by
  unfold tailWord_791085
  simp only [CollatzResearch.WordTrace]
  refine ⟨28853240339041626406726709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19235493559361084271151139 28853240339041626406726709)
  ·
    refine ⟨2704991281785152475630629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28853240339041626406726709 2704991281785152475630629)
    ·
      refine ⟨507185865334716089180743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2704991281785152475630629 507185865334716089180743)
      ·
        refine ⟨760778798002074133771115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507185865334716089180743 760778798002074133771115)
        ·
          refine ⟨1141168197003111200656673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 760778798002074133771115 1141168197003111200656673)
          ·
            refine ⟨855876147752333400492505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1141168197003111200656673 855876147752333400492505)
            ·
              refine ⟨641907110814250050369379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 855876147752333400492505 641907110814250050369379)
              ·
                refine ⟨962860666221375075554069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641907110814250050369379 962860666221375075554069)
                ·
                  refine ⟨45134093729126956666597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 962860666221375075554069 45134093729126956666597)
                  ·
                    rfl

theorem cell23_791085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_791085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791085 prefixEnd_791085 := by exact prefixLift 791085
  have htrace : WordTrace (prefixWord ++ tailWord_791085) baseStart_791085 baseEnd_791085 := by
    simpa [prefixWord, tailWord_791085, baseEnd_791085] using wordTrace_append hprefix tailTrace_791085
  have hstable : (prefixWord ++ tailWord_791085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791085).length < 2 ^ (prefixWord ++ tailWord_791085).sum := by decide
  have hdescent : baseEnd_791085 < baseStart_791085 := by decide
  rcases family_descends (prefixWord ++ tailWord_791085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791090 : List Nat := [3, 2, 1, 1, 2, 1, 3, 10]
def baseStart_791090 : Nat := 118140960795 + 791090 * 2 ^ 59
def prefixEnd_791090 : Nat := 4983230072969 + 3 ^ 40 * 791090 * 2
def baseEnd_791090 : Nat := 15044792998719077423587

theorem tailTrace_791090 : CollatzResearch.WordTrace tailWord_791090 prefixEnd_791090 15044792998719077423587 := by
  unfold tailWord_791090
  simp only [CollatzResearch.WordTrace]
  refine ⟨7213355676005878065164681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19235615136015674840439149 7213355676005878065164681)
  ·
    refine ⟨5410016757004408548873511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7213355676005878065164681 5410016757004408548873511)
    ·
      refine ⟨8115025135506612823310267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5410016757004408548873511 8115025135506612823310267)
      ·
        refine ⟨12172537703259919234965401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8115025135506612823310267 12172537703259919234965401)
        ·
          refine ⟨9129403277444939426224051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12172537703259919234965401 9129403277444939426224051)
          ·
            refine ⟨13694104916167409139336077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9129403277444939426224051 13694104916167409139336077)
            ·
              refine ⟨5135289343562778427251029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13694104916167409139336077 5135289343562778427251029)
              ·
                refine ⟨15044792998719077423587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5135289343562778427251029 15044792998719077423587)
                ·
                  rfl

theorem cell23_791090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 10].length) (baseStart_791090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791090 prefixEnd_791090 := by exact prefixLift 791090
  have htrace : WordTrace (prefixWord ++ tailWord_791090) baseStart_791090 baseEnd_791090 := by
    simpa [prefixWord, tailWord_791090, baseEnd_791090] using wordTrace_append hprefix tailTrace_791090
  have hstable : (prefixWord ++ tailWord_791090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791090).length < 2 ^ (prefixWord ++ tailWord_791090).sum := by decide
  have hdescent : baseEnd_791090 < baseStart_791090 := by decide
  rcases family_descends (prefixWord ++ tailWord_791090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791097 : List Nat := [1, 2, 1, 5, 1, 1, 2, 3, 1, 2, 4]
def baseStart_791097 : Nat := 118140960795 + 791097 * 2 ^ 59
def prefixEnd_791097 : Nat := 4983230072969 + 3 ^ 40 * 791097 * 2
def baseEnd_791097 : Nat := 406213005329996563049317

theorem tailTrace_791097 : CollatzResearch.WordTrace tailWord_791097 prefixEnd_791097 406213005329996563049317 := by
  unfold tailWord_791097
  simp only [CollatzResearch.WordTrace]
  refine ⟨28853678014998152456163545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19235785343332101637442363 28853678014998152456163545)
  ·
    refine ⟨21640258511248614342122659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28853678014998152456163545 21640258511248614342122659)
    ·
      refine ⟨32460387766872921513183989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21640258511248614342122659 32460387766872921513183989)
      ·
        refine ⟨3043161353144336391860999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32460387766872921513183989 3043161353144336391860999)
        ·
          refine ⟨4564742029716504587791499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3043161353144336391860999 4564742029716504587791499)
          ·
            refine ⟨6847113044574756881687249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4564742029716504587791499 6847113044574756881687249)
            ·
              refine ⟨5135334783431067661265437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6847113044574756881687249 5135334783431067661265437)
              ·
                refine ⟨1925750543786650372974539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5135334783431067661265437 1925750543786650372974539)
                ·
                  refine ⟨2888625815679975559461809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1925750543786650372974539 2888625815679975559461809)
                  ·
                    refine ⟨2166469361759981669596357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2888625815679975559461809 2166469361759981669596357)
                    ·
                      refine ⟨406213005329996563049317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2166469361759981669596357 406213005329996563049317)
                      ·
                        rfl

theorem cell23_791097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_791097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791097 prefixEnd_791097 := by exact prefixLift 791097
  have htrace : WordTrace (prefixWord ++ tailWord_791097) baseStart_791097 baseEnd_791097 := by
    simpa [prefixWord, tailWord_791097, baseEnd_791097] using wordTrace_append hprefix tailTrace_791097
  have hstable : (prefixWord ++ tailWord_791097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791097).length < 2 ^ (prefixWord ++ tailWord_791097).sum := by decide
  have hdescent : baseEnd_791097 < baseStart_791097 := by decide
  rcases family_descends (prefixWord ++ tailWord_791097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791101 : List Nat := [1, 4, 1, 3, 2, 3, 1, 2, 1, 1, 4]
def baseStart_791101 : Nat := 118140960795 + 791101 * 2 ^ 59
def prefixEnd_791101 : Nat := 4983230072969 + 3 ^ 40 * 791101 * 2
def baseEnd_791101 : Nat := 406215059252614547399299

theorem tailTrace_791101 : CollatzResearch.WordTrace tailWord_791101 prefixEnd_791101 406215059252614547399299 := by
  unfold tailWord_791101
  simp only [CollatzResearch.WordTrace]
  refine ⟨28853823906983661139309157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19235882604655774092872771 28853823906983661139309157)
  ·
    refine ⟨5410091982559436463620467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28853823906983661139309157 5410091982559436463620467)
    ·
      refine ⟨8115137973839154695430701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5410091982559436463620467 8115137973839154695430701)
      ·
        refine ⟨3043176740189683010786513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8115137973839154695430701 3043176740189683010786513)
        ·
          refine ⟨2282382555142262258089885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3043176740189683010786513 2282382555142262258089885)
          ·
            refine ⟨855893458178348346783707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2282382555142262258089885 855893458178348346783707)
            ·
              refine ⟨1283840187267522520175561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 855893458178348346783707 1283840187267522520175561)
              ·
                refine ⟨962880140450641890131671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1283840187267522520175561 962880140450641890131671)
                ·
                  refine ⟨1444320210675962835197507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 962880140450641890131671 1444320210675962835197507)
                  ·
                    refine ⟨2166480316013944252796261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1444320210675962835197507 2166480316013944252796261)
                    ·
                      refine ⟨406215059252614547399299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2166480316013944252796261 406215059252614547399299)
                      ·
                        rfl

theorem cell23_791101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_791101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791101 prefixEnd_791101 := by exact prefixLift 791101
  have htrace : WordTrace (prefixWord ++ tailWord_791101) baseStart_791101 baseEnd_791101 := by
    simpa [prefixWord, tailWord_791101, baseEnd_791101] using wordTrace_append hprefix tailTrace_791101
  have hstable : (prefixWord ++ tailWord_791101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791101).length < 2 ^ (prefixWord ++ tailWord_791101).sum := by decide
  have hdescent : baseEnd_791101 < baseStart_791101 := by decide
  rcases family_descends (prefixWord ++ tailWord_791101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791104 : List Nat := [2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 3]
def baseStart_791104 : Nat := 118140960795 + 791104 * 2 ^ 59
def prefixEnd_791104 : Nat := 4983230072969 + 3 ^ 40 * 791104 * 2
def baseEnd_791104 : Nat := 406216599694578035661785

theorem tailTrace_791104 : CollatzResearch.WordTrace tailWord_791104 prefixEnd_791104 406216599694578035661785 := by
  unfold tailWord_791104
  simp only [CollatzResearch.WordTrace]
  refine ⟨14426966662986396325834183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19235955550648528434445577 14426966662986396325834183)
  ·
    refine ⟨21640449994479594488751275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14426966662986396325834183 21640449994479594488751275)
    ·
      refine ⟨32460674991719391733126913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21640449994479594488751275 32460674991719391733126913)
      ·
        refine ⟨24345506243789543799845185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32460674991719391733126913 24345506243789543799845185)
        ·
          refine ⟨18259129682842157849883889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24345506243789543799845185 18259129682842157849883889)
          ·
            refine ⟨13694347262131618387412917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18259129682842157849883889 13694347262131618387412917)
            ·
              refine ⟨1283845055824839223819961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13694347262131618387412917 1283845055824839223819961)
              ·
                refine ⟨962883791868629417864971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1283845055824839223819961 962883791868629417864971)
                ·
                  refine ⟨1444325687802944126797457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 962883791868629417864971 1444325687802944126797457)
                  ·
                    refine ⟨1083244265852208095098093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1444325687802944126797457 1083244265852208095098093)
                    ·
                      refine ⟨406216599694578035661785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1083244265852208095098093 406216599694578035661785)
                      ·
                        rfl

theorem cell23_791104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 3].length) (baseStart_791104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791104 prefixEnd_791104 := by exact prefixLift 791104
  have htrace : WordTrace (prefixWord ++ tailWord_791104) baseStart_791104 baseEnd_791104 := by
    simpa [prefixWord, tailWord_791104, baseEnd_791104] using wordTrace_append hprefix tailTrace_791104
  have hstable : (prefixWord ++ tailWord_791104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791104).length < 2 ^ (prefixWord ++ tailWord_791104).sum := by decide
  have hdescent : baseEnd_791104 < baseStart_791104 := by decide
  rcases family_descends (prefixWord ++ tailWord_791104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791121 : List Nat := [1, 2, 2, 1, 3, 4, 3, 1, 1, 2, 3]
def baseStart_791121 : Nat := 118140960795 + 791121 * 2 ^ 59
def prefixEnd_791121 : Nat := 4983230072969 + 3 ^ 40 * 791121 * 2
def baseEnd_791121 : Nat := 406225328865704469149207

theorem tailTrace_791121 : CollatzResearch.WordTrace tailWord_791121 prefixEnd_791121 406225328865704469149207 := by
  unfold tailWord_791121
  simp only [CollatzResearch.WordTrace]
  refine ⟨28854553366911204555037217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19236368911274136370024811 28854553366911204555037217)
  ·
    refine ⟨21640915025183403416277913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28854553366911204555037217 21640915025183403416277913)
    ·
      refine ⟨16230686268887552562208435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21640915025183403416277913 16230686268887552562208435)
      ·
        refine ⟨24346029403331328843312653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16230686268887552562208435 24346029403331328843312653)
        ·
          refine ⟨9129761026249248316242245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24346029403331328843312653 9129761026249248316242245)
          ·
            refine ⟨1711830192421734059295421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9129761026249248316242245 1711830192421734059295421)
            ·
              refine ⟨641936322158150272235783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1711830192421734059295421 641936322158150272235783)
              ·
                refine ⟨962904483237225408353675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641936322158150272235783 962904483237225408353675)
                ·
                  refine ⟨1444356724855838112530513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 962904483237225408353675 1444356724855838112530513)
                  ·
                    refine ⟨1083267543641878584397885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1444356724855838112530513 1083267543641878584397885)
                    ·
                      refine ⟨406225328865704469149207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1083267543641878584397885 406225328865704469149207)
                      ·
                        rfl

theorem cell23_791121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 1, 2, 3].length) (baseStart_791121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791121 prefixEnd_791121 := by exact prefixLift 791121
  have htrace : WordTrace (prefixWord ++ tailWord_791121) baseStart_791121 baseEnd_791121 := by
    simpa [prefixWord, tailWord_791121, baseEnd_791121] using wordTrace_append hprefix tailTrace_791121
  have hstable : (prefixWord ++ tailWord_791121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791121).length < 2 ^ (prefixWord ++ tailWord_791121).sum := by decide
  have hdescent : baseEnd_791121 < baseStart_791121 := by decide
  rcases family_descends (prefixWord ++ tailWord_791121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791130 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7]
def baseStart_791130 : Nat := 118140960795 + 791130 * 2 ^ 59
def prefixEnd_791130 : Nat := 4983230072969 + 3 ^ 40 * 791130 * 2
def baseEnd_791130 : Nat := 406229950191594933936665

theorem tailTrace_791130 : CollatzResearch.WordTrace tailWord_791130 prefixEnd_791130 406229950191594933936665 := by
  unfold tailWord_791130
  simp only [CollatzResearch.WordTrace]
  refine ⟨7213720405969649773028711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19236587749252399394743229 7213720405969649773028711)
  ·
    refine ⟨10820580608954474659543067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7213720405969649773028711 10820580608954474659543067)
    ·
      refine ⟨16230870913431711989314601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10820580608954474659543067 16230870913431711989314601)
      ·
        refine ⟨12173153185073783991985951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16230870913431711989314601 12173153185073783991985951)
        ·
          refine ⟨18259729777610675987978927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12173153185073783991985951 18259729777610675987978927)
          ·
            refine ⟨27389594666416013981968391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18259729777610675987978927 27389594666416013981968391)
            ·
              refine ⟨41084391999624020972952587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27389594666416013981968391 41084391999624020972952587)
              ·
                refine ⟨61626587999436031459428881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41084391999624020972952587 61626587999436031459428881)
                ·
                  refine ⟨46219940999577023594571661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61626587999436031459428881 46219940999577023594571661)
                  ·
                    refine ⟨17332477874841383847964373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46219940999577023594571661 17332477874841383847964373)
                    ·
                      refine ⟨406229950191594933936665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 17332477874841383847964373 406229950191594933936665)
                      ·
                        rfl

theorem cell23_791130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_791130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791130 prefixEnd_791130 := by exact prefixLift 791130
  have htrace : WordTrace (prefixWord ++ tailWord_791130) baseStart_791130 baseEnd_791130 := by
    simpa [prefixWord, tailWord_791130, baseEnd_791130] using wordTrace_append hprefix tailTrace_791130
  have hstable : (prefixWord ++ tailWord_791130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791130).length < 2 ^ (prefixWord ++ tailWord_791130).sum := by decide
  have hdescent : baseEnd_791130 < baseStart_791130 := by decide
  rcases family_descends (prefixWord ++ tailWord_791130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791178 : List Nat := [3, 1, 2, 3, 3, 1, 1, 3, 1, 3, 2]
def baseStart_791178 : Nat := 118140960795 + 791178 * 2 ^ 59
def prefixEnd_791178 : Nat := 4983230072969 + 3 ^ 40 * 791178 * 2
def baseEnd_791178 : Nat := 406254597263010746136445

theorem tailTrace_791178 : CollatzResearch.WordTrace tailWord_791178 prefixEnd_791178 406254597263010746136445 := by
  unfold tailWord_791178
  simp only [CollatzResearch.WordTrace]
  refine ⟨7214158081926175822465547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19237754885136468859908125 7214158081926175822465547)
  ·
    refine ⟨10821237122889263733698321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7214158081926175822465547 10821237122889263733698321)
    ·
      refine ⟨8115927842166947800273741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10821237122889263733698321 8115927842166947800273741)
      ·
        refine ⟨3043472940812605425102653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8115927842166947800273741 3043472940812605425102653)
        ·
          refine ⟨1141302352804727034413495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3043472940812605425102653 1141302352804727034413495)
          ·
            refine ⟨1711953529207090551620243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1141302352804727034413495 1711953529207090551620243)
            ·
              refine ⟨2567930293810635827430365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1711953529207090551620243 2567930293810635827430365)
              ·
                refine ⟨962973860178988435286387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2567930293810635827430365 962973860178988435286387)
                ·
                  refine ⟨1444460790268482652929581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 962973860178988435286387 1444460790268482652929581)
                  ·
                    refine ⟨541672796350680994848593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1444460790268482652929581 541672796350680994848593)
                    ·
                      refine ⟨406254597263010746136445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 541672796350680994848593 406254597263010746136445)
                      ·
                        rfl

theorem cell23_791178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_791178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791178 prefixEnd_791178 := by exact prefixLift 791178
  have htrace : WordTrace (prefixWord ++ tailWord_791178) baseStart_791178 baseEnd_791178 := by
    simpa [prefixWord, tailWord_791178, baseEnd_791178] using wordTrace_append hprefix tailTrace_791178
  have hstable : (prefixWord ++ tailWord_791178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791178).length < 2 ^ (prefixWord ++ tailWord_791178).sum := by decide
  have hdescent : baseEnd_791178 < baseStart_791178 := by decide
  rcases family_descends (prefixWord ++ tailWord_791178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791191 : List Nat := [1, 1, 3, 3, 2, 1, 3, 1, 4, 2, 2]
def baseStart_791191 : Nat := 118140960795 + 791191 * 2 ^ 59
def prefixEnd_791191 : Nat := 4983230072969 + 3 ^ 40 * 791191 * 2
def baseEnd_791191 : Nat := 406261272511519195273885

theorem tailTrace_791191 : CollatzResearch.WordTrace tailWord_791191 prefixEnd_791191 406261272511519195273885 := by
  unfold tailWord_791191
  simp only [CollatzResearch.WordTrace]
  refine ⟨28857106476657606510085427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19238070984438404340056951 28857106476657606510085427)
  ·
    refine ⟨43285659714986409765128141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28857106476657606510085427 43285659714986409765128141)
    ·
      refine ⟨16232122393119903661923053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43285659714986409765128141 16232122393119903661923053)
      ·
        refine ⟨6087045897419963873221145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16232122393119903661923053 6087045897419963873221145)
        ·
          refine ⟨4565284423064972904915859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6087045897419963873221145 4565284423064972904915859)
          ·
            refine ⟨6847926634597459357373789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4565284423064972904915859 6847926634597459357373789)
            ·
              refine ⟨2567972487974047259015171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6847926634597459357373789 2567972487974047259015171)
              ·
                refine ⟨3851958731961070888522757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2567972487974047259015171 3851958731961070888522757)
                ·
                  refine ⟨722242262242700791598017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3851958731961070888522757 722242262242700791598017)
                  ·
                    refine ⟨541681696682025593698513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 722242262242700791598017 541681696682025593698513)
                    ·
                      refine ⟨406261272511519195273885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 541681696682025593698513 406261272511519195273885)
                      ·
                        rfl

theorem cell23_791191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_791191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791191 prefixEnd_791191 := by exact prefixLift 791191
  have htrace : WordTrace (prefixWord ++ tailWord_791191) baseStart_791191 baseEnd_791191 := by
    simpa [prefixWord, tailWord_791191, baseEnd_791191] using wordTrace_append hprefix tailTrace_791191
  have hstable : (prefixWord ++ tailWord_791191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791191).length < 2 ^ (prefixWord ++ tailWord_791191).sum := by decide
  have hdescent : baseEnd_791191 < baseStart_791191 := by decide
  rcases family_descends (prefixWord ++ tailWord_791191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791197 : List Nat := [1, 4, 2, 1, 1, 1, 3, 3, 7]
def baseStart_791197 : Nat := 118140960795 + 791197 * 2 ^ 59
def prefixEnd_791197 : Nat := 4983230072969 + 3 ^ 40 * 791197 * 2
def baseEnd_791197 : Nat := 45140483710605130199873

theorem tailTrace_791197 : CollatzResearch.WordTrace tailWord_791197 prefixEnd_791197 45140483710605130199873 := by
  unfold tailWord_791197
  simp only [CollatzResearch.WordTrace]
  refine ⟨28857325314635869534803845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19238216876423913023202563 28857325314635869534803845)
  ·
    refine ⟨5410748496494225537775721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28857325314635869534803845 5410748496494225537775721)
    ·
      refine ⟨4058061372370669153331791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5410748496494225537775721 4058061372370669153331791)
      ·
        refine ⟨6087092058556003729997687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4058061372370669153331791 6087092058556003729997687)
        ·
          refine ⟨9130638087834005594996531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6087092058556003729997687 9130638087834005594996531)
          ·
            refine ⟨13695957131751008392494797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9130638087834005594996531 13695957131751008392494797)
            ·
              refine ⟨5135983924406628147185549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13695957131751008392494797 5135983924406628147185549)
              ·
                refine ⟨1925993971652485555194581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5135983924406628147185549 1925993971652485555194581)
                ·
                  refine ⟨45140483710605130199873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1925993971652485555194581 45140483710605130199873)
                  ·
                    rfl

theorem cell23_791197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_791197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791197 prefixEnd_791197 := by exact prefixLift 791197
  have htrace : WordTrace (prefixWord ++ tailWord_791197) baseStart_791197 baseEnd_791197 := by
    simpa [prefixWord, tailWord_791197, baseEnd_791197] using wordTrace_append hprefix tailTrace_791197
  have hstable : (prefixWord ++ tailWord_791197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791197).length < 2 ^ (prefixWord ++ tailWord_791197).sum := by decide
  have hdescent : baseEnd_791197 < baseStart_791197 := by decide
  rcases family_descends (prefixWord ++ tailWord_791197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791231 : List Nat := [1, 1, 2, 2, 2, 6, 1, 3, 5]
def baseStart_791231 : Nat := 118140960795 + 791231 * 2 ^ 59
def prefixEnd_791231 : Nat := 4983230072969 + 3 ^ 40 * 791231 * 2
def baseEnd_791231 : Nat := 45142423526411004308189

theorem tailTrace_791231 : CollatzResearch.WordTrace tailWord_791231 prefixEnd_791231 45142423526411004308189 := by
  unfold tailWord_791231
  simp only [CollatzResearch.WordTrace]
  refine ⟨28858565396512693341541547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19239043597675128894361031 28858565396512693341541547)
  ·
    refine ⟨43287848094769040012312321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28858565396512693341541547 43287848094769040012312321)
    ·
      refine ⟨32465886071076780009234241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43287848094769040012312321 32465886071076780009234241)
      ·
        refine ⟨24349414553307585006925681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32465886071076780009234241 24349414553307585006925681)
        ·
          refine ⟨18262060914980688755194261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24349414553307585006925681 18262060914980688755194261)
          ·
            refine ⟨856034105389719785399731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18262060914980688755194261 856034105389719785399731)
            ·
              refine ⟨1284051158084579678099597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 856034105389719785399731 1284051158084579678099597)
              ·
                refine ⟨481519184281717379287349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1284051158084579678099597 481519184281717379287349)
                ·
                  refine ⟨45142423526411004308189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 481519184281717379287349 45142423526411004308189)
                  ·
                    rfl

theorem cell23_791231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3, 5].length) (baseStart_791231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791231 prefixEnd_791231 := by exact prefixLift 791231
  have htrace : WordTrace (prefixWord ++ tailWord_791231) baseStart_791231 baseEnd_791231 := by
    simpa [prefixWord, tailWord_791231, baseEnd_791231] using wordTrace_append hprefix tailTrace_791231
  have hstable : (prefixWord ++ tailWord_791231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791231).length < 2 ^ (prefixWord ++ tailWord_791231).sum := by decide
  have hdescent : baseEnd_791231 < baseStart_791231 := by decide
  rcases family_descends (prefixWord ++ tailWord_791231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791244 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 4, 5]
def baseStart_791244 : Nat := 118140960795 + 791244 * 2 ^ 59
def prefixEnd_791244 : Nat := 4983230072969 + 3 ^ 40 * 791244 * 2
def baseEnd_791244 : Nat := 135429495662069162637047

theorem tailTrace_791244 : CollatzResearch.WordTrace tailWord_791244 prefixEnd_791244 135429495662069162637047 := by
  unfold tailWord_791244
  simp only [CollatzResearch.WordTrace]
  refine ⟨14429519772732798280882393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19239359696977064374509857 14429519772732798280882393)
  ·
    refine ⟨10822139829549598710661795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14429519772732798280882393 10822139829549598710661795)
    ·
      refine ⟨16233209744324398065992693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10822139829549598710661795 16233209744324398065992693)
      ·
        refine ⟨1521863413530412318686815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16233209744324398065992693 1521863413530412318686815)
        ·
          refine ⟨2282795120295618478030223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1521863413530412318686815 2282795120295618478030223)
          ·
            refine ⟨3424192680443427717045335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2282795120295618478030223 3424192680443427717045335)
            ·
              refine ⟨5136289020665141575568003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3424192680443427717045335 5136289020665141575568003)
              ·
                refine ⟨7704433530997712363352005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5136289020665141575568003 7704433530997712363352005)
                ·
                  refine ⟨1444581287062071068128501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7704433530997712363352005 1444581287062071068128501)
                  ·
                    refine ⟨135429495662069162637047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1444581287062071068128501 135429495662069162637047)
                    ·
                      rfl

theorem cell23_791244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 4, 5].length) (baseStart_791244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791244 prefixEnd_791244 := by exact prefixLift 791244
  have htrace : WordTrace (prefixWord ++ tailWord_791244) baseStart_791244 baseEnd_791244 := by
    simpa [prefixWord, tailWord_791244, baseEnd_791244] using wordTrace_append hprefix tailTrace_791244
  have hstable : (prefixWord ++ tailWord_791244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791244).length < 2 ^ (prefixWord ++ tailWord_791244).sum := by decide
  have hdescent : baseEnd_791244 < baseStart_791244 := by decide
  rcases family_descends (prefixWord ++ tailWord_791244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791264 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 1, 6, 2]
def baseStart_791264 : Nat := 118140960795 + 791264 * 2 ^ 59
def prefixEnd_791264 : Nat := 4983230072969 + 3 ^ 40 * 791264 * 2
def baseEnd_791264 : Nat := 406298756599297409661049

theorem tailTrace_791264 : CollatzResearch.WordTrace tailWord_791264 prefixEnd_791264 406298756599297409661049 := by
  unfold tailWord_791264
  simp only [CollatzResearch.WordTrace]
  refine ⟨14429884502696569988746423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19239846003595426651661897 14429884502696569988746423)
  ·
    refine ⟨21644826754044854983119635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14429884502696569988746423 21644826754044854983119635)
    ·
      refine ⟨32467240131067282474679453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21644826754044854983119635 32467240131067282474679453)
      ·
        refine ⟨12175215049150230928004795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32467240131067282474679453 12175215049150230928004795)
        ·
          refine ⟨18262822573725346392007193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12175215049150230928004795 18262822573725346392007193)
          ·
            refine ⟨13697116930294009794005395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18262822573725346392007193 13697116930294009794005395)
            ·
              refine ⟨20545675395441014691008093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13697116930294009794005395 20545675395441014691008093)
              ·
                refine ⟨7704628273290380509128035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20545675395441014691008093 7704628273290380509128035)
                ·
                  refine ⟨11556942409935570763692053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7704628273290380509128035 11556942409935570763692053)
                  ·
                    refine ⟨541731675465729879548065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11556942409935570763692053 541731675465729879548065)
                    ·
                      refine ⟨406298756599297409661049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 541731675465729879548065 406298756599297409661049)
                      ·
                        rfl

theorem cell23_791264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 1, 6, 2].length) (baseStart_791264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791264 prefixEnd_791264 := by exact prefixLift 791264
  have htrace : WordTrace (prefixWord ++ tailWord_791264) baseStart_791264 baseEnd_791264 := by
    simpa [prefixWord, tailWord_791264, baseEnd_791264] using wordTrace_append hprefix tailTrace_791264
  have hstable : (prefixWord ++ tailWord_791264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791264).length < 2 ^ (prefixWord ++ tailWord_791264).sum := by decide
  have hdescent : baseEnd_791264 < baseStart_791264 := by decide
  rcases family_descends (prefixWord ++ tailWord_791264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791274 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 5, 4]
def baseStart_791274 : Nat := 118140960795 + 791274 * 2 ^ 59
def prefixEnd_791274 : Nat := 4983230072969 + 3 ^ 40 * 791274 * 2
def baseEnd_791274 : Nat := 135434630468614123512001

theorem tailTrace_791274 : CollatzResearch.WordTrace tailWord_791274 prefixEnd_791274 135434630468614123512001 := by
  unfold tailWord_791274
  simp only [CollatzResearch.WordTrace]
  refine ⟨7215033433839227921339219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19240089156904607790237917 7215033433839227921339219)
  ·
    refine ⟨10822550150758841882008829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7215033433839227921339219 10822550150758841882008829)
    ·
      refine ⟨4058456306534565705753311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10822550150758841882008829 4058456306534565705753311)
      ·
        refine ⟨6087684459801848558629967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4058456306534565705753311 6087684459801848558629967)
        ·
          refine ⟨9131526689702772837944951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6087684459801848558629967 9131526689702772837944951)
          ·
            refine ⟨13697290034554159256917427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9131526689702772837944951 13697290034554159256917427)
            ·
              refine ⟨20545935051831238885376141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13697290034554159256917427 20545935051831238885376141)
              ·
                refine ⟨7704725644436714582016053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20545935051831238885376141 7704725644436714582016053)
                ·
                  refine ⟨722318029165941992064005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7704725644436714582016053 722318029165941992064005)
                  ·
                    refine ⟨135434630468614123512001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 722318029165941992064005 135434630468614123512001)
                    ·
                      rfl

theorem cell23_791274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_791274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791274 prefixEnd_791274 := by exact prefixLift 791274
  have htrace : WordTrace (prefixWord ++ tailWord_791274) baseStart_791274 baseEnd_791274 := by
    simpa [prefixWord, tailWord_791274, baseEnd_791274] using wordTrace_append hprefix tailTrace_791274
  have hstable : (prefixWord ++ tailWord_791274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791274).length < 2 ^ (prefixWord ++ tailWord_791274).sum := by decide
  have hdescent : baseEnd_791274 < baseStart_791274 := by decide
  rcases family_descends (prefixWord ++ tailWord_791274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791304 : List Nat := [2, 1, 3, 2, 2, 2, 1, 4, 6]
def baseStart_791304 : Nat := 118140960795 + 791304 * 2 ^ 59
def prefixEnd_791304 : Nat := 4983230072969 + 3 ^ 40 * 791304 * 2
def baseEnd_791304 : Nat := 45146588425053028128985

theorem tailTrace_791304 : CollatzResearch.WordTrace tailWord_791304 prefixEnd_791304 45146588425053028128985 := by
  unfold tailWord_791304
  simp only [CollatzResearch.WordTrace]
  refine ⟨14430613962624113404474483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19240818616832151205965977 14430613962624113404474483)
  ·
    refine ⟨21645920943936170106711725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14430613962624113404474483 21645920943936170106711725)
    ·
      refine ⟨8117220353976063790016897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21645920943936170106711725 8117220353976063790016897)
      ·
        refine ⟨6087915265482047842512673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8117220353976063790016897 6087915265482047842512673)
        ·
          refine ⟨4565936449111535881884505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6087915265482047842512673 4565936449111535881884505)
          ·
            refine ⟨3424452336833651911413379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4565936449111535881884505 3424452336833651911413379)
            ·
              refine ⟨5136678505250477867120069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3424452336833651911413379 5136678505250477867120069)
              ·
                refine ⟨963127219734464600085013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5136678505250477867120069 963127219734464600085013)
                ·
                  refine ⟨45146588425053028128985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 963127219734464600085013 45146588425053028128985)
                  ·
                    rfl

theorem cell23_791304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 6].length) (baseStart_791304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791304 prefixEnd_791304 := by exact prefixLift 791304
  have htrace : WordTrace (prefixWord ++ tailWord_791304) baseStart_791304 baseEnd_791304 := by
    simpa [prefixWord, tailWord_791304, baseEnd_791304] using wordTrace_append hprefix tailTrace_791304
  have hstable : (prefixWord ++ tailWord_791304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791304).length < 2 ^ (prefixWord ++ tailWord_791304).sum := by decide
  have hdescent : baseEnd_791304 < baseStart_791304 := by decide
  rcases family_descends (prefixWord ++ tailWord_791304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791307 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 6]
def baseStart_791307 : Nat := 118140960795 + 791307 * 2 ^ 59
def prefixEnd_791307 : Nat := 4983230072969 + 3 ^ 40 * 791307 * 2
def baseEnd_791307 : Nat := 406320836267440741423351

theorem tailTrace_791307 : CollatzResearch.WordTrace tailWord_791307 prefixEnd_791307 406320836267440741423351 := by
  unfold tailWord_791307
  simp only [CollatzResearch.WordTrace]
  refine ⟨28861337344237358321308175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19240891562824905547538783 28861337344237358321308175)
  ·
    refine ⟨43292006016356037481962263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28861337344237358321308175 43292006016356037481962263)
    ·
      refine ⟨64938009024534056222943395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43292006016356037481962263 64938009024534056222943395)
      ·
        refine ⟨97407013536801084334415093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64938009024534056222943395 97407013536801084334415093)
        ·
          refine ⟨9131907519075101656351415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97407013536801084334415093 9131907519075101656351415)
          ·
            refine ⟨13697861278612652484527123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9131907519075101656351415 13697861278612652484527123)
            ·
              refine ⟨20546791917918978726790685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13697861278612652484527123 20546791917918978726790685)
              ·
                refine ⟨7705046969219617022546507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20546791917918978726790685 7705046969219617022546507)
                ·
                  refine ⟨11557570453829425533819761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7705046969219617022546507 11557570453829425533819761)
                  ·
                    refine ⟨8668177840372069150364821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11557570453829425533819761 8668177840372069150364821)
                    ·
                      refine ⟨406320836267440741423351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8668177840372069150364821 406320836267440741423351)
                      ·
                        rfl

theorem cell23_791307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 6].length) (baseStart_791307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791307 prefixEnd_791307 := by exact prefixLift 791307
  have htrace : WordTrace (prefixWord ++ tailWord_791307) baseStart_791307 baseEnd_791307 := by
    simpa [prefixWord, tailWord_791307, baseEnd_791307] using wordTrace_append hprefix tailTrace_791307
  have hstable : (prefixWord ++ tailWord_791307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791307).length < 2 ^ (prefixWord ++ tailWord_791307).sum := by decide
  have hdescent : baseEnd_791307 < baseStart_791307 := by decide
  rcases family_descends (prefixWord ++ tailWord_791307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791388 : List Nat := [2, 2, 4, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_791388 : Nat := 118140960795 + 791388 * 2 ^ 59
def prefixEnd_791388 : Nat := 4983230072969 + 3 ^ 40 * 791388 * 2
def baseEnd_791388 : Nat := 406362428200454924510479

theorem tailTrace_791388 : CollatzResearch.WordTrace tailWord_791388 prefixEnd_791388 406362428200454924510479 := by
  unfold tailWord_791388
  simp only [CollatzResearch.WordTrace]
  refine ⟨14432145828471954577503409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19242861104629272770004545 14432145828471954577503409)
  ·
    refine ⟨10824109371353965933127557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14432145828471954577503409 10824109371353965933127557)
    ·
      refine ⟨2029520507128868612461417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10824109371353965933127557 2029520507128868612461417)
      ·
        refine ⟨1522140380346651459346063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2029520507128868612461417 1522140380346651459346063)
        ·
          refine ⟨2283210570519977189019095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1522140380346651459346063 2283210570519977189019095)
          ·
            refine ⟨3424815855779965783528643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2283210570519977189019095 3424815855779965783528643)
            ·
              refine ⟨5137223783669948675292965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3424815855779965783528643 5137223783669948675292965)
              ·
                refine ⟨963229459438115376617431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5137223783669948675292965 963229459438115376617431)
                ·
                  refine ⟨1444844189157173064926147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 963229459438115376617431 1444844189157173064926147)
                  ·
                    refine ⟨2167266283735759597389221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1444844189157173064926147 2167266283735759597389221)
                    ·
                      refine ⟨406362428200454924510479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2167266283735759597389221 406362428200454924510479)
                      ·
                        rfl

theorem cell23_791388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_791388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791388 prefixEnd_791388 := by exact prefixLift 791388
  have htrace : WordTrace (prefixWord ++ tailWord_791388) baseStart_791388 baseEnd_791388 := by
    simpa [prefixWord, tailWord_791388, baseEnd_791388] using wordTrace_append hprefix tailTrace_791388
  have hstable : (prefixWord ++ tailWord_791388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791388).length < 2 ^ (prefixWord ++ tailWord_791388).sum := by decide
  have hdescent : baseEnd_791388 < baseStart_791388 := by decide
  rcases family_descends (prefixWord ++ tailWord_791388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791442 : List Nat := [3, 2, 3, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_791442 : Nat := 118140960795 + 791442 * 2 ^ 59
def prefixEnd_791442 : Nat := 4983230072969 + 3 ^ 40 * 791442 * 2
def baseEnd_791442 : Nat := 406390156155797713235231

theorem tailTrace_791442 : CollatzResearch.WordTrace tailWord_791442 prefixEnd_791442 406390156155797713235231 := by
  unfold tailWord_791442
  simp only [CollatzResearch.WordTrace]
  refine ⟨7216565299687069094368145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19244174132498850918315053 7216565299687069094368145)
  ·
    refine ⟨5412423974765301820776109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7216565299687069094368145 5412423974765301820776109)
    ·
      refine ⟨2029658990536988182791041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5412423974765301820776109 2029658990536988182791041)
      ·
        refine ⟨1522244242902741137093281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2029658990536988182791041 1522244242902741137093281)
        ·
          refine ⟨1141683182177055852819961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1522244242902741137093281 1141683182177055852819961)
          ·
            refine ⟨856262386632791889614971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1141683182177055852819961 856262386632791889614971)
            ·
              refine ⟨1284393579949187834422457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 856262386632791889614971 1284393579949187834422457)
              ·
                refine ⟨963295184961890875816843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1284393579949187834422457 963295184961890875816843)
                ·
                  refine ⟨1444942777442836313725265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 963295184961890875816843 1444942777442836313725265)
                  ·
                    refine ⟨1083707083082127235293949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1444942777442836313725265 1083707083082127235293949)
                    ·
                      refine ⟨406390156155797713235231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1083707083082127235293949 406390156155797713235231)
                      ·
                        rfl

theorem cell23_791442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_791442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791442 prefixEnd_791442 := by exact prefixLift 791442
  have htrace : WordTrace (prefixWord ++ tailWord_791442) baseStart_791442 baseEnd_791442 := by
    simpa [prefixWord, tailWord_791442, baseEnd_791442] using wordTrace_append hprefix tailTrace_791442
  have hstable : (prefixWord ++ tailWord_791442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791442).length < 2 ^ (prefixWord ++ tailWord_791442).sum := by decide
  have hdescent : baseEnd_791442 < baseStart_791442 := by decide
  rcases family_descends (prefixWord ++ tailWord_791442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791465 : List Nat := [1, 2, 1, 1, 1, 1, 9, 1, 1, 3, 2]
def baseStart_791465 : Nat := 118140960795 + 791465 * 2 ^ 59
def prefixEnd_791465 : Nat := 4983230072969 + 3 ^ 40 * 791465 * 2
def baseEnd_791465 : Nat := 406401966210851123247625

theorem tailTrace_791465 : CollatzResearch.WordTrace tailWord_791465 prefixEnd_791465 406401966210851123247625 := by
  unfold tailWord_791465
  simp only [CollatzResearch.WordTrace]
  refine ⟨28867100077664951305559849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19244733385109967537039899 28867100077664951305559849)
  ·
    refine ⟨21650325058248713479169887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28867100077664951305559849 21650325058248713479169887)
    ·
      refine ⟨32475487587373070218754831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21650325058248713479169887 32475487587373070218754831)
      ·
        refine ⟨48713231381059605328132247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32475487587373070218754831 48713231381059605328132247)
        ·
          refine ⟨73069847071589407992198371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48713231381059605328132247 73069847071589407992198371)
          ·
            refine ⟨109604770607384111988297557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73069847071589407992198371 109604770607384111988297557)
            ·
              refine ⟨642215452777641281181431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 109604770607384111988297557 642215452777641281181431)
              ·
                refine ⟨963323179166461921772147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 642215452777641281181431 963323179166461921772147)
                ·
                  refine ⟨1444984768749692882658221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 963323179166461921772147 1444984768749692882658221)
                  ·
                    refine ⟨541869288281134830996833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1444984768749692882658221 541869288281134830996833)
                    ·
                      refine ⟨406401966210851123247625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 541869288281134830996833 406401966210851123247625)
                      ·
                        rfl

theorem cell23_791465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 1, 3, 2].length) (baseStart_791465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791465 prefixEnd_791465 := by exact prefixLift 791465
  have htrace : WordTrace (prefixWord ++ tailWord_791465) baseStart_791465 baseEnd_791465 := by
    simpa [prefixWord, tailWord_791465, baseEnd_791465] using wordTrace_append hprefix tailTrace_791465
  have hstable : (prefixWord ++ tailWord_791465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791465).length < 2 ^ (prefixWord ++ tailWord_791465).sum := by decide
  have hdescent : baseEnd_791465 < baseStart_791465 := by decide
  rcases family_descends (prefixWord ++ tailWord_791465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791474 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6]
def baseStart_791474 : Nat := 118140960795 + 791474 * 2 ^ 59
def prefixEnd_791474 : Nat := 4983230072969 + 3 ^ 40 * 791474 * 2
def baseEnd_791474 : Nat := 406406587536741588035083

theorem tailTrace_791474 : CollatzResearch.WordTrace tailWord_791474 prefixEnd_791474 406406587536741588035083 := by
  unfold tailWord_791474
  simp only [CollatzResearch.WordTrace]
  refine ⟨7216857083658086460659369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19244952223088230561758317 7216857083658086460659369)
  ·
    refine ⟨5412642812743564845494527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7216857083658086460659369 5412642812743564845494527)
    ·
      refine ⟨8118964219115347268241791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5412642812743564845494527 8118964219115347268241791)
      ·
        refine ⟨12178446328673020902362687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8118964219115347268241791 12178446328673020902362687)
        ·
          refine ⟨18267669493009531353544031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12178446328673020902362687 18267669493009531353544031)
          ·
            refine ⟨27401504239514297030316047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18267669493009531353544031 27401504239514297030316047)
            ·
              refine ⟨41102256359271445545474071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27401504239514297030316047 41102256359271445545474071)
              ·
                refine ⟨61653384538907168318211107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41102256359271445545474071 61653384538907168318211107)
                ·
                  refine ⟨92480076808360752477316661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61653384538907168318211107 92480076808360752477316661)
                  ·
                    refine ⟨8670007200783820544748437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92480076808360752477316661 8670007200783820544748437)
                    ·
                      refine ⟨406406587536741588035083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8670007200783820544748437 406406587536741588035083)
                      ·
                        rfl

theorem cell23_791474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_791474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791474 prefixEnd_791474 := by exact prefixLift 791474
  have htrace : WordTrace (prefixWord ++ tailWord_791474) baseStart_791474 baseEnd_791474 := by
    simpa [prefixWord, tailWord_791474, baseEnd_791474] using wordTrace_append hprefix tailTrace_791474
  have hstable : (prefixWord ++ tailWord_791474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791474).length < 2 ^ (prefixWord ++ tailWord_791474).sum := by decide
  have hdescent : baseEnd_791474 < baseStart_791474 := by decide
  rcases family_descends (prefixWord ++ tailWord_791474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791481 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 2, 4, 3]
def baseStart_791481 : Nat := 118140960795 + 791481 * 2 ^ 59
def prefixEnd_791481 : Nat := 4983230072969 + 3 ^ 40 * 791481 * 2
def baseEnd_791481 : Nat := 406410181901323060647551

theorem tailTrace_791481 : CollatzResearch.WordTrace tailWord_791481 prefixEnd_791481 406410181901323060647551 := by
  unfold tailWord_791481
  simp only [CollatzResearch.WordTrace]
  refine ⟨28867683645606986038142297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19245122430404657358761531 28867683645606986038142297)
  ·
    refine ⟨21650762734205239528606723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28867683645606986038142297 21650762734205239528606723)
    ·
      refine ⟨32476144101307859292910085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21650762734205239528606723 32476144101307859292910085)
      ·
        refine ⟨6089277018995223617420641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32476144101307859292910085 6089277018995223617420641)
        ·
          refine ⟨4566957764246417713065481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6089277018995223617420641 4566957764246417713065481)
          ·
            refine ⟨3425218323184813284799111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4566957764246417713065481 3425218323184813284799111)
            ·
              refine ⟨5137827484777219927198667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3425218323184813284799111 5137827484777219927198667)
              ·
                refine ⟨7706741227165829890798001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5137827484777219927198667 7706741227165829890798001)
                ·
                  refine ⟨5780055920374372418098501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7706741227165829890798001 5780055920374372418098501)
                  ·
                    refine ⟨1083760485070194828393469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5780055920374372418098501 1083760485070194828393469)
                    ·
                      refine ⟨406410181901323060647551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1083760485070194828393469 406410181901323060647551)
                      ·
                        rfl

theorem cell23_791481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_791481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791481 prefixEnd_791481 := by exact prefixLift 791481
  have htrace : WordTrace (prefixWord ++ tailWord_791481) baseStart_791481 baseEnd_791481 := by
    simpa [prefixWord, tailWord_791481, baseEnd_791481] using wordTrace_append hprefix tailTrace_791481
  have hstable : (prefixWord ++ tailWord_791481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791481).length < 2 ^ (prefixWord ++ tailWord_791481).sum := by decide
  have hdescent : baseEnd_791481 < baseStart_791481 := by decide
  rcases family_descends (prefixWord ++ tailWord_791481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791495 : List Nat := [1, 1, 4, 1, 1, 2, 4, 3, 2, 2, 2]
def baseStart_791495 : Nat := 118140960795 + 791495 * 2 ^ 59
def prefixEnd_791495 : Nat := 4983230072969 + 3 ^ 40 * 791495 * 2
def baseEnd_791495 : Nat := 406417370630486005872487

theorem tailTrace_791495 : CollatzResearch.WordTrace tailWord_791495 prefixEnd_791495 406417370630486005872487 := by
  unfold tailWord_791495
  simp only [CollatzResearch.WordTrace]
  refine ⟨28868194267556266429151939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19245462845037510952767959 28868194267556266429151939)
  ·
    refine ⟨43302291401334399643727909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28868194267556266429151939 43302291401334399643727909)
    ·
      refine ⟨8119179637750199933198983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43302291401334399643727909 8119179637750199933198983)
      ·
        refine ⟨12178769456625299899798475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8119179637750199933198983 12178769456625299899798475)
        ·
          refine ⟨18268154184937949849697713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12178769456625299899798475 18268154184937949849697713)
          ·
            refine ⟨13701115638703462387273285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18268154184937949849697713 13701115638703462387273285)
            ·
              refine ⟨2568959182256899197613741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13701115638703462387273285 2568959182256899197613741)
              ·
                refine ⟨963359693346337199105153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2568959182256899197613741 963359693346337199105153)
                ·
                  refine ⟨722519770009752899328865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 963359693346337199105153 722519770009752899328865)
                  ·
                    refine ⟨541889827507314674496649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 722519770009752899328865 541889827507314674496649)
                    ·
                      refine ⟨406417370630486005872487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 541889827507314674496649 406417370630486005872487)
                      ·
                        rfl

theorem cell23_791495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2, 2, 2].length) (baseStart_791495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791495 prefixEnd_791495 := by exact prefixLift 791495
  have htrace : WordTrace (prefixWord ++ tailWord_791495) baseStart_791495 baseEnd_791495 := by
    simpa [prefixWord, tailWord_791495, baseEnd_791495] using wordTrace_append hprefix tailTrace_791495
  have hstable : (prefixWord ++ tailWord_791495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791495).length < 2 ^ (prefixWord ++ tailWord_791495).sum := by decide
  have hdescent : baseEnd_791495 < baseStart_791495 := by decide
  rcases family_descends (prefixWord ++ tailWord_791495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791608 : List Nat := [2, 1, 2, 1, 5, 2, 1, 3, 6]
def baseStart_791608 : Nat := 118140960795 + 791608 * 2 ^ 59
def prefixEnd_791608 : Nat := 4983230072969 + 3 ^ 40 * 791608 * 2
def baseEnd_791608 : Nat := 45163932660493784862163

theorem tailTrace_791608 : CollatzResearch.WordTrace tailWord_791608 prefixEnd_791608 45163932660493784862163 := by
  unfold tailWord_791608
  simp only [CollatzResearch.WordTrace]
  refine ⟨14436157858073443364007739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19248210477431257818676985 14436157858073443364007739)
  ·
    refine ⟨21654236787110165046011609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14436157858073443364007739 21654236787110165046011609)
    ·
      refine ⟨16240677590332623784508707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21654236787110165046011609 16240677590332623784508707)
      ·
        refine ⟨24361016385498935676763061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16240677590332623784508707 24361016385498935676763061)
        ·
          refine ⟨2283845286140525219696537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24361016385498935676763061 2283845286140525219696537)
          ·
            refine ⟨1712883964605393914772403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2283845286140525219696537 1712883964605393914772403)
            ·
              refine ⟨2569325946908090872158605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1712883964605393914772403 2569325946908090872158605)
              ·
                refine ⟨963497230090534077059477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2569325946908090872158605 963497230090534077059477)
                ·
                  refine ⟨45163932660493784862163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 963497230090534077059477 45163932660493784862163)
                  ·
                    rfl

theorem cell23_791608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 6].length) (baseStart_791608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791608 prefixEnd_791608 := by exact prefixLift 791608
  have htrace : WordTrace (prefixWord ++ tailWord_791608) baseStart_791608 baseEnd_791608 := by
    simpa [prefixWord, tailWord_791608, baseEnd_791608] using wordTrace_append hprefix tailTrace_791608
  have hstable : (prefixWord ++ tailWord_791608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791608).length < 2 ^ (prefixWord ++ tailWord_791608).sum := by decide
  have hdescent : baseEnd_791608 < baseStart_791608 := by decide
  rcases family_descends (prefixWord ++ tailWord_791608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791622 : List Nat := [6, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_791622 : Nat := 118140960795 + 791622 * 2 ^ 59
def prefixEnd_791622 : Nat := 4983230072969 + 3 ^ 40 * 791622 * 2
def baseEnd_791622 : Nat := 406482582673607008984403

theorem tailTrace_791622 : CollatzResearch.WordTrace tailWord_791622 prefixEnd_791622 406482582673607008984403 := by
  unfold tailWord_791622
  simp only [CollatzResearch.WordTrace]
  refine ⟨902275823065505222469535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19248550892064111412683413 902275823065505222469535)
  ·
    refine ⟨1353413734598257833704303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 902275823065505222469535 1353413734598257833704303)
    ·
      refine ⟨2030120601897386750556455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1353413734598257833704303 2030120601897386750556455)
      ·
        refine ⟨3045180902846080125834683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2030120601897386750556455 3045180902846080125834683)
        ·
          refine ⟨4567771354269120188752025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3045180902846080125834683 4567771354269120188752025)
          ·
            refine ⟨3425828515701840141564019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4567771354269120188752025 3425828515701840141564019)
            ·
              refine ⟨5138742773552760212346029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3425828515701840141564019 5138742773552760212346029)
              ·
                refine ⟨1927028540082285079629761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5138742773552760212346029 1927028540082285079629761)
                ·
                  refine ⟨1445271405061713809722321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1927028540082285079629761 1445271405061713809722321)
                  ·
                    refine ⟨1083953553796285357291741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1445271405061713809722321 1083953553796285357291741)
                    ·
                      refine ⟨406482582673607008984403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1083953553796285357291741 406482582673607008984403)
                      ·
                        rfl

theorem cell23_791622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_791622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791622 prefixEnd_791622 := by exact prefixLift 791622
  have htrace : WordTrace (prefixWord ++ tailWord_791622) baseStart_791622 baseEnd_791622 := by
    simpa [prefixWord, tailWord_791622, baseEnd_791622] using wordTrace_append hprefix tailTrace_791622
  have hstable : (prefixWord ++ tailWord_791622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791622).length < 2 ^ (prefixWord ++ tailWord_791622).sum := by decide
  have hdescent : baseEnd_791622 < baseStart_791622 := by decide
  rcases family_descends (prefixWord ++ tailWord_791622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791646 : List Nat := [4, 4, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_791646 : Nat := 118140960795 + 791646 * 2 ^ 59
def prefixEnd_791646 : Nat := 4983230072969 + 3 ^ 40 * 791646 * 2
def baseEnd_791646 : Nat := 135498302069771638361431

theorem tailTrace_791646 : CollatzResearch.WordTrace tailWord_791646 prefixEnd_791646 135498302069771638361431 := by
  unfold tailWord_791646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3609212711251152402237349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19249134460006146145265861 3609212711251152402237349)
  ·
    refine ⟨676727383359591075419503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3609212711251152402237349 676727383359591075419503)
    ·
      refine ⟨1015091075039386613129255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 676727383359591075419503 1015091075039386613129255)
      ·
        refine ⟨1522636612559079919693883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1015091075039386613129255 1522636612559079919693883)
        ·
          refine ⟨2283954918838619879540825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1522636612559079919693883 2283954918838619879540825)
          ·
            refine ⟨1712966189128964909655619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2283954918838619879540825 1712966189128964909655619)
            ·
              refine ⟨2569449283693447364483429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1712966189128964909655619 2569449283693447364483429)
              ·
                refine ⟨481771740692521380840643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2569449283693447364483429 481771740692521380840643)
                ·
                  refine ⟨722657611038782071260965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 481771740692521380840643 722657611038782071260965)
                  ·
                    refine ⟨135498302069771638361431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 722657611038782071260965 135498302069771638361431)
                    ·
                      rfl

theorem cell23_791646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_791646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791646 prefixEnd_791646 := by exact prefixLift 791646
  have htrace : WordTrace (prefixWord ++ tailWord_791646) baseStart_791646 baseEnd_791646 := by
    simpa [prefixWord, tailWord_791646, baseEnd_791646] using wordTrace_append hprefix tailTrace_791646
  have hstable : (prefixWord ++ tailWord_791646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791646).length < 2 ^ (prefixWord ++ tailWord_791646).sum := by decide
  have hdescent : baseEnd_791646 < baseStart_791646 := by decide
  rcases family_descends (prefixWord ++ tailWord_791646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791651 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 5, 6]
def baseStart_791651 : Nat := 118140960795 + 791651 * 2 ^ 59
def prefixEnd_791651 : Nat := 4983230072969 + 3 ^ 40 * 791651 * 2
def baseEnd_791651 : Nat := 135499157870862465173923

theorem tailTrace_791651 : CollatzResearch.WordTrace tailWord_791651 prefixEnd_791651 135499157870862465173923 := by
  unfold tailWord_791651
  simp only [CollatzResearch.WordTrace]
  refine ⟨28873884054991105071830807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19249256036660736714553871 28873884054991105071830807)
  ·
    refine ⟨43310826082486657607746211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28873884054991105071830807 43310826082486657607746211)
    ·
      refine ⟨64966239123729986411619317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43310826082486657607746211 64966239123729986411619317)
      ·
        refine ⟨6090584917849686226089311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64966239123729986411619317 6090584917849686226089311)
        ·
          refine ⟨9135877376774529339133967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6090584917849686226089311 9135877376774529339133967)
          ·
            refine ⟨13703816065161794008700951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9135877376774529339133967 13703816065161794008700951)
            ·
              refine ⟨20555724097742691013051427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13703816065161794008700951 20555724097742691013051427)
              ·
                refine ⟨30833586146614036519577141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20555724097742691013051427 30833586146614036519577141)
                ·
                  refine ⟨2890648701245065923710357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30833586146614036519577141 2890648701245065923710357)
                  ·
                    refine ⟨135499157870862465173923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2890648701245065923710357 135499157870862465173923)
                    ·
                      rfl

theorem cell23_791651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 6].length) (baseStart_791651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791651 prefixEnd_791651 := by exact prefixLift 791651
  have htrace : WordTrace (prefixWord ++ tailWord_791651) baseStart_791651 baseEnd_791651 := by
    simpa [prefixWord, tailWord_791651, baseEnd_791651] using wordTrace_append hprefix tailTrace_791651
  have hstable : (prefixWord ++ tailWord_791651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791651).length < 2 ^ (prefixWord ++ tailWord_791651).sum := by decide
  have hdescent : baseEnd_791651 < baseStart_791651 := by decide
  rcases family_descends (prefixWord ++ tailWord_791651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791669 : List Nat := [1, 3, 4, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_791669 : Nat := 118140960795 + 791669 * 2 ^ 59
def prefixEnd_791669 : Nat := 4983230072969 + 3 ^ 40 * 791669 * 2
def baseEnd_791669 : Nat := 406506716264368325096687

theorem tailTrace_791669 : CollatzResearch.WordTrace tailWord_791669 prefixEnd_791669 406506716264368325096687 := by
  unfold tailWord_791669
  simp only [CollatzResearch.WordTrace]
  refine ⟨28874540568925894145986061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19249693712617262763990707 28874540568925894145986061)
  ·
    refine ⟨10827952713347210304744773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28874540568925894145986061 10827952713347210304744773)
    ·
      refine ⟨2030241133752601932139645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10827952713347210304744773 2030241133752601932139645)
      ·
        refine ⟨761340425157225724552367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2030241133752601932139645 761340425157225724552367)
        ·
          refine ⟨1142010637735838586828551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 761340425157225724552367 1142010637735838586828551)
          ·
            refine ⟨1713015956603757880242827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1142010637735838586828551 1713015956603757880242827)
            ·
              refine ⟨2569523934905636820364241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1713015956603757880242827 2569523934905636820364241)
              ·
                refine ⟨1927142951179227615273181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2569523934905636820364241 1927142951179227615273181)
                ·
                  refine ⟨722678606692210355727443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1927142951179227615273181 722678606692210355727443)
                  ·
                    refine ⟨1084017910038315533591165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 722678606692210355727443 1084017910038315533591165)
                    ·
                      refine ⟨406506716264368325096687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1084017910038315533591165 406506716264368325096687)
                      ·
                        rfl

theorem cell23_791669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_791669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791669 prefixEnd_791669 := by exact prefixLift 791669
  have htrace : WordTrace (prefixWord ++ tailWord_791669) baseStart_791669 baseEnd_791669 := by
    simpa [prefixWord, tailWord_791669, baseEnd_791669] using wordTrace_append hprefix tailTrace_791669
  have hstable : (prefixWord ++ tailWord_791669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791669).length < 2 ^ (prefixWord ++ tailWord_791669).sum := by decide
  have hdescent : baseEnd_791669 < baseStart_791669 := by decide
  rcases family_descends (prefixWord ++ tailWord_791669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791698 : List Nat := [3, 2, 3, 1, 1, 3, 10]
def baseStart_791698 : Nat := 118140960795 + 791698 * 2 ^ 59
def prefixEnd_791698 : Nat := 4983230072969 + 3 ^ 40 * 791698 * 2
def baseEnd_791698 : Nat := 5018785274115416193013

theorem tailTrace_791698 : CollatzResearch.WordTrace tailWord_791698 prefixEnd_791698 5018785274115416193013 := by
  unfold tailWord_791698
  simp only [CollatzResearch.WordTrace]
  refine ⟨7218899571455208024697937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19250398857213888065861165 7218899571455208024697937)
  ·
    refine ⟨5414174678591406018523453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7218899571455208024697937 5414174678591406018523453)
    ·
      refine ⟨2030315504471777256946295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5414174678591406018523453 2030315504471777256946295)
      ·
        refine ⟨3045473256707665885419443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2030315504471777256946295 3045473256707665885419443)
        ·
          refine ⟨4568209885061498828129165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3045473256707665885419443 4568209885061498828129165)
          ·
            refine ⟨1713078706898062060548437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4568209885061498828129165 1713078706898062060548437)
            ·
              refine ⟨5018785274115416193013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1713078706898062060548437 5018785274115416193013)
              ·
                rfl

theorem cell23_791698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 10].length) (baseStart_791698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791698 prefixEnd_791698 := by exact prefixLift 791698
  have htrace : WordTrace (prefixWord ++ tailWord_791698) baseStart_791698 baseEnd_791698 := by
    simpa [prefixWord, tailWord_791698, baseEnd_791698] using wordTrace_append hprefix tailTrace_791698
  have hstable : (prefixWord ++ tailWord_791698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791698).length < 2 ^ (prefixWord ++ tailWord_791698).sum := by decide
  have hdescent : baseEnd_791698 < baseStart_791698 := by decide
  rcases family_descends (prefixWord ++ tailWord_791698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791709 : List Nat := [1, 4, 2, 1, 1, 2, 1, 6, 1, 2, 2]
def baseStart_791709 : Nat := 118140960795 + 791709 * 2 ^ 59
def prefixEnd_791709 : Nat := 4983230072969 + 3 ^ 40 * 791709 * 2
def baseEnd_791709 : Nat := 406527255490548168596503

theorem tailTrace_791709 : CollatzResearch.WordTrace tailWord_791709 prefixEnd_791709 406527255490548168596503 := by
  unfold tailWord_791709
  simp only [CollatzResearch.WordTrace]
  refine ⟨28875999488780980977442181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19250666325853987318294787 28875999488780980977442181)
  ·
    refine ⟨5414249904146433933270409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28875999488780980977442181 5414249904146433933270409)
    ·
      refine ⟨4060687428109825449952807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5414249904146433933270409 4060687428109825449952807)
      ·
        refine ⟨6091031142164738174929211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4060687428109825449952807 6091031142164738174929211)
        ·
          refine ⟨9136546713247107262393817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6091031142164738174929211 9136546713247107262393817)
          ·
            refine ⟨6852410034935330446795363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9136546713247107262393817 6852410034935330446795363)
            ·
              refine ⟨10278615052402995670193045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6852410034935330446795363 10278615052402995670193045)
              ·
                refine ⟨481810080581390422040299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10278615052402995670193045 481810080581390422040299)
                ·
                  refine ⟨722715120872085633060449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 481810080581390422040299 722715120872085633060449)
                  ·
                    refine ⟨542036340654064224795337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 722715120872085633060449 542036340654064224795337)
                    ·
                      refine ⟨406527255490548168596503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 542036340654064224795337 406527255490548168596503)
                      ·
                        rfl

theorem cell23_791709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_791709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791709 prefixEnd_791709 := by exact prefixLift 791709
  have htrace : WordTrace (prefixWord ++ tailWord_791709) baseStart_791709 baseEnd_791709 := by
    simpa [prefixWord, tailWord_791709, baseEnd_791709] using wordTrace_append hprefix tailTrace_791709
  have hstable : (prefixWord ++ tailWord_791709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791709).length < 2 ^ (prefixWord ++ tailWord_791709).sum := by decide
  have hdescent : baseEnd_791709 < baseStart_791709 := by decide
  rcases family_descends (prefixWord ++ tailWord_791709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791719 : List Nat := [1, 1, 6, 2, 1, 2, 3, 1, 2, 4]
def baseStart_791719 : Nat := 118140960795 + 791719 * 2 ^ 59
def prefixEnd_791719 : Nat := 4983230072969 + 3 ^ 40 * 791719 * 2
def baseEnd_791719 : Nat := 135510796765697709823819

theorem tailTrace_791719 : CollatzResearch.WordTrace tailWord_791719 prefixEnd_791719 135510796765697709823819 := by
  unfold tailWord_791719
  simp only [CollatzResearch.WordTrace]
  refine ⟨28876364218744752685306211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19250909479163168456870807 28876364218744752685306211)
  ·
    refine ⟨43314546328117129027959317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28876364218744752685306211 43314546328117129027959317)
    ·
      refine ⟨2030369359130490423185593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43314546328117129027959317 2030369359130490423185593)
      ·
        refine ⟨1522777019347867817389195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2030369359130490423185593 1522777019347867817389195)
        ·
          refine ⟨2284165529021801726083793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1522777019347867817389195 2284165529021801726083793)
          ·
            refine ⟨1713124146766351294562845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2284165529021801726083793 1713124146766351294562845)
            ·
              refine ⟨642421555037381735461067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1713124146766351294562845 642421555037381735461067)
              ·
                refine ⟨963632332556072603191601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 642421555037381735461067 963632332556072603191601)
                ·
                  refine ⟨722724249417054452393701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 963632332556072603191601 722724249417054452393701)
                  ·
                    refine ⟨135510796765697709823819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 722724249417054452393701 135510796765697709823819)
                    ·
                      rfl

theorem cell23_791719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_791719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791719 prefixEnd_791719 := by exact prefixLift 791719
  have htrace : WordTrace (prefixWord ++ tailWord_791719) baseStart_791719 baseEnd_791719 := by
    simpa [prefixWord, tailWord_791719, baseEnd_791719] using wordTrace_append hprefix tailTrace_791719
  have hstable : (prefixWord ++ tailWord_791719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791719).length < 2 ^ (prefixWord ++ tailWord_791719).sum := by decide
  have hdescent : baseEnd_791719 < baseStart_791719 := by decide
  rcases family_descends (prefixWord ++ tailWord_791719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791722 : List Nat := [3, 1, 5, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_791722 : Nat := 118140960795 + 791722 * 2 ^ 59
def prefixEnd_791722 : Nat := 4983230072969 + 3 ^ 40 * 791722 * 2
def baseEnd_791722 : Nat := 406533930739056617733943

theorem tailTrace_791722 : CollatzResearch.WordTrace tailWord_791722 prefixEnd_791722 406533930739056617733943 := by
  unfold tailWord_791722
  simp only [CollatzResearch.WordTrace]
  refine ⟨7219118409433471049416355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19250982425155922798443613 7219118409433471049416355)
  ·
    refine ⟨10828677614150206574124533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7219118409433471049416355 10828677614150206574124533)
    ·
      refine ⟨1015188526326581866324175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10828677614150206574124533 1015188526326581866324175)
      ·
        refine ⟨1522782789489872799486263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1015188526326581866324175 1522782789489872799486263)
        ·
          refine ⟨2284174184234809199229395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1522782789489872799486263 2284174184234809199229395)
          ·
            refine ⟨3426261276352213798844093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2284174184234809199229395 3426261276352213798844093)
            ·
              refine ⟨1284847978632080174566535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3426261276352213798844093 1284847978632080174566535)
              ·
                refine ⟨1927271967948120261849803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1284847978632080174566535 1927271967948120261849803)
                ·
                  refine ⟨2890907951922180392774705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1927271967948120261849803 2890907951922180392774705)
                  ·
                    refine ⟨2168180963941635294581029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2890907951922180392774705 2168180963941635294581029)
                    ·
                      refine ⟨406533930739056617733943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2168180963941635294581029 406533930739056617733943)
                      ·
                        rfl

theorem cell23_791722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_791722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791722 prefixEnd_791722 := by exact prefixLift 791722
  have htrace : WordTrace (prefixWord ++ tailWord_791722) baseStart_791722 baseEnd_791722 := by
    simpa [prefixWord, tailWord_791722, baseEnd_791722] using wordTrace_append hprefix tailTrace_791722
  have hstable : (prefixWord ++ tailWord_791722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791722).length < 2 ^ (prefixWord ++ tailWord_791722).sum := by decide
  have hdescent : baseEnd_791722 < baseStart_791722 := by decide
  rcases family_descends (prefixWord ++ tailWord_791722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791742 : List Nat := [4, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3]
def baseStart_791742 : Nat := 118140960795 + 791742 * 2 ^ 59
def prefixEnd_791742 : Nat := 4983230072969 + 3 ^ 40 * 791742 * 2
def baseEnd_791742 : Nat := 406544200352146539483851

theorem tailTrace_791742 : CollatzResearch.WordTrace tailWord_791742 prefixEnd_791742 406544200352146539483851 := by
  unfold tailWord_791742
  simp only [CollatzResearch.WordTrace]
  refine ⟨3609650387207678451674185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19251468731774285075595653 3609650387207678451674185)
  ·
    refine ⟨2707237790405758838755639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3609650387207678451674185 2707237790405758838755639)
    ·
      refine ⟨4060856685608638258133459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2707237790405758838755639 4060856685608638258133459)
      ·
        refine ⟨6091285028412957387200189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4060856685608638258133459 6091285028412957387200189)
        ·
          refine ⟨2284231885654859020200071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6091285028412957387200189 2284231885654859020200071)
          ·
            refine ⟨3426347828482288530300107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2284231885654859020200071 3426347828482288530300107)
            ·
              refine ⟨5139521742723432795450161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3426347828482288530300107 5139521742723432795450161)
              ·
                refine ⟨3854641307042574596587621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5139521742723432795450161 3854641307042574596587621)
                ·
                  refine ⟨722745245070482736860179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3854641307042574596587621 722745245070482736860179)
                  ·
                    refine ⟨1084117867605724105290269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 722745245070482736860179 1084117867605724105290269)
                    ·
                      refine ⟨406544200352146539483851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1084117867605724105290269 406544200352146539483851)
                      ·
                        rfl

theorem cell23_791742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_791742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791742 prefixEnd_791742 := by exact prefixLift 791742
  have htrace : WordTrace (prefixWord ++ tailWord_791742) baseStart_791742 baseEnd_791742 := by
    simpa [prefixWord, tailWord_791742, baseEnd_791742] using wordTrace_append hprefix tailTrace_791742
  have hstable : (prefixWord ++ tailWord_791742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791742).length < 2 ^ (prefixWord ++ tailWord_791742).sum := by decide
  have hdescent : baseEnd_791742 < baseStart_791742 := by decide
  rcases family_descends (prefixWord ++ tailWord_791742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791752 : List Nat := [2, 1, 3, 1, 2, 1, 4, 3, 1, 3, 2]
def baseStart_791752 : Nat := 118140960795 + 791752 * 2 ^ 59
def prefixEnd_791752 : Nat := 4983230072969 + 3 ^ 40 * 791752 * 2
def baseEnd_791752 : Nat := 406549335158691500358805

theorem tailTrace_791752 : CollatzResearch.WordTrace tailWord_791752 prefixEnd_791752 406549335158691500358805 := by
  unfold tailWord_791752
  simp only [CollatzResearch.WordTrace]
  refine ⟨14438783913812599660628755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19251711885083466214171673 14438783913812599660628755)
  ·
    refine ⟨21658175870718899490943133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14438783913812599660628755 21658175870718899490943133)
    ·
      refine ⟨8121815951519587309103675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21658175870718899490943133 8121815951519587309103675)
      ·
        refine ⟨12182723927279380963655513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8121815951519587309103675 12182723927279380963655513)
        ·
          refine ⟨9137042945459535722741635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12182723927279380963655513 9137042945459535722741635)
          ·
            refine ⟨13705564418189303584112453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9137042945459535722741635 13705564418189303584112453)
            ·
              refine ⟨2569793328410494422021085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13705564418189303584112453 2569793328410494422021085)
              ·
                refine ⟨963672498153935408257907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2569793328410494422021085 963672498153935408257907)
                ·
                  refine ⟨1445508747230903112386861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 963672498153935408257907 1445508747230903112386861)
                  ·
                    refine ⟨542065780211588667145073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1445508747230903112386861 542065780211588667145073)
                    ·
                      refine ⟨406549335158691500358805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 542065780211588667145073 406549335158691500358805)
                      ·
                        rfl

theorem cell23_791752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 1, 3, 2].length) (baseStart_791752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791752 prefixEnd_791752 := by exact prefixLift 791752
  have htrace : WordTrace (prefixWord ++ tailWord_791752) baseStart_791752 baseEnd_791752 := by
    simpa [prefixWord, tailWord_791752, baseEnd_791752] using wordTrace_append hprefix tailTrace_791752
  have hstable : (prefixWord ++ tailWord_791752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791752).length < 2 ^ (prefixWord ++ tailWord_791752).sum := by decide
  have hdescent : baseEnd_791752 < baseStart_791752 := by decide
  rcases family_descends (prefixWord ++ tailWord_791752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791816 : List Nat := [2, 1, 3, 2, 4, 1, 2, 2, 2, 2, 2]
def baseStart_791816 : Nat := 118140960795 + 791816 * 2 ^ 59
def prefixEnd_791816 : Nat := 4983230072969 + 3 ^ 40 * 791816 * 2
def baseEnd_791816 : Nat := 406582197920579249958511

theorem tailTrace_791816 : CollatzResearch.WordTrace tailWord_791816 prefixEnd_791816 406582197920579249958511 := by
  unfold tailWord_791816
  simp only [CollatzResearch.WordTrace]
  refine ⟨14439951049696669125793651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19253268066262225501058201 14439951049696669125793651)
  ·
    refine ⟨21659926574545003688690477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14439951049696669125793651 21659926574545003688690477)
    ·
      refine ⟨8122472465454376383258929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21659926574545003688690477 8122472465454376383258929)
      ·
        refine ⟨6091854349090782287444197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8122472465454376383258929 6091854349090782287444197)
        ·
          refine ⟨1142222690454521678895787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6091854349090782287444197 1142222690454521678895787)
          ·
            refine ⟨1713334035681782518343681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1142222690454521678895787 1713334035681782518343681)
            ·
              refine ⟨1285000526761336888757761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1713334035681782518343681 1285000526761336888757761)
              ·
                refine ⟨963750395071002666568321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1285000526761336888757761 963750395071002666568321)
                ·
                  refine ⟨722812796303251999926241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 963750395071002666568321 722812796303251999926241)
                  ·
                    refine ⟨542109597227438999944681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 722812796303251999926241 542109597227438999944681)
                    ·
                      refine ⟨406582197920579249958511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 542109597227438999944681 406582197920579249958511)
                      ·
                        rfl

theorem cell23_791816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_791816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791816 prefixEnd_791816 := by exact prefixLift 791816
  have htrace : WordTrace (prefixWord ++ tailWord_791816) baseStart_791816 baseEnd_791816 := by
    simpa [prefixWord, tailWord_791816, baseEnd_791816] using wordTrace_append hprefix tailTrace_791816
  have hstable : (prefixWord ++ tailWord_791816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791816).length < 2 ^ (prefixWord ++ tailWord_791816).sum := by decide
  have hdescent : baseEnd_791816 < baseStart_791816 := by decide
  rcases family_descends (prefixWord ++ tailWord_791816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791818 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 3, 7]
def baseStart_791818 : Nat := 118140960795 + 791818 * 2 ^ 59
def prefixEnd_791818 : Nat := 4983230072969 + 3 ^ 40 * 791818 * 2
def baseEnd_791818 : Nat := 135527741627296080711167

theorem tailTrace_791818 : CollatzResearch.WordTrace tailWord_791818 prefixEnd_791818 135527741627296080711167 := by
  unfold tailWord_791818
  simp only [CollatzResearch.WordTrace]
  refine ⟨7219993761346523148290027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19253316696924061728773405 7219993761346523148290027)
  ·
    refine ⟨10829990642019784722435041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7219993761346523148290027 10829990642019784722435041)
    ·
      refine ⟨8122492981514838541826281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10829990642019784722435041 8122492981514838541826281)
      ·
        refine ⟨6091869736136128906369711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8122492981514838541826281 6091869736136128906369711)
        ·
          refine ⟨9137804604204193359554567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6091869736136128906369711 9137804604204193359554567)
          ·
            refine ⟨13706706906306290039331851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9137804604204193359554567 13706706906306290039331851)
            ·
              refine ⟨20560060359459435058997777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13706706906306290039331851 20560060359459435058997777)
              ·
                refine ⟨15420045269594576294248333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20560060359459435058997777 15420045269594576294248333)
                ·
                  refine ⟨5782516976097966110343125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15420045269594576294248333 5782516976097966110343125)
                  ·
                    refine ⟨135527741627296080711167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5782516976097966110343125 135527741627296080711167)
                    ·
                      rfl

theorem cell23_791818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_791818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791818 prefixEnd_791818 := by exact prefixLift 791818
  have htrace : WordTrace (prefixWord ++ tailWord_791818) baseStart_791818 baseEnd_791818 := by
    simpa [prefixWord, tailWord_791818, baseEnd_791818] using wordTrace_append hprefix tailTrace_791818
  have hstable : (prefixWord ++ tailWord_791818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791818).length < 2 ^ (prefixWord ++ tailWord_791818).sum := by decide
  have hdescent : baseEnd_791818 < baseStart_791818 := by decide
  rcases family_descends (prefixWord ++ tailWord_791818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791822 : List Nat := [4, 1, 1, 2, 1, 4, 1, 4, 5]
def baseStart_791822 : Nat := 118140960795 + 791822 * 2 ^ 59
def prefixEnd_791822 : Nat := 4983230072969 + 3 ^ 40 * 791822 * 2
def baseEnd_791822 : Nat := 45176142089389580720387

theorem tailTrace_791822 : CollatzResearch.WordTrace tailWord_791822 prefixEnd_791822 45176142089389580720387 := by
  unfold tailWord_791822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3610015117171450159538215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19253413958247734184203813 3610015117171450159538215)
  ·
    refine ⟨5415022675757175239307323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3610015117171450159538215 5415022675757175239307323)
    ·
      refine ⟨8122534013635762858960985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5415022675757175239307323 8122534013635762858960985)
      ·
        refine ⟨6091900510226822144220739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8122534013635762858960985 6091900510226822144220739)
        ·
          refine ⟨9137850765340233216331109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6091900510226822144220739 9137850765340233216331109)
          ·
            refine ⟨1713347018501293728062083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9137850765340233216331109 1713347018501293728062083)
            ·
              refine ⟨2570020527751940592093125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1713347018501293728062083 2570020527751940592093125)
              ·
                refine ⟨481878848953488861017461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2570020527751940592093125 481878848953488861017461)
                ·
                  refine ⟨45176142089389580720387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 481878848953488861017461 45176142089389580720387)
                  ·
                    rfl

theorem cell23_791822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4, 5].length) (baseStart_791822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791822 prefixEnd_791822 := by exact prefixLift 791822
  have htrace : WordTrace (prefixWord ++ tailWord_791822) baseStart_791822 baseEnd_791822 := by
    simpa [prefixWord, tailWord_791822, baseEnd_791822] using wordTrace_append hprefix tailTrace_791822
  have hstable : (prefixWord ++ tailWord_791822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791822).length < 2 ^ (prefixWord ++ tailWord_791822).sum := by decide
  have hdescent : baseEnd_791822 < baseStart_791822 := by decide
  rcases family_descends (prefixWord ++ tailWord_791822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791825 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 1, 7, 2]
def baseStart_791825 : Nat := 118140960795 + 791825 * 2 ^ 59
def prefixEnd_791825 : Nat := 4983230072969 + 3 ^ 40 * 791825 * 2
def baseEnd_791825 : Nat := 406586819246469714745969

theorem tailTrace_791825 : CollatzResearch.WordTrace tailWord_791825 prefixEnd_791825 406586819246469714745969 := by
  unfold tailWord_791825
  simp only [CollatzResearch.WordTrace]
  refine ⟨28880230356360732788664929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19253486904240488525776619 28880230356360732788664929)
  ·
    refine ⟨21660172767270549591498697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28880230356360732788664929 21660172767270549591498697)
    ·
      refine ⟨16245129575452912193624023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21660172767270549591498697 16245129575452912193624023)
      ·
        refine ⟨24367694363179368290436035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16245129575452912193624023 24367694363179368290436035)
        ·
          refine ⟨36551541544769052435654053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24367694363179368290436035 36551541544769052435654053)
          ·
            refine ⟨6853414039644197331685135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36551541544769052435654053 6853414039644197331685135)
            ·
              refine ⟨10280121059466295997527703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6853414039644197331685135 10280121059466295997527703)
              ·
                refine ⟨15420181589199443996291555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10280121059466295997527703 15420181589199443996291555)
                ·
                  refine ⟨23130272383799165994437333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15420181589199443996291555 23130272383799165994437333)
                  ·
                    refine ⟨542115758995292952994625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23130272383799165994437333 542115758995292952994625)
                    ·
                      refine ⟨406586819246469714745969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 542115758995292952994625 406586819246469714745969)
                      ·
                        rfl

theorem cell23_791825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 7, 2].length) (baseStart_791825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791825 prefixEnd_791825 := by exact prefixLift 791825
  have htrace : WordTrace (prefixWord ++ tailWord_791825) baseStart_791825 baseEnd_791825 := by
    simpa [prefixWord, tailWord_791825, baseEnd_791825] using wordTrace_append hprefix tailTrace_791825
  have hstable : (prefixWord ++ tailWord_791825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791825).length < 2 ^ (prefixWord ++ tailWord_791825).sum := by decide
  have hdescent : baseEnd_791825 < baseStart_791825 := by decide
  rcases family_descends (prefixWord ++ tailWord_791825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791855 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 3, 6, 2]
def baseStart_791855 : Nat := 118140960795 + 791855 * 2 ^ 59
def prefixEnd_791855 : Nat := 4983230072969 + 3 ^ 40 * 791855 * 2
def baseEnd_791855 : Nat := 406602223666104597370831

theorem tailTrace_791855 : CollatzResearch.WordTrace tailWord_791855 prefixEnd_791855 406602223666104597370831 := by
  unfold tailWord_791855
  simp only [CollatzResearch.WordTrace]
  refine ⟨28881324546252047912257019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19254216364168031941504679 28881324546252047912257019)
  ·
    refine ⟨43321986819378071868385529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28881324546252047912257019 43321986819378071868385529)
    ·
      refine ⟨32491490114533553901289147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43321986819378071868385529 32491490114533553901289147)
      ·
        refine ⟨48737235171800330851933721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32491490114533553901289147 48737235171800330851933721)
        ·
          refine ⟨36552926378850248138950291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48737235171800330851933721 36552926378850248138950291)
          ·
            refine ⟨54829389568275372208425437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36552926378850248138950291 54829389568275372208425437)
            ·
              refine ⟨20561021088103264578159539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54829389568275372208425437 20561021088103264578159539)
              ·
                refine ⟨30841531632154896867239309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20561021088103264578159539 30841531632154896867239309)
                ·
                  refine ⟨11565574362058086325214741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30841531632154896867239309 11565574362058086325214741)
                  ·
                    refine ⟨542136298221472796494441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11565574362058086325214741 542136298221472796494441)
                    ·
                      refine ⟨406602223666104597370831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 542136298221472796494441 406602223666104597370831)
                      ·
                        rfl

theorem cell23_791855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 6, 2].length) (baseStart_791855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791855 prefixEnd_791855 := by exact prefixLift 791855
  have htrace : WordTrace (prefixWord ++ tailWord_791855) baseStart_791855 baseEnd_791855 := by
    simpa [prefixWord, tailWord_791855, baseEnd_791855] using wordTrace_append hprefix tailTrace_791855
  have hstable : (prefixWord ++ tailWord_791855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791855).length < 2 ^ (prefixWord ++ tailWord_791855).sum := by decide
  have hdescent : baseEnd_791855 < baseStart_791855 := by decide
  rcases family_descends (prefixWord ++ tailWord_791855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791875 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 4, 2, 3]
def baseStart_791875 : Nat := 118140960795 + 791875 * 2 ^ 59
def prefixEnd_791875 : Nat := 4983230072969 + 3 ^ 40 * 791875 * 2
def baseEnd_791875 : Nat := 406612493279194519120739

theorem tailTrace_791875 : CollatzResearch.WordTrace tailWord_791875 prefixEnd_791875 406612493279194519120739 := by
  unfold tailWord_791875
  simp only [CollatzResearch.WordTrace]
  refine ⟨28882054006179591327985079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19254702670786394218656719 28882054006179591327985079)
  ·
    refine ⟨43323081009269386991977619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28882054006179591327985079 43323081009269386991977619)
    ·
      refine ⟨64984621513904080487966429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43323081009269386991977619 64984621513904080487966429)
      ·
        refine ⟨24369233067714030182987411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64984621513904080487966429 24369233067714030182987411)
        ·
          refine ⟨36553849601571045274481117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24369233067714030182987411 36553849601571045274481117)
          ·
            refine ⟨13707693600589141977930419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36553849601571045274481117 13707693600589141977930419)
            ·
              refine ⟨20561540400883712966895629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13707693600589141977930419 20561540400883712966895629)
              ·
                refine ⟨7710577650331392362585861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20561540400883712966895629 7710577650331392362585861)
                ·
                  refine ⟨1445733309437136067984849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7710577650331392362585861 1445733309437136067984849)
                  ·
                    refine ⟨1084299982077852050988637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1445733309437136067984849 1084299982077852050988637)
                    ·
                      refine ⟨406612493279194519120739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1084299982077852050988637 406612493279194519120739)
                      ·
                        rfl

theorem cell23_791875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2, 3].length) (baseStart_791875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791875 prefixEnd_791875 := by exact prefixLift 791875
  have htrace : WordTrace (prefixWord ++ tailWord_791875) baseStart_791875 baseEnd_791875 := by
    simpa [prefixWord, tailWord_791875, baseEnd_791875] using wordTrace_append hprefix tailTrace_791875
  have hstable : (prefixWord ++ tailWord_791875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791875).length < 2 ^ (prefixWord ++ tailWord_791875).sum := by decide
  have hdescent : baseEnd_791875 < baseStart_791875 := by decide
  rcases family_descends (prefixWord ++ tailWord_791875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791916 : List Nat := [2, 2, 1, 1, 5, 3, 1, 3, 1, 4]
def baseStart_791916 : Nat := 118140960795 + 791916 * 2 ^ 59
def prefixEnd_791916 : Nat := 4983230072969 + 3 ^ 40 * 791916 * 2
def baseEnd_791916 : Nat := 135544515328676286236017

theorem tailTrace_791916 : CollatzResearch.WordTrace tailWord_791916 prefixEnd_791916 135544515328676286236017 := by
  unfold tailWord_791916
  simp only [CollatzResearch.WordTrace]
  refine ⟨14441774699515527665113801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19255699599354036886818401 14441774699515527665113801)
  ·
    refine ⟨10831331024636645748835351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14441774699515527665113801 10831331024636645748835351)
    ·
      refine ⟨16246996536954968623253027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10831331024636645748835351 16246996536954968623253027)
      ·
        refine ⟨24370494805432452934879541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16246996536954968623253027 24370494805432452934879541)
        ·
          refine ⟨2284733888009292462644957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24370494805432452934879541 2284733888009292462644957)
          ·
            refine ⟨856775208003484673491859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2284733888009292462644957 856775208003484673491859)
            ·
              refine ⟨1285162812005227010237789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 856775208003484673491859 1285162812005227010237789)
              ·
                refine ⟨481936054501960128839171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1285162812005227010237789 481936054501960128839171)
                ·
                  refine ⟨722904081752940193258757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 481936054501960128839171 722904081752940193258757)
                  ·
                    refine ⟨135544515328676286236017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 722904081752940193258757 135544515328676286236017)
                    ·
                      rfl

theorem cell23_791916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3, 1, 4].length) (baseStart_791916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791916 prefixEnd_791916 := by exact prefixLift 791916
  have htrace : WordTrace (prefixWord ++ tailWord_791916) baseStart_791916 baseEnd_791916 := by
    simpa [prefixWord, tailWord_791916, baseEnd_791916] using wordTrace_append hprefix tailTrace_791916
  have hstable : (prefixWord ++ tailWord_791916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791916).length < 2 ^ (prefixWord ++ tailWord_791916).sum := by decide
  have hdescent : baseEnd_791916 < baseStart_791916 := by decide
  rcases family_descends (prefixWord ++ tailWord_791916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791939 : List Nat := [1, 1, 1, 3, 5, 1, 3, 1, 3, 1, 3]
def baseStart_791939 : Nat := 118140960795 + 791939 * 2 ^ 59
def prefixEnd_791939 : Nat := 4983230072969 + 3 ^ 40 * 791939 * 2
def baseEnd_791939 : Nat := 406645356041082268720445

theorem tailTrace_791939 : CollatzResearch.WordTrace tailWord_791939 prefixEnd_791939 406645356041082268720445 := by
  unfold tailWord_791939
  simp only [CollatzResearch.WordTrace]
  refine ⟨28884388277947730258314871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19256258851965153505543247 28884388277947730258314871)
  ·
    refine ⟨43326582416921595387472307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28884388277947730258314871 43326582416921595387472307)
    ·
      refine ⟨64989873625382393081208461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43326582416921595387472307 64989873625382393081208461)
      ·
        refine ⟨24371202609518397405453173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64989873625382393081208461 24371202609518397405453173)
        ·
          refine ⟨2284800244642349756761235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24371202609518397405453173 2284800244642349756761235)
          ·
            refine ⟨3427200366963524635141853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2284800244642349756761235 3427200366963524635141853)
            ·
              refine ⟨1285200137611321738178195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3427200366963524635141853 1285200137611321738178195)
              ·
                refine ⟨1927800206416982607267293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1285200137611321738178195 1927800206416982607267293)
                ·
                  refine ⟨722925077406368477725235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1927800206416982607267293 722925077406368477725235)
                  ·
                    refine ⟨1084387616109552716587853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 722925077406368477725235 1084387616109552716587853)
                    ·
                      refine ⟨406645356041082268720445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1084387616109552716587853 406645356041082268720445)
                      ·
                        rfl

theorem cell23_791939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3, 1, 3].length) (baseStart_791939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791939 prefixEnd_791939 := by exact prefixLift 791939
  have htrace : WordTrace (prefixWord ++ tailWord_791939) baseStart_791939 baseEnd_791939 := by
    simpa [prefixWord, tailWord_791939, baseEnd_791939] using wordTrace_append hprefix tailTrace_791939
  have hstable : (prefixWord ++ tailWord_791939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791939).length < 2 ^ (prefixWord ++ tailWord_791939).sum := by decide
  have hdescent : baseEnd_791939 < baseStart_791939 := by decide
  rcases family_descends (prefixWord ++ tailWord_791939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791962 : List Nat := [3, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4]
def baseStart_791962 : Nat := 118140960795 + 791962 * 2 ^ 59
def prefixEnd_791962 : Nat := 4983230072969 + 3 ^ 40 * 791962 * 2
def baseEnd_791962 : Nat := 406657166096135678732839

theorem tailTrace_791962 : CollatzResearch.WordTrace tailWord_791962 prefixEnd_791962 406657166096135678732839 := by
  unfold tailWord_791962
  simp only [CollatzResearch.WordTrace]
  refine ⟨7221306789216101296600535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19256818104576270124268093 7221306789216101296600535)
  ·
    refine ⟨10831960183824151944900803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7221306789216101296600535 10831960183824151944900803)
    ·
      refine ⟨16247940275736227917351205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10831960183824151944900803 16247940275736227917351205)
      ·
        refine ⟨3046488801700542734503351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16247940275736227917351205 3046488801700542734503351)
        ·
          refine ⟨4569733202550814101755027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3046488801700542734503351 4569733202550814101755027)
          ·
            refine ⟨6854599803826221152632541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4569733202550814101755027 6854599803826221152632541)
            ·
              refine ⟨2570474926434832932237203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6854599803826221152632541 2570474926434832932237203)
              ·
                refine ⟨3855712389652249398355805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2570474926434832932237203 3855712389652249398355805)
                ·
                  refine ⟨1445892146119593524383427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3855712389652249398355805 1445892146119593524383427)
                  ·
                    refine ⟨2168838219179390286575141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1445892146119593524383427 2168838219179390286575141)
                    ·
                      refine ⟨406657166096135678732839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2168838219179390286575141 406657166096135678732839)
                      ·
                        rfl

theorem cell23_791962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_791962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791962 prefixEnd_791962 := by exact prefixLift 791962
  have htrace : WordTrace (prefixWord ++ tailWord_791962) baseStart_791962 baseEnd_791962 := by
    simpa [prefixWord, tailWord_791962, baseEnd_791962] using wordTrace_append hprefix tailTrace_791962
  have hstable : (prefixWord ++ tailWord_791962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791962).length < 2 ^ (prefixWord ++ tailWord_791962).sum := by decide
  have hdescent : baseEnd_791962 < baseStart_791962 := by decide
  rcases family_descends (prefixWord ++ tailWord_791962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791989 : List Nat := [1, 3, 3, 2, 2, 1, 1, 4, 2, 4]
def baseStart_791989 : Nat := 118140960795 + 791989 * 2 ^ 59
def prefixEnd_791989 : Nat := 4983230072969 + 3 ^ 40 * 791989 * 2
def baseEnd_791989 : Nat := 135557010024602357698405

theorem tailTrace_791989 : CollatzResearch.WordTrace tailWord_791989 prefixEnd_791989 135557010024602357698405 := by
  unfold tailWord_791989
  simp only [CollatzResearch.WordTrace]
  refine ⟨28886211927766588797635021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19257474618511059198423347 28886211927766588797635021)
  ·
    refine ⟨10832329472912470799113133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28886211927766588797635021 10832329472912470799113133)
    ·
      refine ⟨4062123552342176549667425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10832329472912470799113133 4062123552342176549667425)
      ·
        refine ⟨3046592664256632412250569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4062123552342176549667425 3046592664256632412250569)
        ·
          refine ⟨2284944498192474309187927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3046592664256632412250569 2284944498192474309187927)
          ·
            refine ⟨3427416747288711463781891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2284944498192474309187927 3427416747288711463781891)
            ·
              refine ⟨5141125120933067195672837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3427416747288711463781891 5141125120933067195672837)
              ·
                refine ⟨963960960174950099188657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5141125120933067195672837 963960960174950099188657)
                ·
                  refine ⟨722970720131212574391493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 963960960174950099188657 722970720131212574391493)
                  ·
                    refine ⟨135557010024602357698405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 722970720131212574391493 135557010024602357698405)
                    ·
                      rfl

theorem cell23_791989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_791989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791989 prefixEnd_791989 := by exact prefixLift 791989
  have htrace : WordTrace (prefixWord ++ tailWord_791989) baseStart_791989 baseEnd_791989 := by
    simpa [prefixWord, tailWord_791989, baseEnd_791989] using wordTrace_append hprefix tailTrace_791989
  have hstable : (prefixWord ++ tailWord_791989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791989).length < 2 ^ (prefixWord ++ tailWord_791989).sum := by decide
  have hdescent : baseEnd_791989 < baseStart_791989 := by decide
  rcases family_descends (prefixWord ++ tailWord_791989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791995 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 1, 9, 3]
def baseStart_791995 : Nat := 118140960795 + 791995 * 2 ^ 59
def prefixEnd_791995 : Nat := 4983230072969 + 3 ^ 40 * 791995 * 2
def baseEnd_791995 : Nat := 406674110957734049620187

theorem tailTrace_791995 : CollatzResearch.WordTrace tailWord_791995 prefixEnd_791995 406674110957734049620187 := by
  unfold tailWord_791995
  simp only [CollatzResearch.WordTrace]
  refine ⟨28886430765744851822353439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19257620510496567881568959 28886430765744851822353439)
  ·
    refine ⟨43329646148617277733530159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28886430765744851822353439 43329646148617277733530159)
    ·
      refine ⟨64994469222925916600295239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43329646148617277733530159 64994469222925916600295239)
      ·
        refine ⟨97491703834388874900442859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64994469222925916600295239 97491703834388874900442859)
        ·
          refine ⟨146237555751583312350664289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97491703834388874900442859 146237555751583312350664289)
          ·
            refine ⟨109678166813687484262998217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146237555751583312350664289 109678166813687484262998217)
            ·
              refine ⟨82258625110265613197248663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109678166813687484262998217 82258625110265613197248663)
              ·
                refine ⟨123387937665398419795872995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82258625110265613197248663 123387937665398419795872995)
                ·
                  refine ⟨185081906498097629693809493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123387937665398419795872995 185081906498097629693809493)
                  ·
                    refine ⟨1084464295887290798987165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 185081906498097629693809493 1084464295887290798987165)
                    ·
                      refine ⟨406674110957734049620187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1084464295887290798987165 406674110957734049620187)
                      ·
                        rfl

theorem cell23_791995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9, 3].length) (baseStart_791995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_791995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_791995 prefixEnd_791995 := by exact prefixLift 791995
  have htrace : WordTrace (prefixWord ++ tailWord_791995) baseStart_791995 baseEnd_791995 := by
    simpa [prefixWord, tailWord_791995, baseEnd_791995] using wordTrace_append hprefix tailTrace_791995
  have hstable : (prefixWord ++ tailWord_791995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791995).length < 2 ^ (prefixWord ++ tailWord_791995).sum := by decide
  have hdescent : baseEnd_791995 < baseStart_791995 := by decide
  rcases family_descends (prefixWord ++ tailWord_791995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792029 : List Nat := [1, 4, 3, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_792029 : Nat := 118140960795 + 792029 * 2 ^ 59
def prefixEnd_792029 : Nat := 4983230072969 + 3 ^ 40 * 792029 * 2
def baseEnd_792029 : Nat := 406691569299986916595031

theorem tailTrace_792029 : CollatzResearch.WordTrace tailWord_792029 prefixEnd_792029 406691569299986916595031 := by
  unfold tailWord_792029
  simp only [CollatzResearch.WordTrace]
  refine ⟨28887670847621675629091141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19258447231747783752727427 28887670847621675629091141)
  ·
    refine ⟨5416438283929064180454589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28887670847621675629091141 5416438283929064180454589)
    ·
      refine ⟨2031164356473399067670471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5416438283929064180454589 2031164356473399067670471)
      ·
        refine ⟨3046746534710098601505707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2031164356473399067670471 3046746534710098601505707)
        ·
          refine ⟨4570119802065147902258561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3046746534710098601505707 4570119802065147902258561)
          ·
            refine ⟨3427589851548860926693921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4570119802065147902258561 3427589851548860926693921)
            ·
              refine ⟨2570692388661645695020441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3427589851548860926693921 2570692388661645695020441)
              ·
                refine ⟨1928019291496234271265331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2570692388661645695020441 1928019291496234271265331)
                ·
                  refine ⟨2892028937244351406897997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1928019291496234271265331 2892028937244351406897997)
                  ·
                    refine ⟨1084510851466631777586749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2892028937244351406897997 1084510851466631777586749)
                    ·
                      refine ⟨406691569299986916595031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1084510851466631777586749 406691569299986916595031)
                      ·
                        rfl

theorem cell23_792029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_792029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792029 prefixEnd_792029 := by exact prefixLift 792029
  have htrace : WordTrace (prefixWord ++ tailWord_792029) baseStart_792029 baseEnd_792029 := by
    simpa [prefixWord, tailWord_792029, baseEnd_792029] using wordTrace_append hprefix tailTrace_792029
  have hstable : (prefixWord ++ tailWord_792029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792029).length < 2 ^ (prefixWord ++ tailWord_792029).sum := by decide
  have hdescent : baseEnd_792029 < baseStart_792029 := by decide
  rcases family_descends (prefixWord ++ tailWord_792029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792055 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 5]
def baseStart_792055 : Nat := 118140960795 + 792055 * 2 ^ 59
def prefixEnd_792055 : Nat := 4983230072969 + 3 ^ 40 * 792055 * 2
def baseEnd_792055 : Nat := 406704919797003814869911

theorem tailTrace_792055 : CollatzResearch.WordTrace tailWord_792055 prefixEnd_792055 406704919797003814869911 := by
  unfold tailWord_792055
  simp only [CollatzResearch.WordTrace]
  refine ⟨28888619145527482069537619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19259079430351654713025079 28888619145527482069537619)
  ·
    refine ⟨43332928718291223104306429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28888619145527482069537619 43332928718291223104306429)
    ·
      refine ⟨16249848269359208664114911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43332928718291223104306429 16249848269359208664114911)
      ·
        refine ⟨24374772404038812996172367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16249848269359208664114911 24374772404038812996172367)
        ·
          refine ⟨36562158606058219494258551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24374772404038812996172367 36562158606058219494258551)
          ·
            refine ⟨54843237909087329241387827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36562158606058219494258551 54843237909087329241387827)
            ·
              refine ⟨82264856863630993862081741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54843237909087329241387827 82264856863630993862081741)
              ·
                refine ⟨30849321323861622698280653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82264856863630993862081741 30849321323861622698280653)
                ·
                  refine ⟨11568495496448108511855245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30849321323861622698280653 11568495496448108511855245)
                  ·
                    refine ⟨4338185811168040691945717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11568495496448108511855245 4338185811168040691945717)
                    ·
                      refine ⟨406704919797003814869911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4338185811168040691945717 406704919797003814869911)
                      ·
                        rfl

theorem cell23_792055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_792055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792055 prefixEnd_792055 := by exact prefixLift 792055
  have htrace : WordTrace (prefixWord ++ tailWord_792055) baseStart_792055 baseEnd_792055 := by
    simpa [prefixWord, tailWord_792055, baseEnd_792055] using wordTrace_append hprefix tailTrace_792055
  have hstable : (prefixWord ++ tailWord_792055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792055).length < 2 ^ (prefixWord ++ tailWord_792055).sum := by decide
  have hdescent : baseEnd_792055 < baseStart_792055 := by decide
  rcases family_descends (prefixWord ++ tailWord_792055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792070 : List Nat := [6, 2, 1, 1, 2, 2, 2, 7]
def baseStart_792070 : Nat := 118140960795 + 792070 * 2 ^ 59
def prefixEnd_792070 : Nat := 4983230072969 + 3 ^ 40 * 792070 * 2
def baseEnd_792070 : Nat := 15063430444697083562309

theorem tailTrace_792070 : CollatzResearch.WordTrace tailWord_792070 prefixEnd_792070 15063430444697083562309 := by
  unfold tailWord_792070
  simp only [CollatzResearch.WordTrace]
  refine ⟨902786445014785613479177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19259444160315426420889109 902786445014785613479177)
  ·
    refine ⟨677089833761089210109383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 902786445014785613479177 677089833761089210109383)
    ·
      refine ⟨1015634750641633815164075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 677089833761089210109383 1015634750641633815164075)
      ·
        refine ⟨1523452125962450722746113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1015634750641633815164075 1523452125962450722746113)
        ·
          refine ⟨1142589094471838042059585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1523452125962450722746113 1142589094471838042059585)
          ·
            refine ⟨856941820853878531544689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1142589094471838042059585 856941820853878531544689)
            ·
              refine ⟨642706365640408898658517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 856941820853878531544689 642706365640408898658517)
              ·
                refine ⟨15063430444697083562309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 642706365640408898658517 15063430444697083562309)
                ·
                  rfl

theorem cell23_792070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_792070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792070 prefixEnd_792070 := by exact prefixLift 792070
  have htrace : WordTrace (prefixWord ++ tailWord_792070) baseStart_792070 baseEnd_792070 := by
    simpa [prefixWord, tailWord_792070, baseEnd_792070] using wordTrace_append hprefix tailTrace_792070
  have hstable : (prefixWord ++ tailWord_792070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792070).length < 2 ^ (prefixWord ++ tailWord_792070).sum := by decide
  have hdescent : baseEnd_792070 < baseStart_792070 := by decide
  rcases family_descends (prefixWord ++ tailWord_792070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792072 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 2, 4, 3]
def baseStart_792072 : Nat := 118140960795 + 792072 * 2 ^ 59
def prefixEnd_792072 : Nat := 4983230072969 + 3 ^ 40 * 792072 * 2
def baseEnd_792072 : Nat := 406713648968130248357333

theorem tailTrace_792072 : CollatzResearch.WordTrace tailWord_792072 prefixEnd_792072 406713648968130248357333 := by
  unfold tailWord_792072
  simp only [CollatzResearch.WordTrace]
  refine ⟨14444619593232946986453235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19259492790977262648604313 14444619593232946986453235)
  ·
    refine ⟨21666929389849420479679853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14444619593232946986453235 21666929389849420479679853)
    ·
      refine ⟨8125098521193532679879945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21666929389849420479679853 8125098521193532679879945)
      ·
        refine ⟨6093823890895149509909959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8125098521193532679879945 6093823890895149509909959)
        ·
          refine ⟨9140735836342724264864939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6093823890895149509909959 9140735836342724264864939)
          ·
            refine ⟨13711103754514086397297409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9140735836342724264864939 13711103754514086397297409)
            ·
              refine ⟨10283327815885564797973057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13711103754514086397297409 10283327815885564797973057)
              ·
                refine ⟨7712495861914173598479793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10283327815885564797973057 7712495861914173598479793)
                ·
                  refine ⟨5784371896435630198859845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7712495861914173598479793 5784371896435630198859845)
                  ·
                    refine ⟨1084569730581680662286221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5784371896435630198859845 1084569730581680662286221)
                    ·
                      refine ⟨406713648968130248357333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1084569730581680662286221 406713648968130248357333)
                      ·
                        rfl

theorem cell23_792072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_792072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792072 prefixEnd_792072 := by exact prefixLift 792072
  have htrace : WordTrace (prefixWord ++ tailWord_792072) baseStart_792072 baseEnd_792072 := by
    simpa [prefixWord, tailWord_792072, baseEnd_792072] using wordTrace_append hprefix tailTrace_792072
  have hstable : (prefixWord ++ tailWord_792072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792072).length < 2 ^ (prefixWord ++ tailWord_792072).sum := by decide
  have hdescent : baseEnd_792072 < baseStart_792072 := by decide
  rcases family_descends (prefixWord ++ tailWord_792072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792105 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 1, 13]
def baseStart_792105 : Nat := 118140960795 + 792105 * 2 ^ 59
def prefixEnd_792105 : Nat := 4983230072969 + 3 ^ 40 * 792105 * 2
def baseEnd_792105 : Nat := 135576864609909539748227

theorem tailTrace_792105 : CollatzResearch.WordTrace tailWord_792105 prefixEnd_792105 135576864609909539748227 := by
  unfold tailWord_792105
  simp only [CollatzResearch.WordTrace]
  refine ⟨28890442795346340608857769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19260295196897560405905179 28890442795346340608857769)
  ·
    refine ⟨21667832096509755456643327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28890442795346340608857769 21667832096509755456643327)
    ·
      refine ⟨32501748144764633184964991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21667832096509755456643327 32501748144764633184964991)
      ·
        refine ⟨48752622217146949777447487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32501748144764633184964991 48752622217146949777447487)
        ·
          refine ⟨73128933325720424666171231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48752622217146949777447487 73128933325720424666171231)
          ·
            refine ⟨109693399988580636999256847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73128933325720424666171231 109693399988580636999256847)
            ·
              refine ⟨164540099982870955498885271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109693399988580636999256847 164540099982870955498885271)
              ·
                refine ⟨246810149974306433248327907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164540099982870955498885271 246810149974306433248327907)
                ·
                  refine ⟨370215224961459649872491861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 246810149974306433248327907 370215224961459649872491861)
                  ·
                    refine ⟨135576864609909539748227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 13 370215224961459649872491861 135576864609909539748227)
                    ·
                      rfl

theorem cell23_792105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 13].length) (baseStart_792105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792105 prefixEnd_792105 := by exact prefixLift 792105
  have htrace : WordTrace (prefixWord ++ tailWord_792105) baseStart_792105 baseEnd_792105 := by
    simpa [prefixWord, tailWord_792105, baseEnd_792105] using wordTrace_append hprefix tailTrace_792105
  have hstable : (prefixWord ++ tailWord_792105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792105).length < 2 ^ (prefixWord ++ tailWord_792105).sum := by decide
  have hdescent : baseEnd_792105 < baseStart_792105 := by decide
  rcases family_descends (prefixWord ++ tailWord_792105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792120 : List Nat := [2, 1, 2, 1, 4, 4, 2, 1, 2, 2, 2]
def baseStart_792120 : Nat := 118140960795 + 792120 * 2 ^ 59
def prefixEnd_792120 : Nat := 4983230072969 + 3 ^ 40 * 792120 * 2
def baseEnd_792120 : Nat := 406738296039546060557113

theorem tailTrace_792120 : CollatzResearch.WordTrace tailWord_792120 prefixEnd_792120 406738296039546060557113 := by
  unfold tailWord_792120
  simp only [CollatzResearch.WordTrace]
  refine ⟨14445494945145999085326907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19260659926861332113769209 14445494945145999085326907)
  ·
    refine ⟨21668242417718998627990361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14445494945145999085326907 21668242417718998627990361)
    ·
      refine ⟨16251181813289248970992771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21668242417718998627990361 16251181813289248970992771)
      ·
        refine ⟨24376772719933873456489157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16251181813289248970992771 24376772719933873456489157)
        ·
          refine ⟨4570644884987601273091717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24376772719933873456489157 4570644884987601273091717)
          ·
            refine ⟨856995915935175238704697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4570644884987601273091717 856995915935175238704697)
            ·
              refine ⟨642746936951381429028523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 856995915935175238704697 642746936951381429028523)
              ·
                refine ⟨964120405427072143542785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 642746936951381429028523 964120405427072143542785)
                ·
                  refine ⟨723090304070304107657089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 964120405427072143542785 723090304070304107657089)
                  ·
                    refine ⟨542317728052728080742817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 723090304070304107657089 542317728052728080742817)
                    ·
                      refine ⟨406738296039546060557113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 542317728052728080742817 406738296039546060557113)
                      ·
                        rfl

theorem cell23_792120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 2, 2, 2].length) (baseStart_792120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792120 prefixEnd_792120 := by exact prefixLift 792120
  have htrace : WordTrace (prefixWord ++ tailWord_792120) baseStart_792120 baseEnd_792120 := by
    simpa [prefixWord, tailWord_792120, baseEnd_792120] using wordTrace_append hprefix tailTrace_792120
  have hstable : (prefixWord ++ tailWord_792120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792120).length < 2 ^ (prefixWord ++ tailWord_792120).sum := by decide
  have hdescent : baseEnd_792120 < baseStart_792120 := by decide
  rcases family_descends (prefixWord ++ tailWord_792120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792122 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 4, 5]
def baseStart_792122 : Nat := 118140960795 + 792122 * 2 ^ 59
def prefixEnd_792122 : Nat := 4983230072969 + 3 ^ 40 * 792122 * 2
def baseEnd_792122 : Nat := 135579774333618350910701

theorem tailTrace_792122 : CollatzResearch.WordTrace tailWord_792122 prefixEnd_792122 135579774333618350910701 := by
  unfold tailWord_792122
  simp only [CollatzResearch.WordTrace]
  refine ⟨7222765709071188128056655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19260708557523168341484413 7222765709071188128056655)
  ·
    refine ⟨10834148563606782192084983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7222765709071188128056655 10834148563606782192084983)
    ·
      refine ⟨16251222845410173288127475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10834148563606782192084983 16251222845410173288127475)
      ·
        refine ⟨24376834268115259932191213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16251222845410173288127475 24376834268115259932191213)
        ·
          refine ⟨9141312850543222474571705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24376834268115259932191213 9141312850543222474571705)
          ·
            refine ⟨6855984637907416855928779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9141312850543222474571705 6855984637907416855928779)
            ·
              refine ⟨10283976956861125283893169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6855984637907416855928779 10283976956861125283893169)
              ·
                refine ⟨7712982717645843962919877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10283976956861125283893169 7712982717645843962919877)
                ·
                  refine ⟨1446184259558595743047477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7712982717645843962919877 1446184259558595743047477)
                  ·
                    refine ⟨135579774333618350910701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1446184259558595743047477 135579774333618350910701)
                    ·
                      rfl

theorem cell23_792122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 4, 5].length) (baseStart_792122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792122 prefixEnd_792122 := by exact prefixLift 792122
  have htrace : WordTrace (prefixWord ++ tailWord_792122) baseStart_792122 baseEnd_792122 := by
    simpa [prefixWord, tailWord_792122, baseEnd_792122] using wordTrace_append hprefix tailTrace_792122
  have hstable : (prefixWord ++ tailWord_792122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792122).length < 2 ^ (prefixWord ++ tailWord_792122).sum := by decide
  have hdescent : baseEnd_792122 < baseStart_792122 := by decide
  rcases family_descends (prefixWord ++ tailWord_792122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792172 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 4]
def baseStart_792172 : Nat := 118140960795 + 792172 * 2 ^ 59
def prefixEnd_792172 : Nat := 4983230072969 + 3 ^ 40 * 792172 * 2
def baseEnd_792172 : Nat := 406764997033579857106873

theorem tailTrace_792172 : CollatzResearch.WordTrace tailWord_792172 prefixEnd_792172 406764997033579857106873 := by
  unfold tailWord_792172
  simp only [CollatzResearch.WordTrace]
  refine ⟨14446443243051805525773385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19261924324069074034364513 14446443243051805525773385)
  ·
    refine ⟨10834832432288854144330039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14446443243051805525773385 10834832432288854144330039)
    ·
      refine ⟨16252248648433281216495059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10834832432288854144330039 16252248648433281216495059)
      ·
        refine ⟨24378372972649921824742589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16252248648433281216495059 24378372972649921824742589)
        ·
          refine ⟨9141889864743720684278471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24378372972649921824742589 9141889864743720684278471)
          ·
            refine ⟨13712834797115581026417707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9141889864743720684278471 13712834797115581026417707)
            ·
              refine ⟨20569252195673371539626561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13712834797115581026417707 20569252195673371539626561)
              ·
                refine ⟨15426939146755028654719921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20569252195673371539626561 15426939146755028654719921)
                ·
                  refine ⟨11570204360066271491039941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15426939146755028654719921 11570204360066271491039941)
                  ·
                    refine ⟨2169413317512425904569989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11570204360066271491039941 2169413317512425904569989)
                    ·
                      refine ⟨406764997033579857106873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2169413317512425904569989 406764997033579857106873)
                      ·
                        rfl

theorem cell23_792172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_792172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792172 prefixEnd_792172 := by exact prefixLift 792172
  have htrace : WordTrace (prefixWord ++ tailWord_792172) baseStart_792172 baseEnd_792172 := by
    simpa [prefixWord, tailWord_792172, baseEnd_792172] using wordTrace_append hprefix tailTrace_792172
  have hstable : (prefixWord ++ tailWord_792172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792172).length < 2 ^ (prefixWord ++ tailWord_792172).sum := by decide
  have hdescent : baseEnd_792172 < baseStart_792172 := by decide
  rcases family_descends (prefixWord ++ tailWord_792172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792176 : List Nat := [2, 1, 1, 1, 6, 2, 1, 1, 2, 4, 2]
def baseStart_792176 : Nat := 118140960795 + 792176 * 2 ^ 59
def prefixEnd_792176 : Nat := 4983230072969 + 3 ^ 40 * 792176 * 2
def baseEnd_792176 : Nat := 406767050956197841456855

theorem tailTrace_792176 : CollatzResearch.WordTrace tailWord_792176 prefixEnd_792176 406767050956197841456855 := by
  unfold tailWord_792176
  simp only [CollatzResearch.WordTrace]
  refine ⟨14446516189044559867346191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19262021585392746489794921 14446516189044559867346191)
  ·
    refine ⟨21669774283566839801019287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14446516189044559867346191 21669774283566839801019287)
    ·
      refine ⟨32504661425350259701528931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21669774283566839801019287 32504661425350259701528931)
      ·
        refine ⟨48756992138025389552293397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32504661425350259701528931 48756992138025389552293397)
        ·
          refine ⟨2285484006469940135263753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48756992138025389552293397 2285484006469940135263753)
          ·
            refine ⟨1714113004852455101447815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2285484006469940135263753 1714113004852455101447815)
            ·
              refine ⟨2571169507278682652171723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1714113004852455101447815 2571169507278682652171723)
              ·
                refine ⟨3856754260918023978257585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2571169507278682652171723 3856754260918023978257585)
                ·
                  refine ⟨2892565695688517983693189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3856754260918023978257585 2892565695688517983693189)
                  ·
                    refine ⟨542356067941597121942473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2892565695688517983693189 542356067941597121942473)
                    ·
                      refine ⟨406767050956197841456855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 542356067941597121942473 406767050956197841456855)
                      ·
                        rfl

theorem cell23_792176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 2, 4, 2].length) (baseStart_792176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792176 prefixEnd_792176 := by exact prefixLift 792176
  have htrace : WordTrace (prefixWord ++ tailWord_792176) baseStart_792176 baseEnd_792176 := by
    simpa [prefixWord, tailWord_792176, baseEnd_792176] using wordTrace_append hprefix tailTrace_792176
  have hstable : (prefixWord ++ tailWord_792176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792176).length < 2 ^ (prefixWord ++ tailWord_792176).sum := by decide
  have hdescent : baseEnd_792176 < baseStart_792176 := by decide
  rcases family_descends (prefixWord ++ tailWord_792176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792196 : List Nat := [2, 3, 2, 1, 4, 1, 1, 1, 1, 4, 3]
def baseStart_792196 : Nat := 118140960795 + 792196 * 2 ^ 59
def prefixEnd_792196 : Nat := 4983230072969 + 3 ^ 40 * 792196 * 2
def baseEnd_792196 : Nat := 406777320569287763206763

theorem tailTrace_792196 : CollatzResearch.WordTrace tailWord_792196 prefixEnd_792196 406777320569287763206763 := by
  unfold tailWord_792196
  simp only [CollatzResearch.WordTrace]
  refine ⟨14446880919008331575210221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19262507892011108766946961 14446880919008331575210221)
  ·
    refine ⟨5417580344628124340703833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14446880919008331575210221 5417580344628124340703833)
    ·
      refine ⟨4063185258471093255527875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5417580344628124340703833 4063185258471093255527875)
      ·
        refine ⟨6094777887706639883291813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4063185258471093255527875 6094777887706639883291813)
        ·
          refine ⟨1142770853944994978117215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6094777887706639883291813 1142770853944994978117215)
          ·
            refine ⟨1714156280917492467175823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1142770853944994978117215 1714156280917492467175823)
            ·
              refine ⟨2571234421376238700763735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1714156280917492467175823 2571234421376238700763735)
              ·
                refine ⟨3856851632064358051145603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2571234421376238700763735 3856851632064358051145603)
                ·
                  refine ⟨5785277448096537076718405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3856851632064358051145603 5785277448096537076718405)
                  ·
                    refine ⟨1084739521518100701884701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5785277448096537076718405 1084739521518100701884701)
                    ·
                      refine ⟨406777320569287763206763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1084739521518100701884701 406777320569287763206763)
                      ·
                        rfl

theorem cell23_792196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_792196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792196 prefixEnd_792196 := by exact prefixLift 792196
  have htrace : WordTrace (prefixWord ++ tailWord_792196) baseStart_792196 baseEnd_792196 := by
    simpa [prefixWord, tailWord_792196, baseEnd_792196] using wordTrace_append hprefix tailTrace_792196
  have hstable : (prefixWord ++ tailWord_792196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792196).length < 2 ^ (prefixWord ++ tailWord_792196).sum := by decide
  have hdescent : baseEnd_792196 < baseStart_792196 := by decide
  rcases family_descends (prefixWord ++ tailWord_792196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792216 : List Nat := [2, 1, 2, 4, 1, 4, 1, 2, 6]
def baseStart_792216 : Nat := 118140960795 + 792216 * 2 ^ 59
def prefixEnd_792216 : Nat := 4983230072969 + 3 ^ 40 * 792216 * 2
def baseEnd_792216 : Nat := 45198621131375298328519

theorem tailTrace_792216 : CollatzResearch.WordTrace tailWord_792216 prefixEnd_792216 45198621131375298328519 := by
  unfold tailWord_792216
  simp only [CollatzResearch.WordTrace]
  refine ⟨14447245648972103283074251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19262994198629471044099001 14447245648972103283074251)
  ·
    refine ⟨21670868473458154924611377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14447245648972103283074251 21670868473458154924611377)
    ·
      refine ⟨16253151355093616193458533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21670868473458154924611377 16253151355093616193458533)
      ·
        refine ⟨3047465879080053036273475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16253151355093616193458533 3047465879080053036273475)
        ·
          refine ⟨4571198818620079554410213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3047465879080053036273475 4571198818620079554410213)
          ·
            refine ⟨857099778491264916451915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4571198818620079554410213 857099778491264916451915)
            ·
              refine ⟨1285649667736897374677873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 857099778491264916451915 1285649667736897374677873)
              ·
                refine ⟨964237250802673031008405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1285649667736897374677873 964237250802673031008405)
                ·
                  refine ⟨45198621131375298328519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 964237250802673031008405 45198621131375298328519)
                  ·
                    rfl

theorem cell23_792216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 6].length) (baseStart_792216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792216 prefixEnd_792216 := by exact prefixLift 792216
  have htrace : WordTrace (prefixWord ++ tailWord_792216) baseStart_792216 baseEnd_792216 := by
    simpa [prefixWord, tailWord_792216, baseEnd_792216] using wordTrace_append hprefix tailTrace_792216
  have hstable : (prefixWord ++ tailWord_792216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792216).length < 2 ^ (prefixWord ++ tailWord_792216).sum := by decide
  have hdescent : baseEnd_792216 < baseStart_792216 := by decide
  rcases family_descends (prefixWord ++ tailWord_792216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792249 : List Nat := [1, 2, 1, 4, 1, 1, 2, 3, 3, 1, 4]
def baseStart_792249 : Nat := 118140960795 + 792249 * 2 ^ 59
def prefixEnd_792249 : Nat := 4983230072969 + 3 ^ 40 * 792249 * 2
def baseEnd_792249 : Nat := 406804535043976055844019

theorem tailTrace_792249 : CollatzResearch.WordTrace tailWord_792249 prefixEnd_792249 406804535043976055844019 := by
  unfold tailWord_792249
  simp only [CollatzResearch.WordTrace]
  refine ⟨28895694906824653202099801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19263796604549768801399867 28895694906824653202099801)
  ·
    refine ⟨21671771180118489901574851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28895694906824653202099801 21671771180118489901574851)
    ·
      refine ⟨32507656770177734852362277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21671771180118489901574851 32507656770177734852362277)
      ·
        refine ⟨6095185644408325284817927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32507656770177734852362277 6095185644408325284817927)
        ·
          refine ⟨9142778466612487927226891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6095185644408325284817927 9142778466612487927226891)
          ·
            refine ⟨13714167699918731890840337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9142778466612487927226891 13714167699918731890840337)
            ·
              refine ⟨10285625774939048918130253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13714167699918731890840337 10285625774939048918130253)
              ·
                refine ⟨3857109665602143344298845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10285625774939048918130253 3857109665602143344298845)
                ·
                  refine ⟨1446416124600803754112067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3857109665602143344298845 1446416124600803754112067)
                  ·
                    refine ⟨2169624186901205631168101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1446416124600803754112067 2169624186901205631168101)
                    ·
                      refine ⟨406804535043976055844019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2169624186901205631168101 406804535043976055844019)
                      ·
                        rfl

theorem cell23_792249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_792249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792249 prefixEnd_792249 := by exact prefixLift 792249
  have htrace : WordTrace (prefixWord ++ tailWord_792249) baseStart_792249 baseEnd_792249 := by
    simpa [prefixWord, tailWord_792249, baseEnd_792249] using wordTrace_append hprefix tailTrace_792249
  have hstable : (prefixWord ++ tailWord_792249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792249).length < 2 ^ (prefixWord ++ tailWord_792249).sum := by decide
  have hdescent : baseEnd_792249 < baseStart_792249 := by decide
  rcases family_descends (prefixWord ++ tailWord_792249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792316 : List Nat := [2, 2, 2, 1, 3, 1, 3, 2, 1, 3, 3]
def baseStart_792316 : Nat := 118140960795 + 792316 * 2 ^ 59
def prefixEnd_792316 : Nat := 4983230072969 + 3 ^ 40 * 792316 * 2
def baseEnd_792316 : Nat := 406838938247827293706211

theorem tailTrace_792316 : CollatzResearch.WordTrace tailWord_792316 prefixEnd_792316 406838938247827293706211 := by
  unfold tailWord_792316
  simp only [CollatzResearch.WordTrace]
  refine ⟨14449069298790961822394401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19265425731721282429859201 14449069298790961822394401)
  ·
    refine ⟨10836801974093221366795801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14449069298790961822394401 10836801974093221366795801)
    ·
      refine ⟨8127601480569916025096851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10836801974093221366795801 8127601480569916025096851)
      ·
        refine ⟨12191402220854874037645277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8127601480569916025096851 12191402220854874037645277)
        ·
          refine ⟨4571775832820577764116979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12191402220854874037645277 4571775832820577764116979)
          ·
            refine ⟨6857663749230866646175469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4571775832820577764116979 6857663749230866646175469)
            ·
              refine ⟨2571623905961574992315801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6857663749230866646175469 2571623905961574992315801)
              ·
                refine ⟨1928717929471181244236851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2571623905961574992315801 1928717929471181244236851)
                ·
                  refine ⟨2893076894206771866355277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1928717929471181244236851 2893076894206771866355277)
                  ·
                    refine ⟨1084903835327539449883229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2893076894206771866355277 1084903835327539449883229)
                    ·
                      refine ⟨406838938247827293706211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1084903835327539449883229 406838938247827293706211)
                      ·
                        rfl

theorem cell23_792316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_792316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792316 prefixEnd_792316 := by exact prefixLift 792316
  have htrace : WordTrace (prefixWord ++ tailWord_792316) baseStart_792316 baseEnd_792316 := by
    simpa [prefixWord, tailWord_792316, baseEnd_792316] using wordTrace_append hprefix tailTrace_792316
  have hstable : (prefixWord ++ tailWord_792316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792316).length < 2 ^ (prefixWord ++ tailWord_792316).sum := by decide
  have hdescent : baseEnd_792316 < baseStart_792316 := by decide
  rcases family_descends (prefixWord ++ tailWord_792316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792343 : List Nat := [1, 1, 3, 4, 2, 1, 1, 2, 3, 3, 2]
def baseStart_792343 : Nat := 118140960795 + 792343 * 2 ^ 59
def prefixEnd_792343 : Nat := 4983230072969 + 3 ^ 40 * 792343 * 2
def baseEnd_792343 : Nat := 406852802225498688068587

theorem tailTrace_792343 : CollatzResearch.WordTrace tailWord_792343 prefixEnd_792343 406852802225498688068587 := by
  unfold tailWord_792343
  simp only [CollatzResearch.WordTrace]
  refine ⟨28899123368484107256021683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19266082245656071504014455 28899123368484107256021683)
  ·
    refine ⟨43348685052726160884032525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28899123368484107256021683 43348685052726160884032525)
    ·
      refine ⟨16255756894772310331512197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43348685052726160884032525 16255756894772310331512197)
      ·
        refine ⟨3047954417769808187158537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16255756894772310331512197 3047954417769808187158537)
        ·
          refine ⟨2285965813327356140368903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3047954417769808187158537 2285965813327356140368903)
          ·
            refine ⟨3428948719991034210553355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2285965813327356140368903 3428948719991034210553355)
            ·
              refine ⟨5143423079986551315830033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3428948719991034210553355 5143423079986551315830033)
              ·
                refine ⟨3857567309989913486872525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5143423079986551315830033 3857567309989913486872525)
                ·
                  refine ⟨1446587741246217557577197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3857567309989913486872525 1446587741246217557577197)
                  ·
                    refine ⟨542470402967331584091449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1446587741246217557577197 542470402967331584091449)
                    ·
                      refine ⟨406852802225498688068587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 542470402967331584091449 406852802225498688068587)
                      ·
                        rfl

theorem cell23_792343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_792343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792343 prefixEnd_792343 := by exact prefixLift 792343
  have htrace : WordTrace (prefixWord ++ tailWord_792343) baseStart_792343 baseEnd_792343 := by
    simpa [prefixWord, tailWord_792343, baseEnd_792343] using wordTrace_append hprefix tailTrace_792343
  have hstable : (prefixWord ++ tailWord_792343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792343).length < 2 ^ (prefixWord ++ tailWord_792343).sum := by decide
  have hdescent : baseEnd_792343 < baseStart_792343 := by decide
  rcases family_descends (prefixWord ++ tailWord_792343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792377 : List Nat := [1, 2, 1, 7, 1, 1, 1, 3, 1, 3, 2]
def baseStart_792377 : Nat := 118140960795 + 792377 * 2 ^ 59
def prefixEnd_792377 : Nat := 4983230072969 + 3 ^ 40 * 792377 * 2
def baseEnd_792377 : Nat := 406870260567751555043431

theorem tailTrace_792377 : CollatzResearch.WordTrace tailWord_792377 prefixEnd_792377 406870260567751555043431 := by
  unfold tailWord_792377
  simp only [CollatzResearch.WordTrace]
  refine ⟨28900363450360931062759385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19266908966907287375172923 28900363450360931062759385)
  ·
    refine ⟨21675272587770698297069539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28900363450360931062759385 21675272587770698297069539)
    ·
      refine ⟨32512908881656047445604309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21675272587770698297069539 32512908881656047445604309)
      ·
        refine ⟨762021301913813612006351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 32512908881656047445604309 762021301913813612006351)
        ·
          refine ⟨1143031952870720418009527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 762021301913813612006351 1143031952870720418009527)
          ·
            refine ⟨1714547929306080627014291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1143031952870720418009527 1714547929306080627014291)
            ·
              refine ⟨2571821893959120940521437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1714547929306080627014291 2571821893959120940521437)
              ·
                refine ⟨964433210234670352695539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2571821893959120940521437 964433210234670352695539)
                ·
                  refine ⟨1446649815352005529043309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 964433210234670352695539 1446649815352005529043309)
                  ·
                    refine ⟨542493680757002073391241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1446649815352005529043309 542493680757002073391241)
                    ·
                      refine ⟨406870260567751555043431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 542493680757002073391241 406870260567751555043431)
                      ·
                        rfl

theorem cell23_792377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_792377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792377 prefixEnd_792377 := by exact prefixLift 792377
  have htrace : WordTrace (prefixWord ++ tailWord_792377) baseStart_792377 baseEnd_792377 := by
    simpa [prefixWord, tailWord_792377, baseEnd_792377] using wordTrace_append hprefix tailTrace_792377
  have hstable : (prefixWord ++ tailWord_792377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792377).length < 2 ^ (prefixWord ++ tailWord_792377).sum := by decide
  have hdescent : baseEnd_792377 < baseStart_792377 := by decide
  rcases family_descends (prefixWord ++ tailWord_792377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792407 : List Nat := [1, 1, 3, 2, 6, 1, 1, 1, 1, 4, 2]
def baseStart_792407 : Nat := 118140960795 + 792407 * 2 ^ 59
def prefixEnd_792407 : Nat := 4983230072969 + 3 ^ 40 * 792407 * 2
def baseEnd_792407 : Nat := 406885664987386437668293

theorem tailTrace_792407 : CollatzResearch.WordTrace tailWord_792407 prefixEnd_792407 406885664987386437668293 := by
  unfold tailWord_792407
  simp only [CollatzResearch.WordTrace]
  refine ⟨28901457640252246186351475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19267638426834830790900983 28901457640252246186351475)
  ·
    refine ⟨43352186460378369279527213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28901457640252246186351475 43352186460378369279527213)
    ·
      refine ⟨16257069922641888479822705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43352186460378369279527213 16257069922641888479822705)
      ·
        refine ⟨12192802441981416359867029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16257069922641888479822705 12192802441981416359867029)
        ·
          refine ⟨571537614467878891868767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12192802441981416359867029 571537614467878891868767)
          ·
            refine ⟨857306421701818337803151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571537614467878891868767 857306421701818337803151)
            ·
              refine ⟨1285959632552727506704727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 857306421701818337803151 1285959632552727506704727)
              ·
                refine ⟨1928939448829091260057091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1285959632552727506704727 1928939448829091260057091)
                ·
                  refine ⟨2893409173243636890085637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1928939448829091260057091 2893409173243636890085637)
                  ·
                    refine ⟨542514219983181916891057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2893409173243636890085637 542514219983181916891057)
                    ·
                      refine ⟨406885664987386437668293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 542514219983181916891057 406885664987386437668293)
                      ·
                        rfl

theorem cell23_792407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 1, 4, 2].length) (baseStart_792407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792407 prefixEnd_792407 := by exact prefixLift 792407
  have htrace : WordTrace (prefixWord ++ tailWord_792407) baseStart_792407 baseEnd_792407 := by
    simpa [prefixWord, tailWord_792407, baseEnd_792407] using wordTrace_append hprefix tailTrace_792407
  have hstable : (prefixWord ++ tailWord_792407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792407).length < 2 ^ (prefixWord ++ tailWord_792407).sum := by decide
  have hdescent : baseEnd_792407 < baseStart_792407 := by decide
  rcases family_descends (prefixWord ++ tailWord_792407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792409 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 3, 7]
def baseStart_792409 : Nat := 118140960795 + 792409 * 2 ^ 59
def prefixEnd_792409 : Nat := 4983230072969 + 3 ^ 40 * 792409 * 2
def baseEnd_792409 : Nat := 135628897316231809947761

theorem tailTrace_792409 : CollatzResearch.WordTrace tailWord_792409 prefixEnd_792409 135628897316231809947761 := by
  unfold tailWord_792409
  simp only [CollatzResearch.WordTrace]
  refine ⟨28901530586245000527924281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19267687057496667018616187 28901530586245000527924281)
  ·
    refine ⟨21676147939683750395943211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28901530586245000527924281 21676147939683750395943211)
    ·
      refine ⟨32514221909525625593914817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21676147939683750395943211 32514221909525625593914817)
      ·
        refine ⟨24385666432144219195436113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32514221909525625593914817 24385666432144219195436113)
        ·
          refine ⟨18289249824108164396577085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24385666432144219195436113 18289249824108164396577085)
          ·
            refine ⟨6858468684040561648716407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18289249824108164396577085 6858468684040561648716407)
            ·
              refine ⟨10287703026060842473074611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6858468684040561648716407 10287703026060842473074611)
              ·
                refine ⟨15431554539091263709611917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10287703026060842473074611 15431554539091263709611917)
                ·
                  refine ⟨5786832952159223891104469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15431554539091263709611917 5786832952159223891104469)
                  ·
                    refine ⟨135628897316231809947761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5786832952159223891104469 135628897316231809947761)
                    ·
                      rfl

theorem cell23_792409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 7].length) (baseStart_792409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792409 prefixEnd_792409 := by exact prefixLift 792409
  have htrace : WordTrace (prefixWord ++ tailWord_792409) baseStart_792409 baseEnd_792409 := by
    simpa [prefixWord, tailWord_792409, baseEnd_792409] using wordTrace_append hprefix tailTrace_792409
  have hstable : (prefixWord ++ tailWord_792409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792409).length < 2 ^ (prefixWord ++ tailWord_792409).sum := by decide
  have hdescent : baseEnd_792409 < baseStart_792409 := by decide
  rcases family_descends (prefixWord ++ tailWord_792409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792430 : List Nat := [4, 1, 2, 3, 1, 1, 3, 3, 5]
def baseStart_792430 : Nat := 118140960795 + 792430 * 2 ^ 59
def prefixEnd_792430 : Nat := 4983230072969 + 3 ^ 40 * 792430 * 2
def baseEnd_792430 : Nat := 45210830560271094186743

theorem tailTrace_792430 : CollatzResearch.WordTrace tailWord_792430 prefixEnd_792430 45210830560271094186743 := by
  unfold tailWord_792430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3612787064896115139304843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19268197679445947409625829 3612787064896115139304843)
  ·
    refine ⟨5419180597344172708957265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3612787064896115139304843 5419180597344172708957265)
    ·
      refine ⟨4064385448008129531717949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5419180597344172708957265 4064385448008129531717949)
      ·
        refine ⟨1524144543003048574394231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4064385448008129531717949 1524144543003048574394231)
        ·
          refine ⟨2286216814504572861591347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1524144543003048574394231 2286216814504572861591347)
          ·
            refine ⟨3429325221756859292387021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2286216814504572861591347 3429325221756859292387021)
            ·
              refine ⟨1285996958158822234645133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3429325221756859292387021 1285996958158822234645133)
              ·
                refine ⟨482248859309558337991925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1285996958158822234645133 482248859309558337991925)
                ·
                  refine ⟨45210830560271094186743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 482248859309558337991925 45210830560271094186743)
                  ·
                    rfl

theorem cell23_792430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3, 5].length) (baseStart_792430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792430 prefixEnd_792430 := by exact prefixLift 792430
  have htrace : WordTrace (prefixWord ++ tailWord_792430) baseStart_792430 baseEnd_792430 := by
    simpa [prefixWord, tailWord_792430, baseEnd_792430] using wordTrace_append hprefix tailTrace_792430
  have hstable : (prefixWord ++ tailWord_792430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792430).length < 2 ^ (prefixWord ++ tailWord_792430).sum := by decide
  have hdescent : baseEnd_792430 < baseStart_792430 := by decide
  rcases family_descends (prefixWord ++ tailWord_792430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792523 : List Nat := [1, 1, 1, 1, 3, 4, 2, 2, 1, 5, 2]
def baseStart_792523 : Nat := 118140960795 + 792523 * 2 ^ 59
def prefixEnd_792523 : Nat := 4983230072969 + 3 ^ 40 * 792523 * 2
def baseEnd_792523 : Nat := 406945228743307983817759

theorem tailTrace_792523 : CollatzResearch.WordTrace tailWord_792523 prefixEnd_792523 406945228743307983817759 := by
  unfold tailWord_792523
  simp only [CollatzResearch.WordTrace]
  refine ⟨28905688507831997997574223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19270459005221331998382815 28905688507831997997574223)
  ·
    refine ⟨43358532761747996996361335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28905688507831997997574223 43358532761747996996361335)
    ·
      refine ⟨65037799142621995494542003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43358532761747996996361335 65037799142621995494542003)
      ·
        refine ⟨97556698713932993241813005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65037799142621995494542003 97556698713932993241813005)
        ·
          refine ⟨36583762017724872465679877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97556698713932993241813005 36583762017724872465679877)
          ·
            refine ⟨6859455378323413587314977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36583762017724872465679877 6859455378323413587314977)
            ·
              refine ⟨5144591533742560190486233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6859455378323413587314977 5144591533742560190486233)
              ·
                refine ⟨3858443650306920142864675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5144591533742560190486233 3858443650306920142864675)
                ·
                  refine ⟨5787665475460380214297013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3858443650306920142864675 5787665475460380214297013)
                  ·
                    refine ⟨542593638324410645090345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5787665475460380214297013 542593638324410645090345)
                    ·
                      refine ⟨406945228743307983817759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 542593638324410645090345 406945228743307983817759)
                      ·
                        rfl

theorem cell23_792523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 5, 2].length) (baseStart_792523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792523 prefixEnd_792523 := by exact prefixLift 792523
  have htrace : WordTrace (prefixWord ++ tailWord_792523) baseStart_792523 baseEnd_792523 := by
    simpa [prefixWord, tailWord_792523, baseEnd_792523] using wordTrace_append hprefix tailTrace_792523
  have hstable : (prefixWord ++ tailWord_792523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792523).length < 2 ^ (prefixWord ++ tailWord_792523).sum := by decide
  have hdescent : baseEnd_792523 < baseStart_792523 := by decide
  rcases family_descends (prefixWord ++ tailWord_792523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792526 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7]
def baseStart_792526 : Nat := 118140960795 + 792526 * 2 ^ 59
def prefixEnd_792526 : Nat := 4983230072969 + 3 ^ 40 * 792526 * 2
def baseEnd_792526 : Nat := 406946769185271472080245

theorem tailTrace_792526 : CollatzResearch.WordTrace tailWord_792526 prefixEnd_792526 406946769185271472080245 := by
  unfold tailWord_792526
  simp only [CollatzResearch.WordTrace]
  refine ⟨3613224740852641188741679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19270531951214086339955621 3613224740852641188741679)
  ·
    refine ⟨5419837111278961783112519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3613224740852641188741679 5419837111278961783112519)
    ·
      refine ⟨8129755666918442674668779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5419837111278961783112519 8129755666918442674668779)
      ·
        refine ⟨12194633500377664012003169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8129755666918442674668779 12194633500377664012003169)
        ·
          refine ⟨9145975125283248009002377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12194633500377664012003169 9145975125283248009002377)
          ·
            refine ⟨6859481343962436006751783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9145975125283248009002377 6859481343962436006751783)
            ·
              refine ⟨10289222015943654010127675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6859481343962436006751783 10289222015943654010127675)
              ·
                refine ⟨15433833023915481015191513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10289222015943654010127675 15433833023915481015191513)
                ·
                  refine ⟨11575374767936610761393635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15433833023915481015191513 11575374767936610761393635)
                  ·
                    refine ⟨17363062151904916142090453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11575374767936610761393635 17363062151904916142090453)
                    ·
                      refine ⟨406946769185271472080245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 17363062151904916142090453 406946769185271472080245)
                      ·
                        rfl

theorem cell23_792526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_792526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792526 prefixEnd_792526 := by exact prefixLift 792526
  have htrace : WordTrace (prefixWord ++ tailWord_792526) baseStart_792526 baseEnd_792526 := by
    simpa [prefixWord, tailWord_792526, baseEnd_792526] using wordTrace_append hprefix tailTrace_792526
  have hstable : (prefixWord ++ tailWord_792526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792526).length < 2 ^ (prefixWord ++ tailWord_792526).sum := by decide
  have hdescent : baseEnd_792526 < baseStart_792526 := by decide
  rcases family_descends (prefixWord ++ tailWord_792526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792533 : List Nat := [1, 3, 2, 3, 2, 1, 2, 1, 3, 5]
def baseStart_792533 : Nat := 118140960795 + 792533 * 2 ^ 59
def prefixEnd_792533 : Nat := 4983230072969 + 3 ^ 40 * 792533 * 2
def baseEnd_792533 : Nat := 135650121183284314897571

theorem tailTrace_792533 : CollatzResearch.WordTrace tailWord_792533 prefixEnd_792533 135650121183284314897571 := by
  unfold tailWord_792533
  simp only [CollatzResearch.WordTrace]
  refine ⟨28906053237795769705438253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19270702158530513136958835 28906053237795769705438253)
  ·
    refine ⟨10839769964173413639539345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28906053237795769705438253 10839769964173413639539345)
    ·
      refine ⟨8129827473130060229654509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10839769964173413639539345 8129827473130060229654509)
      ·
        refine ⟨3048685302423772586120441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8129827473130060229654509 3048685302423772586120441)
        ·
          refine ⟨2286513976817829439590331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3048685302423772586120441 2286513976817829439590331)
          ·
            refine ⟨3429770965226744159385497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2286513976817829439590331 3429770965226744159385497)
            ·
              refine ⟨2572328223920058119539123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3429770965226744159385497 2572328223920058119539123)
              ·
                refine ⟨3858492335880087179308685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2572328223920058119539123 3858492335880087179308685)
                ·
                  refine ⟨1446934625955032692240757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3858492335880087179308685 1446934625955032692240757)
                  ·
                    refine ⟨135650121183284314897571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1446934625955032692240757 135650121183284314897571)
                    ·
                      rfl

theorem cell23_792533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_792533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792533 prefixEnd_792533 := by exact prefixLift 792533
  have htrace : WordTrace (prefixWord ++ tailWord_792533) baseStart_792533 baseEnd_792533 := by
    simpa [prefixWord, tailWord_792533, baseEnd_792533] using wordTrace_append hprefix tailTrace_792533
  have hstable : (prefixWord ++ tailWord_792533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792533).length < 2 ^ (prefixWord ++ tailWord_792533).sum := by decide
  have hdescent : baseEnd_792533 < baseStart_792533 := by decide
  rcases family_descends (prefixWord ++ tailWord_792533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792534 : List Nat := [5, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_792534 : Nat := 118140960795 + 792534 * 2 ^ 59
def prefixEnd_792534 : Nat := 4983230072969 + 3 ^ 40 * 792534 * 2
def baseEnd_792534 : Nat := 406950877030507440780209

theorem tailTrace_792534 : CollatzResearch.WordTrace tailWord_792534 prefixEnd_792534 406950877030507440780209 := by
  unfold tailWord_792534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1806630606924509179764041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19270726473861431250816437 1806630606924509179764041)
  ·
    refine ⟨1354972955193381884823031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1806630606924509179764041 1354972955193381884823031)
    ·
      refine ⟨2032459432790072827234547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1354972955193381884823031 2032459432790072827234547)
      ·
        refine ⟨3048689149185109240851821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2032459432790072827234547 3048689149185109240851821)
        ·
          refine ⟨1143258430944415965319433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3048689149185109240851821 1143258430944415965319433)
          ·
            refine ⟨857443823208311973989575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1143258430944415965319433 857443823208311973989575)
            ·
              refine ⟨1286165734812467960984363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 857443823208311973989575 1286165734812467960984363)
              ·
                refine ⟨1929248602218701941476545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1286165734812467960984363 1929248602218701941476545)
                ·
                  refine ⟨1446936451664026456107409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1929248602218701941476545 1446936451664026456107409)
                  ·
                    refine ⟨1085202338748019842080557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1446936451664026456107409 1085202338748019842080557)
                    ·
                      refine ⟨406950877030507440780209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1085202338748019842080557 406950877030507440780209)
                      ·
                        rfl

theorem cell23_792534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_792534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792534 prefixEnd_792534 := by exact prefixLift 792534
  have htrace : WordTrace (prefixWord ++ tailWord_792534) baseStart_792534 baseEnd_792534 := by
    simpa [prefixWord, tailWord_792534, baseEnd_792534] using wordTrace_append hprefix tailTrace_792534
  have hstable : (prefixWord ++ tailWord_792534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792534).length < 2 ^ (prefixWord ++ tailWord_792534).sum := by decide
  have hdescent : baseEnd_792534 < baseStart_792534 := by decide
  rcases family_descends (prefixWord ++ tailWord_792534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792547 : List Nat := [1, 1, 1, 6, 1, 2, 1, 5, 1, 1, 3]
def baseStart_792547 : Nat := 118140960795 + 792547 * 2 ^ 59
def prefixEnd_792547 : Nat := 4983230072969 + 3 ^ 40 * 792547 * 2
def baseEnd_792547 : Nat := 406957552279015889917649

theorem tailTrace_792547 : CollatzResearch.WordTrace tailWord_792547 prefixEnd_792547 406957552279015889917649 := by
  unfold tailWord_792547
  simp only [CollatzResearch.WordTrace]
  refine ⟨28906563859745050096447895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19271042573163366730965263 28906563859745050096447895)
  ·
    refine ⟨43359845789617575144671843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28906563859745050096447895 43359845789617575144671843)
    ·
      refine ⟨65039768684426362717007765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43359845789617575144671843 65039768684426362717007765)
      ·
        refine ⟨3048739157082485752359739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 65039768684426362717007765 3048739157082485752359739)
        ·
          refine ⟨4573108735623728628539609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3048739157082485752359739 4573108735623728628539609)
          ·
            refine ⟨3429831551717796471404707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4573108735623728628539609 3429831551717796471404707)
            ·
              refine ⟨5144747327576694707107061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3429831551717796471404707 5144747327576694707107061)
              ·
                refine ⟨482320061960315128791287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5144747327576694707107061 482320061960315128791287)
                ·
                  refine ⟨723480092940472693186931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 482320061960315128791287 723480092940472693186931)
                  ·
                    refine ⟨1085220139410709039780397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 723480092940472693186931 1085220139410709039780397)
                    ·
                      refine ⟨406957552279015889917649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1085220139410709039780397 406957552279015889917649)
                      ·
                        rfl

theorem cell23_792547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_792547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792547 prefixEnd_792547 := by exact prefixLift 792547
  have htrace : WordTrace (prefixWord ++ tailWord_792547) baseStart_792547 baseEnd_792547 := by
    simpa [prefixWord, tailWord_792547, baseEnd_792547] using wordTrace_append hprefix tailTrace_792547
  have hstable : (prefixWord ++ tailWord_792547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792547).length < 2 ^ (prefixWord ++ tailWord_792547).sum := by decide
  have hdescent : baseEnd_792547 < baseStart_792547 := by decide
  rcases family_descends (prefixWord ++ tailWord_792547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792556 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 5]
def baseStart_792556 : Nat := 118140960795 + 792556 * 2 ^ 59
def prefixEnd_792556 : Nat := 4983230072969 + 3 ^ 40 * 792556 * 2
def baseEnd_792556 : Nat := 406962173604906354705107

theorem tailTrace_792556 : CollatzResearch.WordTrace tailWord_792556 prefixEnd_792556 406962173604906354705107 := by
  unfold tailWord_792556
  simp only [CollatzResearch.WordTrace]
  refine ⟨14453446058356222316762761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19271261411141629755683681 14453446058356222316762761)
  ·
    refine ⟨10840084543767166737572071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14453446058356222316762761 10840084543767166737572071)
    ·
      refine ⟨16260126815650750106358107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10840084543767166737572071 16260126815650750106358107)
      ·
        refine ⟨24390190223476125159537161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16260126815650750106358107 24390190223476125159537161)
        ·
          refine ⟨18292642667607093869652871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24390190223476125159537161 18292642667607093869652871)
          ·
            refine ⟨27438964001410640804479307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18292642667607093869652871 27438964001410640804479307)
            ·
              refine ⟨41158446002115961206718961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27438964001410640804479307 41158446002115961206718961)
              ·
                refine ⟨30868834501586970905039221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41158446002115961206718961 30868834501586970905039221)
                ·
                  refine ⟨2893953234523778522347427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30868834501586970905039221 2893953234523778522347427)
                  ·
                    refine ⟨4340929851785667783521141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2893953234523778522347427 4340929851785667783521141)
                    ·
                      refine ⟨406962173604906354705107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4340929851785667783521141 406962173604906354705107)
                      ·
                        rfl

theorem cell23_792556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_792556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792556 prefixEnd_792556 := by exact prefixLift 792556
  have htrace : WordTrace (prefixWord ++ tailWord_792556) baseStart_792556 baseEnd_792556 := by
    simpa [prefixWord, tailWord_792556, baseEnd_792556] using wordTrace_append hprefix tailTrace_792556
  have hstable : (prefixWord ++ tailWord_792556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792556).length < 2 ^ (prefixWord ++ tailWord_792556).sum := by decide
  have hdescent : baseEnd_792556 < baseStart_792556 := by decide
  rcases family_descends (prefixWord ++ tailWord_792556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792573 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 5, 2, 3]
def baseStart_792573 : Nat := 118140960795 + 792573 * 2 ^ 59
def prefixEnd_792573 : Nat := 4983230072969 + 3 ^ 40 * 792573 * 2
def baseEnd_792573 : Nat := 406970902776032788192529

theorem tailTrace_792573 : CollatzResearch.WordTrace tailWord_792573 prefixEnd_792573 406970902776032788192529 := by
  unfold tailWord_792573
  simp only [CollatzResearch.WordTrace]
  refine ⟨28907512157650856536894373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19271674771767237691262915 28907512157650856536894373)
  ·
    refine ⟨5420158529559535600667695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28907512157650856536894373 5420158529559535600667695)
    ·
      refine ⟨8130237794339303401001543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5420158529559535600667695 8130237794339303401001543)
      ·
        refine ⟨12195356691508955101502315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8130237794339303401001543 12195356691508955101502315)
        ·
          refine ⟨18293035037263432652253473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12195356691508955101502315 18293035037263432652253473)
          ·
            refine ⟨13719776277947574489190105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18293035037263432652253473 13719776277947574489190105)
            ·
              refine ⟨10289832208460680866892579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13719776277947574489190105 10289832208460680866892579)
              ·
                refine ⟨15434748312691021300338869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10289832208460680866892579 15434748312691021300338869)
                ·
                  refine ⟨1447007654314783246906769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15434748312691021300338869 1447007654314783246906769)
                  ·
                    refine ⟨1085255740736087435180077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1447007654314783246906769 1085255740736087435180077)
                    ·
                      refine ⟨406970902776032788192529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1085255740736087435180077 406970902776032788192529)
                      ·
                        rfl

theorem cell23_792573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_792573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792573 prefixEnd_792573 := by exact prefixLift 792573
  have htrace : WordTrace (prefixWord ++ tailWord_792573) baseStart_792573 baseEnd_792573 := by
    simpa [prefixWord, tailWord_792573, baseEnd_792573] using wordTrace_append hprefix tailTrace_792573
  have hstable : (prefixWord ++ tailWord_792573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792573).length < 2 ^ (prefixWord ++ tailWord_792573).sum := by decide
  have hdescent : baseEnd_792573 < baseStart_792573 := by decide
  rcases family_descends (prefixWord ++ tailWord_792573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792583 : List Nat := [1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 6]
def baseStart_792583 : Nat := 118140960795 + 792583 * 2 ^ 59
def prefixEnd_792583 : Nat := 4983230072969 + 3 ^ 40 * 792583 * 2
def baseEnd_792583 : Nat := 406976037582577749067483

theorem tailTrace_792583 : CollatzResearch.WordTrace tailWord_792583 prefixEnd_792583 406976037582577749067483 := by
  unfold tailWord_792583
  simp only [CollatzResearch.WordTrace]
  refine ⟨28907876887614628244758403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19271917925076418829838935 28907876887614628244758403)
  ·
    refine ⟨43361815331421942367137605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28907876887614628244758403 43361815331421942367137605)
    ·
      refine ⟨8130340374641614193838301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43361815331421942367137605 8130340374641614193838301)
      ·
        refine ⟨3048877640490605322689363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8130340374641614193838301 3048877640490605322689363)
        ·
          refine ⟨4573316460735907984034045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3048877640490605322689363 4573316460735907984034045)
          ·
            refine ⟨1714993672775965494012767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4573316460735907984034045 1714993672775965494012767)
            ·
              refine ⟨2572490509163948241019151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1714993672775965494012767 2572490509163948241019151)
              ·
                refine ⟨3858735763745922361528727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2572490509163948241019151 3858735763745922361528727)
                ·
                  refine ⟨5788103645618883542293091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3858735763745922361528727 5788103645618883542293091)
                  ·
                    refine ⟨8682155468428325313439637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5788103645618883542293091 8682155468428325313439637)
                    ·
                      refine ⟨406976037582577749067483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8682155468428325313439637 406976037582577749067483)
                      ·
                        rfl

theorem cell23_792583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_792583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792583 prefixEnd_792583 := by exact prefixLift 792583
  have htrace : WordTrace (prefixWord ++ tailWord_792583) baseStart_792583 baseEnd_792583 := by
    simpa [prefixWord, tailWord_792583, baseEnd_792583] using wordTrace_append hprefix tailTrace_792583
  have hstable : (prefixWord ++ tailWord_792583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792583).length < 2 ^ (prefixWord ++ tailWord_792583).sum := by decide
  have hdescent : baseEnd_792583 < baseStart_792583 := by decide
  rcases family_descends (prefixWord ++ tailWord_792583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792637 : List Nat := [1, 4, 1, 3, 1, 1, 3, 3, 2, 1, 3]
def baseStart_792637 : Nat := 118140960795 + 792637 * 2 ^ 59
def prefixEnd_792637 : Nat := 4983230072969 + 3 ^ 40 * 792637 * 2
def baseEnd_792637 : Nat := 407003765537920537792235

theorem tailTrace_792637 : CollatzResearch.WordTrace tailWord_792637 prefixEnd_792637 407003765537920537792235 := by
  unfold tailWord_792637
  simp only [CollatzResearch.WordTrace]
  refine ⟨28909846429418995467224165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19273230952945996978149443 28909846429418995467224165)
  ·
    refine ⟨5420596205516061650104531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28909846429418995467224165 5420596205516061650104531)
    ·
      refine ⟨8130894308274092475156797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5420596205516061650104531 8130894308274092475156797)
      ·
        refine ⟨3049085365602784678183799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8130894308274092475156797 3049085365602784678183799)
        ·
          refine ⟨4573628048404177017275699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3049085365602784678183799 4573628048404177017275699)
          ·
            refine ⟨6860442072606265525913549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4573628048404177017275699 6860442072606265525913549)
            ·
              refine ⟨2572665777227349572217581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6860442072606265525913549 2572665777227349572217581)
              ·
                refine ⟨964749666460256089581593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2572665777227349572217581 964749666460256089581593)
                ·
                  refine ⟨723562249845192067186195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 964749666460256089581593 723562249845192067186195)
                  ·
                    refine ⟨1085343374767788100779293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 723562249845192067186195 1085343374767788100779293)
                    ·
                      refine ⟨407003765537920537792235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1085343374767788100779293 407003765537920537792235)
                      ·
                        rfl

theorem cell23_792637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_792637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792637 prefixEnd_792637 := by exact prefixLift 792637
  have htrace : WordTrace (prefixWord ++ tailWord_792637) baseStart_792637 baseEnd_792637 := by
    simpa [prefixWord, tailWord_792637, baseEnd_792637] using wordTrace_append hprefix tailTrace_792637
  have hstable : (prefixWord ++ tailWord_792637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792637).length < 2 ^ (prefixWord ++ tailWord_792637).sum := by decide
  have hdescent : baseEnd_792637 < baseStart_792637 := by decide
  rcases family_descends (prefixWord ++ tailWord_792637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792663 : List Nat := [1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 5]
def baseStart_792663 : Nat := 118140960795 + 792663 * 2 ^ 59
def prefixEnd_792663 : Nat := 4983230072969 + 3 ^ 40 * 792663 * 2
def baseEnd_792663 : Nat := 407017116034937436067115

theorem tailTrace_792663 : CollatzResearch.WordTrace tailWord_792663 prefixEnd_792663 407017116034937436067115 := by
  unfold tailWord_792663
  simp only [CollatzResearch.WordTrace]
  refine ⟨28910794727324801907670643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19273863151549867938447095 28910794727324801907670643)
  ·
    refine ⟨43366192090987202861505965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28910794727324801907670643 43366192090987202861505965)
    ·
      refine ⟨16262322034120201073064737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43366192090987202861505965 16262322034120201073064737)
      ·
        refine ⟨12196741525590150804798553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16262322034120201073064737 12196741525590150804798553)
        ·
          refine ⟨9147556144192613103598915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12196741525590150804798553 9147556144192613103598915)
          ·
            refine ⟨13721334216288919655398373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9147556144192613103598915 13721334216288919655398373)
            ·
              refine ⟨2572750165554172435387195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13721334216288919655398373 2572750165554172435387195)
              ·
                refine ⟨3859125248331258653080793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2572750165554172435387195 3859125248331258653080793)
                ·
                  refine ⟨2894343936248443989810595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3859125248331258653080793 2894343936248443989810595)
                  ·
                    refine ⟨4341515904372665984715893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2894343936248443989810595 4341515904372665984715893)
                    ·
                      refine ⟨407017116034937436067115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4341515904372665984715893 407017116034937436067115)
                      ·
                        rfl

theorem cell23_792663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_792663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792663 prefixEnd_792663 := by exact prefixLift 792663
  have htrace : WordTrace (prefixWord ++ tailWord_792663) baseStart_792663 baseEnd_792663 := by
    simpa [prefixWord, tailWord_792663, baseEnd_792663] using wordTrace_append hprefix tailTrace_792663
  have hstable : (prefixWord ++ tailWord_792663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792663).length < 2 ^ (prefixWord ++ tailWord_792663).sum := by decide
  have hdescent : baseEnd_792663 < baseStart_792663 := by decide
  rcases family_descends (prefixWord ++ tailWord_792663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792664 : List Nat := [2, 1, 2, 2, 1, 5, 3, 1, 1, 3, 2]
def baseStart_792664 : Nat := 118140960795 + 792664 * 2 ^ 59
def prefixEnd_792664 : Nat := 4983230072969 + 3 ^ 40 * 792664 * 2
def baseEnd_792664 : Nat := 407017629515591932154611

theorem tailTrace_792664 : CollatzResearch.WordTrace tailWord_792664 prefixEnd_792664 407017629515591932154611 := by
  unfold tailWord_792664
  simp only [CollatzResearch.WordTrace]
  refine ⟨14455415600160589539228523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19273887466880786052304697 14455415600160589539228523)
  ·
    refine ⟨21683123400240884308842785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14455415600160589539228523 21683123400240884308842785)
    ·
      refine ⟨16262342550180663231632089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21683123400240884308842785 16262342550180663231632089)
      ·
        refine ⟨12196756912635497423724067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16262342550180663231632089 12196756912635497423724067)
        ·
          refine ⟨18295135368953246135586101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12196756912635497423724067 18295135368953246135586101)
          ·
            refine ⟨1715168940839366825211197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18295135368953246135586101 1715168940839366825211197)
            ·
              refine ⟨643188352814762559454199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1715168940839366825211197 643188352814762559454199)
              ·
                refine ⟨964782529222143839181299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 643188352814762559454199 964782529222143839181299)
                ·
                  refine ⟨1447173793833215758771949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 964782529222143839181299 1447173793833215758771949)
                  ·
                    refine ⟨542690172687455909539481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1447173793833215758771949 542690172687455909539481)
                    ·
                      refine ⟨407017629515591932154611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 542690172687455909539481 407017629515591932154611)
                      ·
                        rfl

theorem cell23_792664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 1, 3, 2].length) (baseStart_792664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792664 prefixEnd_792664 := by exact prefixLift 792664
  have htrace : WordTrace (prefixWord ++ tailWord_792664) baseStart_792664 baseEnd_792664 := by
    simpa [prefixWord, tailWord_792664, baseEnd_792664] using wordTrace_append hprefix tailTrace_792664
  have hstable : (prefixWord ++ tailWord_792664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792664).length < 2 ^ (prefixWord ++ tailWord_792664).sum := by decide
  have hdescent : baseEnd_792664 < baseStart_792664 := by decide
  rcases family_descends (prefixWord ++ tailWord_792664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792673 : List Nat := [1, 2, 3, 1, 1, 2, 1, 4, 2, 2, 4]
def baseStart_792673 : Nat := 118140960795 + 792673 * 2 ^ 59
def prefixEnd_792673 : Nat := 4983230072969 + 3 ^ 40 * 792673 * 2
def baseEnd_792673 : Nat := 407022250841482396942069

theorem tailTrace_792673 : CollatzResearch.WordTrace tailWord_792673 prefixEnd_792673 407022250841482396942069 := by
  unfold tailWord_792673
  simp only [CollatzResearch.WordTrace]
  refine ⟨28911159457288573615534673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19274106304859049077023115 28911159457288573615534673)
  ·
    refine ⟨21683369592966430211651005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28911159457288573615534673 21683369592966430211651005)
    ·
      refine ⟨8131263597362411329369127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21683369592966430211651005 8131263597362411329369127)
      ·
        refine ⟨12196895396043616994053691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8131263597362411329369127 12196895396043616994053691)
        ·
          refine ⟨18295343094065425491080537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12196895396043616994053691 18295343094065425491080537)
          ·
            refine ⟨13721507320549069118310403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18295343094065425491080537 13721507320549069118310403)
            ·
              refine ⟨20582260980823603677465605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13721507320549069118310403 20582260980823603677465605)
              ·
                refine ⟨3859173933904425689524801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20582260980823603677465605 3859173933904425689524801)
                ·
                  refine ⟨2894380450428319267143601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3859173933904425689524801 2894380450428319267143601)
                  ·
                    refine ⟨2170785337821239450357701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2894380450428319267143601 2170785337821239450357701)
                    ·
                      refine ⟨407022250841482396942069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2170785337821239450357701 407022250841482396942069)
                      ·
                        rfl

theorem cell23_792673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_792673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792673 prefixEnd_792673 := by exact prefixLift 792673
  have htrace : WordTrace (prefixWord ++ tailWord_792673) baseStart_792673 baseEnd_792673 := by
    simpa [prefixWord, tailWord_792673, baseEnd_792673] using wordTrace_append hprefix tailTrace_792673
  have hstable : (prefixWord ++ tailWord_792673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792673).length < 2 ^ (prefixWord ++ tailWord_792673).sum := by decide
  have hdescent : baseEnd_792673 < baseStart_792673 := by decide
  rcases family_descends (prefixWord ++ tailWord_792673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792690 : List Nat := [3, 2, 1, 2, 2, 3, 1, 1, 2, 2, 4]
def baseStart_792690 : Nat := 118140960795 + 792690 * 2 ^ 59
def prefixEnd_792690 : Nat := 4983230072969 + 3 ^ 40 * 792690 * 2
def baseEnd_792690 : Nat := 407030980012608830429491

theorem tailTrace_792690 : CollatzResearch.WordTrace tailWord_792690 prefixEnd_792690 407030980012608830429491 := by
  unfold tailWord_792690
  simp only [CollatzResearch.WordTrace]
  refine ⟨7227944874556746379725881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19274519665484657012602349 7227944874556746379725881)
  ·
    refine ⟨5420958655917559784794411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7227944874556746379725881 5420958655917559784794411)
    ·
      refine ⟨8131437983876339677191617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5420958655917559784794411 8131437983876339677191617)
      ·
        refine ⟨6098578487907254757893713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8131437983876339677191617 6098578487907254757893713)
        ·
          refine ⟨4573933865930441068420285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6098578487907254757893713 4573933865930441068420285)
          ·
            refine ⟨1715225199723915400657607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4573933865930441068420285 1715225199723915400657607)
            ·
              refine ⟨2572837799585873100986411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1715225199723915400657607 2572837799585873100986411)
              ·
                refine ⟨3859256699378809651479617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2572837799585873100986411 3859256699378809651479617)
                ·
                  refine ⟨2894442524534107238609713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3859256699378809651479617 2894442524534107238609713)
                  ·
                    refine ⟨2170831893400580428957285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2894442524534107238609713 2170831893400580428957285)
                    ·
                      refine ⟨407030980012608830429491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2170831893400580428957285 407030980012608830429491)
                      ·
                        rfl

theorem cell23_792690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_792690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792690 prefixEnd_792690 := by exact prefixLift 792690
  have htrace : WordTrace (prefixWord ++ tailWord_792690) baseStart_792690 baseEnd_792690 := by
    simpa [prefixWord, tailWord_792690, baseEnd_792690] using wordTrace_append hprefix tailTrace_792690
  have hstable : (prefixWord ++ tailWord_792690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792690).length < 2 ^ (prefixWord ++ tailWord_792690).sum := by decide
  have hdescent : baseEnd_792690 < baseStart_792690 := by decide
  rcases family_descends (prefixWord ++ tailWord_792690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792694 : List Nat := [5, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2]
def baseStart_792694 : Nat := 118140960795 + 792694 * 2 ^ 59
def prefixEnd_792694 : Nat := 4983230072969 + 3 ^ 40 * 792694 * 2
def baseEnd_792694 : Nat := 407033033935226814779473

theorem tailTrace_792694 : CollatzResearch.WordTrace tailWord_792694 prefixEnd_792694 407033033935226814779473 := by
  unfold tailWord_792694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1806995336888280887628071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19274616926808329468032757 1806995336888280887628071)
  ·
    refine ⟨2710493005332421331442107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1806995336888280887628071 2710493005332421331442107)
    ·
      refine ⟨4065739507998631997163161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2710493005332421331442107 4065739507998631997163161)
      ·
        refine ⟨3049304630998973997872371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4065739507998631997163161 3049304630998973997872371)
        ·
          refine ⟨4573956946498460996808557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3049304630998973997872371 4573956946498460996808557)
          ·
            refine ⟨1715233854936922873803209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4573956946498460996808557 1715233854936922873803209)
            ·
              refine ⟨1286425391202692155352407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1715233854936922873803209 1286425391202692155352407)
              ·
                refine ⟨1929638086804038233028611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1286425391202692155352407 1929638086804038233028611)
                ·
                  refine ⟨2894457130206057349542917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1929638086804038233028611 2894457130206057349542917)
                  ·
                    refine ⟨542710711913635753039297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2894457130206057349542917 542710711913635753039297)
                    ·
                      refine ⟨407033033935226814779473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 542710711913635753039297 407033033935226814779473)
                      ·
                        rfl

theorem cell23_792694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_792694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792694 prefixEnd_792694 := by exact prefixLift 792694
  have htrace : WordTrace (prefixWord ++ tailWord_792694) baseStart_792694 baseEnd_792694 := by
    simpa [prefixWord, tailWord_792694, baseEnd_792694] using wordTrace_append hprefix tailTrace_792694
  have hstable : (prefixWord ++ tailWord_792694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792694).length < 2 ^ (prefixWord ++ tailWord_792694).sum := by decide
  have hdescent : baseEnd_792694 < baseStart_792694 := by decide
  rcases family_descends (prefixWord ++ tailWord_792694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792713 : List Nat := [1, 2, 1, 1, 4, 2, 3, 1, 1, 7]
def baseStart_792713 : Nat := 118140960795 + 792713 * 2 ^ 59
def prefixEnd_792713 : Nat := 4983230072969 + 3 ^ 40 * 792713 * 2
def baseEnd_792713 : Nat := 135680930022554080147295

theorem tailTrace_792713 : CollatzResearch.WordTrace tailWord_792713 prefixEnd_792713 135680930022554080147295 := by
  unfold tailWord_792713
  simp only [CollatzResearch.WordTrace]
  refine ⟨28912618377143660446990793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19275078918095773631327195 28912618377143660446990793)
  ·
    refine ⟨21684463782857745335243095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28912618377143660446990793 21684463782857745335243095)
    ·
      refine ⟨32526695674286618002864643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21684463782857745335243095 32526695674286618002864643)
      ·
        refine ⟨48790043511429927004296965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32526695674286618002864643 48790043511429927004296965)
        ·
          refine ⟨9148133158393111313305681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48790043511429927004296965 9148133158393111313305681)
          ·
            refine ⟨6861099868794833484979261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9148133158393111313305681 6861099868794833484979261)
            ·
              refine ⟨2572912450798062556867223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6861099868794833484979261 2572912450798062556867223)
              ·
                refine ⟨3859368676197093835300835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2572912450798062556867223 3859368676197093835300835)
                ·
                  refine ⟨5789053014295640752951253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3859368676197093835300835 5789053014295640752951253)
                  ·
                    refine ⟨135680930022554080147295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5789053014295640752951253 135680930022554080147295)
                    ·
                      rfl

theorem cell23_792713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 7].length) (baseStart_792713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792713 prefixEnd_792713 := by exact prefixLift 792713
  have htrace : WordTrace (prefixWord ++ tailWord_792713) baseStart_792713 baseEnd_792713 := by
    simpa [prefixWord, tailWord_792713, baseEnd_792713] using wordTrace_append hprefix tailTrace_792713
  have hstable : (prefixWord ++ tailWord_792713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792713).length < 2 ^ (prefixWord ++ tailWord_792713).sum := by decide
  have hdescent : baseEnd_792713 < baseStart_792713 := by decide
  rcases family_descends (prefixWord ++ tailWord_792713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792728 : List Nat := [2, 1, 2, 4, 4, 1, 1, 2, 2, 2, 2]
def baseStart_792728 : Nat := 118140960795 + 792728 * 2 ^ 59
def prefixEnd_792728 : Nat := 4983230072969 + 3 ^ 40 * 792728 * 2
def baseEnd_792728 : Nat := 407050492277479681754317

theorem tailTrace_792728 : CollatzResearch.WordTrace tailWord_792728 prefixEnd_792728 407050492277479681754317 := by
  unfold tailWord_792728
  simp only [CollatzResearch.WordTrace]
  refine ⟨14456582736044659004393419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19275443648059545339191225 14456582736044659004393419)
  ·
    refine ⟨21684874104066988506590129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14456582736044659004393419 21684874104066988506590129)
    ·
      refine ⟨16263655578050241379942597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21684874104066988506590129 16263655578050241379942597)
      ·
        refine ⟨3049435420884420258739237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16263655578050241379942597 3049435420884420258739237)
        ·
          refine ⟨571769141415828798513607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3049435420884420258739237 571769141415828798513607)
          ·
            refine ⟨857653712123743197770411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571769141415828798513607 857653712123743197770411)
            ·
              refine ⟨1286480568185614796655617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 857653712123743197770411 1286480568185614796655617)
              ·
                refine ⟨964860426139211097491713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1286480568185614796655617 964860426139211097491713)
                ·
                  refine ⟨723645319604408323118785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 964860426139211097491713 723645319604408323118785)
                  ·
                    refine ⟨542733989703306242339089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 723645319604408323118785 542733989703306242339089)
                    ·
                      refine ⟨407050492277479681754317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 542733989703306242339089 407050492277479681754317)
                      ·
                        rfl

theorem cell23_792728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_792728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792728 prefixEnd_792728 := by exact prefixLift 792728
  have htrace : WordTrace (prefixWord ++ tailWord_792728) baseStart_792728 baseEnd_792728 := by
    simpa [prefixWord, tailWord_792728, baseEnd_792728] using wordTrace_append hprefix tailTrace_792728
  have hstable : (prefixWord ++ tailWord_792728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792728).length < 2 ^ (prefixWord ++ tailWord_792728).sum := by decide
  have hdescent : baseEnd_792728 < baseStart_792728 := by decide
  rcases family_descends (prefixWord ++ tailWord_792728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792760 : List Nat := [2, 1, 2, 1, 2, 1, 3, 4, 3, 4]
def baseStart_792760 : Nat := 118140960795 + 792760 * 2 ^ 59
def prefixEnd_792760 : Nat := 4983230072969 + 3 ^ 40 * 792760 * 2
def baseEnd_792760 : Nat := 135688974552807852184723

theorem tailTrace_792760 : CollatzResearch.WordTrace tailWord_792760 prefixEnd_792760 135688974552807852184723 := by
  unfold tailWord_792760
  simp only [CollatzResearch.WordTrace]
  refine ⟨14457166303986693736975867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19276221738648924982634489 14457166303986693736975867)
  ·
    refine ⟨21685749455980040605463801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14457166303986693736975867 21685749455980040605463801)
    ·
      refine ⟨16264312091985030454097851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21685749455980040605463801 16264312091985030454097851)
      ·
        refine ⟨24396468137977545681146777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16264312091985030454097851 24396468137977545681146777)
        ·
          refine ⟨18297351103483159260860083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24396468137977545681146777 18297351103483159260860083)
          ·
            refine ⟨27446026655224738891290125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18297351103483159260860083 27446026655224738891290125)
            ·
              refine ⟨10292259995709277084233797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27446026655224738891290125 10292259995709277084233797)
              ·
                refine ⟨1929798749195489453293837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10292259995709277084233797 1929798749195489453293837)
                ·
                  refine ⟨723674530948308544985189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1929798749195489453293837 723674530948308544985189)
                  ·
                    refine ⟨135688974552807852184723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 723674530948308544985189 135688974552807852184723)
                    ·
                      rfl

theorem cell23_792760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 3, 4].length) (baseStart_792760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792760 prefixEnd_792760 := by exact prefixLift 792760
  have htrace : WordTrace (prefixWord ++ tailWord_792760) baseStart_792760 baseEnd_792760 := by
    simpa [prefixWord, tailWord_792760, baseEnd_792760] using wordTrace_append hprefix tailTrace_792760
  have hstable : (prefixWord ++ tailWord_792760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792760).length < 2 ^ (prefixWord ++ tailWord_792760).sum := by decide
  have hdescent : baseEnd_792760 < baseStart_792760 := by decide
  rcases family_descends (prefixWord ++ tailWord_792760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792763 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 4]
def baseStart_792763 : Nat := 118140960795 + 792763 * 2 ^ 59
def prefixEnd_792763 : Nat := 4983230072969 + 3 ^ 40 * 792763 * 2
def baseEnd_792763 : Nat := 407068464100387044816655

theorem tailTrace_792763 : CollatzResearch.WordTrace tailWord_792763 prefixEnd_792763 407068464100387044816655 := by
  unfold tailWord_792763
  simp only [CollatzResearch.WordTrace]
  refine ⟨28914442026962518986310943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19276294684641679324207295 28914442026962518986310943)
  ·
    refine ⟨43371663040443778479466415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28914442026962518986310943 43371663040443778479466415)
    ·
      refine ⟨65057494560665667719199623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43371663040443778479466415 65057494560665667719199623)
      ·
        refine ⟨97586241840998501578799435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65057494560665667719199623 97586241840998501578799435)
        ·
          refine ⟨146379362761497752368199153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97586241840998501578799435 146379362761497752368199153)
          ·
            refine ⟨109784522071123314276149365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146379362761497752368199153 109784522071123314276149365)
            ·
              refine ⟨10292298944167810713389003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109784522071123314276149365 10292298944167810713389003)
              ·
                refine ⟨15438448416251716070083505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10292298944167810713389003 15438448416251716070083505)
                ·
                  refine ⟨11578836312188787052562629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15438448416251716070083505 11578836312188787052562629)
                  ·
                    refine ⟨2171031808535397572355493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11578836312188787052562629 2171031808535397572355493)
                    ·
                      refine ⟨407068464100387044816655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2171031808535397572355493 407068464100387044816655)
                      ·
                        rfl

theorem cell23_792763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 4].length) (baseStart_792763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792763 prefixEnd_792763 := by exact prefixLift 792763
  have htrace : WordTrace (prefixWord ++ tailWord_792763) baseStart_792763 baseEnd_792763 := by
    simpa [prefixWord, tailWord_792763, baseEnd_792763] using wordTrace_append hprefix tailTrace_792763
  have hstable : (prefixWord ++ tailWord_792763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792763).length < 2 ^ (prefixWord ++ tailWord_792763).sum := by decide
  have hdescent : baseEnd_792763 < baseStart_792763 := by decide
  rcases family_descends (prefixWord ++ tailWord_792763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792773 : List Nat := [1, 3, 1, 1, 1, 1, 5, 2, 8]
def baseStart_792773 : Nat := 118140960795 + 792773 * 2 ^ 59
def prefixEnd_792773 : Nat := 4983230072969 + 3 ^ 40 * 792773 * 2
def baseEnd_792773 : Nat := 45230399878548000632401

theorem tailTrace_792773 : CollatzResearch.WordTrace tailWord_792773 prefixEnd_792773 45230399878548000632401 := by
  unfold tailWord_792773
  simp only [CollatzResearch.WordTrace]
  refine ⟨28914806756926290694174973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19276537837950860462783315 28914806756926290694174973)
  ·
    refine ⟨10843052533847359010315615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28914806756926290694174973 10843052533847359010315615)
    ·
      refine ⟨16264578800771038515473423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10843052533847359010315615 16264578800771038515473423)
      ·
        refine ⟨24396868201156557773210135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16264578800771038515473423 24396868201156557773210135)
        ·
          refine ⟨36595302301734836659815203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24396868201156557773210135 36595302301734836659815203)
          ·
            refine ⟨54892953452602254989722805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36595302301734836659815203 54892953452602254989722805)
            ·
              refine ⟨5146214386181461405286513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54892953452602254989722805 5146214386181461405286513)
              ·
                refine ⟨3859660789636096053964885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5146214386181461405286513 3859660789636096053964885)
                ·
                  refine ⟨45230399878548000632401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3859660789636096053964885 45230399878548000632401)
                  ·
                    rfl

theorem cell23_792773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 8].length) (baseStart_792773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792773 prefixEnd_792773 := by exact prefixLift 792773
  have htrace : WordTrace (prefixWord ++ tailWord_792773) baseStart_792773 baseEnd_792773 := by
    simpa [prefixWord, tailWord_792773, baseEnd_792773] using wordTrace_append hprefix tailTrace_792773
  have hstable : (prefixWord ++ tailWord_792773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792773).length < 2 ^ (prefixWord ++ tailWord_792773).sum := by decide
  have hdescent : baseEnd_792773 < baseStart_792773 := by decide
  rcases family_descends (prefixWord ++ tailWord_792773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792777 : List Nat := [1, 2, 1, 1, 2, 1, 1, 9, 1, 4]
def baseStart_792777 : Nat := 118140960795 + 792777 * 2 ^ 59
def prefixEnd_792777 : Nat := 4983230072969 + 3 ^ 40 * 792777 * 2
def baseEnd_792777 : Nat := 135691884276516663347197

theorem tailTrace_792777 : CollatzResearch.WordTrace tailWord_792777 prefixEnd_792777 135691884276516663347197 := by
  unfold tailWord_792777
  simp only [CollatzResearch.WordTrace]
  refine ⟨28914952648911799377320585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19276635099274532918213723 28914952648911799377320585)
  ·
    refine ⟨21686214486683849532990439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28914952648911799377320585 21686214486683849532990439)
    ·
      refine ⟨32529321730025774299485659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21686214486683849532990439 32529321730025774299485659)
      ·
        refine ⟨48793982595038661449228489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32529321730025774299485659 48793982595038661449228489)
        ·
          refine ⟨36595486946278996086921367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48793982595038661449228489 36595486946278996086921367)
          ·
            refine ⟨54893230419418494130382051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36595486946278996086921367 54893230419418494130382051)
            ·
              refine ⟨82339845629127741195573077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54893230419418494130382051 82339845629127741195573077)
              ·
                refine ⟨482460032983170358567811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 82339845629127741195573077 482460032983170358567811)
                ·
                  refine ⟨723690049474755537851717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 482460032983170358567811 723690049474755537851717)
                  ·
                    refine ⟨135691884276516663347197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 723690049474755537851717 135691884276516663347197)
                    ·
                      rfl

theorem cell23_792777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9, 1, 4].length) (baseStart_792777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792777 prefixEnd_792777 := by exact prefixLift 792777
  have htrace : WordTrace (prefixWord ++ tailWord_792777) baseStart_792777 baseEnd_792777 := by
    simpa [prefixWord, tailWord_792777, baseEnd_792777] using wordTrace_append hprefix tailTrace_792777
  have hstable : (prefixWord ++ tailWord_792777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792777).length < 2 ^ (prefixWord ++ tailWord_792777).sum := by decide
  have hdescent : baseEnd_792777 < baseStart_792777 := by decide
  rcases family_descends (prefixWord ++ tailWord_792777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792793 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 1, 1, 8]
def baseStart_792793 : Nat := 118140960795 + 792793 * 2 ^ 59
def prefixEnd_792793 : Nat := 4983230072969 + 3 ^ 40 * 792793 * 2
def baseEnd_792793 : Nat := 407083868520021927441517

theorem tailTrace_792793 : CollatzResearch.WordTrace tailWord_792793 prefixEnd_792793 407083868520021927441517 := by
  unfold tailWord_792793
  simp only [CollatzResearch.WordTrace]
  refine ⟨28915536216853834109903033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19277024144569222739935355 28915536216853834109903033)
  ·
    refine ⟨21686652162640375582427275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28915536216853834109903033 21686652162640375582427275)
    ·
      refine ⟨32529978243960563373640913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21686652162640375582427275 32529978243960563373640913)
      ·
        refine ⟨24397483682970422530230685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32529978243960563373640913 24397483682970422530230685)
        ·
          refine ⟨9149056381113908448836507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24397483682970422530230685 9149056381113908448836507)
          ·
            refine ⟨13723584571670862673254761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9149056381113908448836507 13723584571670862673254761)
            ·
              refine ⟨10292688428753147004941071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13723584571670862673254761 10292688428753147004941071)
              ·
                refine ⟨15439032643129720507411607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10292688428753147004941071 15439032643129720507411607)
                ·
                  refine ⟨23158548964694580761117411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15439032643129720507411607 23158548964694580761117411)
                  ·
                    refine ⟨34737823447041871141676117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23158548964694580761117411 34737823447041871141676117)
                    ·
                      refine ⟨407083868520021927441517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 34737823447041871141676117 407083868520021927441517)
                      ·
                        rfl

theorem cell23_792793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_792793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792793 prefixEnd_792793 := by exact prefixLift 792793
  have htrace : WordTrace (prefixWord ++ tailWord_792793) baseStart_792793 baseEnd_792793 := by
    simpa [prefixWord, tailWord_792793, baseEnd_792793] using wordTrace_append hprefix tailTrace_792793
  have hstable : (prefixWord ++ tailWord_792793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792793).length < 2 ^ (prefixWord ++ tailWord_792793).sum := by decide
  have hdescent : baseEnd_792793 < baseStart_792793 := by decide
  rcases family_descends (prefixWord ++ tailWord_792793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792807 : List Nat := [1, 1, 5, 3, 1, 2, 1, 3, 6]
def baseStart_792807 : Nat := 118140960795 + 792807 * 2 ^ 59
def prefixEnd_792807 : Nat := 4983230072969 + 3 ^ 40 * 792807 * 2
def baseEnd_792807 : Nat := 45232339694353874740717

theorem tailTrace_792807 : CollatzResearch.WordTrace tailWord_792807 prefixEnd_792807 45232339694353874740717 := by
  unfold tailWord_792807
  simp only [CollatzResearch.WordTrace]
  refine ⟨28916046838803114500912675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19277364559202076333941783 28916046838803114500912675)
  ·
    refine ⟨43374070258204671751369013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28916046838803114500912675 43374070258204671751369013)
    ·
      refine ⟨4066319086706687976690845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43374070258204671751369013 4066319086706687976690845)
      ·
        refine ⟨1524869657515007991259067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4066319086706687976690845 1524869657515007991259067)
        ·
          refine ⟨2287304486272511986888601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1524869657515007991259067 2287304486272511986888601)
          ·
            refine ⟨1715478364704383990166451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2287304486272511986888601 1715478364704383990166451)
            ·
              refine ⟨2573217547056575985249677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1715478364704383990166451 2573217547056575985249677)
              ·
                refine ⟨964956580146215994468629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2573217547056575985249677 964956580146215994468629)
                ·
                  refine ⟨45232339694353874740717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 964956580146215994468629 45232339694353874740717)
                  ·
                    rfl

theorem cell23_792807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 6].length) (baseStart_792807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792807 prefixEnd_792807 := by exact prefixLift 792807
  have htrace : WordTrace (prefixWord ++ tailWord_792807) baseStart_792807 baseEnd_792807 := by
    simpa [prefixWord, tailWord_792807, baseEnd_792807] using wordTrace_append hprefix tailTrace_792807
  have hstable : (prefixWord ++ tailWord_792807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792807).length < 2 ^ (prefixWord ++ tailWord_792807).sum := by decide
  have hdescent : baseEnd_792807 < baseStart_792807 := by decide
  rcases family_descends (prefixWord ++ tailWord_792807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792817 : List Nat := [1, 2, 2, 2, 2, 1, 2, 4, 3, 1, 3]
def baseStart_792817 : Nat := 118140960795 + 792817 * 2 ^ 59
def prefixEnd_792817 : Nat := 4983230072969 + 3 ^ 40 * 792817 * 2
def baseEnd_792817 : Nat := 407096192055729833541407

theorem tailTrace_792817 : CollatzResearch.WordTrace tailWord_792817 prefixEnd_792817 407096192055729833541407 := by
  unfold tailWord_792817
  simp only [CollatzResearch.WordTrace]
  refine ⟨28916411568766886208776705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19277607712511257472517803 28916411568766886208776705)
  ·
    refine ⟨21687308676575164656582529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28916411568766886208776705 21687308676575164656582529)
    ·
      refine ⟨16265481507431373492436897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21687308676575164656582529 16265481507431373492436897)
      ·
        refine ⟨12199111130573530119327673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16265481507431373492436897 12199111130573530119327673)
        ·
          refine ⟨9149333347930147589495755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12199111130573530119327673 9149333347930147589495755)
          ·
            refine ⟨13724000021895221384243633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9149333347930147589495755 13724000021895221384243633)
            ·
              refine ⟨10293000016421416038182725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13724000021895221384243633 10293000016421416038182725)
              ·
                refine ⟨1929937503079015507159261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10293000016421416038182725 1929937503079015507159261)
                ·
                  refine ⟨723726563654630815184723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1929937503079015507159261 723726563654630815184723)
                  ·
                    refine ⟨1085589845481946222777085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 723726563654630815184723 1085589845481946222777085)
                    ·
                      refine ⟨407096192055729833541407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1085589845481946222777085 407096192055729833541407)
                      ·
                        rfl

theorem cell23_792817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_792817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792817 prefixEnd_792817 := by exact prefixLift 792817
  have htrace : WordTrace (prefixWord ++ tailWord_792817) baseStart_792817 baseEnd_792817 := by
    simpa [prefixWord, tailWord_792817, baseEnd_792817] using wordTrace_append hprefix tailTrace_792817
  have hstable : (prefixWord ++ tailWord_792817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792817).length < 2 ^ (prefixWord ++ tailWord_792817).sum := by decide
  have hdescent : baseEnd_792817 < baseStart_792817 := by decide
  rcases family_descends (prefixWord ++ tailWord_792817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792860 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_792860 : Nat := 118140960795 + 792860 * 2 ^ 59
def prefixEnd_792860 : Nat := 4983230072969 + 3 ^ 40 * 792860 * 2
def baseEnd_792860 : Nat := 407118271723873165303709

theorem tailTrace_792860 : CollatzResearch.WordTrace tailWord_792860 prefixEnd_792860 407118271723873165303709 := by
  unfold tailWord_792860
  simp only [CollatzResearch.WordTrace]
  refine ⟨14458989953805552276296017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19278653271740736368394689 14458989953805552276296017)
  ·
    refine ⟨10844242465354164207222013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14458989953805552276296017 10844242465354164207222013)
    ·
      refine ⟨4066590924507811577708255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10844242465354164207222013 4066590924507811577708255)
      ·
        refine ⟨6099886386761717366562383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4066590924507811577708255 6099886386761717366562383)
        ·
          refine ⟨9149829580142576049843575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6099886386761717366562383 9149829580142576049843575)
          ·
            refine ⟨13724744370213864074765363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9149829580142576049843575 13724744370213864074765363)
            ·
              refine ⟨20587116555320796112148045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13724744370213864074765363 20587116555320796112148045)
              ·
                refine ⟨7720168708245298542055517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20587116555320796112148045 7720168708245298542055517)
                ·
                  refine ⟨2895063265591986953270819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7720168708245298542055517 2895063265591986953270819)
                  ·
                    refine ⟨4342594898387980429906229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2895063265591986953270819 4342594898387980429906229)
                    ·
                      refine ⟨407118271723873165303709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4342594898387980429906229 407118271723873165303709)
                      ·
                        rfl

theorem cell23_792860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_792860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792860 prefixEnd_792860 := by exact prefixLift 792860
  have htrace : WordTrace (prefixWord ++ tailWord_792860) baseStart_792860 baseEnd_792860 := by
    simpa [prefixWord, tailWord_792860, baseEnd_792860] using wordTrace_append hprefix tailTrace_792860
  have hstable : (prefixWord ++ tailWord_792860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792860).length < 2 ^ (prefixWord ++ tailWord_792860).sum := by decide
  have hdescent : baseEnd_792860 < baseStart_792860 := by decide
  rcases family_descends (prefixWord ++ tailWord_792860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792867 : List Nat := [1, 1, 1, 4, 2, 2, 1, 5, 2, 4]
def baseStart_792867 : Nat := 118140960795 + 792867 * 2 ^ 59
def prefixEnd_792867 : Nat := 4983230072969 + 3 ^ 40 * 792867 * 2
def baseEnd_792867 : Nat := 135707288696151545972059

theorem tailTrace_792867 : CollatzResearch.WordTrace tailWord_792867 prefixEnd_792867 135707288696151545972059 := by
  unfold tailWord_792867
  simp only [CollatzResearch.WordTrace]
  refine ⟨28918235218585744748096855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19278823479057163165397903 28918235218585744748096855)
  ·
    refine ⟨43377352827878617122145283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28918235218585744748096855 43377352827878617122145283)
    ·
      refine ⟨65066029241817925683217925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43377352827878617122145283 65066029241817925683217925)
      ·
        refine ⟨12199880482840861065603361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65066029241817925683217925 12199880482840861065603361)
        ·
          refine ⟨9149910362130645799202521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12199880482840861065603361 9149910362130645799202521)
          ·
            refine ⟨6862432771597984349401891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9149910362130645799202521 6862432771597984349401891)
            ·
              refine ⟨10293649157396976524102837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6862432771597984349401891 10293649157396976524102837)
              ·
                refine ⟨965029608505966549134641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10293649157396976524102837 965029608505966549134641)
                ·
                  refine ⟨723772206379474911850981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 965029608505966549134641 723772206379474911850981)
                  ·
                    refine ⟨135707288696151545972059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 723772206379474911850981 135707288696151545972059)
                    ·
                      rfl

theorem cell23_792867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2, 4].length) (baseStart_792867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792867 prefixEnd_792867 := by exact prefixLift 792867
  have htrace : WordTrace (prefixWord ++ tailWord_792867) baseStart_792867 baseEnd_792867 := by
    simpa [prefixWord, tailWord_792867, baseEnd_792867] using wordTrace_append hprefix tailTrace_792867
  have hstable : (prefixWord ++ tailWord_792867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792867).length < 2 ^ (prefixWord ++ tailWord_792867).sum := by decide
  have hdescent : baseEnd_792867 < baseStart_792867 := by decide
  rcases family_descends (prefixWord ++ tailWord_792867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792897 : List Nat := [1, 2, 5, 2, 2, 1, 10]
def baseStart_792897 : Nat := 118140960795 + 792897 * 2 ^ 59
def prefixEnd_792897 : Nat := 4983230072969 + 3 ^ 40 * 792897 * 2
def baseEnd_792897 : Nat := 5026386055655426179519

theorem tailTrace_792897 : CollatzResearch.WordTrace tailWord_792897 prefixEnd_792897 5026386055655426179519 := by
  unfold tailWord_792897
  simp only [CollatzResearch.WordTrace]
  refine ⟨28919329408477059871688945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19279552938984706581125963 28919329408477059871688945)
  ·
    refine ⟨21689497056357794903766709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28919329408477059871688945 21689497056357794903766709)
    ·
      refine ⟨2033390349033543272228129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21689497056357794903766709 2033390349033543272228129)
      ·
        refine ⟨1525042761775157454171097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2033390349033543272228129 1525042761775157454171097)
        ·
          refine ⟨1143782071331368090628323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1525042761775157454171097 1143782071331368090628323)
          ·
            refine ⟨1715673106997052135942485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1143782071331368090628323 1715673106997052135942485)
            ·
              refine ⟨5026386055655426179519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1715673106997052135942485 5026386055655426179519)
              ·
                rfl

theorem cell23_792897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 10].length) (baseStart_792897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792897 prefixEnd_792897 := by exact prefixLift 792897
  have htrace : WordTrace (prefixWord ++ tailWord_792897) baseStart_792897 baseEnd_792897 := by
    simpa [prefixWord, tailWord_792897, baseEnd_792897] using wordTrace_append hprefix tailTrace_792897
  have hstable : (prefixWord ++ tailWord_792897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792897).length < 2 ^ (prefixWord ++ tailWord_792897).sum := by decide
  have hdescent : baseEnd_792897 < baseStart_792897 := by decide
  rcases family_descends (prefixWord ++ tailWord_792897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792910 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 2, 7]
def baseStart_792910 : Nat := 118140960795 + 792910 * 2 ^ 59
def prefixEnd_792910 : Nat := 4983230072969 + 3 ^ 40 * 792910 * 2
def baseEnd_792910 : Nat := 135714648585532656559493

theorem tailTrace_792910 : CollatzResearch.WordTrace tailWord_792910 prefixEnd_792910 135714648585532656559493 := by
  unfold tailWord_792910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3614975444678745386489023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19279869038286642061274789 3614975444678745386489023)
  ·
    refine ⟨5422463167018118079733535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3614975444678745386489023 5422463167018118079733535)
    ·
      refine ⟨8133694750527177119600303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5422463167018118079733535 8133694750527177119600303)
      ·
        refine ⟨12200542125790765679400455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8133694750527177119600303 12200542125790765679400455)
        ·
          refine ⟨18300813188686148519100683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12200542125790765679400455 18300813188686148519100683)
          ·
            refine ⟨27451219783029222778651025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18300813188686148519100683 27451219783029222778651025)
            ·
              refine ⟨20588414837271917083988269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27451219783029222778651025 20588414837271917083988269)
              ·
                refine ⟨7720655563976968906495601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20588414837271917083988269 7720655563976968906495601)
                ·
                  refine ⟨5790491672982726679871701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7720655563976968906495601 5790491672982726679871701)
                  ·
                    refine ⟨135714648585532656559493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5790491672982726679871701 135714648585532656559493)
                    ·
                      rfl

theorem cell23_792910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_792910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792910 prefixEnd_792910 := by exact prefixLift 792910
  have htrace : WordTrace (prefixWord ++ tailWord_792910) baseStart_792910 baseEnd_792910 := by
    simpa [prefixWord, tailWord_792910, baseEnd_792910] using wordTrace_append hprefix tailTrace_792910
  have hstable : (prefixWord ++ tailWord_792910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792910).length < 2 ^ (prefixWord ++ tailWord_792910).sum := by decide
  have hdescent : baseEnd_792910 < baseStart_792910 := by decide
  rcases family_descends (prefixWord ++ tailWord_792910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792967 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 2, 4, 3]
def baseStart_792967 : Nat := 118140960795 + 792967 * 2 ^ 59
def prefixEnd_792967 : Nat := 4983230072969 + 3 ^ 40 * 792967 * 2
def baseEnd_792967 : Nat := 407173214153904246665717

theorem tailTrace_792967 : CollatzResearch.WordTrace tailWord_792967 prefixEnd_792967 407173214153904246665717 := by
  unfold tailWord_792967
  simp only [CollatzResearch.WordTrace]
  refine ⟨28921882518223461826737155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19281255012148974551158103 28921882518223461826737155)
  ·
    refine ⟨43382823777335192740105733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28921882518223461826737155 43382823777335192740105733)
    ·
      refine ⟨8134279458250348638769825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43382823777335192740105733 8134279458250348638769825)
      ·
        refine ⟨6100709593687761479077369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8134279458250348638769825 6100709593687761479077369)
        ·
          refine ⟨4575532195265821109308027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6100709593687761479077369 4575532195265821109308027)
          ·
            refine ⟨6863298292898731663962041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4575532195265821109308027 6863298292898731663962041)
            ·
              refine ⟨5147473719674048747971531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6863298292898731663962041 5147473719674048747971531)
              ·
                refine ⟨7721210579511073121957297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5147473719674048747971531 7721210579511073121957297)
                ·
                  refine ⟨5790907934633304841467973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7721210579511073121957297 5790907934633304841467973)
                  ·
                    refine ⟨1085795237743744657775245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5790907934633304841467973 1085795237743744657775245)
                    ·
                      refine ⟨407173214153904246665717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1085795237743744657775245 407173214153904246665717)
                      ·
                        rfl

theorem cell23_792967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_792967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_792967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_792967 prefixEnd_792967 := by exact prefixLift 792967
  have htrace : WordTrace (prefixWord ++ tailWord_792967) baseStart_792967 baseEnd_792967 := by
    simpa [prefixWord, tailWord_792967, baseEnd_792967] using wordTrace_append hprefix tailTrace_792967
  have hstable : (prefixWord ++ tailWord_792967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792967).length < 2 ^ (prefixWord ++ tailWord_792967).sum := by decide
  have hdescent : baseEnd_792967 < baseStart_792967 := by decide
  rcases family_descends (prefixWord ++ tailWord_792967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793021 : List Nat := [1, 4, 1, 2, 2, 2, 4, 2, 5]
def baseStart_793021 : Nat := 118140960795 + 793021 * 2 ^ 59
def prefixEnd_793021 : Nat := 4983230072969 + 3 ^ 40 * 793021 * 2
def baseEnd_793021 : Nat := 45244549123249670598941

theorem tailTrace_793021 : CollatzResearch.WordTrace tailWord_793021 prefixEnd_793021 45244549123249670598941 := by
  unfold tailWord_793021
  simp only [CollatzResearch.WordTrace]
  refine ⟨28923852060027829049202917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19282568040018552699468611 28923852060027829049202917)
  ·
    refine ⟨5423222261255217946725547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28923852060027829049202917 5423222261255217946725547)
    ·
      refine ⟨8134833391882826920088321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5423222261255217946725547 8134833391882826920088321)
      ·
        refine ⟨6101125043912120190066241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8134833391882826920088321 6101125043912120190066241)
        ·
          refine ⟨4575843782934090142549681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6101125043912120190066241 4575843782934090142549681)
          ·
            refine ⟨3431882837200567606912261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4575843782934090142549681 3431882837200567606912261)
            ·
              refine ⟨643478031975106426296049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3431882837200567606912261 643478031975106426296049)
              ·
                refine ⟨482608523981329819722037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 643478031975106426296049 482608523981329819722037)
                ·
                  refine ⟨45244549123249670598941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 482608523981329819722037 45244549123249670598941)
                  ·
                    rfl

theorem cell23_793021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2, 5].length) (baseStart_793021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793021 prefixEnd_793021 := by exact prefixLift 793021
  have htrace : WordTrace (prefixWord ++ tailWord_793021) baseStart_793021 baseEnd_793021 := by
    simpa [prefixWord, tailWord_793021, baseEnd_793021] using wordTrace_append hprefix tailTrace_793021
  have hstable : (prefixWord ++ tailWord_793021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793021).length < 2 ^ (prefixWord ++ tailWord_793021).sum := by decide
  have hdescent : baseEnd_793021 < baseStart_793021 := by decide
  rcases family_descends (prefixWord ++ tailWord_793021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793081 : List Nat := [1, 2, 1, 3, 1, 2, 4, 4, 1, 4]
def baseStart_793081 : Nat := 118140960795 + 793081 * 2 ^ 59
def prefixEnd_793081 : Nat := 4983230072969 + 3 ^ 40 * 793081 * 2
def baseEnd_793081 : Nat := 135743916982838933546731

theorem tailTrace_793081 : CollatzResearch.WordTrace tailWord_793081 prefixEnd_793081 135743916982838933546731 := by
  unfold tailWord_793081
  simp only [CollatzResearch.WordTrace]
  refine ⟨28926040439810459296387097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19284026959873639530924731 28926040439810459296387097)
  ·
    refine ⟨21694530329857844472290323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28926040439810459296387097 21694530329857844472290323)
    ·
      refine ⟨32541795494786766708435485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21694530329857844472290323 32541795494786766708435485)
      ·
        refine ⟨12203173310545037515663307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32541795494786766708435485 12203173310545037515663307)
        ·
          refine ⟨18304759965817556273494961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12203173310545037515663307 18304759965817556273494961)
          ·
            refine ⟨13728569974363167205121221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18304759965817556273494961 13728569974363167205121221)
            ·
              refine ⟨2574106870193093850960229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13728569974363167205121221 2574106870193093850960229)
              ·
                refine ⟨482645038161205097055043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2574106870193093850960229 482645038161205097055043)
                ·
                  refine ⟨723967557241807645582565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 482645038161205097055043 723967557241807645582565)
                  ·
                    refine ⟨135743916982838933546731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 723967557241807645582565 135743916982838933546731)
                    ·
                      rfl

theorem cell23_793081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4, 1, 4].length) (baseStart_793081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793081 prefixEnd_793081 := by exact prefixLift 793081
  have htrace : WordTrace (prefixWord ++ tailWord_793081) baseStart_793081 baseEnd_793081 := by
    simpa [prefixWord, tailWord_793081, baseEnd_793081] using wordTrace_append hprefix tailTrace_793081
  have hstable : (prefixWord ++ tailWord_793081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793081).length < 2 ^ (prefixWord ++ tailWord_793081).sum := by decide
  have hdescent : baseEnd_793081 < baseStart_793081 := by decide
  rcases family_descends (prefixWord ++ tailWord_793081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793104 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 9, 1, 3]
def baseStart_793104 : Nat := 118140960795 + 793104 * 2 ^ 59
def prefixEnd_793104 : Nat := 4983230072969 + 3 ^ 40 * 793104 * 2
def baseEnd_793104 : Nat := 407243561003570210652587

theorem tailTrace_793104 : CollatzResearch.WordTrace tailWord_793104 prefixEnd_793104 407243561003570210652587 := by
  unfold tailWord_793104
  simp only [CollatzResearch.WordTrace]
  refine ⟨14463439659363567112237183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19284586212484756149649577 14463439659363567112237183)
  ·
    refine ⟨21695159489045350668355775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14463439659363567112237183 21695159489045350668355775)
    ·
      refine ⟨32542739233568026002533663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21695159489045350668355775 32542739233568026002533663)
      ·
        refine ⟨48814108850352039003800495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32542739233568026002533663 48814108850352039003800495)
        ·
          refine ⟨73221163275528058505700743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48814108850352039003800495 73221163275528058505700743)
          ·
            refine ⟨109831744913292087758551115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73221163275528058505700743 109831744913292087758551115)
            ·
              refine ⟨164747617369938131637826673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109831744913292087758551115 164747617369938131637826673)
              ·
                refine ⟨123560713027453598728370005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164747617369938131637826673 123560713027453598728370005)
                ·
                  refine ⟨723988552895235930049043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 123560713027453598728370005 723988552895235930049043)
                  ·
                    refine ⟨1085982829342853895073565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 723988552895235930049043 1085982829342853895073565)
                    ·
                      refine ⟨407243561003570210652587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1085982829342853895073565 407243561003570210652587)
                      ·
                        rfl

theorem cell23_793104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 9, 1, 3].length) (baseStart_793104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793104 prefixEnd_793104 := by exact prefixLift 793104
  have htrace : WordTrace (prefixWord ++ tailWord_793104) baseStart_793104 baseEnd_793104 := by
    simpa [prefixWord, tailWord_793104, baseEnd_793104] using wordTrace_append hprefix tailTrace_793104
  have hstable : (prefixWord ++ tailWord_793104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793104).length < 2 ^ (prefixWord ++ tailWord_793104).sum := by decide
  have hdescent : baseEnd_793104 < baseStart_793104 := by decide
  rcases family_descends (prefixWord ++ tailWord_793104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793138 : List Nat := [3, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3]
def baseStart_793138 : Nat := 118140960795 + 793138 * 2 ^ 59
def prefixEnd_793138 : Nat := 4983230072969 + 3 ^ 40 * 793138 * 2
def baseEnd_793138 : Nat := 407261019345823077627431

theorem tailTrace_793138 : CollatzResearch.WordTrace tailWord_793138 prefixEnd_793138 407261019345823077627431 := by
  unfold tailWord_793138
  simp only [CollatzResearch.WordTrace]
  refine ⟨7232029850150989507803017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19285412933735972020808045 7232029850150989507803017)
  ·
    refine ⟨5424022387613242130852263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7232029850150989507803017 5424022387613242130852263)
    ·
      refine ⟨8136033581419863196278395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5424022387613242130852263 8136033581419863196278395)
      ·
        refine ⟨12204050372129794794417593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8136033581419863196278395 12204050372129794794417593)
        ·
          refine ⟨9153037779097346095813195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12204050372129794794417593 9153037779097346095813195)
          ·
            refine ⟨13729556668646019143719793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9153037779097346095813195 13729556668646019143719793)
            ·
              refine ⟨10297167501484514357789845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13729556668646019143719793 10297167501484514357789845)
              ·
                refine ⟨482679726632086610521399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10297167501484514357789845 482679726632086610521399)
                ·
                  refine ⟨724019589948129915782099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 482679726632086610521399 724019589948129915782099)
                  ·
                    refine ⟨1086029384922194873673149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 724019589948129915782099 1086029384922194873673149)
                    ·
                      refine ⟨407261019345823077627431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1086029384922194873673149 407261019345823077627431)
                      ·
                        rfl

theorem cell23_793138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3].length) (baseStart_793138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793138 prefixEnd_793138 := by exact prefixLift 793138
  have htrace : WordTrace (prefixWord ++ tailWord_793138) baseStart_793138 baseEnd_793138 := by
    simpa [prefixWord, tailWord_793138, baseEnd_793138] using wordTrace_append hprefix tailTrace_793138
  have hstable : (prefixWord ++ tailWord_793138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793138).length < 2 ^ (prefixWord ++ tailWord_793138).sum := by decide
  have hdescent : baseEnd_793138 < baseStart_793138 := by decide
  rcases family_descends (prefixWord ++ tailWord_793138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793144 : List Nat := [2, 1, 2, 1, 4, 1, 2, 2, 3, 1, 4]
def baseStart_793144 : Nat := 118140960795 + 793144 * 2 ^ 59
def prefixEnd_793144 : Nat := 4983230072969 + 3 ^ 40 * 793144 * 2
def baseEnd_793144 : Nat := 407264100229750054152403

theorem tailTrace_793144 : CollatzResearch.WordTrace tailWord_793144 prefixEnd_793144 407264100229750054152403 := by
  unfold tailWord_793144
  simp only [CollatzResearch.WordTrace]
  refine ⟨14464169119291110527965243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19285558825721480703953657 14464169119291110527965243)
  ·
    refine ⟨21696253678936665791947865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14464169119291110527965243 21696253678936665791947865)
    ·
      refine ⟨16272190259202499343960899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21696253678936665791947865 16272190259202499343960899)
      ·
        refine ⟨24408285388803749015941349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16272190259202499343960899 24408285388803749015941349)
        ·
          refine ⟨4576553510400702940489003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24408285388803749015941349 4576553510400702940489003)
          ·
            refine ⟨6864830265601054410733505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4576553510400702940489003 6864830265601054410733505)
            ·
              refine ⟨5148622699200790808050129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6864830265601054410733505 5148622699200790808050129)
              ·
                refine ⟨3861467024400593106037597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5148622699200790808050129 3861467024400593106037597)
                ·
                  refine ⟨1448050134150222414764099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3861467024400593106037597 1448050134150222414764099)
                  ·
                    refine ⟨2172075201225333622146149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1448050134150222414764099 2172075201225333622146149)
                    ·
                      refine ⟨407264100229750054152403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2172075201225333622146149 407264100229750054152403)
                      ·
                        rfl

theorem cell23_793144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_793144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793144 prefixEnd_793144 := by exact prefixLift 793144
  have htrace : WordTrace (prefixWord ++ tailWord_793144) baseStart_793144 baseEnd_793144 := by
    simpa [prefixWord, tailWord_793144, baseEnd_793144] using wordTrace_append hprefix tailTrace_793144
  have hstable : (prefixWord ++ tailWord_793144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793144).length < 2 ^ (prefixWord ++ tailWord_793144).sum := by decide
  have hdescent : baseEnd_793144 < baseStart_793144 := by decide
  rcases family_descends (prefixWord ++ tailWord_793144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793147 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 5]
def baseStart_793147 : Nat := 118140960795 + 793147 * 2 ^ 59
def prefixEnd_793147 : Nat := 4983230072969 + 3 ^ 40 * 793147 * 2
def baseEnd_793147 : Nat := 407265640671713542414889

theorem tailTrace_793147 : CollatzResearch.WordTrace tailWord_793147 prefixEnd_793147 407265640671713542414889 := by
  unfold tailWord_793147
  simp only [CollatzResearch.WordTrace]
  refine ⟨28928447657571352568289695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19285631771714235045526463 28928447657571352568289695)
  ·
    refine ⟨43392671486357028852434543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28928447657571352568289695 43392671486357028852434543)
    ·
      refine ⟨65089007229535543278651815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43392671486357028852434543 65089007229535543278651815)
      ·
        refine ⟨97633510844303314917977723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65089007229535543278651815 97633510844303314917977723)
        ·
          refine ⟨146450266266454972376966585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97633510844303314917977723 146450266266454972376966585)
          ·
            refine ⟨109837699699841229282724939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146450266266454972376966585 109837699699841229282724939)
            ·
              refine ⟨164756549549761843924087409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109837699699841229282724939 164756549549761843924087409)
              ·
                refine ⟨123567412162321382943065557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164756549549761843924087409 123567412162321382943065557)
                ·
                  refine ⟨2896111222554407412728099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 123567412162321382943065557 2896111222554407412728099)
                  ·
                    refine ⟨4344166833831611119092149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2896111222554407412728099 4344166833831611119092149)
                    ·
                      refine ⟨407265640671713542414889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4344166833831611119092149 407265640671713542414889)
                      ·
                        rfl

theorem cell23_793147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 5].length) (baseStart_793147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793147 prefixEnd_793147 := by exact prefixLift 793147
  have htrace : WordTrace (prefixWord ++ tailWord_793147) baseStart_793147 baseEnd_793147 := by
    simpa [prefixWord, tailWord_793147, baseEnd_793147] using wordTrace_append hprefix tailTrace_793147
  have hstable : (prefixWord ++ tailWord_793147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793147).length < 2 ^ (prefixWord ++ tailWord_793147).sum := by decide
  have hdescent : baseEnd_793147 < baseStart_793147 := by decide
  rcases family_descends (prefixWord ++ tailWord_793147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793158 : List Nat := [6, 1, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_793158 : Nat := 118140960795 + 793158 * 2 ^ 59
def prefixEnd_793158 : Nat := 4983230072969 + 3 ^ 40 * 793158 * 2
def baseEnd_793158 : Nat := 135757096319637666459113

theorem tailTrace_793158 : CollatzResearch.WordTrace tailWord_793158 prefixEnd_793158 135757096319637666459113 := by
  unfold tailWord_793158
  simp only [CollatzResearch.WordTrace]
  refine ⟨904026526891609420216879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19285899240354334297960085 904026526891609420216879)
  ·
    refine ⟨1356039790337414130325319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 904026526891609420216879 1356039790337414130325319)
    ·
      refine ⟨2034059685506121195487979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1356039790337414130325319 2034059685506121195487979)
      ·
        refine ⟨3051089528259181793231969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2034059685506121195487979 3051089528259181793231969)
        ·
          refine ⟨2288317146194386344923977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3051089528259181793231969 2288317146194386344923977)
          ·
            refine ⟨1716237859645789758692983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2288317146194386344923977 1716237859645789758692983)
            ·
              refine ⟨2574356789468684638039475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1716237859645789758692983 2574356789468684638039475)
              ·
                refine ⟨3861535184203026957059213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2574356789468684638039475 3861535184203026957059213)
                ·
                  refine ⟨1448075694076135108897205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3861535184203026957059213 1448075694076135108897205)
                  ·
                    refine ⟨135757096319637666459113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1448075694076135108897205 135757096319637666459113)
                    ·
                      rfl

theorem cell23_793158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_793158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793158 prefixEnd_793158 := by exact prefixLift 793158
  have htrace : WordTrace (prefixWord ++ tailWord_793158) baseStart_793158 baseEnd_793158 := by
    simpa [prefixWord, tailWord_793158, baseEnd_793158] using wordTrace_append hprefix tailTrace_793158
  have hstable : (prefixWord ++ tailWord_793158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793158).length < 2 ^ (prefixWord ++ tailWord_793158).sum := by decide
  have hdescent : baseEnd_793158 < baseStart_793158 := by decide
  rcases family_descends (prefixWord ++ tailWord_793158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793165 : List Nat := [1, 6, 1, 1, 2, 2, 2, 1, 2, 3, 2]
def baseStart_793165 : Nat := 118140960795 + 793165 * 2 ^ 59
def prefixEnd_793165 : Nat := 4983230072969 + 3 ^ 40 * 793165 * 2
def baseEnd_793165 : Nat := 407274883323494471989807

theorem tailTrace_793165 : CollatzResearch.WordTrace tailWord_793165 prefixEnd_793165 407274883323494471989807 := by
  unfold tailWord_793165
  simp only [CollatzResearch.WordTrace]
  refine ⟨28929104171506141642444949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19286069447670761094963299 28929104171506141642444949)
  ·
    refine ⟨1356051758039350389489607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 28929104171506141642444949 1356051758039350389489607)
    ·
      refine ⟨2034077637059025584234411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1356051758039350389489607 2034077637059025584234411)
      ·
        refine ⟨3051116455588538376351617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2034077637059025584234411 3051116455588538376351617)
        ·
          refine ⟨2288337341691403782263713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3051116455588538376351617 2288337341691403782263713)
          ·
            refine ⟨1716253006268552836697785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2288337341691403782263713 1716253006268552836697785)
            ·
              refine ⟨1287189754701414627523339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1716253006268552836697785 1287189754701414627523339)
              ·
                refine ⟨1930784632052121941285009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1287189754701414627523339 1930784632052121941285009)
                ·
                  refine ⟨1448088474039091455963757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1930784632052121941285009 1448088474039091455963757)
                  ·
                    refine ⟨543033177764659295986409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1448088474039091455963757 543033177764659295986409)
                    ·
                      refine ⟨407274883323494471989807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 543033177764659295986409 407274883323494471989807)
                      ·
                        rfl

theorem cell23_793165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_793165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793165 prefixEnd_793165 := by exact prefixLift 793165
  have htrace : WordTrace (prefixWord ++ tailWord_793165) baseStart_793165 baseEnd_793165 := by
    simpa [prefixWord, tailWord_793165, baseEnd_793165] using wordTrace_append hprefix tailTrace_793165
  have hstable : (prefixWord ++ tailWord_793165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793165).length < 2 ^ (prefixWord ++ tailWord_793165).sum := by decide
  have hdescent : baseEnd_793165 < baseStart_793165 := by decide
  rcases family_descends (prefixWord ++ tailWord_793165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793167 : List Nat := [1, 1, 2, 1, 1, 2, 6, 9]
def baseStart_793167 : Nat := 118140960795 + 793167 * 2 ^ 59
def prefixEnd_793167 : Nat := 4983230072969 + 3 ^ 40 * 793167 * 2
def baseEnd_793167 : Nat := 15084292973511239413511

theorem tailTrace_793167 : CollatzResearch.WordTrace tailWord_793167 prefixEnd_793167 15084292973511239413511 := by
  unfold tailWord_793167
  simp only [CollatzResearch.WordTrace]
  refine ⟨28929177117498895984017755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19286118078332597322678503 28929177117498895984017755)
  ·
    refine ⟨43393765676248343976026633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28929177117498895984017755 43393765676248343976026633)
    ·
      refine ⟨32545324257186257982019975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43393765676248343976026633 32545324257186257982019975)
      ·
        refine ⟨48817986385779386973029963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32545324257186257982019975 48817986385779386973029963)
        ·
          refine ⟨73226979578669080459544945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48817986385779386973029963 73226979578669080459544945)
          ·
            refine ⟨54920234684001810344658709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73226979578669080459544945 54920234684001810344658709)
            ·
              refine ⟨2574386000812584859905877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 54920234684001810344658709 2574386000812584859905877)
              ·
                refine ⟨15084292973511239413511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2574386000812584859905877 15084292973511239413511)
                ·
                  rfl

theorem cell23_793167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 9].length) (baseStart_793167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793167 prefixEnd_793167 := by exact prefixLift 793167
  have htrace : WordTrace (prefixWord ++ tailWord_793167) baseStart_793167 baseEnd_793167 := by
    simpa [prefixWord, tailWord_793167, baseEnd_793167] using wordTrace_append hprefix tailTrace_793167
  have hstable : (prefixWord ++ tailWord_793167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793167).length < 2 ^ (prefixWord ++ tailWord_793167).sum := by decide
  have hdescent : baseEnd_793167 < baseStart_793167 := by decide
  rcases family_descends (prefixWord ++ tailWord_793167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793189 : List Nat := [1, 3, 1, 3, 5, 1, 2, 2, 1, 1, 3]
def baseStart_793189 : Nat := 118140960795 + 793189 * 2 ^ 59
def prefixEnd_793189 : Nat := 4983230072969 + 3 ^ 40 * 793189 * 2
def baseEnd_793189 : Nat := 407287206859202378089697

theorem tailTrace_793189 : CollatzResearch.WordTrace tailWord_793189 prefixEnd_793189 407287206859202378089697 := by
  unfold tailWord_793189
  simp only [CollatzResearch.WordTrace]
  refine ⟨28929979523419193741318621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19286653015612795827545747 28929979523419193741318621)
  ·
    refine ⟨10848742321282197652994483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28929979523419193741318621 10848742321282197652994483)
    ·
      refine ⟨16273113481923296479491725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10848742321282197652994483 16273113481923296479491725)
      ·
        refine ⟨6102417555721236179809397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16273113481923296479491725 6102417555721236179809397)
        ·
          refine ⟨572101645848865891857131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6102417555721236179809397 572101645848865891857131)
          ·
            refine ⟨858152468773298837785697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572101645848865891857131 858152468773298837785697)
            ·
              refine ⟨643614351579974128339273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 858152468773298837785697 643614351579974128339273)
              ·
                refine ⟨482710763684980596254455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 643614351579974128339273 482710763684980596254455)
                ·
                  refine ⟨724066145527470894381683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 482710763684980596254455 724066145527470894381683)
                  ·
                    refine ⟨1086099218291206341572525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 724066145527470894381683 1086099218291206341572525)
                    ·
                      refine ⟨407287206859202378089697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1086099218291206341572525 407287206859202378089697)
                      ·
                        rfl

theorem cell23_793189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_793189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793189 prefixEnd_793189 := by exact prefixLift 793189
  have htrace : WordTrace (prefixWord ++ tailWord_793189) baseStart_793189 baseEnd_793189 := by
    simpa [prefixWord, tailWord_793189, baseEnd_793189] using wordTrace_append hprefix tailTrace_793189
  have hstable : (prefixWord ++ tailWord_793189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793189).length < 2 ^ (prefixWord ++ tailWord_793189).sum := by decide
  have hdescent : baseEnd_793189 < baseStart_793189 := by decide
  rcases family_descends (prefixWord ++ tailWord_793189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793261 : List Nat := [1, 5, 2, 1, 1, 2, 2, 1, 2, 6]
def baseStart_793261 : Nat := 118140960795 + 793261 * 2 ^ 59
def prefixEnd_793261 : Nat := 4983230072969 + 3 ^ 40 * 793261 * 2
def baseEnd_793261 : Nat := 135774725822108698796455

theorem tailTrace_793261 : CollatzResearch.WordTrace tailWord_793261 prefixEnd_793261 135774725822108698796455 := by
  unfold tailWord_793261
  simp only [CollatzResearch.WordTrace]
  refine ⟨28932605579158350037939637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19288403719438900025293091 28932605579158350037939637)
  ·
    refine ⟨2712431773046095316056841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28932605579158350037939637 2712431773046095316056841)
    ·
      refine ⟨2034323829784571487042631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2712431773046095316056841 2034323829784571487042631)
      ·
        refine ⟨3051485744676857230563947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2034323829784571487042631 3051485744676857230563947)
        ·
          refine ⟨4577228617015285845845921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3051485744676857230563947 4577228617015285845845921)
          ·
            refine ⟨3432921462761464384384441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4577228617015285845845921 3432921462761464384384441)
            ·
              refine ⟨2574691097071098288288331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3432921462761464384384441 2574691097071098288288331)
              ·
                refine ⟨3862036645606647432432497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2574691097071098288288331 3862036645606647432432497)
                ·
                  refine ⟨2896527484204985574324373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3862036645606647432432497 2896527484204985574324373)
                  ·
                    refine ⟨135774725822108698796455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2896527484204985574324373 135774725822108698796455)
                    ·
                      rfl

theorem cell23_793261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_793261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793261 prefixEnd_793261 := by exact prefixLift 793261
  have htrace : WordTrace (prefixWord ++ tailWord_793261) baseStart_793261 baseEnd_793261 := by
    simpa [prefixWord, tailWord_793261, baseEnd_793261] using wordTrace_append hprefix tailTrace_793261
  have hstable : (prefixWord ++ tailWord_793261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793261).length < 2 ^ (prefixWord ++ tailWord_793261).sum := by decide
  have hdescent : baseEnd_793261 < baseStart_793261 := by decide
  rcases family_descends (prefixWord ++ tailWord_793261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793274 : List Nat := [3, 1, 1, 1, 2, 3, 1, 4, 7]
def baseStart_793274 : Nat := 118140960795 + 793274 * 2 ^ 59
def prefixEnd_793274 : Nat := 4983230072969 + 3 ^ 40 * 793274 * 2
def baseEnd_793274 : Nat := 45258983634981616169645

theorem tailTrace_793274 : CollatzResearch.WordTrace tailWord_793274 prefixEnd_793274 45258983634981616169645 := by
  unfold tailWord_793274
  simp only [CollatzResearch.WordTrace]
  refine ⟨7233269932027813314540719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19288719818740835505441917 7233269932027813314540719)
  ·
    refine ⟨10849904898041719971811079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7233269932027813314540719 10849904898041719971811079)
    ·
      refine ⟨16274857347062579957716619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10849904898041719971811079 16274857347062579957716619)
      ·
        refine ⟨24412286020593869936574929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16274857347062579957716619 24412286020593869936574929)
        ·
          refine ⟨18309214515445402452431197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24412286020593869936574929 18309214515445402452431197)
          ·
            refine ⟨6865955443292025919661699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18309214515445402452431197 6865955443292025919661699)
            ·
              refine ⟨10298933164938038879492549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6865955443292025919661699 10298933164938038879492549)
              ·
                refine ⟨1931049968425882289904853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10298933164938038879492549 1931049968425882289904853)
                ·
                  refine ⟨45258983634981616169645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1931049968425882289904853 45258983634981616169645)
                  ·
                    rfl

theorem cell23_793274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 7].length) (baseStart_793274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793274 prefixEnd_793274 := by exact prefixLift 793274
  have htrace : WordTrace (prefixWord ++ tailWord_793274) baseStart_793274 baseEnd_793274 := by
    simpa [prefixWord, tailWord_793274, baseEnd_793274] using wordTrace_append hprefix tailTrace_793274
  have hstable : (prefixWord ++ tailWord_793274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793274).length < 2 ^ (prefixWord ++ tailWord_793274).sum := by decide
  have hdescent : baseEnd_793274 < baseStart_793274 := by decide
  rcases family_descends (prefixWord ++ tailWord_793274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793308 : List Nat := [2, 2, 5, 1, 1, 1, 3, 1, 7]
def baseStart_793308 : Nat := 118140960795 + 793308 * 2 ^ 59
def prefixEnd_793308 : Nat := 4983230072969 + 3 ^ 40 * 793308 * 2
def baseEnd_793308 : Nat := 45260923450787490277961

theorem tailTrace_793308 : CollatzResearch.WordTrace tailWord_793308 prefixEnd_793308 45260923450787490277961 := by
  unfold tailWord_793308
  simp only [CollatzResearch.WordTrace]
  refine ⟨14467159904994038532450289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19289546539992051376600385 14467159904994038532450289)
  ·
    refine ⟨10850369928745528899337717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14467159904994038532450289 10850369928745528899337717)
    ·
      refine ⟨1017222180819893334312911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10850369928745528899337717 1017222180819893334312911)
      ·
        refine ⟨1525833271229840001469367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1017222180819893334312911 1525833271229840001469367)
        ·
          refine ⟨2288749906844760002204051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1525833271229840001469367 2288749906844760002204051)
          ·
            refine ⟨3433124860267140003306077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2288749906844760002204051 3433124860267140003306077)
            ·
              refine ⟨1287421822600177501239779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3433124860267140003306077 1287421822600177501239779)
              ·
                refine ⟨1931132733900266251859669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1287421822600177501239779 1931132733900266251859669)
                ·
                  refine ⟨45260923450787490277961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1931132733900266251859669 45260923450787490277961)
                  ·
                    rfl

theorem cell23_793308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 7].length) (baseStart_793308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793308 prefixEnd_793308 := by exact prefixLift 793308
  have htrace : WordTrace (prefixWord ++ tailWord_793308) baseStart_793308 baseEnd_793308 := by
    simpa [prefixWord, tailWord_793308, baseEnd_793308] using wordTrace_append hprefix tailTrace_793308
  have hstable : (prefixWord ++ tailWord_793308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793308).length < 2 ^ (prefixWord ++ tailWord_793308).sum := by decide
  have hdescent : baseEnd_793308 < baseStart_793308 := by decide
  rcases family_descends (prefixWord ++ tailWord_793308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793344 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 5]
def baseStart_793344 : Nat := 118140960795 + 793344 * 2 ^ 59
def prefixEnd_793344 : Nat := 4983230072969 + 3 ^ 40 * 793344 * 2
def baseEnd_793344 : Nat := 407366796360649271651483

theorem tailTrace_793344 : CollatzResearch.WordTrace tailWord_793344 prefixEnd_793344 407366796360649271651483 := by
  unfold tailWord_793344
  simp only [CollatzResearch.WordTrace]
  refine ⟨14467816418928827606605543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19290421891905103475474057 14467816418928827606605543)
  ·
    refine ⟨21701724628393241409908315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14467816418928827606605543 21701724628393241409908315)
    ·
      refine ⟨32552586942589862114862473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21701724628393241409908315 32552586942589862114862473)
      ·
        refine ⟨24414440206942396586146855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32552586942589862114862473 24414440206942396586146855)
        ·
          refine ⟨36621660310413594879220283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24414440206942396586146855 36621660310413594879220283)
          ·
            refine ⟨54932490465620392318830425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36621660310413594879220283 54932490465620392318830425)
            ·
              refine ⟨41199367849215294239122819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54932490465620392318830425 41199367849215294239122819)
              ·
                refine ⟨61799051773822941358684229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41199367849215294239122819 61799051773822941358684229)
                ·
                  refine ⟨11587322207591801504753293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61799051773822941358684229 11587322207591801504753293)
                  ·
                    refine ⟨4345245827846925564282485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11587322207591801504753293 4345245827846925564282485)
                    ·
                      refine ⟨407366796360649271651483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4345245827846925564282485 407366796360649271651483)
                      ·
                        rfl

theorem cell23_793344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_793344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793344 prefixEnd_793344 := by exact prefixLift 793344
  have htrace : WordTrace (prefixWord ++ tailWord_793344) baseStart_793344 baseEnd_793344 := by
    simpa [prefixWord, tailWord_793344, baseEnd_793344] using wordTrace_append hprefix tailTrace_793344
  have hstable : (prefixWord ++ tailWord_793344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793344).length < 2 ^ (prefixWord ++ tailWord_793344).sum := by decide
  have hdescent : baseEnd_793344 < baseStart_793344 := by decide
  rcases family_descends (prefixWord ++ tailWord_793344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793358 : List Nat := [4, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2]
def baseStart_793358 : Nat := 118140960795 + 793358 * 2 ^ 59
def prefixEnd_793358 : Nat := 4983230072969 + 3 ^ 40 * 793358 * 2
def baseEnd_793358 : Nat := 407373985089812216876419

theorem tailTrace_793358 : CollatzResearch.WordTrace tailWord_793358 prefixEnd_793358 407373985089812216876419 := by
  unfold tailWord_793358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3617017932475866950527591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19290762306537957069480485 3617017932475866950527591)
  ·
    refine ⟨5425526898713800425791387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3617017932475866950527591 5425526898713800425791387)
    ·
      refine ⟨8138290348070700638687081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5425526898713800425791387 8138290348070700638687081)
      ·
        refine ⟨6103717761053025479015311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8138290348070700638687081 6103717761053025479015311)
        ·
          refine ⟨9155576641579538218522967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6103717761053025479015311 9155576641579538218522967)
          ·
            refine ⟨13733364962369307327784451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9155576641579538218522967 13733364962369307327784451)
            ·
              refine ⟨20600047443553960991676677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13733364962369307327784451 20600047443553960991676677)
              ·
                refine ⟨3862508895666367685939377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20600047443553960991676677 3862508895666367685939377)
                ·
                  refine ⟨2896881671749775764454533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3862508895666367685939377 2896881671749775764454533)
                  ·
                    refine ⟨543165313453082955835225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2896881671749775764454533 543165313453082955835225)
                    ·
                      refine ⟨407373985089812216876419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 543165313453082955835225 407373985089812216876419)
                      ·
                        rfl

theorem cell23_793358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_793358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793358 prefixEnd_793358 := by exact prefixLift 793358
  have htrace : WordTrace (prefixWord ++ tailWord_793358) baseStart_793358 baseEnd_793358 := by
    simpa [prefixWord, tailWord_793358, baseEnd_793358] using wordTrace_append hprefix tailTrace_793358
  have hstable : (prefixWord ++ tailWord_793358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793358).length < 2 ^ (prefixWord ++ tailWord_793358).sum := by decide
  have hdescent : baseEnd_793358 < baseStart_793358 := by decide
  rcases family_descends (prefixWord ++ tailWord_793358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793381 : List Nat := [1, 3, 1, 2, 3, 1, 1, 5, 6]
def baseStart_793381 : Nat := 118140960795 + 793381 * 2 ^ 59
def prefixEnd_793381 : Nat := 4983230072969 + 3 ^ 40 * 793381 * 2
def baseEnd_793381 : Nat := 45265088349429514098757

theorem tailTrace_793381 : CollatzResearch.WordTrace tailWord_793381 prefixEnd_793381 45265088349429514098757 := by
  unfold tailWord_793381
  simp only [CollatzResearch.WordTrace]
  refine ⟨28936982338723610532307997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19291321559149073688205331 28936982338723610532307997)
  ·
    refine ⟨10851368377021353949615499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28936982338723610532307997 10851368377021353949615499)
    ·
      refine ⟨16277052565532030924423249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10851368377021353949615499 16277052565532030924423249)
      ·
        refine ⟨12207789424149023193317437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16277052565532030924423249 12207789424149023193317437)
        ·
          refine ⟨4577921034055883697494039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12207789424149023193317437 4577921034055883697494039)
          ·
            refine ⟨6866881551083825546241059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4577921034055883697494039 6866881551083825546241059)
            ·
              refine ⟨10300322326625738319361589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6866881551083825546241059 10300322326625738319361589)
              ·
                refine ⟨965655218121162967440149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10300322326625738319361589 965655218121162967440149)
                ·
                  refine ⟨45265088349429514098757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 965655218121162967440149 45265088349429514098757)
                  ·
                    rfl

theorem cell23_793381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 6].length) (baseStart_793381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793381 prefixEnd_793381 := by exact prefixLift 793381
  have htrace : WordTrace (prefixWord ++ tailWord_793381) baseStart_793381 baseEnd_793381 := by
    simpa [prefixWord, tailWord_793381, baseEnd_793381] using wordTrace_append hprefix tailTrace_793381
  have hstable : (prefixWord ++ tailWord_793381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793381).length < 2 ^ (prefixWord ++ tailWord_793381).sum := by decide
  have hdescent : baseEnd_793381 < baseStart_793381 := by decide
  rcases family_descends (prefixWord ++ tailWord_793381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793389 : List Nat := [1, 5, 3, 2, 2, 1, 1, 1, 2, 5]
def baseStart_793389 : Nat := 118140960795 + 793389 * 2 ^ 59
def prefixEnd_793389 : Nat := 4983230072969 + 3 ^ 40 * 793389 * 2
def baseEnd_793389 : Nat := 135796634330033865196259

theorem tailTrace_793389 : CollatzResearch.WordTrace tailWord_793389 prefixEnd_793389 135796634330033865196259 := by
  unfold tailWord_793389
  simp only [CollatzResearch.WordTrace]
  refine ⟨28937274122694627898599221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19291516081796418599066147 28937274122694627898599221)
  ·
    refine ⟨2712869449002621365493677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28937274122694627898599221 2712869449002621365493677)
    ·
      refine ⟨1017326043375983012060129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2712869449002621365493677 1017326043375983012060129)
      ·
        refine ⟨762994532531987259045097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1017326043375983012060129 762994532531987259045097)
        ·
          refine ⟨572245899398990444283823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 762994532531987259045097 572245899398990444283823)
          ·
            refine ⟨858368849098485666425735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572245899398990444283823 858368849098485666425735)
            ·
              refine ⟨1287553273647728499638603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858368849098485666425735 1287553273647728499638603)
              ·
                refine ⟨1931329910471592749457905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1287553273647728499638603 1931329910471592749457905)
                ·
                  refine ⟨1448497432853694562093429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1931329910471592749457905 1448497432853694562093429)
                  ·
                    refine ⟨135796634330033865196259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1448497432853694562093429 135796634330033865196259)
                    ·
                      rfl

theorem cell23_793389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_793389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793389 prefixEnd_793389 := by exact prefixLift 793389
  have htrace : WordTrace (prefixWord ++ tailWord_793389) baseStart_793389 baseEnd_793389 := by
    simpa [prefixWord, tailWord_793389, baseEnd_793389] using wordTrace_append hprefix tailTrace_793389
  have hstable : (prefixWord ++ tailWord_793389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793389).length < 2 ^ (prefixWord ++ tailWord_793389).sum := by decide
  have hdescent : baseEnd_793389 < baseStart_793389 := by decide
  rcases family_descends (prefixWord ++ tailWord_793389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793395 : List Nat := [1, 1, 1, 2, 6, 3, 1, 1, 2, 2, 3]
def baseStart_793395 : Nat := 118140960795 + 793395 * 2 ^ 59
def prefixEnd_793395 : Nat := 4983230072969 + 3 ^ 40 * 793395 * 2
def baseEnd_793395 : Nat := 407392983874028572113749

theorem tailTrace_793395 : CollatzResearch.WordTrace tailWord_793395 prefixEnd_793395 407392983874028572113749 := by
  unfold tailWord_793395
  simp only [CollatzResearch.WordTrace]
  refine ⟨28937492960672890923317639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19291661973781927282211759 28937492960672890923317639)
  ·
    refine ⟨43406239441009336384976459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28937492960672890923317639 43406239441009336384976459)
    ·
      refine ⟨65109359161514004577464689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43406239441009336384976459 65109359161514004577464689)
      ·
        refine ⟨48832019371135503433098517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65109359161514004577464689 48832019371135503433098517)
        ·
          refine ⟨2289000908021976723426493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48832019371135503433098517 2289000908021976723426493)
          ·
            refine ⟨858375340508241271284935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2289000908021976723426493 858375340508241271284935)
            ·
              refine ⟨1287563010762361906927403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858375340508241271284935 1287563010762361906927403)
              ·
                refine ⟨1931344516143542860391105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1287563010762361906927403 1931344516143542860391105)
                ·
                  refine ⟨1448508387107657145293329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1931344516143542860391105 1448508387107657145293329)
                  ·
                    refine ⟨1086381290330742858969997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1448508387107657145293329 1086381290330742858969997)
                    ·
                      refine ⟨407392983874028572113749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1086381290330742858969997 407392983874028572113749)
                      ·
                        rfl

theorem cell23_793395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 2, 3].length) (baseStart_793395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793395 prefixEnd_793395 := by exact prefixLift 793395
  have htrace : WordTrace (prefixWord ++ tailWord_793395) baseStart_793395 baseEnd_793395 := by
    simpa [prefixWord, tailWord_793395, baseEnd_793395] using wordTrace_append hprefix tailTrace_793395
  have hstable : (prefixWord ++ tailWord_793395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793395).length < 2 ^ (prefixWord ++ tailWord_793395).sum := by decide
  have hdescent : baseEnd_793395 < baseStart_793395 := by decide
  rcases family_descends (prefixWord ++ tailWord_793395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793402 : List Nat := [3, 1, 1, 1, 6, 1, 2, 3, 1, 4]
def baseStart_793402 : Nat := 118140960795 + 793402 * 2 ^ 59
def prefixEnd_793402 : Nat := 4983230072969 + 3 ^ 40 * 793402 * 2
def baseEnd_793402 : Nat := 135798859412870014908739

theorem tailTrace_793402 : CollatzResearch.WordTrace tailWord_793402 prefixEnd_793402 135798859412870014908739 := by
  unfold tailWord_793402
  simp only [CollatzResearch.WordTrace]
  refine ⟨7234437067911882779705615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19291832181098354079214973 7234437067911882779705615)
  ·
    refine ⟨10851655601867824169558423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7234437067911882779705615 10851655601867824169558423)
    ·
      refine ⟨16277483402801736254337635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10851655601867824169558423 16277483402801736254337635)
      ·
        refine ⟨24416225104202604381506453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16277483402801736254337635 24416225104202604381506453)
        ·
          refine ⟨1144510551759497080383115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24416225104202604381506453 1144510551759497080383115)
          ·
            refine ⟨1716765827639245620574673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1144510551759497080383115 1716765827639245620574673)
            ·
              refine ⟨1287574370729434215431005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1716765827639245620574673 1287574370729434215431005)
              ·
                refine ⟨482840389023537830786627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1287574370729434215431005 482840389023537830786627)
                ·
                  refine ⟨724260583535306746179941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 482840389023537830786627 724260583535306746179941)
                  ·
                    refine ⟨135798859412870014908739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 724260583535306746179941 135798859412870014908739)
                    ·
                      rfl

theorem cell23_793402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3, 1, 4].length) (baseStart_793402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793402 prefixEnd_793402 := by exact prefixLift 793402
  have htrace : WordTrace (prefixWord ++ tailWord_793402) baseStart_793402 baseEnd_793402 := by
    simpa [prefixWord, tailWord_793402, baseEnd_793402] using wordTrace_append hprefix tailTrace_793402
  have hstable : (prefixWord ++ tailWord_793402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793402).length < 2 ^ (prefixWord ++ tailWord_793402).sum := by decide
  have hdescent : baseEnd_793402 < baseStart_793402 := by decide
  rcases family_descends (prefixWord ++ tailWord_793402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793441 : List Nat := [1, 2, 3, 1, 1, 1, 2, 5, 1, 6]
def baseStart_793441 : Nat := 118140960795 + 793441 * 2 ^ 59
def prefixEnd_793441 : Nat := 4983230072969 + 3 ^ 40 * 793441 * 2
def baseEnd_793441 : Nat := 135805534661378464046179

theorem tailTrace_793441 : CollatzResearch.WordTrace tailWord_793441 prefixEnd_793441 135805534661378464046179 := by
  unfold tailWord_793441
  simp only [CollatzResearch.WordTrace]
  refine ⟨28939170718506240779492177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19292780479004160519661451 28939170718506240779492177)
  ·
    refine ⟨21704378038879680584619133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28939170718506240779492177 21704378038879680584619133)
    ·
      refine ⟨8139141764579880219232175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21704378038879680584619133 8139141764579880219232175)
      ·
        refine ⟨12208712646869820328848263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8139141764579880219232175 12208712646869820328848263)
        ·
          refine ⟨18313068970304730493272395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12208712646869820328848263 18313068970304730493272395)
          ·
            refine ⟨27469603455457095739908593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18313068970304730493272395 27469603455457095739908593)
            ·
              refine ⟨20602202591592821804931445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27469603455457095739908593 20602202591592821804931445)
              ·
                refine ⟨1931456492961827044212323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20602202591592821804931445 1931456492961827044212323)
                ·
                  refine ⟨2897184739442740566318485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1931456492961827044212323 2897184739442740566318485)
                  ·
                    refine ⟨135805534661378464046179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2897184739442740566318485 135805534661378464046179)
                    ·
                      rfl

theorem cell23_793441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_793441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793441 prefixEnd_793441 := by exact prefixLift 793441
  have htrace : WordTrace (prefixWord ++ tailWord_793441) baseStart_793441 baseEnd_793441 := by
    simpa [prefixWord, tailWord_793441, baseEnd_793441] using wordTrace_append hprefix tailTrace_793441
  have hstable : (prefixWord ++ tailWord_793441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793441).length < 2 ^ (prefixWord ++ tailWord_793441).sum := by decide
  have hdescent : baseEnd_793441 < baseStart_793441 := by decide
  rcases family_descends (prefixWord ++ tailWord_793441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793458 : List Nat := [3, 2, 1, 2, 1, 1, 3, 2, 4, 4]
def baseStart_793458 : Nat := 118140960795 + 793458 * 2 ^ 59
def prefixEnd_793458 : Nat := 4983230072969 + 3 ^ 40 * 793458 * 2
def baseEnd_793458 : Nat := 135808444385087275208653

theorem tailTrace_793458 : CollatzResearch.WordTrace tailWord_793458 prefixEnd_793458 135808444385087275208653 := by
  unfold tailWord_793458
  simp only [CollatzResearch.WordTrace]
  refine ⟨7234947689861163170715257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19293193839629768455240685 7234947689861163170715257)
  ·
    refine ⟨5426210767395872378036443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7234947689861163170715257 5426210767395872378036443)
    ·
      refine ⟨8139316151093808567054665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5426210767395872378036443 8139316151093808567054665)
      ·
        refine ⟨6104487113320356425290999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8139316151093808567054665 6104487113320356425290999)
        ·
          refine ⟨9156730669980534637936499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6104487113320356425290999 9156730669980534637936499)
          ·
            refine ⟨13735096004970801956904749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9156730669980534637936499 13735096004970801956904749)
            ·
              refine ⟨5150661001864050733839281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13735096004970801956904749 5150661001864050733839281)
              ·
                refine ⟨3862995751398038050379461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5150661001864050733839281 3862995751398038050379461)
                ·
                  refine ⟨724311703387132134446149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3862995751398038050379461 724311703387132134446149)
                  ·
                    refine ⟨135808444385087275208653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 724311703387132134446149 135808444385087275208653)
                    ·
                      rfl

theorem cell23_793458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_793458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793458 prefixEnd_793458 := by exact prefixLift 793458
  have htrace : WordTrace (prefixWord ++ tailWord_793458) baseStart_793458 baseEnd_793458 := by
    simpa [prefixWord, tailWord_793458, baseEnd_793458] using wordTrace_append hprefix tailTrace_793458
  have hstable : (prefixWord ++ tailWord_793458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793458).length < 2 ^ (prefixWord ++ tailWord_793458).sum := by decide
  have hdescent : baseEnd_793458 < baseStart_793458 := by decide
  rcases family_descends (prefixWord ++ tailWord_793458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793533 : List Nat := [1, 4, 1, 2, 4, 2, 2, 2, 1, 2, 2]
def baseStart_793533 : Nat := 118140960795 + 793533 * 2 ^ 59
def prefixEnd_793533 : Nat := 4983230072969 + 3 ^ 40 * 793533 * 2
def baseEnd_793533 : Nat := 407463844204349032188115

theorem tailTrace_793533 : CollatzResearch.WordTrace tailWord_793533 prefixEnd_793533 407463844204349032188115 := by
  unfold tailWord_793533
  simp only [CollatzResearch.WordTrace]
  refine ⟨28942526234172940491841253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19295017489448626994560835 28942526234172940491841253)
  ·
    refine ⟨5426723668907426342220235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28942526234172940491841253 5426723668907426342220235)
    ·
      refine ⟨8140085503361139513330353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5426723668907426342220235 8140085503361139513330353)
      ·
        refine ⟨6105064127520854634997765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8140085503361139513330353 6105064127520854634997765)
        ·
          refine ⟨1144699523910160244062081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6105064127520854634997765 1144699523910160244062081)
          ·
            refine ⟨858524642932620183046561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1144699523910160244062081 858524642932620183046561)
            ·
              refine ⟨643893482199465137284921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 858524642932620183046561 643893482199465137284921)
              ·
                refine ⟨482920111649598852963691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 643893482199465137284921 482920111649598852963691)
                ·
                  refine ⟨724380167474398279445537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 482920111649598852963691 724380167474398279445537)
                  ·
                    refine ⟨543285125605798709584153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 724380167474398279445537 543285125605798709584153)
                    ·
                      refine ⟨407463844204349032188115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 543285125605798709584153 407463844204349032188115)
                      ·
                        rfl

theorem cell23_793533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_793533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793533 prefixEnd_793533 := by exact prefixLift 793533
  have htrace : WordTrace (prefixWord ++ tailWord_793533) baseStart_793533 baseEnd_793533 := by
    simpa [prefixWord, tailWord_793533, baseEnd_793533] using wordTrace_append hprefix tailTrace_793533
  have hstable : (prefixWord ++ tailWord_793533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793533).length < 2 ^ (prefixWord ++ tailWord_793533).sum := by decide
  have hdescent : baseEnd_793533 < baseStart_793533 := by decide
  rcases family_descends (prefixWord ++ tailWord_793533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793548 : List Nat := [2, 2, 1, 4, 1, 1, 3, 1, 2, 6]
def baseStart_793548 : Nat := 118140960795 + 793548 * 2 ^ 59
def prefixEnd_793548 : Nat := 4983230072969 + 3 ^ 40 * 793548 * 2
def baseEnd_793548 : Nat := 135823848804722157833515

theorem tailTrace_793548 : CollatzResearch.WordTrace tailWord_793548 prefixEnd_793548 135823848804722157833515 := by
  unfold tailWord_793548
  simp only [CollatzResearch.WordTrace]
  refine ⟨14471536664559299026818649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19295382219412398702424865 14471536664559299026818649)
  ·
    refine ⟨10853652498419474270113987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14471536664559299026818649 10853652498419474270113987)
    ·
      refine ⟨16280478747629211405170981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10853652498419474270113987 16280478747629211405170981)
      ·
        refine ⟨3052589765180477138469559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16280478747629211405170981 3052589765180477138469559)
        ·
          refine ⟨4578884647770715707704339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3052589765180477138469559 4578884647770715707704339)
          ·
            refine ⟨6868326971656073561556509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4578884647770715707704339 6868326971656073561556509)
            ·
              refine ⟨2575622614371027585583691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6868326971656073561556509 2575622614371027585583691)
              ·
                refine ⟨3863433921556541378375537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2575622614371027585583691 3863433921556541378375537)
                ·
                  refine ⟨2897575441167406033781653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3863433921556541378375537 2897575441167406033781653)
                  ·
                    refine ⟨135823848804722157833515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2897575441167406033781653 135823848804722157833515)
                    ·
                      rfl

theorem cell23_793548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 2, 6].length) (baseStart_793548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793548 prefixEnd_793548 := by exact prefixLift 793548
  have htrace : WordTrace (prefixWord ++ tailWord_793548) baseStart_793548 baseEnd_793548 := by
    simpa [prefixWord, tailWord_793548, baseEnd_793548] using wordTrace_append hprefix tailTrace_793548
  have hstable : (prefixWord ++ tailWord_793548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793548).length < 2 ^ (prefixWord ++ tailWord_793548).sum := by decide
  have hdescent : baseEnd_793548 < baseStart_793548 := by decide
  rcases family_descends (prefixWord ++ tailWord_793548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793608 : List Nat := [2, 1, 3, 2, 1, 3, 1, 2, 1, 7]
def baseStart_793608 : Nat := 118140960795 + 793608 * 2 ^ 59
def prefixEnd_793608 : Nat := 4983230072969 + 3 ^ 40 * 793608 * 2
def baseEnd_793608 : Nat := 135834118417812079583423

theorem tailTrace_793608 : CollatzResearch.WordTrace tailWord_793608 prefixEnd_793608 135834118417812079583423 := by
  unfold tailWord_793608
  simp only [CollatzResearch.WordTrace]
  refine ⟨14472630854450614150410739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19296841139267485533880985 14472630854450614150410739)
  ·
    refine ⟨21708946281675921225616109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14472630854450614150410739 21708946281675921225616109)
    ·
      refine ⟨8140854855628470459606041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21708946281675921225616109 8140854855628470459606041)
      ·
        refine ⟨6105641141721352844704531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8140854855628470459606041 6105641141721352844704531)
        ·
          refine ⟨9158461712582029267056797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6105641141721352844704531 9158461712582029267056797)
          ·
            refine ⟨3434423142218260975146299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9158461712582029267056797 3434423142218260975146299)
            ·
              refine ⟨5151634713327391462719449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3434423142218260975146299 5151634713327391462719449)
              ·
                refine ⟨3863726034995543597039587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5151634713327391462719449 3863726034995543597039587)
                ·
                  refine ⟨5795589052493315395559381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3863726034995543597039587 5795589052493315395559381)
                  ·
                    refine ⟨135834118417812079583423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5795589052493315395559381 135834118417812079583423)
                    ·
                      rfl

theorem cell23_793608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_793608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793608 prefixEnd_793608 := by exact prefixLift 793608
  have htrace : WordTrace (prefixWord ++ tailWord_793608) baseStart_793608 baseEnd_793608 := by
    simpa [prefixWord, tailWord_793608, baseEnd_793608] using wordTrace_append hprefix tailTrace_793608
  have hstable : (prefixWord ++ tailWord_793608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793608).length < 2 ^ (prefixWord ++ tailWord_793608).sum := by decide
  have hdescent : baseEnd_793608 < baseStart_793608 := by decide
  rcases family_descends (prefixWord ++ tailWord_793608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793629 : List Nat := [1, 4, 2, 2, 3, 2, 1, 3, 5]
def baseStart_793629 : Nat := 118140960795 + 793629 * 2 ^ 59
def prefixEnd_793629 : Nat := 4983230072969 + 3 ^ 40 * 793629 * 2
def baseEnd_793629 : Nat := 45279237594131184065297

theorem tailTrace_793629 : CollatzResearch.WordTrace tailWord_793629 prefixEnd_793629 45279237594131184065297 := by
  unfold tailWord_793629
  simp only [CollatzResearch.WordTrace]
  refine ⟨28946027641825148887335941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19297351761216765924890627 28946027641825148887335941)
  ·
    refine ⟨5427380182842215416375489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28946027641825148887335941 5427380182842215416375489)
    ·
      refine ⟨4070535137131661562281617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5427380182842215416375489 4070535137131661562281617)
      ·
        refine ⟨3052901352848746171711213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4070535137131661562281617 3052901352848746171711213)
        ·
          refine ⟨1144838007318279814391705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3052901352848746171711213 1144838007318279814391705)
          ·
            refine ⟨858628505488709860793779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1144838007318279814391705 858628505488709860793779)
            ·
              refine ⟨1287942758233064791190669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858628505488709860793779 1287942758233064791190669)
              ·
                refine ⟨482978534337399296696501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1287942758233064791190669 482978534337399296696501)
                ·
                  refine ⟨45279237594131184065297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 482978534337399296696501 45279237594131184065297)
                  ·
                    rfl

theorem cell23_793629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3, 5].length) (baseStart_793629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793629 prefixEnd_793629 := by exact prefixLift 793629
  have htrace : WordTrace (prefixWord ++ tailWord_793629) baseStart_793629 baseEnd_793629 := by
    simpa [prefixWord, tailWord_793629, baseEnd_793629] using wordTrace_append hprefix tailTrace_793629
  have hstable : (prefixWord ++ tailWord_793629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793629).length < 2 ^ (prefixWord ++ tailWord_793629).sum := by decide
  have hdescent : baseEnd_793629 < baseStart_793629 := by decide
  rcases family_descends (prefixWord ++ tailWord_793629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793642 : List Nat := [3, 1, 4, 1, 3, 1, 1, 2, 2, 5]
def baseStart_793642 : Nat := 118140960795 + 793642 * 2 ^ 59
def prefixEnd_793642 : Nat := 4983230072969 + 3 ^ 40 * 793642 * 2
def baseEnd_793642 : Nat := 135839937865229701908371

theorem tailTrace_793642 : CollatzResearch.WordTrace tailWord_793642 prefixEnd_793642 135839937865229701908371 := by
  unfold tailWord_793642
  simp only [CollatzResearch.WordTrace]
  refine ⟨7236625447694513026889795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19297667860518701405039453 7236625447694513026889795)
  ·
    refine ⟨10854938171541769540334693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7236625447694513026889795 10854938171541769540334693)
    ·
      refine ⟨2035300907164081788812755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10854938171541769540334693 2035300907164081788812755)
      ·
        refine ⟨3052951360746122683219133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2035300907164081788812755 3052951360746122683219133)
        ·
          refine ⟨1144856760279796006207175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3052951360746122683219133 1144856760279796006207175)
          ·
            refine ⟨1717285140419694009310763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1144856760279796006207175 1717285140419694009310763)
            ·
              refine ⟨2575927710629541013966145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1717285140419694009310763 2575927710629541013966145)
              ·
                refine ⟨1931945782972155760474609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2575927710629541013966145 1931945782972155760474609)
                ·
                  refine ⟨1448959337229116820355957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1931945782972155760474609 1448959337229116820355957)
                  ·
                    refine ⟨135839937865229701908371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1448959337229116820355957 135839937865229701908371)
                    ·
                      rfl

theorem cell23_793642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_793642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793642 prefixEnd_793642 := by exact prefixLift 793642
  have htrace : WordTrace (prefixWord ++ tailWord_793642) baseStart_793642 baseEnd_793642 := by
    simpa [prefixWord, tailWord_793642, baseEnd_793642] using wordTrace_append hprefix tailTrace_793642
  have hstable : (prefixWord ++ tailWord_793642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793642).length < 2 ^ (prefixWord ++ tailWord_793642).sum := by decide
  have hdescent : baseEnd_793642 < baseStart_793642 := by decide
  rcases family_descends (prefixWord ++ tailWord_793642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793652 : List Nat := [2, 5, 1, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_793652 : Nat := 118140960795 + 793652 * 2 ^ 59
def prefixEnd_793652 : Nat := 4983230072969 + 3 ^ 40 * 793652 * 2
def baseEnd_793652 : Nat := 407524948402234066600067

theorem tailTrace_793652 : CollatzResearch.WordTrace tailWord_793652 prefixEnd_793652 407524948402234066600067 := by
  unfold tailWord_793652
  simp only [CollatzResearch.WordTrace]
  refine ⟨14473433260370911907711605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19297911013827882543615473 14473433260370911907711605)
  ·
    refine ⟨1356884368159772991347963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14473433260370911907711605 1356884368159772991347963)
    ·
      refine ⟨2035326552239659487021945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1356884368159772991347963 2035326552239659487021945)
      ·
        refine ⟨1526494914179744615266459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2035326552239659487021945 1526494914179744615266459)
        ·
          refine ⟨2289742371269616922899689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1526494914179744615266459 2289742371269616922899689)
          ·
            refine ⟨1717306778452212692174767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2289742371269616922899689 1717306778452212692174767)
            ·
              refine ⟨2575960167678319038262151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1717306778452212692174767 2575960167678319038262151)
              ·
                refine ⟨3863940251517478557393227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2575960167678319038262151 3863940251517478557393227)
                ·
                  refine ⟨5795910377276217836089841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3863940251517478557393227 5795910377276217836089841)
                  ·
                    refine ⟨4346932782957163377067381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5795910377276217836089841 4346932782957163377067381)
                    ·
                      refine ⟨407524948402234066600067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4346932782957163377067381 407524948402234066600067)
                      ·
                        rfl

theorem cell23_793652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_793652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793652 prefixEnd_793652 := by exact prefixLift 793652
  have htrace : WordTrace (prefixWord ++ tailWord_793652) baseStart_793652 baseEnd_793652 := by
    simpa [prefixWord, tailWord_793652, baseEnd_793652] using wordTrace_append hprefix tailTrace_793652
  have hstable : (prefixWord ++ tailWord_793652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793652).length < 2 ^ (prefixWord ++ tailWord_793652).sum := by decide
  have hdescent : baseEnd_793652 < baseStart_793652 := by decide
  rcases family_descends (prefixWord ++ tailWord_793652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793658 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6]
def baseStart_793658 : Nat := 118140960795 + 793658 * 2 ^ 59
def prefixEnd_793658 : Nat := 4983230072969 + 3 ^ 40 * 793658 * 2
def baseEnd_793658 : Nat := 407528029286161043125039

theorem tailTrace_793658 : CollatzResearch.WordTrace tailWord_793658 prefixEnd_793658 407528029286161043125039 := by
  unfold tailWord_793658
  simp only [CollatzResearch.WordTrace]
  refine ⟨7236771339680021710035407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19298056905813391226761085 7236771339680021710035407)
  ·
    refine ⟨10855157009520032565053111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7236771339680021710035407 10855157009520032565053111)
    ·
      refine ⟨16282735514280048847579667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10855157009520032565053111 16282735514280048847579667)
      ·
        refine ⟨24424103271420073271369501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16282735514280048847579667 24424103271420073271369501)
        ·
          refine ⟨9159038726782527476763563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24424103271420073271369501 9159038726782527476763563)
          ·
            refine ⟨13738558090173791215145345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9159038726782527476763563 13738558090173791215145345)
            ·
              refine ⟨10303918567630343411359009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13738558090173791215145345 10303918567630343411359009)
              ·
                refine ⟨7727938925722757558519257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10303918567630343411359009 7727938925722757558519257)
                ·
                  refine ⟨5795954194292068168889443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7727938925722757558519257 5795954194292068168889443)
                  ·
                    refine ⟨8693931291438102253334165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5795954194292068168889443 8693931291438102253334165)
                    ·
                      refine ⟨407528029286161043125039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8693931291438102253334165 407528029286161043125039)
                      ·
                        rfl

theorem cell23_793658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_793658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_793658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_793658 prefixEnd_793658 := by exact prefixLift 793658
  have htrace : WordTrace (prefixWord ++ tailWord_793658) baseStart_793658 baseEnd_793658 := by
    simpa [prefixWord, tailWord_793658, baseEnd_793658] using wordTrace_append hprefix tailTrace_793658
  have hstable : (prefixWord ++ tailWord_793658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793658).length < 2 ^ (prefixWord ++ tailWord_793658).sum := by decide
  have hdescent : baseEnd_793658 < baseStart_793658 := by decide
  rcases family_descends (prefixWord ++ tailWord_793658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
