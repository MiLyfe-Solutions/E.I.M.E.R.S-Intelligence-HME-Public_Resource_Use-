import V185TrunkScan22Chunk242

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2166893 : List Nat := [1, 5, 1, 1, 2, 1, 1, 6, 4]
def baseStart_2166893 : Nat := 118140960795 + 2166893 * 2 ^ 59
def prefixEnd_2166893 : Nat := 4983230072969 + 3 ^ 40 * 2166893 * 2
def baseEnd_2166893 : Nat := 247257252414021278860477

theorem tailTrace_2166893 : CollatzResearch.WordTrace tailWord_2166893 prefixEnd_2166893 247257252414021278860477 := by
  unfold tailWord_2166893
  simp only [CollatzResearch.WordTrace]
  refine ⟨79033080538724211706265333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52688720359149474470843555 79033080538724211706265333)
  ·
    refine ⟨7409351300505394847462375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79033080538724211706265333 7409351300505394847462375)
    ·
      refine ⟨11114026950758092271193563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7409351300505394847462375 11114026950758092271193563)
      ·
        refine ⟨16671040426137138406790345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11114026950758092271193563 16671040426137138406790345)
        ·
          refine ⟨12503280319602853805092759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16671040426137138406790345 12503280319602853805092759)
          ·
            refine ⟨18754920479404280707639139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12503280319602853805092759 18754920479404280707639139)
            ·
              refine ⟨28132380719106421061458709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18754920479404280707639139 28132380719106421061458709)
              ·
                refine ⟨1318705346208113487255877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28132380719106421061458709 1318705346208113487255877)
                ·
                  refine ⟨247257252414021278860477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1318705346208113487255877 247257252414021278860477)
                  ·
                    rfl

theorem cell22_2166893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_2166893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166893 prefixEnd_2166893 := by exact prefixLift 2166893
  have htrace : WordTrace (prefixWord ++ tailWord_2166893) baseStart_2166893 baseEnd_2166893 := by
    simpa [prefixWord, tailWord_2166893, baseEnd_2166893] using wordTrace_append hprefix tailTrace_2166893
  have hstable : (prefixWord ++ tailWord_2166893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166893).length < 2 ^ (prefixWord ++ tailWord_2166893).sum := by decide
  have hdescent : baseEnd_2166893 < baseStart_2166893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166904 : List Nat := [2, 1, 2, 1, 1, 1, 3, 11]
def baseStart_2166904 : Nat := 118140960795 + 2166904 * 2 ^ 59
def prefixEnd_2166904 : Nat := 4983230072969 + 3 ^ 40 * 2166904 * 2
def baseEnd_2166904 : Nat := 82419502529651497172933

theorem tailTrace_2166904 : CollatzResearch.WordTrace tailWord_2166904 prefixEnd_2166904 82419502529651497172933 := by
  unfold tailWord_2166904
  simp only [CollatzResearch.WordTrace]
  refine ⟨39516740870842180292457883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52688987827789573723277177 39516740870842180292457883)
  ·
    refine ⟨59275111306263270438686825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39516740870842180292457883 59275111306263270438686825)
    ·
      refine ⟨44456333479697452829015119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59275111306263270438686825 44456333479697452829015119)
      ·
        refine ⟨66684500219546179243522679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44456333479697452829015119 66684500219546179243522679)
        ·
          refine ⟨100026750329319268865284019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66684500219546179243522679 100026750329319268865284019)
          ·
            refine ⟨150040125493978903297926029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100026750329319268865284019 150040125493978903297926029)
            ·
              refine ⟨56265047060242088736722261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150040125493978903297926029 56265047060242088736722261)
              ·
                refine ⟨82419502529651497172933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 56265047060242088736722261 82419502529651497172933)
                ·
                  rfl

theorem cell22_2166904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 11].length) (baseStart_2166904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166904 prefixEnd_2166904 := by exact prefixLift 2166904
  have htrace : WordTrace (prefixWord ++ tailWord_2166904) baseStart_2166904 baseEnd_2166904 := by
    simpa [prefixWord, tailWord_2166904, baseEnd_2166904] using wordTrace_append hprefix tailTrace_2166904
  have hstable : (prefixWord ++ tailWord_2166904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166904).length < 2 ^ (prefixWord ++ tailWord_2166904).sum := by decide
  have hdescent : baseEnd_2166904 < baseStart_2166904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166908 : List Nat := [2, 2, 2, 1, 1, 6, 1, 1, 1, 5]
def baseStart_2166908 : Nat := 118140960795 + 2166908 * 2 ^ 59
def prefixEnd_2166908 : Nat := 4983230072969 + 3 ^ 40 * 2166908 * 2
def baseEnd_2166908 : Nat := 741776892048608797456385

theorem tailTrace_2166908 : CollatzResearch.WordTrace tailWord_2166908 prefixEnd_2166908 741776892048608797456385 := by
  unfold tailWord_2166908
  simp only [CollatzResearch.WordTrace]
  refine ⟨39516813816834934634030689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52689085089113246178707585 39516813816834934634030689)
  ·
    refine ⟨29637610362626200975523017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39516813816834934634030689 29637610362626200975523017)
    ·
      refine ⟨22228207771969650731642263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29637610362626200975523017 22228207771969650731642263)
      ·
        refine ⟨33342311657954476097463395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22228207771969650731642263 33342311657954476097463395)
        ·
          refine ⟨50013467486931714146195093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33342311657954476097463395 50013467486931714146195093)
          ·
            refine ⟨2344381288449924100602895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 50013467486931714146195093 2344381288449924100602895)
            ·
              refine ⟨3516571932674886150904343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2344381288449924100602895 3516571932674886150904343)
              ·
                refine ⟨5274857899012329226356515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3516571932674886150904343 5274857899012329226356515)
                ·
                  refine ⟨7912286848518493839534773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5274857899012329226356515 7912286848518493839534773)
                  ·
                    refine ⟨741776892048608797456385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7912286848518493839534773 741776892048608797456385)
                    ·
                      rfl

theorem cell22_2166908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_2166908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166908 prefixEnd_2166908 := by exact prefixLift 2166908
  have htrace : WordTrace (prefixWord ++ tailWord_2166908) baseStart_2166908 baseEnd_2166908 := by
    simpa [prefixWord, tailWord_2166908, baseEnd_2166908] using wordTrace_append hprefix tailTrace_2166908
  have hstable : (prefixWord ++ tailWord_2166908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166908).length < 2 ^ (prefixWord ++ tailWord_2166908).sum := by decide
  have hdescent : baseEnd_2166908 < baseStart_2166908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2166938 : List Nat := [3, 1, 1, 5, 2, 2, 8]
def baseStart_2166938 : Nat := 118140960795 + 2166938 * 2 ^ 59
def prefixEnd_2166938 : Nat := 4983230072969 + 3 ^ 40 * 2166938 * 2
def baseEnd_2166938 : Nat := 27473598580062915526159

theorem tailTrace_2166938 : CollatzResearch.WordTrace tailWord_2166938 prefixEnd_2166938 27473598580062915526159 := by
  unfold tailWord_2166938
  simp only [CollatzResearch.WordTrace]
  refine ⟨19758680455890296097913367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52689814549040789594435645 19758680455890296097913367)
  ·
    refine ⟨29638020683835444146870051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19758680455890296097913367 29638020683835444146870051)
    ·
      refine ⟨44457031025753166220305077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29638020683835444146870051 44457031025753166220305077)
      ·
        refine ⟨4167846658664359333153601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44457031025753166220305077 4167846658664359333153601)
        ·
          refine ⟨3125884993998269499865201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4167846658664359333153601 3125884993998269499865201)
          ·
            refine ⟨2344413745498702124898901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3125884993998269499865201 2344413745498702124898901)
            ·
              refine ⟨27473598580062915526159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2344413745498702124898901 27473598580062915526159)
              ·
                rfl

theorem cell22_2166938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 8].length) (baseStart_2166938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2166938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2166938 prefixEnd_2166938 := by exact prefixLift 2166938
  have htrace : WordTrace (prefixWord ++ tailWord_2166938) baseStart_2166938 baseEnd_2166938 := by
    simpa [prefixWord, tailWord_2166938, baseEnd_2166938] using wordTrace_append hprefix tailTrace_2166938
  have hstable : (prefixWord ++ tailWord_2166938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2166938).length < 2 ^ (prefixWord ++ tailWord_2166938).sum := by decide
  have hdescent : baseEnd_2166938 < baseStart_2166938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2166938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167013 : List Nat := [1, 3, 1, 4, 2, 1, 1, 2, 3, 4]
def baseStart_2167013 : Nat := 118140960795 + 2167013 * 2 ^ 59
def prefixEnd_2167013 : Nat := 4983230072969 + 3 ^ 40 * 2167013 * 2
def baseEnd_2167013 : Nat := 741812835694423523581063

theorem tailTrace_2167013 : CollatzResearch.WordTrace tailWord_2167013 prefixEnd_2167013 741812835694423523581063 := by
  unfold tailWord_2167013
  simp only [CollatzResearch.WordTrace]
  refine ⟨79037457298289472200633693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52691638198859648133755795 79037457298289472200633693)
  ·
    refine ⟨29639046486858552075237635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79037457298289472200633693 29639046486858552075237635)
    ·
      refine ⟨44458569730287828112856453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29639046486858552075237635 44458569730287828112856453)
      ·
        refine ⟨8335981824428967771160585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44458569730287828112856453 8335981824428967771160585)
        ·
          refine ⟨6251986368321725828370439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8335981824428967771160585 6251986368321725828370439)
          ·
            refine ⟨9377979552482588742555659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6251986368321725828370439 9377979552482588742555659)
            ·
              refine ⟨14066969328723883113833489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9377979552482588742555659 14066969328723883113833489)
              ·
                refine ⟨10550226996542912335375117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14066969328723883113833489 10550226996542912335375117)
                ·
                  refine ⟨3956335123703592125765669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10550226996542912335375117 3956335123703592125765669)
                  ·
                    refine ⟨741812835694423523581063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3956335123703592125765669 741812835694423523581063)
                    ·
                      rfl

theorem cell22_2167013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_2167013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2167013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2167013 prefixEnd_2167013 := by exact prefixLift 2167013
  have htrace : WordTrace (prefixWord ++ tailWord_2167013) baseStart_2167013 baseEnd_2167013 := by
    simpa [prefixWord, tailWord_2167013, baseEnd_2167013] using wordTrace_append hprefix tailTrace_2167013
  have hstable : (prefixWord ++ tailWord_2167013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167013).length < 2 ^ (prefixWord ++ tailWord_2167013).sum := by decide
  have hdescent : baseEnd_2167013 < baseStart_2167013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167043 : List Nat := [1, 1, 1, 3, 2, 3, 2, 2, 4, 3]
def baseStart_2167043 : Nat := 118140960795 + 2167043 * 2 ^ 59
def prefixEnd_2167043 : Nat := 4983230072969 + 3 ^ 40 * 2167043 * 2
def baseEnd_2167043 : Nat := 741823105307513445330971

theorem tailTrace_2167043 : CollatzResearch.WordTrace tailWord_2167043 prefixEnd_2167043 741823105307513445330971 := by
  unfold tailWord_2167043
  simp only [CollatzResearch.WordTrace]
  refine ⟨79038551488180787324225783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52692367658787191549483855 79038551488180787324225783)
  ·
    refine ⟨118557827232271180986338675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79038551488180787324225783 118557827232271180986338675)
    ·
      refine ⟨177836740848406771479508013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118557827232271180986338675 177836740848406771479508013)
      ·
        refine ⟨66688777818152539304815505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177836740848406771479508013 66688777818152539304815505)
        ·
          refine ⟨50016583363614404478611629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66688777818152539304815505 50016583363614404478611629)
          ·
            refine ⟨18756218761355401679479361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50016583363614404478611629 18756218761355401679479361)
            ·
              refine ⟨14067164071016551259609521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18756218761355401679479361 14067164071016551259609521)
              ·
                refine ⟨10550373053262413444707141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14067164071016551259609521 10550373053262413444707141)
                ·
                  refine ⟨1978194947486702520882589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10550373053262413444707141 1978194947486702520882589)
                  ·
                    refine ⟨741823105307513445330971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1978194947486702520882589 741823105307513445330971)
                    ·
                      rfl

theorem cell22_2167043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4, 3].length) (baseStart_2167043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2167043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2167043 prefixEnd_2167043 := by exact prefixLift 2167043
  have htrace : WordTrace (prefixWord ++ tailWord_2167043) baseStart_2167043 baseEnd_2167043 := by
    simpa [prefixWord, tailWord_2167043, baseEnd_2167043] using wordTrace_append hprefix tailTrace_2167043
  have hstable : (prefixWord ++ tailWord_2167043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167043).length < 2 ^ (prefixWord ++ tailWord_2167043).sum := by decide
  have hdescent : baseEnd_2167043 < baseStart_2167043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167047 : List Nat := [1, 1, 4, 5, 1, 1, 1, 3, 1, 4]
def baseStart_2167047 : Nat := 118140960795 + 2167047 * 2 ^ 59
def prefixEnd_2167047 : Nat := 4983230072969 + 3 ^ 40 * 2167047 * 2
def baseEnd_2167047 : Nat := 741824474589258768230959

theorem tailTrace_2167047 : CollatzResearch.WordTrace tailWord_2167047 prefixEnd_2167047 741824474589258768230959 := by
  unfold tailWord_2167047
  simp only [CollatzResearch.WordTrace]
  refine ⟨79038697380166296007371395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52692464920110864004914263 79038697380166296007371395)
  ·
    refine ⟨118558046070249444011057093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79038697380166296007371395 118558046070249444011057093)
    ·
      refine ⟨22229633638171770752073205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118558046070249444011057093 22229633638171770752073205)
      ·
        refine ⟨2084028153578603508006863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22229633638171770752073205 2084028153578603508006863)
        ·
          refine ⟨3126042230367905262010295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2084028153578603508006863 3126042230367905262010295)
          ·
            refine ⟨4689063345551857893015443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3126042230367905262010295 4689063345551857893015443)
            ·
              refine ⟨7033595018327786839523165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4689063345551857893015443 7033595018327786839523165)
              ·
                refine ⟨2637598131872920064821187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7033595018327786839523165 2637598131872920064821187)
                ·
                  refine ⟨3956397197809380097231781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2637598131872920064821187 3956397197809380097231781)
                  ·
                    refine ⟨741824474589258768230959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3956397197809380097231781 741824474589258768230959)
                    ·
                      rfl

theorem cell22_2167047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_2167047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2167047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2167047 prefixEnd_2167047 := by exact prefixLift 2167047
  have htrace : WordTrace (prefixWord ++ tailWord_2167047) baseStart_2167047 baseEnd_2167047 := by
    simpa [prefixWord, tailWord_2167047, baseEnd_2167047] using wordTrace_append hprefix tailTrace_2167047
  have hstable : (prefixWord ++ tailWord_2167047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167047).length < 2 ^ (prefixWord ++ tailWord_2167047).sum := by decide
  have hdescent : baseEnd_2167047 < baseStart_2167047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167077 : List Nat := [1, 3, 1, 2, 6, 1, 1, 1, 1, 5]
def baseStart_2167077 : Nat := 118140960795 + 2167077 * 2 ^ 59
def prefixEnd_2167077 : Nat := 4983230072969 + 3 ^ 40 * 2167077 * 2
def baseEnd_2167077 : Nat := 741834744202348689980867

theorem tailTrace_2167077 : CollatzResearch.WordTrace tailWord_2167077 prefixEnd_2167077 741834744202348689980867 := by
  unfold tailWord_2167077
  simp only [CollatzResearch.WordTrace]
  refine ⟨79039791570057611130963485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52693194380038407420642323 79039791570057611130963485)
  ·
    refine ⟨29639921838771604174111307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79039791570057611130963485 29639921838771604174111307)
    ·
      refine ⟨44459882758157406261166961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29639921838771604174111307 44459882758157406261166961)
      ·
        refine ⟨33344912068618054695875221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44459882758157406261166961 33344912068618054695875221)
        ·
          refine ⟨1563042753216471313869151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33344912068618054695875221 1563042753216471313869151)
          ·
            refine ⟨2344564129824706970803727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1563042753216471313869151 2344564129824706970803727)
            ·
              refine ⟨3516846194737060456205591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2344564129824706970803727 3516846194737060456205591)
              ·
                refine ⟨5275269292105590684308387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3516846194737060456205591 5275269292105590684308387)
                ·
                  refine ⟨7912903938158386026462581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5275269292105590684308387 7912903938158386026462581)
                  ·
                    refine ⟨741834744202348689980867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7912903938158386026462581 741834744202348689980867)
                    ·
                      rfl

theorem cell22_2167077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 1, 5].length) (baseStart_2167077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2167077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2167077 prefixEnd_2167077 := by exact prefixLift 2167077
  have htrace : WordTrace (prefixWord ++ tailWord_2167077) baseStart_2167077 baseEnd_2167077 := by
    simpa [prefixWord, tailWord_2167077, baseEnd_2167077] using wordTrace_append hprefix tailTrace_2167077
  have hstable : (prefixWord ++ tailWord_2167077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167077).length < 2 ^ (prefixWord ++ tailWord_2167077).sum := by decide
  have hdescent : baseEnd_2167077 < baseStart_2167077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167088 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 5, 3]
def baseStart_2167088 : Nat := 118140960795 + 2167088 * 2 ^ 59
def prefixEnd_2167088 : Nat := 4983230072969 + 3 ^ 40 * 2167088 * 2
def baseEnd_2167088 : Nat := 741838509727148327955833

theorem tailTrace_2167088 : CollatzResearch.WordTrace tailWord_2167088 prefixEnd_2167088 741838509727148327955833 := by
  unfold tailWord_2167088
  simp only [CollatzResearch.WordTrace]
  refine ⟨39520096386508880004806959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52693461848678506673075945 39520096386508880004806959)
  ·
    refine ⟨59280144579763320007210439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39520096386508880004806959 59280144579763320007210439)
    ·
      refine ⟨88920216869644980010815659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59280144579763320007210439 88920216869644980010815659)
      ·
        refine ⟨133380325304467470016223489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88920216869644980010815659 133380325304467470016223489)
        ·
          refine ⟨100035243978350602512167617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133380325304467470016223489 100035243978350602512167617)
          ·
            refine ⟨75026432983762951884125713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100035243978350602512167617 75026432983762951884125713)
            ·
              refine ⟨56269824737822213913094285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75026432983762951884125713 56269824737822213913094285)
              ·
                refine ⟨21101184276683330217410357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56269824737822213913094285 21101184276683330217410357)
                ·
                  refine ⟨1978236025939062207882221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21101184276683330217410357 1978236025939062207882221)
                  ·
                    refine ⟨741838509727148327955833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1978236025939062207882221 741838509727148327955833)
                    ·
                      rfl

theorem cell22_2167088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 5, 3].length) (baseStart_2167088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2167088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2167088 prefixEnd_2167088 := by exact prefixLift 2167088
  have htrace : WordTrace (prefixWord ++ tailWord_2167088) baseStart_2167088 baseEnd_2167088 := by
    simpa [prefixWord, tailWord_2167088, baseEnd_2167088] using wordTrace_append hprefix tailTrace_2167088
  have hstable : (prefixWord ++ tailWord_2167088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167088).length < 2 ^ (prefixWord ++ tailWord_2167088).sum := by decide
  have hdescent : baseEnd_2167088 < baseStart_2167088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167122 : List Nat := [3, 2, 2, 1, 1, 1, 2, 6, 1, 3]
def baseStart_2167122 : Nat := 118140960795 + 2167122 * 2 ^ 59
def prefixEnd_2167122 : Nat := 4983230072969 + 3 ^ 40 * 2167122 * 2
def baseEnd_2167122 : Nat := 741850148621983572605729

theorem tailTrace_2167122 : CollatzResearch.WordTrace tailWord_2167122 prefixEnd_2167122 741850148621983572605729 := by
  unfold tailWord_2167122
  simp only [CollatzResearch.WordTrace]
  refine ⟨19760358213723645954087905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52694288569929722544234413 19760358213723645954087905)
  ·
    refine ⟨14820268660292734465565929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19760358213723645954087905 14820268660292734465565929)
    ·
      refine ⟨11115201495219550849174447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14820268660292734465565929 11115201495219550849174447)
      ·
        refine ⟨16672802242829326273761671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11115201495219550849174447 16672802242829326273761671)
        ·
          refine ⟨25009203364243989410642507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16672802242829326273761671 25009203364243989410642507)
          ·
            refine ⟨37513805046365984115963761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25009203364243989410642507 37513805046365984115963761)
            ·
              refine ⟨28135353784774488086972821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37513805046365984115963761 28135353784774488086972821)
              ·
                refine ⟨1318844708661304129076851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28135353784774488086972821 1318844708661304129076851)
                ·
                  refine ⟨1978267062991956193615277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1318844708661304129076851 1978267062991956193615277)
                  ·
                    refine ⟨741850148621983572605729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1978267062991956193615277 741850148621983572605729)
                    ·
                      rfl

theorem cell22_2167122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_2167122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2167122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2167122 prefixEnd_2167122 := by exact prefixLift 2167122
  have htrace : WordTrace (prefixWord ++ tailWord_2167122) baseStart_2167122 baseEnd_2167122 := by
    simpa [prefixWord, tailWord_2167122, baseEnd_2167122] using wordTrace_append hprefix tailTrace_2167122
  have hstable : (prefixWord ++ tailWord_2167122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167122).length < 2 ^ (prefixWord ++ tailWord_2167122).sum := by decide
  have hdescent : baseEnd_2167122 < baseStart_2167122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167135 : List Nat := [1, 1, 2, 3, 1, 2, 6, 1, 5]
def baseStart_2167135 : Nat := 118140960795 + 2167135 * 2 ^ 59
def prefixEnd_2167135 : Nat := 4983230072969 + 3 ^ 40 * 2167135 * 2
def baseEnd_2167135 : Nat := 247284866262551957343563

theorem tailTrace_2167135 : CollatzResearch.WordTrace tailWord_2167135 prefixEnd_2167135 247284866262551957343563 := by
  unfold tailWord_2167135
  simp only [CollatzResearch.WordTrace]
  refine ⟨79041907003847487036574859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52694604669231658024383239 79041907003847487036574859)
  ·
    refine ⟨118562860505771230554862289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79041907003847487036574859 118562860505771230554862289)
    ·
      refine ⟨88922145379328422916146717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118562860505771230554862289 88922145379328422916146717)
      ·
        refine ⟨33345804517248158593555019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88922145379328422916146717 33345804517248158593555019)
        ·
          refine ⟨50018706775872237890332529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33345804517248158593555019 50018706775872237890332529)
          ·
            refine ⟨37514030081904178417749397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50018706775872237890332529 37514030081904178417749397)
            ·
              refine ⟨1758470160089258363332003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37514030081904178417749397 1758470160089258363332003)
              ·
                refine ⟨2637705240133887544998005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1758470160089258363332003 2637705240133887544998005)
                ·
                  refine ⟨247284866262551957343563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2637705240133887544998005 247284866262551957343563)
                  ·
                    rfl

theorem cell22_2167135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 5].length) (baseStart_2167135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2167135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2167135 prefixEnd_2167135 := by exact prefixLift 2167135
  have htrace : WordTrace (prefixWord ++ tailWord_2167135) baseStart_2167135 baseEnd_2167135 := by
    simpa [prefixWord, tailWord_2167135, baseEnd_2167135] using wordTrace_append hprefix tailTrace_2167135
  have hstable : (prefixWord ++ tailWord_2167135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167135).length < 2 ^ (prefixWord ++ tailWord_2167135).sum := by decide
  have hdescent : baseEnd_2167135 < baseStart_2167135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167193 : List Nat := [1, 2, 1, 2, 1, 4, 2, 2, 1, 6]
def baseStart_2167193 : Nat := 118140960795 + 2167193 * 2 ^ 59
def prefixEnd_2167193 : Nat := 4983230072969 + 3 ^ 40 * 2167193 * 2
def baseEnd_2167193 : Nat := 741874453372963054080511

theorem tailTrace_2167193 : CollatzResearch.WordTrace tailWord_2167193 prefixEnd_2167193 741874453372963054080511 := by
  unfold tailWord_2167193
  simp only [CollatzResearch.WordTrace]
  refine ⟨79044022437637362942186233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52696014958424908628124155 79044022437637362942186233)
  ·
    refine ⟨59283016828228022206639675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79044022437637362942186233 59283016828228022206639675)
    ·
      refine ⟨88924525242342033309959513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59283016828228022206639675 88924525242342033309959513)
      ·
        refine ⟨66693393931756524982469635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88924525242342033309959513 66693393931756524982469635)
        ·
          refine ⟨100040090897634787473704453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66693393931756524982469635 100040090897634787473704453)
          ·
            refine ⟨18757517043306522651319585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100040090897634787473704453 18757517043306522651319585)
            ·
              refine ⟨14068137782479891988489689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18757517043306522651319585 14068137782479891988489689)
              ·
                refine ⟨10551103336859918991367267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14068137782479891988489689 10551103336859918991367267)
                ·
                  refine ⟨15826655005289878487050901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10551103336859918991367267 15826655005289878487050901)
                  ·
                    refine ⟨741874453372963054080511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15826655005289878487050901 741874453372963054080511)
                    ·
                      rfl

theorem cell22_2167193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 6].length) (baseStart_2167193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2167193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2167193 prefixEnd_2167193 := by exact prefixLift 2167193
  have htrace : WordTrace (prefixWord ++ tailWord_2167193) baseStart_2167193 baseEnd_2167193 := by
    simpa [prefixWord, tailWord_2167193, baseEnd_2167193] using wordTrace_append hprefix tailTrace_2167193
  have hstable : (prefixWord ++ tailWord_2167193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167193).length < 2 ^ (prefixWord ++ tailWord_2167193).sum := by decide
  have hdescent : baseEnd_2167193 < baseStart_2167193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167229 : List Nat := [1, 4, 1, 2, 2, 4, 1, 2, 2, 3]
def baseStart_2167229 : Nat := 118140960795 + 2167229 * 2 ^ 59
def prefixEnd_2167229 : Nat := 4983230072969 + 3 ^ 40 * 2167229 * 2
def baseEnd_2167229 : Nat := 741886776908670960180401

theorem tailTrace_2167229 : CollatzResearch.WordTrace tailWord_2167229 prefixEnd_2167229 741886776908670960180401 := by
  unfold tailWord_2167229
  simp only [CollatzResearch.WordTrace]
  refine ⟨79045335465506941090496741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52696890310337960726997827 79045335465506941090496741)
  ·
    refine ⟨14821000399782551454468139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79045335465506941090496741 14821000399782551454468139)
    ·
      refine ⟨22231500599673827181702209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14821000399782551454468139 22231500599673827181702209)
      ·
        refine ⟨16673625449755370386276657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22231500599673827181702209 16673625449755370386276657)
        ·
          refine ⟨12505219087316527789707493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16673625449755370386276657 12505219087316527789707493)
          ·
            refine ⟨2344728578871848960570155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12505219087316527789707493 2344728578871848960570155)
            ·
              refine ⟨3517092868307773440855233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2344728578871848960570155 3517092868307773440855233)
              ·
                refine ⟨2637819651230830080641425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3517092868307773440855233 2637819651230830080641425)
                ·
                  refine ⟨1978364738423122560481069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2637819651230830080641425 1978364738423122560481069)
                  ·
                    refine ⟨741886776908670960180401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1978364738423122560481069 741886776908670960180401)
                    ·
                      rfl

theorem cell22_2167229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_2167229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2167229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2167229 prefixEnd_2167229 := by exact prefixLift 2167229
  have htrace : WordTrace (prefixWord ++ tailWord_2167229) baseStart_2167229 baseEnd_2167229 := by
    simpa [prefixWord, tailWord_2167229, baseEnd_2167229] using wordTrace_append hprefix tailTrace_2167229
  have hstable : (prefixWord ++ tailWord_2167229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167229).length < 2 ^ (prefixWord ++ tailWord_2167229).sum := by decide
  have hdescent : baseEnd_2167229 < baseStart_2167229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167360 : List Nat := [2, 1, 1, 2, 2, 2, 5, 7]
def baseStart_2167360 : Nat := 118140960795 + 2167360 * 2 ^ 59
def prefixEnd_2167360 : Nat := 4983230072969 + 3 ^ 40 * 2167360 * 2
def baseEnd_2167360 : Nat := 82436846765092253906111

theorem tailTrace_2167360 : CollatzResearch.WordTrace tailWord_2167360 prefixEnd_2167360 82436846765092253906111 := by
  unfold tailWord_2167360
  simp only [CollatzResearch.WordTrace]
  refine ⟨39525056714016175231757767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52700075618688233642343689 39525056714016175231757767)
  ·
    refine ⟨59287585071024262847636651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39525056714016175231757767 59287585071024262847636651)
    ·
      refine ⟨88931377606536394271454977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59287585071024262847636651 88931377606536394271454977)
      ·
        refine ⟨66698533204902295703591233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88931377606536394271454977 66698533204902295703591233)
        ·
          refine ⟨50023899903676721777693425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66698533204902295703591233 50023899903676721777693425)
          ·
            refine ⟨37517924927757541333270069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50023899903676721777693425 37517924927757541333270069)
            ·
              refine ⟨3517305461977269499994069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37517924927757541333270069 3517305461977269499994069)
              ·
                refine ⟨82436846765092253906111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3517305461977269499994069 82436846765092253906111)
                ·
                  rfl

theorem cell22_2167360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 7].length) (baseStart_2167360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2167360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2167360 prefixEnd_2167360 := by exact prefixLift 2167360
  have htrace : WordTrace (prefixWord ++ tailWord_2167360) baseStart_2167360 baseEnd_2167360 := by
    simpa [prefixWord, tailWord_2167360, baseEnd_2167360] using wordTrace_append hprefix tailTrace_2167360
  have hstable : (prefixWord ++ tailWord_2167360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167360).length < 2 ^ (prefixWord ++ tailWord_2167360).sum := by decide
  have hdescent : baseEnd_2167360 < baseStart_2167360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167377 : List Nat := [1, 2, 2, 1, 3, 4, 3, 6]
def baseStart_2167377 : Nat := 118140960795 + 2167377 * 2 ^ 59
def prefixEnd_2167377 : Nat := 4983230072969 + 3 ^ 40 * 2167377 * 2
def baseEnd_2167377 : Nat := 82437493370360878608883

theorem tailTrace_2167377 : CollatzResearch.WordTrace tailWord_2167377 prefixEnd_2167377 82437493370360878608883 := by
  unfold tailWord_2167377
  simp only [CollatzResearch.WordTrace]
  refine ⟨79050733468970762366884385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52700488979313841577922923 79050733468970762366884385)
  ·
    refine ⟨59288050101728071775163289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79050733468970762366884385 59288050101728071775163289)
    ·
      refine ⟨44466037576296053831372467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59288050101728071775163289 44466037576296053831372467)
      ·
        refine ⟨66699056364444080747058701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44466037576296053831372467 66699056364444080747058701)
        ·
          refine ⟨25012146136666530280147013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66699056364444080747058701 25012146136666530280147013)
          ·
            refine ⟨4689777400624974427527565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25012146136666530280147013 4689777400624974427527565)
            ·
              refine ⟨1758666525234365410322837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4689777400624974427527565 1758666525234365410322837)
              ·
                refine ⟨82437493370360878608883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1758666525234365410322837 82437493370360878608883)
                ·
                  rfl

theorem cell22_2167377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 6].length) (baseStart_2167377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2167377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2167377 prefixEnd_2167377 := by exact prefixLift 2167377
  have htrace : WordTrace (prefixWord ++ tailWord_2167377) baseStart_2167377 baseEnd_2167377 := by
    simpa [prefixWord, tailWord_2167377, baseEnd_2167377] using wordTrace_append hprefix tailTrace_2167377
  have hstable : (prefixWord ++ tailWord_2167377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167377).length < 2 ^ (prefixWord ++ tailWord_2167377).sum := by decide
  have hdescent : baseEnd_2167377 < baseStart_2167377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167394 : List Nat := [3, 3, 2, 3, 1, 1, 9]
def baseStart_2167394 : Nat := 118140960795 + 2167394 * 2 ^ 59
def prefixEnd_2167394 : Nat := 4983230072969 + 3 ^ 40 * 2167394 * 2
def baseEnd_2167394 : Nat := 27479379991876501103885

theorem tailTrace_2167394 : CollatzResearch.WordTrace tailWord_2167394 prefixEnd_2167394 27479379991876501103885 := by
  unfold tailWord_2167394
  simp only [CollatzResearch.WordTrace]
  refine ⟨19762838377477293567563309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52700902339939449513502157 19762838377477293567563309)
  ·
    refine ⟨7411064391553985087836241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19762838377477293567563309 7411064391553985087836241)
    ·
      refine ⟨5558298293665488815877181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7411064391553985087836241 5558298293665488815877181)
      ·
        refine ⟨2084361860124558305953943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5558298293665488815877181 2084361860124558305953943)
        ·
          refine ⟨3126542790186837458930915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2084361860124558305953943 3126542790186837458930915)
          ·
            refine ⟨4689814185280256188396373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3126542790186837458930915 4689814185280256188396373)
            ·
              refine ⟨27479379991876501103885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4689814185280256188396373 27479379991876501103885)
              ·
                rfl

theorem cell22_2167394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 9].length) (baseStart_2167394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2167394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2167394 prefixEnd_2167394 := by exact prefixLift 2167394
  have htrace : WordTrace (prefixWord ++ tailWord_2167394) baseStart_2167394 baseEnd_2167394 := by
    simpa [prefixWord, tailWord_2167394, baseEnd_2167394] using wordTrace_append hprefix tailTrace_2167394
  have hstable : (prefixWord ++ tailWord_2167394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167394).length < 2 ^ (prefixWord ++ tailWord_2167394).sum := by decide
  have hdescent : baseEnd_2167394 < baseStart_2167394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167473 : List Nat := [1, 2, 2, 6, 1, 2, 2, 1, 5]
def baseStart_2167473 : Nat := 118140960795 + 2167473 * 2 ^ 59
def prefixEnd_2167473 : Nat := 4983230072969 + 3 ^ 40 * 2167473 * 2
def baseEnd_2167473 : Nat := 247323434365045219026551

theorem tailTrace_2167473 : CollatzResearch.WordTrace tailWord_2167473 prefixEnd_2167473 247323434365045219026551 := by
  unfold tailWord_2167473
  simp only [CollatzResearch.WordTrace]
  refine ⟨79054234876622970762379073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52702823251081980508252715 79054234876622970762379073)
  ·
    refine ⟨59290676157467228071784305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79054234876622970762379073 59290676157467228071784305)
    ·
      refine ⟨44468007118100421053838229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59290676157467228071784305 44468007118100421053838229)
      ·
        refine ⟨2084437833660957236898667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44468007118100421053838229 2084437833660957236898667)
        ·
          refine ⟨3126656750491435855348001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2084437833660957236898667 3126656750491435855348001)
          ·
            refine ⟨2344992562868576891511001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3126656750491435855348001 2344992562868576891511001)
            ·
              refine ⟨1758744422151432668633251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2344992562868576891511001 1758744422151432668633251)
              ·
                refine ⟨2638116633227149002949877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1758744422151432668633251 2638116633227149002949877)
                ·
                  refine ⟨247323434365045219026551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2638116633227149002949877 247323434365045219026551)
                  ·
                    rfl

theorem cell22_2167473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 5].length) (baseStart_2167473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2167473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2167473 prefixEnd_2167473 := by exact prefixLift 2167473
  have htrace : WordTrace (prefixWord ++ tailWord_2167473) baseStart_2167473 baseEnd_2167473 := by
    simpa [prefixWord, tailWord_2167473, baseEnd_2167473] using wordTrace_append hprefix tailTrace_2167473
  have hstable : (prefixWord ++ tailWord_2167473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167473).length < 2 ^ (prefixWord ++ tailWord_2167473).sum := by decide
  have hdescent : baseEnd_2167473 < baseStart_2167473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167482 : List Nat := [3, 1, 1, 1, 2, 3, 2, 3, 1, 5]
def baseStart_2167482 : Nat := 118140960795 + 2167482 * 2 ^ 59
def prefixEnd_2167482 : Nat := 4983230072969 + 3 ^ 40 * 2167482 * 2
def baseEnd_2167482 : Nat := 741973383979062633604625

theorem tailTrace_2167482 : CollatzResearch.WordTrace tailWord_2167482 prefixEnd_2167482 741973383979062633604625 := by
  unfold tailWord_2167482
  simp only [CollatzResearch.WordTrace]
  refine ⟨19763640783397591324864175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52703042089060243532971133 19763640783397591324864175)
  ·
    refine ⟨29645461175096386987296263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19763640783397591324864175 29645461175096386987296263)
    ·
      refine ⟨44468191762644580480944395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29645461175096386987296263 44468191762644580480944395)
      ·
        refine ⟨66702287643966870721416593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44468191762644580480944395 66702287643966870721416593)
        ·
          refine ⟨50026715732975153041062445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66702287643966870721416593 50026715732975153041062445)
          ·
            refine ⟨18760018399865682390398417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50026715732975153041062445 18760018399865682390398417)
            ·
              refine ⟨14070013799899261792798813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18760018399865682390398417 14070013799899261792798813)
              ·
                refine ⟨5276255174962223172299555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14070013799899261792798813 5276255174962223172299555)
                ·
                  refine ⟨7914382762443334758449333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5276255174962223172299555 7914382762443334758449333)
                  ·
                    refine ⟨741973383979062633604625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7914382762443334758449333 741973383979062633604625)
                    ·
                      rfl

theorem cell22_2167482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_2167482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2167482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2167482 prefixEnd_2167482 := by exact prefixLift 2167482
  have htrace : WordTrace (prefixWord ++ tailWord_2167482) baseStart_2167482 baseEnd_2167482 := by
    simpa [prefixWord, tailWord_2167482, baseEnd_2167482] using wordTrace_append hprefix tailTrace_2167482
  have hstable : (prefixWord ++ tailWord_2167482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167482).length < 2 ^ (prefixWord ++ tailWord_2167482).sum := by decide
  have hdescent : baseEnd_2167482 < baseStart_2167482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167544 : List Nat := [2, 1, 2, 1, 1, 2, 5, 2, 3, 3]
def baseStart_2167544 : Nat := 118140960795 + 2167544 * 2 ^ 59
def prefixEnd_2167544 : Nat := 4983230072969 + 3 ^ 40 * 2167544 * 2
def baseEnd_2167544 : Nat := 741994607846115138554435

theorem tailTrace_2167544 : CollatzResearch.WordTrace tailWord_2167544 prefixEnd_2167544 741994607846115138554435 := by
  unfold tailWord_2167544
  simp only [CollatzResearch.WordTrace]
  refine ⟨39528412229682874944106843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52704549639577166592142457 39528412229682874944106843)
  ·
    refine ⟨59292618344524312416160265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39528412229682874944106843 59292618344524312416160265)
    ·
      refine ⟨44469463758393234312120199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59292618344524312416160265 44469463758393234312120199)
      ·
        refine ⟨66704195637589851468180299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44469463758393234312120199 66704195637589851468180299)
        ·
          refine ⟨100056293456384777202270449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66704195637589851468180299 100056293456384777202270449)
          ·
            refine ⟨75042220092288582901702837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100056293456384777202270449 75042220092288582901702837)
            ·
              refine ⟨7035208133652054647034641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75042220092288582901702837 7035208133652054647034641)
              ·
                refine ⟨5276406100239040985275981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7035208133652054647034641 5276406100239040985275981)
                ·
                  refine ⟨1978652287589640369478493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5276406100239040985275981 1978652287589640369478493)
                  ·
                    refine ⟨741994607846115138554435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1978652287589640369478493 741994607846115138554435)
                    ·
                      rfl

theorem cell22_2167544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 3, 3].length) (baseStart_2167544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2167544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2167544 prefixEnd_2167544 := by exact prefixLift 2167544
  have htrace : WordTrace (prefixWord ++ tailWord_2167544) baseStart_2167544 baseEnd_2167544 := by
    simpa [prefixWord, tailWord_2167544, baseEnd_2167544] using wordTrace_append hprefix tailTrace_2167544
  have hstable : (prefixWord ++ tailWord_2167544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167544).length < 2 ^ (prefixWord ++ tailWord_2167544).sum := by decide
  have hdescent : baseEnd_2167544 < baseStart_2167544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167561 : List Nat := [1, 2, 1, 1, 3, 2, 3, 5, 1, 3]
def baseStart_2167561 : Nat := 118140960795 + 2167561 * 2 ^ 59
def prefixEnd_2167561 : Nat := 4983230072969 + 3 ^ 40 * 2167561 * 2
def baseEnd_2167561 : Nat := 742000427293532760879383

theorem tailTrace_2167561 : CollatzResearch.WordTrace tailWord_2167561 prefixEnd_2167561 742000427293532760879383 := by
  unfold tailWord_2167561
  simp only [CollatzResearch.WordTrace]
  refine ⟨79057444500304161791582537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52704963000202774527721691 79057444500304161791582537)
  ·
    refine ⟨59293083375228121343686903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79057444500304161791582537 59293083375228121343686903)
    ·
      refine ⟨88939625062842182015530355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59293083375228121343686903 88939625062842182015530355)
      ·
        refine ⟨133409437594263273023295533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88939625062842182015530355 133409437594263273023295533)
        ·
          refine ⟨50028539097848727383735825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133409437594263273023295533 50028539097848727383735825)
          ·
            refine ⟨37521404323386545537801869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50028539097848727383735825 37521404323386545537801869)
            ·
              refine ⟨14070526621269954576675701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37521404323386545537801869 14070526621269954576675701)
              ·
                refine ⟨1319111870744058241563347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14070526621269954576675701 1319111870744058241563347)
                ·
                  refine ⟨1978667806116087362345021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1319111870744058241563347 1978667806116087362345021)
                  ·
                    refine ⟨742000427293532760879383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1978667806116087362345021 742000427293532760879383)
                    ·
                      rfl

theorem cell22_2167561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5, 1, 3].length) (baseStart_2167561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2167561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2167561 prefixEnd_2167561 := by exact prefixLift 2167561
  have htrace : WordTrace (prefixWord ++ tailWord_2167561) baseStart_2167561 baseEnd_2167561 := by
    simpa [prefixWord, tailWord_2167561, baseEnd_2167561] using wordTrace_append hprefix tailTrace_2167561
  have hstable : (prefixWord ++ tailWord_2167561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167561).length < 2 ^ (prefixWord ++ tailWord_2167561).sum := by decide
  have hdescent : baseEnd_2167561 < baseStart_2167561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167698 : List Nat := [3, 2, 3, 2, 2, 2, 1, 7]
def baseStart_2167698 : Nat := 118140960795 + 2167698 * 2 ^ 59
def prefixEnd_2167698 : Nat := 4983230072969 + 3 ^ 40 * 2167698 * 2
def baseEnd_2167698 : Nat := 82449702799256674467107

theorem tailTrace_2167698 : CollatzResearch.WordTrace tailWord_2167698 prefixEnd_2167698 82449702799256674467107 := by
  unfold tailWord_2167698
  simp only [CollatzResearch.WordTrace]
  refine ⟨19765610325201958547329937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52708294200538556126213165 19765610325201958547329937)
  ·
    refine ⟨14824207743901468910497453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19765610325201958547329937 14824207743901468910497453)
    ·
      refine ⟨5559077903963050841436545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14824207743901468910497453 5559077903963050841436545)
      ·
        refine ⟨4169308427972288131077409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5559077903963050841436545 4169308427972288131077409)
        ·
          refine ⟨3126981320979216098308057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4169308427972288131077409 3126981320979216098308057)
          ·
            refine ⟨2345235990734412073731043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3126981320979216098308057 2345235990734412073731043)
            ·
              refine ⟨3517853986101618110596565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2345235990734412073731043 3517853986101618110596565)
              ·
                refine ⟨82449702799256674467107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3517853986101618110596565 82449702799256674467107)
                ·
                  rfl

theorem cell22_2167698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 7].length) (baseStart_2167698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2167698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2167698 prefixEnd_2167698 := by exact prefixLift 2167698
  have htrace : WordTrace (prefixWord ++ tailWord_2167698) baseStart_2167698 baseEnd_2167698 := by
    simpa [prefixWord, tailWord_2167698, baseEnd_2167698] using wordTrace_append hprefix tailTrace_2167698
  have hstable : (prefixWord ++ tailWord_2167698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167698).length < 2 ^ (prefixWord ++ tailWord_2167698).sum := by decide
  have hdescent : baseEnd_2167698 < baseStart_2167698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167702 : List Nat := [5, 3, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_2167702 : Nat := 118140960795 + 2167702 * 2 ^ 59
def prefixEnd_2167702 : Nat := 4983230072969 + 3 ^ 40 * 2167702 * 2
def baseEnd_2167702 : Nat := 742048694475055393103951

theorem tailTrace_2167702 : CollatzResearch.WordTrace tailWord_2167702 prefixEnd_2167702 742048694475055393103951 := by
  unfold tailWord_2167702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4941411699549583929529085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52708391461862228581643573 4941411699549583929529085)
  ·
    refine ⟨1853029387331093973573407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4941411699549583929529085 1853029387331093973573407)
    ·
      refine ⟨2779544080996640960360111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1853029387331093973573407 2779544080996640960360111)
      ·
        refine ⟨4169316121494961440540167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2779544080996640960360111 4169316121494961440540167)
        ·
          refine ⟨6253974182242442160810251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4169316121494961440540167 6253974182242442160810251)
          ·
            refine ⟨9380961273363663241215377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6253974182242442160810251 9380961273363663241215377)
            ·
              refine ⟨7035720955022747430911533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9380961273363663241215377 7035720955022747430911533)
              ·
                refine ⟨2638395358133530286591825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7035720955022747430911533 2638395358133530286591825)
                ·
                  refine ⟨1978796518600147714943869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2638395358133530286591825 1978796518600147714943869)
                  ·
                    refine ⟨742048694475055393103951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1978796518600147714943869 742048694475055393103951)
                    ·
                      rfl

theorem cell22_2167702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_2167702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2167702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2167702 prefixEnd_2167702 := by exact prefixLift 2167702
  have htrace : WordTrace (prefixWord ++ tailWord_2167702) baseStart_2167702 baseEnd_2167702 := by
    simpa [prefixWord, tailWord_2167702, baseEnd_2167702] using wordTrace_append hprefix tailTrace_2167702
  have hstable : (prefixWord ++ tailWord_2167702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167702).length < 2 ^ (prefixWord ++ tailWord_2167702).sum := by decide
  have hdescent : baseEnd_2167702 < baseStart_2167702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167713 : List Nat := [1, 2, 3, 4, 1, 2, 1, 2, 3, 3]
def baseStart_2167713 : Nat := 118140960795 + 2167713 * 2 ^ 59
def prefixEnd_2167713 : Nat := 4983230072969 + 3 ^ 40 * 2167713 * 2
def baseEnd_2167713 : Nat := 742052459999855031078917

theorem tailTrace_2167713 : CollatzResearch.WordTrace tailWord_2167713 prefixEnd_2167713 742052459999855031078917 := by
  unfold tailWord_2167713
  simp only [CollatzResearch.WordTrace]
  refine ⟨79062988395753491751115793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52708658930502327834077195 79062988395753491751115793)
  ·
    refine ⟨59297241296815118813336845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79062988395753491751115793 59297241296815118813336845)
    ·
      refine ⟨22236465486305669555001317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59297241296815118813336845 22236465486305669555001317)
      ·
        refine ⟨4169337278682313041562747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22236465486305669555001317 4169337278682313041562747)
        ·
          refine ⟨6254005918023469562344121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4169337278682313041562747 6254005918023469562344121)
          ·
            refine ⟨4690504438517602171758091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6254005918023469562344121 4690504438517602171758091)
            ·
              refine ⟨7035756657776403257637137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4690504438517602171758091 7035756657776403257637137)
              ·
                refine ⟨5276817493332302443227853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7035756657776403257637137 5276817493332302443227853)
                ·
                  refine ⟨1978806559999613416210445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5276817493332302443227853 1978806559999613416210445)
                  ·
                    refine ⟨742052459999855031078917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1978806559999613416210445 742052459999855031078917)
                    ·
                      rfl

theorem cell22_2167713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_2167713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2167713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2167713 prefixEnd_2167713 := by exact prefixLift 2167713
  have htrace : WordTrace (prefixWord ++ tailWord_2167713) baseStart_2167713 baseEnd_2167713 := by
    simpa [prefixWord, tailWord_2167713, baseEnd_2167713] using wordTrace_append hprefix tailTrace_2167713
  have hstable : (prefixWord ++ tailWord_2167713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167713).length < 2 ^ (prefixWord ++ tailWord_2167713).sum := by decide
  have hdescent : baseEnd_2167713 < baseStart_2167713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167773 : List Nat := [1, 4, 3, 1, 2, 1, 1, 4, 1, 4]
def baseStart_2167773 : Nat := 118140960795 + 2167773 * 2 ^ 59
def prefixEnd_2167773 : Nat := 4983230072969 + 3 ^ 40 * 2167773 * 2
def baseEnd_2167773 : Nat := 742072999226034874578733

theorem tailTrace_2167773 : CollatzResearch.WordTrace tailWord_2167773 prefixEnd_2167773 742072999226034874578733 := by
  unfold tailWord_2167773
  simp only [CollatzResearch.WordTrace]
  refine ⟨79065176775536121998299973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52710117850357414665533315 79065176775536121998299973)
  ·
    refine ⟨14824720645413022874681245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79065176775536121998299973 14824720645413022874681245)
    ·
      refine ⟨5559270242029883578005467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14824720645413022874681245 5559270242029883578005467)
      ·
        refine ⟨8338905363044825367008201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5559270242029883578005467 8338905363044825367008201)
        ·
          refine ⟨6254179022283619025256151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8338905363044825367008201 6254179022283619025256151)
          ·
            refine ⟨9381268533425428537884227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6254179022283619025256151 9381268533425428537884227)
            ·
              refine ⟨14071902800138142806826341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9381268533425428537884227 14071902800138142806826341)
              ·
                refine ⟨2638481775025901776279939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14071902800138142806826341 2638481775025901776279939)
                ·
                  refine ⟨3957722662538852664419909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2638481775025901776279939 3957722662538852664419909)
                  ·
                    refine ⟨742072999226034874578733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3957722662538852664419909 742072999226034874578733)
                    ·
                      rfl

theorem cell22_2167773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_2167773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2167773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2167773 prefixEnd_2167773 := by exact prefixLift 2167773
  have htrace : WordTrace (prefixWord ++ tailWord_2167773) baseStart_2167773 baseEnd_2167773 := by
    simpa [prefixWord, tailWord_2167773, baseEnd_2167773] using wordTrace_append hprefix tailTrace_2167773
  have hstable : (prefixWord ++ tailWord_2167773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167773).length < 2 ^ (prefixWord ++ tailWord_2167773).sum := by decide
  have hdescent : baseEnd_2167773 < baseStart_2167773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167801 : List Nat := [1, 2, 1, 3, 1, 3, 3, 2, 2, 4]
def baseStart_2167801 : Nat := 118140960795 + 2167801 * 2 ^ 59
def prefixEnd_2167801 : Nat := 4983230072969 + 3 ^ 40 * 2167801 * 2
def baseEnd_2167801 : Nat := 742082584198252134878647

theorem tailTrace_2167801 : CollatzResearch.WordTrace tailWord_2167801 prefixEnd_2167801 742082584198252134878647 := by
  unfold tailWord_2167801
  simp only [CollatzResearch.WordTrace]
  refine ⟨79066198019434682780319257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52710798679623121853546171 79066198019434682780319257)
  ·
    refine ⟨59299648514576012085239443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79066198019434682780319257 59299648514576012085239443)
    ·
      refine ⟨88949472771864018127859165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59299648514576012085239443 88949472771864018127859165)
      ·
        refine ⟨33356052289449006797947187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88949472771864018127859165 33356052289449006797947187)
        ·
          refine ⟨50034078434173510196920781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33356052289449006797947187 50034078434173510196920781)
          ·
            refine ⟨18762779412815066323845293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50034078434173510196920781 18762779412815066323845293)
            ·
              refine ⟨7036042279805649871441985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18762779412815066323845293 7036042279805649871441985)
              ·
                refine ⟨5277031709854237403581489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7036042279805649871441985 5277031709854237403581489)
                ·
                  refine ⟨3957773782390678052686117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5277031709854237403581489 3957773782390678052686117)
                  ·
                    refine ⟨742082584198252134878647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3957773782390678052686117 742082584198252134878647)
                    ·
                      rfl

theorem cell22_2167801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 4].length) (baseStart_2167801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2167801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2167801 prefixEnd_2167801 := by exact prefixLift 2167801
  have htrace : WordTrace (prefixWord ++ tailWord_2167801) baseStart_2167801 baseEnd_2167801 := by
    simpa [prefixWord, tailWord_2167801, baseEnd_2167801] using wordTrace_append hprefix tailTrace_2167801
  have hstable : (prefixWord ++ tailWord_2167801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167801).length < 2 ^ (prefixWord ++ tailWord_2167801).sum := by decide
  have hdescent : baseEnd_2167801 < baseStart_2167801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167816 : List Nat := [2, 1, 3, 2, 1, 4, 2, 7]
def baseStart_2167816 : Nat := 118140960795 + 2167816 * 2 ^ 59
def prefixEnd_2167816 : Nat := 4983230072969 + 3 ^ 40 * 2167816 * 2
def baseEnd_2167816 : Nat := 82454191000533010639289

theorem tailTrace_2167816 : CollatzResearch.WordTrace tailWord_2167816 prefixEnd_2167816 82454191000533010639289 := by
  unfold tailWord_2167816
  simp only [CollatzResearch.WordTrace]
  refine ⟨39533372557190170171057651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52711163409586893561410201 39533372557190170171057651)
  ·
    refine ⟨59300058835785255256586477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39533372557190170171057651 59300058835785255256586477)
    ·
      refine ⟨22237522063419470721219929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59300058835785255256586477 22237522063419470721219929)
      ·
        refine ⟨16678141547564603040914947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22237522063419470721219929 16678141547564603040914947)
        ·
          refine ⟨25017212321346904561372421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16678141547564603040914947 25017212321346904561372421)
          ·
            refine ⟨4690727310252544605257329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25017212321346904561372421 4690727310252544605257329)
            ·
              refine ⟨3518045482689408453942997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4690727310252544605257329 3518045482689408453942997)
              ·
                refine ⟨82454191000533010639289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3518045482689408453942997 82454191000533010639289)
                ·
                  rfl

theorem cell22_2167816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 7].length) (baseStart_2167816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2167816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2167816 prefixEnd_2167816 := by exact prefixLift 2167816
  have htrace : WordTrace (prefixWord ++ tailWord_2167816) baseStart_2167816 baseEnd_2167816 := by
    simpa [prefixWord, tailWord_2167816, baseEnd_2167816] using wordTrace_append hprefix tailTrace_2167816
  have hstable : (prefixWord ++ tailWord_2167816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167816).length < 2 ^ (prefixWord ++ tailWord_2167816).sum := by decide
  have hdescent : baseEnd_2167816 < baseStart_2167816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167820 : List Nat := [2, 2, 1, 2, 3, 2, 4, 1, 2, 3]
def baseStart_2167820 : Nat := 118140960795 + 2167820 * 2 ^ 59
def prefixEnd_2167820 : Nat := 4983230072969 + 3 ^ 40 * 2167820 * 2
def baseEnd_2167820 : Nat := 742089088286542418653589

theorem tailTrace_2167820 : CollatzResearch.WordTrace tailWord_2167820 prefixEnd_2167820 742089088286542418653589 := by
  unfold tailWord_2167820
  simp only [CollatzResearch.WordTrace]
  refine ⟨39533445503182924512630457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52711260670910566016840609 39533445503182924512630457)
  ·
    refine ⟨29650084127387193384472843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39533445503182924512630457 29650084127387193384472843)
    ·
      refine ⟨44475126191080790076709265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29650084127387193384472843 44475126191080790076709265)
      ·
        refine ⟨33356344643310592557531949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44475126191080790076709265 33356344643310592557531949)
        ·
          refine ⟨12508629241241472209074481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33356344643310592557531949 12508629241241472209074481)
          ·
            refine ⟨9381471930931104156805861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12508629241241472209074481 9381471930931104156805861)
            ·
              refine ⟨1759025987049582029401099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9381471930931104156805861 1759025987049582029401099)
              ·
                refine ⟨2638538980574373044101649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1759025987049582029401099 2638538980574373044101649)
                ·
                  refine ⟨1978904235430779783076237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2638538980574373044101649 1978904235430779783076237)
                  ·
                    refine ⟨742089088286542418653589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1978904235430779783076237 742089088286542418653589)
                    ·
                      rfl

theorem cell22_2167820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 2, 3].length) (baseStart_2167820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2167820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2167820 prefixEnd_2167820 := by exact prefixLift 2167820
  have htrace : WordTrace (prefixWord ++ tailWord_2167820) baseStart_2167820 baseEnd_2167820 := by
    simpa [prefixWord, tailWord_2167820, baseEnd_2167820] using wordTrace_append hprefix tailTrace_2167820
  have hstable : (prefixWord ++ tailWord_2167820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167820).length < 2 ^ (prefixWord ++ tailWord_2167820).sum := by decide
  have hdescent : baseEnd_2167820 < baseStart_2167820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167912 : List Nat := [2, 1, 4, 4, 1, 2, 1, 2, 5]
def baseStart_2167912 : Nat := 118140960795 + 2167912 * 2 ^ 59
def prefixEnd_2167912 : Nat := 4983230072969 + 3 ^ 40 * 2167912 * 2
def baseEnd_2167912 : Nat := 247373527255561615117769

theorem tailTrace_2167912 : CollatzResearch.WordTrace tailWord_2167912 prefixEnd_2167912 247373527255561615117769 := by
  unfold tailWord_2167912
  simp only [CollatzResearch.WordTrace]
  refine ⟨39535123261016274368804995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52713497681355032491739993 39535123261016274368804995)
  ·
    refine ⟨59302684891524411553207493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39535123261016274368804995 59302684891524411553207493)
    ·
      refine ⟨11119253417160827166226405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59302684891524411553207493 11119253417160827166226405)
      ·
        refine ⟨2084860015717655093667451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11119253417160827166226405 2084860015717655093667451)
        ·
          refine ⟨3127290023576482640501177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2084860015717655093667451 3127290023576482640501177)
          ·
            refine ⟨2345467517682361980375883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3127290023576482640501177 2345467517682361980375883)
            ·
              refine ⟨3518201276523542970563825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2345467517682361980375883 3518201276523542970563825)
              ·
                refine ⟨2638650957392657227922869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3518201276523542970563825 2638650957392657227922869)
                ·
                  refine ⟨247373527255561615117769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2638650957392657227922869 247373527255561615117769)
                  ·
                    rfl

theorem cell22_2167912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 5].length) (baseStart_2167912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2167912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2167912 prefixEnd_2167912 := by exact prefixLift 2167912
  have htrace : WordTrace (prefixWord ++ tailWord_2167912) baseStart_2167912 baseEnd_2167912 := by
    simpa [prefixWord, tailWord_2167912, baseEnd_2167912] using wordTrace_append hprefix tailTrace_2167912
  have hstable : (prefixWord ++ tailWord_2167912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167912).length < 2 ^ (prefixWord ++ tailWord_2167912).sum := by decide
  have hdescent : baseEnd_2167912 < baseStart_2167912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2167936 : List Nat := [2, 1, 1, 2, 1, 3, 3, 2, 1, 6]
def baseStart_2167936 : Nat := 118140960795 + 2167936 * 2 ^ 59
def prefixEnd_2167936 : Nat := 4983230072969 + 3 ^ 40 * 2167936 * 2
def baseEnd_2167936 : Nat := 742128797457156782753233

theorem tailTrace_2167936 : CollatzResearch.WordTrace tailWord_2167936 prefixEnd_2167936 742128797457156782753233 := by
  unfold tailWord_2167936
  simp only [CollatzResearch.WordTrace]
  refine ⟨39535560936972800418241831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52714081249297067224322441 39535560936972800418241831)
  ·
    refine ⟨59303341405459200627362747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39535560936972800418241831 59303341405459200627362747)
    ·
      refine ⟨88955012108188800941044121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59303341405459200627362747 88955012108188800941044121)
      ·
        refine ⟨66716259081141600705783091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88955012108188800941044121 66716259081141600705783091)
        ·
          refine ⟨100074388621712401058674637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66716259081141600705783091 100074388621712401058674637)
          ·
            refine ⟨37527895733142150397002989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100074388621712401058674637 37527895733142150397002989)
            ·
              refine ⟨14072960899928306398876121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37527895733142150397002989 14072960899928306398876121)
              ·
                refine ⟨10554720674946229799157091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14072960899928306398876121 10554720674946229799157091)
                ·
                  refine ⟨15832081012419344698735637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10554720674946229799157091 15832081012419344698735637)
                  ·
                    refine ⟨742128797457156782753233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15832081012419344698735637 742128797457156782753233)
                    ·
                      rfl

theorem cell22_2167936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 1, 6].length) (baseStart_2167936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2167936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2167936 prefixEnd_2167936 := by exact prefixLift 2167936
  have htrace : WordTrace (prefixWord ++ tailWord_2167936) baseStart_2167936 baseEnd_2167936 := by
    simpa [prefixWord, tailWord_2167936, baseEnd_2167936] using wordTrace_append hprefix tailTrace_2167936
  have hstable : (prefixWord ++ tailWord_2167936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2167936).length < 2 ^ (prefixWord ++ tailWord_2167936).sum := by decide
  have hdescent : baseEnd_2167936 < baseStart_2167936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2167936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168011 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 3, 7]
def baseStart_2168011 : Nat := 118140960795 + 2168011 * 2 ^ 59
def prefixEnd_2168011 : Nat := 4983230072969 + 3 ^ 40 * 2168011 * 2
def baseEnd_2168011 : Nat := 742154471489881587128003

theorem tailTrace_2168011 : CollatzResearch.WordTrace tailWord_2168011 prefixEnd_2168011 742154471489881587128003 := by
  unfold tailWord_2168011
  simp only [CollatzResearch.WordTrace]
  refine ⟨79073857348673888645463887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52715904899115925763642591 79073857348673888645463887)
  ·
    refine ⟨118610786023010832968195831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79073857348673888645463887 118610786023010832968195831)
    ·
      refine ⟨177916179034516249452293747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118610786023010832968195831 177916179034516249452293747)
      ·
        refine ⟨266874268551774374178440621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177916179034516249452293747 266874268551774374178440621)
        ·
          refine ⟨100077850706915390316915233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 266874268551774374178440621 100077850706915390316915233)
          ·
            refine ⟨75058388030186542737686425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100077850706915390316915233 75058388030186542737686425)
            ·
              refine ⟨56293791022639907053264819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75058388030186542737686425 56293791022639907053264819)
              ·
                refine ⟨84440686533959860579897229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56293791022639907053264819 84440686533959860579897229)
                ·
                  refine ⟨31665257450234947717461461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84440686533959860579897229 31665257450234947717461461)
                  ·
                    refine ⟨742154471489881587128003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31665257450234947717461461 742154471489881587128003)
                    ·
                      rfl

theorem cell22_2168011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 7].length) (baseStart_2168011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168011 prefixEnd_2168011 := by exact prefixLift 2168011
  have htrace : WordTrace (prefixWord ++ tailWord_2168011) baseStart_2168011 baseEnd_2168011 := by
    simpa [prefixWord, tailWord_2168011, baseEnd_2168011] using wordTrace_append hprefix tailTrace_2168011
  have hstable : (prefixWord ++ tailWord_2168011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168011).length < 2 ^ (prefixWord ++ tailWord_2168011).sum := by decide
  have hdescent : baseEnd_2168011 < baseStart_2168011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168043 : List Nat := [1, 1, 1, 1, 2, 6, 1, 2, 3, 4]
def baseStart_2168043 : Nat := 118140960795 + 2168043 * 2 ^ 59
def prefixEnd_2168043 : Nat := 4983230072969 + 3 ^ 40 * 2168043 * 2
def baseEnd_2168043 : Nat := 742165425743844170327905

theorem tailTrace_2168043 : CollatzResearch.WordTrace tailWord_2168043 prefixEnd_2168043 742165425743844170327905 := by
  unfold tailWord_2168043
  simp only [CollatzResearch.WordTrace]
  refine ⟨79075024484557958110628783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52716682989705305407085855 79075024484557958110628783)
  ·
    refine ⟨118612536726836937165943175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79075024484557958110628783 118612536726836937165943175)
    ·
      refine ⟨177918805090255405748914763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118612536726836937165943175 177918805090255405748914763)
      ·
        refine ⟨266878207635383108623372145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177918805090255405748914763 266878207635383108623372145)
        ·
          refine ⟨200158655726537331467529109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266878207635383108623372145 200158655726537331467529109)
          ·
            refine ⟨9382436987181437412540427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 200158655726537331467529109 9382436987181437412540427)
            ·
              refine ⟨14073655480772156118810641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9382436987181437412540427 14073655480772156118810641)
              ·
                refine ⟨10555241610579117089107981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14073655480772156118810641 10555241610579117089107981)
                ·
                  refine ⟨3958215603967168908415493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10555241610579117089107981 3958215603967168908415493)
                  ·
                    refine ⟨742165425743844170327905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3958215603967168908415493 742165425743844170327905)
                    ·
                      rfl

theorem cell22_2168043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 4].length) (baseStart_2168043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168043 prefixEnd_2168043 := by exact prefixLift 2168043
  have htrace : WordTrace (prefixWord ++ tailWord_2168043) baseStart_2168043 baseEnd_2168043 := by
    simpa [prefixWord, tailWord_2168043, baseEnd_2168043] using wordTrace_append hprefix tailTrace_2168043
  have hstable : (prefixWord ++ tailWord_2168043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168043).length < 2 ^ (prefixWord ++ tailWord_2168043).sum := by decide
  have hdescent : baseEnd_2168043 < baseStart_2168043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168045 : List Nat := [1, 5, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_2168045 : Nat := 118140960795 + 2168045 * 2 ^ 59
def prefixEnd_2168045 : Nat := 4983230072969 + 3 ^ 40 * 2168045 * 2
def baseEnd_2168045 : Nat := 742166110384716831777899

theorem tailTrace_2168045 : CollatzResearch.WordTrace tailWord_2168045 prefixEnd_2168045 742166110384716831777899 := by
  unfold tailWord_2168045
  simp only [CollatzResearch.WordTrace]
  refine ⟨79075097430550712452201589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52716731620367141634801059 79075097430550712452201589)
  ·
    refine ⟨7413290384114129292393899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79075097430550712452201589 7413290384114129292393899)
    ·
      refine ⟨11119935576171193938590849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7413290384114129292393899 11119935576171193938590849)
      ·
        refine ⟨8339951682128395453943137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11119935576171193938590849 8339951682128395453943137)
        ·
          refine ⟨6254963761596296590457353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8339951682128395453943137 6254963761596296590457353)
          ·
            refine ⟨4691222821197222442843015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6254963761596296590457353 4691222821197222442843015)
            ·
              refine ⟨7036834231795833664264523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4691222821197222442843015 7036834231795833664264523)
              ·
                refine ⟨10555251347693750496396785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7036834231795833664264523 10555251347693750496396785)
                ·
                  refine ⟨7916438510770312872297589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10555251347693750496396785 7916438510770312872297589)
                  ·
                    refine ⟨742166110384716831777899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7916438510770312872297589 742166110384716831777899)
                    ·
                      rfl

theorem cell22_2168045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_2168045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168045 prefixEnd_2168045 := by exact prefixLift 2168045
  have htrace : WordTrace (prefixWord ++ tailWord_2168045) baseStart_2168045 baseEnd_2168045 := by
    simpa [prefixWord, tailWord_2168045, baseEnd_2168045] using wordTrace_append hprefix tailTrace_2168045
  have hstable : (prefixWord ++ tailWord_2168045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168045).length < 2 ^ (prefixWord ++ tailWord_2168045).sum := by decide
  have hdescent : baseEnd_2168045 < baseStart_2168045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168058 : List Nat := [3, 1, 1, 1, 1, 4, 3, 2, 6]
def baseStart_2168058 : Nat := 118140960795 + 2168058 * 2 ^ 59
def prefixEnd_2168058 : Nat := 4983230072969 + 3 ^ 40 * 2168058 * 2
def baseEnd_2168058 : Nat := 247390186850129710400953

theorem tailTrace_2168058 : CollatzResearch.WordTrace tailWord_2168058 prefixEnd_2168058 247390186850129710400953 := by
  unfold tailWord_2168058
  simp only [CollatzResearch.WordTrace]
  refine ⟨19768892894875903918106207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52717047719669077114949885 19768892894875903918106207)
  ·
    refine ⟨29653339342313855877159311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19768892894875903918106207 29653339342313855877159311)
    ·
      refine ⟨44480009013470783815738967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29653339342313855877159311 44480009013470783815738967)
      ·
        refine ⟨66720013520206175723608451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44480009013470783815738967 66720013520206175723608451)
        ·
          refine ⟨100080020280309263585412677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66720013520206175723608451 100080020280309263585412677)
          ·
            refine ⟨18765003802557986922264877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100080020280309263585412677 18765003802557986922264877)
            ·
              refine ⟨7036876425959245095849329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18765003802557986922264877 7036876425959245095849329)
              ·
                refine ⟨5277657319469433821886997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7036876425959245095849329 5277657319469433821886997)
                ·
                  refine ⟨247390186850129710400953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5277657319469433821886997 247390186850129710400953)
                  ·
                    rfl

theorem cell22_2168058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 6].length) (baseStart_2168058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168058 prefixEnd_2168058 := by exact prefixLift 2168058
  have htrace : WordTrace (prefixWord ++ tailWord_2168058) baseStart_2168058 baseEnd_2168058 := by
    simpa [prefixWord, tailWord_2168058, baseEnd_2168058] using wordTrace_append hprefix tailTrace_2168058
  have hstable : (prefixWord ++ tailWord_2168058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168058).length < 2 ^ (prefixWord ++ tailWord_2168058).sum := by decide
  have hdescent : baseEnd_2168058 < baseStart_2168058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168073 : List Nat := [1, 2, 1, 1, 3, 3, 1, 4, 1, 5]
def baseStart_2168073 : Nat := 118140960795 + 2168073 * 2 ^ 59
def prefixEnd_2168073 : Nat := 4983230072969 + 3 ^ 40 * 2168073 * 2
def baseEnd_2168073 : Nat := 742175695356934092077813

theorem tailTrace_2168073 : CollatzResearch.WordTrace tailWord_2168073 prefixEnd_2168073 742175695356934092077813 := by
  unfold tailWord_2168073
  simp only [CollatzResearch.WordTrace]
  refine ⟨79076118674449273234220873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52717412449632848822813915 79076118674449273234220873)
  ·
    refine ⟨59307089005836954925665655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79076118674449273234220873 59307089005836954925665655)
    ·
      refine ⟨88960633508755432388498483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59307089005836954925665655 88960633508755432388498483)
      ·
        refine ⟨133440950263133148582747725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88960633508755432388498483 133440950263133148582747725)
        ·
          refine ⟨50040356348674930718530397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133440950263133148582747725 50040356348674930718530397)
          ·
            refine ⟨18765133630753099019448899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50040356348674930718530397 18765133630753099019448899)
            ·
              refine ⟨28147700446129648529173349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18765133630753099019448899 28147700446129648529173349)
              ·
                refine ⟨5277693833649309099220003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28147700446129648529173349 5277693833649309099220003)
                ·
                  refine ⟨7916540750473963648830005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5277693833649309099220003 7916540750473963648830005)
                  ·
                    refine ⟨742175695356934092077813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7916540750473963648830005 742175695356934092077813)
                    ·
                      rfl

theorem cell22_2168073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 4, 1, 5].length) (baseStart_2168073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168073 prefixEnd_2168073 := by exact prefixLift 2168073
  have htrace : WordTrace (prefixWord ++ tailWord_2168073) baseStart_2168073 baseEnd_2168073 := by
    simpa [prefixWord, tailWord_2168073, baseEnd_2168073] using wordTrace_append hprefix tailTrace_2168073
  have hstable : (prefixWord ++ tailWord_2168073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168073).length < 2 ^ (prefixWord ++ tailWord_2168073).sum := by decide
  have hdescent : baseEnd_2168073 < baseStart_2168073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168075 : List Nat := [1, 1, 1, 1, 5, 3, 1, 5, 4]
def baseStart_2168075 : Nat := 118140960795 + 2168075 * 2 ^ 59
def prefixEnd_2168075 : Nat := 4983230072969 + 3 ^ 40 * 2168075 * 2
def baseEnd_2168075 : Nat := 247392126665935584509269

theorem tailTrace_2168075 : CollatzResearch.WordTrace tailWord_2168075 prefixEnd_2168075 247392126665935584509269 := by
  unfold tailWord_2168075
  simp only [CollatzResearch.WordTrace]
  refine ⟨79076191620442027575793679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52717461080294685050529119 79076191620442027575793679)
  ·
    refine ⟨118614287430663041363690519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79076191620442027575793679 118614287430663041363690519)
    ·
      refine ⟨177921431145994562045535779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118614287430663041363690519 177921431145994562045535779)
      ·
        refine ⟨266882146718991843068303669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177921431145994562045535779 266882146718991843068303669)
        ·
          refine ⟨25020201254905485287653469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 266882146718991843068303669 25020201254905485287653469)
          ·
            refine ⟨9382575470589556982870051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25020201254905485287653469 9382575470589556982870051)
            ·
              refine ⟨14073863205884335474305077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9382575470589556982870051 14073863205884335474305077)
              ·
                refine ⟨1319424675551656450716101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14073863205884335474305077 1319424675551656450716101)
                ·
                  refine ⟨247392126665935584509269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1319424675551656450716101 247392126665935584509269)
                  ·
                    rfl

theorem cell22_2168075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5, 4].length) (baseStart_2168075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168075 prefixEnd_2168075 := by exact prefixLift 2168075
  have htrace : WordTrace (prefixWord ++ tailWord_2168075) baseStart_2168075 baseEnd_2168075 := by
    simpa [prefixWord, tailWord_2168075, baseEnd_2168075] using wordTrace_append hprefix tailTrace_2168075
  have hstable : (prefixWord ++ tailWord_2168075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168075).length < 2 ^ (prefixWord ++ tailWord_2168075).sum := by decide
  have hdescent : baseEnd_2168075 < baseStart_2168075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168165 : List Nat := [1, 3, 1, 3, 1, 2, 3, 3, 5]
def baseStart_2168165 : Nat := 118140960795 + 2168165 * 2 ^ 59
def prefixEnd_2168165 : Nat := 4983230072969 + 3 ^ 40 * 2168165 * 2
def baseEnd_2168165 : Nat := 247402396279025506259177

theorem tailTrace_2168165 : CollatzResearch.WordTrace tailWord_2168165 prefixEnd_2168165 247402396279025506259177 := by
  unfold tailWord_2168165
  simp only [CollatzResearch.WordTrace]
  refine ⟨79079474190115972946569949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52719649460077315297713299 79079474190115972946569949)
  ·
    refine ⟨29654802821293489854963731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79079474190115972946569949 29654802821293489854963731)
    ·
      refine ⟨44482204231940234782445597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29654802821293489854963731 44482204231940234782445597)
      ·
        refine ⟨16680826586977588043417099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44482204231940234782445597 16680826586977588043417099)
        ·
          refine ⟨25021239880466382065125649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16680826586977588043417099 25021239880466382065125649)
          ·
            refine ⟨18765929910349786548844237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25021239880466382065125649 18765929910349786548844237)
            ·
              refine ⟨7037223716381169955816589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18765929910349786548844237 7037223716381169955816589)
              ·
                refine ⟨2638958893642938733431221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7037223716381169955816589 2638958893642938733431221)
                ·
                  refine ⟨247402396279025506259177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2638958893642938733431221 247402396279025506259177)
                  ·
                    rfl

theorem cell22_2168165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 5].length) (baseStart_2168165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168165 prefixEnd_2168165 := by exact prefixLift 2168165
  have htrace : WordTrace (prefixWord ++ tailWord_2168165) baseStart_2168165 baseEnd_2168165 := by
    simpa [prefixWord, tailWord_2168165, baseEnd_2168165] using wordTrace_append hprefix tailTrace_2168165
  have hstable : (prefixWord ++ tailWord_2168165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168165).length < 2 ^ (prefixWord ++ tailWord_2168165).sum := by decide
  have hdescent : baseEnd_2168165 < baseStart_2168165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168208 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 1, 11]
def baseStart_2168208 : Nat := 118140960795 + 2168208 * 2 ^ 59
def prefixEnd_2168208 : Nat := 4983230072969 + 3 ^ 40 * 2168208 * 2
def baseEnd_2168208 : Nat := 742221908615838739952399

theorem tailTrace_2168208 : CollatzResearch.WordTrace tailWord_2168208 prefixEnd_2168208 742221908615838739952399 := by
  unfold tailWord_2168208
  simp only [CollatzResearch.WordTrace]
  refine ⟨39540521264480095645192639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52720695019306794193590185 39540521264480095645192639)
  ·
    refine ⟨59310781896720143467788959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39540521264480095645192639 59310781896720143467788959)
    ·
      refine ⟨88966172845080215201683439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59310781896720143467788959 88966172845080215201683439)
      ·
        refine ⟨133449259267620322802525159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88966172845080215201683439 133449259267620322802525159)
        ·
          refine ⟨200173888901430484203787739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133449259267620322802525159 200173888901430484203787739)
          ·
            refine ⟨300260833352145726305681609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200173888901430484203787739 300260833352145726305681609)
            ·
              refine ⟨225195625014109294729261207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 300260833352145726305681609 225195625014109294729261207)
              ·
                refine ⟨337793437521163942093891811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225195625014109294729261207 337793437521163942093891811)
                ·
                  refine ⟨506690156281745913140837717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 337793437521163942093891811 506690156281745913140837717)
                  ·
                    refine ⟨742221908615838739952399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 506690156281745913140837717 742221908615838739952399)
                    ·
                      rfl

theorem cell22_2168208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_2168208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168208 prefixEnd_2168208 := by exact prefixLift 2168208
  have htrace : WordTrace (prefixWord ++ tailWord_2168208) baseStart_2168208 baseEnd_2168208 := by
    simpa [prefixWord, tailWord_2168208, baseEnd_2168208] using wordTrace_append hprefix tailTrace_2168208
  have hstable : (prefixWord ++ tailWord_2168208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168208).length < 2 ^ (prefixWord ++ tailWord_2168208).sum := by decide
  have hdescent : baseEnd_2168208 < baseStart_2168208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168212 : List Nat := [2, 4, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_2168212 : Nat := 118140960795 + 2168212 * 2 ^ 59
def prefixEnd_2168212 : Nat := 4983230072969 + 3 ^ 40 * 2168212 * 2
def baseEnd_2168212 : Nat := 742223277897584062852387

theorem tailTrace_2168212 : CollatzResearch.WordTrace tailWord_2168212 prefixEnd_2168212 742223277897584062852387 := by
  unfold tailWord_2168212
  simp only [CollatzResearch.WordTrace]
  refine ⟨39540594210472849986765445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52720792280630466649020593 39540594210472849986765445)
  ·
    refine ⟨7413861414463659372518521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39540594210472849986765445 7413861414463659372518521)
    ·
      refine ⟨5560396060847744529388891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7413861414463659372518521 5560396060847744529388891)
      ·
        refine ⟨8340594091271616794083337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5560396060847744529388891 8340594091271616794083337)
        ·
          refine ⟨6255445568453712595562503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8340594091271616794083337 6255445568453712595562503)
          ·
            refine ⟨9383168352680568893343755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6255445568453712595562503 9383168352680568893343755)
            ·
              refine ⟨14074752529020853340015633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9383168352680568893343755 14074752529020853340015633)
              ·
                refine ⟨10556064396765640005011725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14074752529020853340015633 10556064396765640005011725)
                ·
                  refine ⟨3958524148787115001879397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10556064396765640005011725 3958524148787115001879397)
                  ·
                    refine ⟨742223277897584062852387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3958524148787115001879397 742223277897584062852387)
                    ·
                      rfl

theorem cell22_2168212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_2168212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168212 prefixEnd_2168212 := by exact prefixLift 2168212
  have htrace : WordTrace (prefixWord ++ tailWord_2168212) baseStart_2168212 baseEnd_2168212 := by
    simpa [prefixWord, tailWord_2168212, baseEnd_2168212] using wordTrace_append hprefix tailTrace_2168212
  have hstable : (prefixWord ++ tailWord_2168212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168212).length < 2 ^ (prefixWord ++ tailWord_2168212).sum := by decide
  have hdescent : baseEnd_2168212 < baseStart_2168212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168240 : List Nat := [2, 1, 1, 1, 2, 1, 1, 7, 2, 4]
def baseStart_2168240 : Nat := 118140960795 + 2168240 * 2 ^ 59
def prefixEnd_2168240 : Nat := 4983230072969 + 3 ^ 40 * 2168240 * 2
def baseEnd_2168240 : Nat := 742232862869801323152301

theorem tailTrace_2168240 : CollatzResearch.WordTrace tailWord_2168240 prefixEnd_2168240 742232862869801323152301 := by
  unfold tailWord_2168240
  simp only [CollatzResearch.WordTrace]
  refine ⟨39541104832422130377775087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52721473109896173837033449 39541104832422130377775087)
  ·
    refine ⟨59311657248633195566662631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39541104832422130377775087 59311657248633195566662631)
    ·
      refine ⟨88967485872949793349993947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59311657248633195566662631 88967485872949793349993947)
      ·
        refine ⟨133451228809424690024990921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88967485872949793349993947 133451228809424690024990921)
        ·
          refine ⟨100088421607068517518743191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133451228809424690024990921 100088421607068517518743191)
          ·
            refine ⟨150132632410602776278114787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100088421607068517518743191 150132632410602776278114787)
            ·
              refine ⟨225198948615904164417172181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150132632410602776278114787 225198948615904164417172181)
              ·
                refine ⟨5278100358185253853527473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 225198948615904164417172181 5278100358185253853527473)
                ·
                  refine ⟨3958575268638940390145605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5278100358185253853527473 3958575268638940390145605)
                  ·
                    refine ⟨742232862869801323152301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3958575268638940390145605 742232862869801323152301)
                    ·
                      rfl

theorem cell22_2168240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 2, 4].length) (baseStart_2168240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168240 prefixEnd_2168240 := by exact prefixLift 2168240
  have htrace : WordTrace (prefixWord ++ tailWord_2168240) baseStart_2168240 baseEnd_2168240 := by
    simpa [prefixWord, tailWord_2168240, baseEnd_2168240] using wordTrace_append hprefix tailTrace_2168240
  have hstable : (prefixWord ++ tailWord_2168240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168240).length < 2 ^ (prefixWord ++ tailWord_2168240).sum := by decide
  have hdescent : baseEnd_2168240 < baseStart_2168240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168276 : List Nat := [2, 4, 1, 2, 4, 1, 1, 1, 1, 5]
def baseStart_2168276 : Nat := 118140960795 + 2168276 * 2 ^ 59
def prefixEnd_2168276 : Nat := 4983230072969 + 3 ^ 40 * 2168276 * 2
def baseEnd_2168276 : Nat := 742245186405509229252191

theorem tailTrace_2168276 : CollatzResearch.WordTrace tailWord_2168276 prefixEnd_2168276 742245186405509229252191 := by
  unfold tailWord_2168276
  simp only [CollatzResearch.WordTrace]
  refine ⟨39541761346356919451930341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52722348461809225935907121 39541761346356919451930341)
  ·
    refine ⟨7414080252441922397236939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39541761346356919451930341 7414080252441922397236939)
    ·
      refine ⟨11121120378662883595855409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7414080252441922397236939 11121120378662883595855409)
      ·
        refine ⟨8340840283997162696891557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11121120378662883595855409 8340840283997162696891557)
        ·
          refine ⟨1563907553249468005667167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8340840283997162696891557 1563907553249468005667167)
          ·
            refine ⟨2345861329874202008500751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1563907553249468005667167 2345861329874202008500751)
            ·
              refine ⟨3518791994811303012751127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2345861329874202008500751 3518791994811303012751127)
              ·
                refine ⟨5278187992216954519126691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3518791994811303012751127 5278187992216954519126691)
                ·
                  refine ⟨7917281988325431778690037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5278187992216954519126691 7917281988325431778690037)
                  ·
                    refine ⟨742245186405509229252191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7917281988325431778690037 742245186405509229252191)
                    ·
                      rfl

theorem cell22_2168276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_2168276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168276 prefixEnd_2168276 := by exact prefixLift 2168276
  have htrace : WordTrace (prefixWord ++ tailWord_2168276) baseStart_2168276 baseEnd_2168276 := by
    simpa [prefixWord, tailWord_2168276, baseEnd_2168276] using wordTrace_append hprefix tailTrace_2168276
  have hstable : (prefixWord ++ tailWord_2168276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168276).length < 2 ^ (prefixWord ++ tailWord_2168276).sum := by decide
  have hdescent : baseEnd_2168276 < baseStart_2168276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168287 : List Nat := [1, 1, 2, 3, 3, 1, 1, 4, 3, 3]
def baseStart_2168287 : Nat := 118140960795 + 2168287 * 2 ^ 59
def prefixEnd_2168287 : Nat := 4983230072969 + 3 ^ 40 * 2168287 * 2
def baseEnd_2168287 : Nat := 742248951930308867227157

theorem tailTrace_2168287 : CollatzResearch.WordTrace tailWord_2168287 prefixEnd_2168287 742248951930308867227157 := by
  unfold tailWord_2168287
  simp only [CollatzResearch.WordTrace]
  refine ⟨79083923895673987782511115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52722615930449325188340743 79083923895673987782511115)
  ·
    refine ⟨118625885843510981673766673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79083923895673987782511115 118625885843510981673766673)
    ·
      refine ⟨88969414382633236255325005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118625885843510981673766673 88969414382633236255325005)
      ·
        refine ⟨33363530393487463595746877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88969414382633236255325005 33363530393487463595746877)
        ·
          refine ⟨12511323897557798848405079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33363530393487463595746877 12511323897557798848405079)
          ·
            refine ⟨18766985846336698272607619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12511323897557798848405079 18766985846336698272607619)
            ·
              refine ⟨28150478769505047408911429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18766985846336698272607619 28150478769505047408911429)
              ·
                refine ⟨5278214769282196389170893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28150478769505047408911429 5278214769282196389170893)
                ·
                  refine ⟨1979330538480823645939085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5278214769282196389170893 1979330538480823645939085)
                  ·
                    refine ⟨742248951930308867227157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1979330538480823645939085 742248951930308867227157)
                    ·
                      rfl

theorem cell22_2168287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 3, 3].length) (baseStart_2168287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168287 prefixEnd_2168287 := by exact prefixLift 2168287
  have htrace : WordTrace (prefixWord ++ tailWord_2168287) baseStart_2168287 baseEnd_2168287 := by
    simpa [prefixWord, tailWord_2168287, baseEnd_2168287] using wordTrace_append hprefix tailTrace_2168287
  have hstable : (prefixWord ++ tailWord_2168287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168287).length < 2 ^ (prefixWord ++ tailWord_2168287).sum := by decide
  have hdescent : baseEnd_2168287 < baseStart_2168287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168321 : List Nat := [1, 2, 4, 1, 4, 2, 1, 1, 3, 3]
def baseStart_2168321 : Nat := 118140960795 + 2168321 * 2 ^ 59
def prefixEnd_2168321 : Nat := 4983230072969 + 3 ^ 40 * 2168321 * 2
def baseEnd_2168321 : Nat := 742260590825144111877053

theorem tailTrace_2168321 : CollatzResearch.WordTrace tailWord_2168321 prefixEnd_2168321 742260590825144111877053 := by
  unfold tailWord_2168321
  simp only [CollatzResearch.WordTrace]
  refine ⟨79085163977550811589248817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52723442651700541059499211 79085163977550811589248817)
  ·
    refine ⟨59313872983163108691936613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79085163977550811589248817 59313872983163108691936613)
    ·
      refine ⟨11121351184343082879738115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59313872983163108691936613 11121351184343082879738115)
      ·
        refine ⟨16682026776514624319607173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11121351184343082879738115 16682026776514624319607173)
        ·
          refine ⟨3127880020596492059926345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16682026776514624319607173 3127880020596492059926345)
          ·
            refine ⟨2345910015447369044944759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3127880020596492059926345 2345910015447369044944759)
            ·
              refine ⟨3518865023171053567417139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2345910015447369044944759 3518865023171053567417139)
              ·
                refine ⟨5278297534756580351125709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3518865023171053567417139 5278297534756580351125709)
                ·
                  refine ⟨1979361575533717631672141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5278297534756580351125709 1979361575533717631672141)
                  ·
                    refine ⟨742260590825144111877053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1979361575533717631672141 742260590825144111877053)
                    ·
                      rfl

theorem cell22_2168321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_2168321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168321 prefixEnd_2168321 := by exact prefixLift 2168321
  have htrace : WordTrace (prefixWord ++ tailWord_2168321) baseStart_2168321 baseEnd_2168321 := by
    simpa [prefixWord, tailWord_2168321, baseEnd_2168321] using wordTrace_append hprefix tailTrace_2168321
  have hstable : (prefixWord ++ tailWord_2168321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168321).length < 2 ^ (prefixWord ++ tailWord_2168321).sum := by decide
  have hdescent : baseEnd_2168321 < baseStart_2168321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168334 : List Nat := [4, 1, 1, 2, 4, 1, 1, 3, 5]
def baseStart_2168334 : Nat := 118140960795 + 2168334 * 2 ^ 59
def prefixEnd_2168334 : Nat := 4983230072969 + 3 ^ 40 * 2168334 * 2
def baseEnd_2168334 : Nat := 247421680330272137100671

theorem tailTrace_2168334 : CollatzResearch.WordTrace tailWord_2168334 prefixEnd_2168334 247421680330272137100671 := by
  unfold tailWord_2168334
  simp only [CollatzResearch.WordTrace]
  refine ⟨9885704765812964351184007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52723758751002476539648037 9885704765812964351184007)
  ·
    refine ⟨14828557148719446526776011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9885704765812964351184007 14828557148719446526776011)
    ·
      refine ⟨22242835723079169790164017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14828557148719446526776011 22242835723079169790164017)
      ·
        refine ⟨16682126792309377342623013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22242835723079169790164017 16682126792309377342623013)
        ·
          refine ⟨3127898773558008251741815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16682126792309377342623013 3127898773558008251741815)
          ·
            refine ⟨4691848160337012377612723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3127898773558008251741815 4691848160337012377612723)
            ·
              refine ⟨7037772240505518566419085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4691848160337012377612723 7037772240505518566419085)
              ·
                refine ⟨2639164590189569462407157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7037772240505518566419085 2639164590189569462407157)
                ·
                  refine ⟨247421680330272137100671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2639164590189569462407157 247421680330272137100671)
                  ·
                    rfl

theorem cell22_2168334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_2168334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168334 prefixEnd_2168334 := by exact prefixLift 2168334
  have htrace : WordTrace (prefixWord ++ tailWord_2168334) baseStart_2168334 baseEnd_2168334 := by
    simpa [prefixWord, tailWord_2168334, baseEnd_2168334] using wordTrace_append hprefix tailTrace_2168334
  have hstable : (prefixWord ++ tailWord_2168334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168334).length < 2 ^ (prefixWord ++ tailWord_2168334).sum := by decide
  have hdescent : baseEnd_2168334 < baseStart_2168334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168394 : List Nat := [3, 1, 2, 1, 1, 3, 1, 5, 2, 3]
def baseStart_2168394 : Nat := 118140960795 + 2168394 * 2 ^ 59
def prefixEnd_2168394 : Nat := 4983230072969 + 3 ^ 40 * 2168394 * 2
def baseEnd_2168394 : Nat := 742285580216996254801829

theorem tailTrace_2168394 : CollatzResearch.WordTrace tailWord_2168394 prefixEnd_2168394 742285580216996254801829 := by
  unfold tailWord_2168394
  simp only [CollatzResearch.WordTrace]
  refine ⟨19771956626571586264164059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52725217670857563371104157 19771956626571586264164059)
  ·
    refine ⟨29657934939857379396246089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19771956626571586264164059 29657934939857379396246089)
    ·
      refine ⟨22243451204893034547184567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29657934939857379396246089 22243451204893034547184567)
      ·
        refine ⟨33365176807339551820776851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22243451204893034547184567 33365176807339551820776851)
        ·
          refine ⟨50047765211009327731165277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33365176807339551820776851 50047765211009327731165277)
          ·
            refine ⟨18767911954128497899186979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50047765211009327731165277 18767911954128497899186979)
            ·
              refine ⟨28151867931192746848780469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18767911954128497899186979 28151867931192746848780469)
              ·
                refine ⟨2639237618549320017073169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28151867931192746848780469 2639237618549320017073169)
                ·
                  refine ⟨1979428213911990012804877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2639237618549320017073169 1979428213911990012804877)
                  ·
                    refine ⟨742285580216996254801829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1979428213911990012804877 742285580216996254801829)
                    ·
                      rfl

theorem cell22_2168394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_2168394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168394 prefixEnd_2168394 := by exact prefixLift 2168394
  have htrace : WordTrace (prefixWord ++ tailWord_2168394) baseStart_2168394 baseEnd_2168394 := by
    simpa [prefixWord, tailWord_2168394, baseEnd_2168394] using wordTrace_append hprefix tailTrace_2168394
  have hstable : (prefixWord ++ tailWord_2168394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168394).length < 2 ^ (prefixWord ++ tailWord_2168394).sum := by decide
  have hdescent : baseEnd_2168394 < baseStart_2168394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168527 : List Nat := [1, 1, 2, 1, 1, 3, 1, 5, 1, 6]
def baseStart_2168527 : Nat := 118140960795 + 2168527 * 2 ^ 59
def prefixEnd_2168527 : Nat := 4983230072969 + 3 ^ 40 * 2168527 * 2
def baseEnd_2168527 : Nat := 742331108835028241226421

theorem tailTrace_2168527 : CollatzResearch.WordTrace tailWord_2168527 prefixEnd_2168527 742331108835028241226421 := by
  unfold tailWord_2168527
  simp only [CollatzResearch.WordTrace]
  refine ⟨79092677414804508771247835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52728451609869672514165223 79092677414804508771247835)
  ·
    refine ⟨118639016122206763156871753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79092677414804508771247835 118639016122206763156871753)
    ·
      refine ⟨88979262091655072367653815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118639016122206763156871753 88979262091655072367653815)
      ·
        refine ⟨133468893137482608551480723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88979262091655072367653815 133468893137482608551480723)
        ·
          refine ⟨200203339706223912827221085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133468893137482608551480723 200203339706223912827221085)
          ·
            refine ⟨75076252389833967310207907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 200203339706223912827221085 75076252389833967310207907)
            ·
              refine ⟨112614378584750950965311861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75076252389833967310207907 112614378584750950965311861)
              ·
                refine ⟨10557597992320401652997987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 112614378584750950965311861 10557597992320401652997987)
                ·
                  refine ⟨15836396988480602479496981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10557597992320401652997987 15836396988480602479496981)
                  ·
                    refine ⟨742331108835028241226421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15836396988480602479496981 742331108835028241226421)
                    ·
                      rfl

theorem cell22_2168527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 1, 6].length) (baseStart_2168527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168527 prefixEnd_2168527 := by exact prefixLift 2168527
  have htrace : WordTrace (prefixWord ++ tailWord_2168527) baseStart_2168527 baseEnd_2168527 := by
    simpa [prefixWord, tailWord_2168527, baseEnd_2168527] using wordTrace_append hprefix tailTrace_2168527
  have hstable : (prefixWord ++ tailWord_2168527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168527).length < 2 ^ (prefixWord ++ tailWord_2168527).sum := by decide
  have hdescent : baseEnd_2168527 < baseStart_2168527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168529 : List Nat := [1, 2, 2, 1, 2, 5, 1, 2, 1, 5]
def baseStart_2168529 : Nat := 118140960795 + 2168529 * 2 ^ 59
def prefixEnd_2168529 : Nat := 4983230072969 + 3 ^ 40 * 2168529 * 2
def baseEnd_2168529 : Nat := 742331793475900902676415

theorem tailTrace_2168529 : CollatzResearch.WordTrace tailWord_2168529 prefixEnd_2168529 742331793475900902676415 := by
  unfold tailWord_2168529
  simp only [CollatzResearch.WordTrace]
  refine ⟨79092750360797263112820641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52728500240531508741880427 79092750360797263112820641)
  ·
    refine ⟨59319562770597947334615481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79092750360797263112820641 59319562770597947334615481)
    ·
      refine ⟨44489672077948460500961611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59319562770597947334615481 44489672077948460500961611)
      ·
        refine ⟨66734508116922690751442417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44489672077948460500961611 66734508116922690751442417)
        ·
          refine ⟨50050881087692018063581813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66734508116922690751442417 50050881087692018063581813)
          ·
            refine ⟨4692270101971126693460795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50050881087692018063581813 4692270101971126693460795)
            ·
              refine ⟨7038405152956690040191193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4692270101971126693460795 7038405152956690040191193)
              ·
                refine ⟨5278803864717517530143395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7038405152956690040191193 5278803864717517530143395)
                ·
                  refine ⟨7918205797076276295215093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5278803864717517530143395 7918205797076276295215093)
                  ·
                    refine ⟨742331793475900902676415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7918205797076276295215093 742331793475900902676415)
                    ·
                      rfl

theorem cell22_2168529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_2168529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168529 prefixEnd_2168529 := by exact prefixLift 2168529
  have htrace : WordTrace (prefixWord ++ tailWord_2168529) baseStart_2168529 baseEnd_2168529 := by
    simpa [prefixWord, tailWord_2168529, baseEnd_2168529] using wordTrace_append hprefix tailTrace_2168529
  have hstable : (prefixWord ++ tailWord_2168529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168529).length < 2 ^ (prefixWord ++ tailWord_2168529).sum := by decide
  have hdescent : baseEnd_2168529 < baseStart_2168529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168544 : List Nat := [2, 1, 1, 3, 1, 2, 4, 2, 2, 4]
def baseStart_2168544 : Nat := 118140960795 + 2168544 * 2 ^ 59
def prefixEnd_2168544 : Nat := 4983230072969 + 3 ^ 40 * 2168544 * 2
def baseEnd_2168544 : Nat := 742336928282445863551369

theorem tailTrace_2168544 : CollatzResearch.WordTrace tailWord_2168544 prefixEnd_2168544 742336928282445863551369 := by
  unfold tailWord_2168544
  simp only [CollatzResearch.WordTrace]
  refine ⟨39546648727871460337308343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52728864970495280449744457 39546648727871460337308343)
  ·
    refine ⟨59319973091807190505962515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39546648727871460337308343 59319973091807190505962515)
    ·
      refine ⟨88979959637710785758943773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59319973091807190505962515 88979959637710785758943773)
      ·
        refine ⟨33367484864141544659603915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88979959637710785758943773 33367484864141544659603915)
        ·
          refine ⟨50051227296212316989405873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33367484864141544659603915 50051227296212316989405873)
          ·
            refine ⟨37538420472159237742054405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50051227296212316989405873 37538420472159237742054405)
            ·
              refine ⟨7038453838529857076635201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37538420472159237742054405 7038453838529857076635201)
              ·
                refine ⟨5278840378897392807476401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7038453838529857076635201 5278840378897392807476401)
                ·
                  refine ⟨3959130284173044605607301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5278840378897392807476401 3959130284173044605607301)
                  ·
                    refine ⟨742336928282445863551369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3959130284173044605607301 742336928282445863551369)
                    ·
                      rfl

theorem cell22_2168544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 2, 4].length) (baseStart_2168544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168544 prefixEnd_2168544 := by exact prefixLift 2168544
  have htrace : WordTrace (prefixWord ++ tailWord_2168544) baseStart_2168544 baseEnd_2168544 := by
    simpa [prefixWord, tailWord_2168544, baseEnd_2168544] using wordTrace_append hprefix tailTrace_2168544
  have hstable : (prefixWord ++ tailWord_2168544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168544).length < 2 ^ (prefixWord ++ tailWord_2168544).sum := by decide
  have hdescent : baseEnd_2168544 < baseStart_2168544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168604 : List Nat := [2, 2, 3, 1, 1, 2, 3, 1, 7]
def baseStart_2168604 : Nat := 118140960795 + 2168604 * 2 ^ 59
def prefixEnd_2168604 : Nat := 4983230072969 + 3 ^ 40 * 2168604 * 2
def baseEnd_2168604 : Nat := 247452489169541902350395

theorem tailTrace_2168604 : CollatzResearch.WordTrace tailWord_2168604 prefixEnd_2168604 247452489169541902350395 := by
  unfold tailWord_2168604
  simp only [CollatzResearch.WordTrace]
  refine ⟨39547742917762775460900433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52730323890350367281200577 39547742917762775460900433)
  ·
    refine ⟨29660807188322081595675325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39547742917762775460900433 29660807188322081595675325)
    ·
      refine ⟨11122802695620780598378247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29660807188322081595675325 11122802695620780598378247)
      ·
        refine ⟨16684204043431170897567371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11122802695620780598378247 16684204043431170897567371)
        ·
          refine ⟨25026306065146756346351057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16684204043431170897567371 25026306065146756346351057)
          ·
            refine ⟨18769729548860067259763293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25026306065146756346351057 18769729548860067259763293)
            ·
              refine ⟨7038648580822525222411235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18769729548860067259763293 7038648580822525222411235)
              ·
                refine ⟨10557972871233787833616853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7038648580822525222411235 10557972871233787833616853)
                ·
                  refine ⟨247452489169541902350395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10557972871233787833616853 247452489169541902350395)
                  ·
                    rfl

theorem cell22_2168604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 7].length) (baseStart_2168604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168604 prefixEnd_2168604 := by exact prefixLift 2168604
  have htrace : WordTrace (prefixWord ++ tailWord_2168604) baseStart_2168604 baseEnd_2168604 := by
    simpa [prefixWord, tailWord_2168604, baseEnd_2168604] using wordTrace_append hprefix tailTrace_2168604
  have hstable : (prefixWord ++ tailWord_2168604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168604).length < 2 ^ (prefixWord ++ tailWord_2168604).sum := by decide
  have hdescent : baseEnd_2168604 < baseStart_2168604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168608 : List Nat := [2, 1, 1, 5, 1, 1, 1, 6, 1, 3]
def baseStart_2168608 : Nat := 118140960795 + 2168608 * 2 ^ 59
def prefixEnd_2168608 : Nat := 4983230072969 + 3 ^ 40 * 2168608 * 2
def baseEnd_2168608 : Nat := 742358836790371029951173

theorem tailTrace_2168608 : CollatzResearch.WordTrace tailWord_2168608 prefixEnd_2168608 742358836790371029951173 := by
  unfold tailWord_2168608
  simp only [CollatzResearch.WordTrace]
  refine ⟨39547815863755529802473239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52730421151674039736630985 39547815863755529802473239)
  ·
    refine ⟨59321723795633294703709859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39547815863755529802473239 59321723795633294703709859)
    ·
      refine ⟨88982585693449942055564789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59321723795633294703709859 88982585693449942055564789)
      ·
        refine ⟨8342117408760932067709199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88982585693449942055564789 8342117408760932067709199)
        ·
          refine ⟨12513176113141398101563799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8342117408760932067709199 12513176113141398101563799)
          ·
            refine ⟨18769764169712097152345699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12513176113141398101563799 18769764169712097152345699)
            ·
              refine ⟨28154646254568145728518549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18769764169712097152345699 28154646254568145728518549)
              ·
                refine ⟨1319749043182881831024307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28154646254568145728518549 1319749043182881831024307)
                ·
                  refine ⟨1979623564774322746536461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1319749043182881831024307 1979623564774322746536461)
                  ·
                    refine ⟨742358836790371029951173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1979623564774322746536461 742358836790371029951173)
                    ·
                      rfl

theorem cell22_2168608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 6, 1, 3].length) (baseStart_2168608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168608 prefixEnd_2168608 := by exact prefixLift 2168608
  have htrace : WordTrace (prefixWord ++ tailWord_2168608) baseStart_2168608 baseEnd_2168608 := by
    simpa [prefixWord, tailWord_2168608, baseEnd_2168608] using wordTrace_append hprefix tailTrace_2168608
  have hstable : (prefixWord ++ tailWord_2168608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168608).length < 2 ^ (prefixWord ++ tailWord_2168608).sum := by decide
  have hdescent : baseEnd_2168608 < baseStart_2168608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168702 : List Nat := [4, 2, 3, 1, 1, 2, 3, 1, 1, 4]
def baseStart_2168702 : Nat := 118140960795 + 2168702 * 2 ^ 59
def prefixEnd_2168702 : Nat := 4983230072969 + 3 ^ 40 * 2168702 * 2
def baseEnd_2168702 : Nat := 742391014911386118100885

theorem tailTrace_2168702 : CollatzResearch.WordTrace tailWord_2168702 prefixEnd_2168702 742391014911386118100885 := by
  unfold tailWord_2168702
  simp only [CollatzResearch.WordTrace]
  refine ⟨9887382523646314207358545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52732706792780342439245573 9887382523646314207358545)
  ·
    refine ⟨7415536892734735655518909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9887382523646314207358545 7415536892734735655518909)
    ·
      refine ⟨2780826334775525870819591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7415536892734735655518909 2780826334775525870819591)
      ·
        refine ⟨4171239502163288806229387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2780826334775525870819591 4171239502163288806229387)
        ·
          refine ⟨6256859253244933209344081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4171239502163288806229387 6256859253244933209344081)
          ·
            refine ⟨4692644439933699907008061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6256859253244933209344081 4692644439933699907008061)
            ·
              refine ⟨1759741664975137465128023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4692644439933699907008061 1759741664975137465128023)
              ·
                refine ⟨2639612497462706197692035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1759741664975137465128023 2639612497462706197692035)
                ·
                  refine ⟨3959418746194059296538053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2639612497462706197692035 3959418746194059296538053)
                  ·
                    refine ⟨742391014911386118100885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3959418746194059296538053 742391014911386118100885)
                    ·
                      rfl

theorem cell22_2168702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_2168702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168702 prefixEnd_2168702 := by exact prefixLift 2168702
  have htrace : WordTrace (prefixWord ++ tailWord_2168702) baseStart_2168702 baseEnd_2168702 := by
    simpa [prefixWord, tailWord_2168702, baseEnd_2168702] using wordTrace_append hprefix tailTrace_2168702
  have hstable : (prefixWord ++ tailWord_2168702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168702).length < 2 ^ (prefixWord ++ tailWord_2168702).sum := by decide
  have hdescent : baseEnd_2168702 < baseStart_2168702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168711 : List Nat := [1, 1, 4, 2, 5, 9]
def baseStart_2168711 : Nat := 118140960795 + 2168711 * 2 ^ 59
def prefixEnd_2168711 : Nat := 4983230072969 + 3 ^ 40 * 2168711 * 2
def baseEnd_2168711 : Nat := 9165359207349544378097

theorem tailTrace_2168711 : CollatzResearch.WordTrace tailWord_2168711 prefixEnd_2168711 9165359207349544378097 := by
  unfold tailWord_2168711
  simp only [CollatzResearch.WordTrace]
  refine ⟨79099388446137908195945987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52732925630758605463963991 79099388446137908195945987)
  ·
    refine ⟨118649082669206862293918981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79099388446137908195945987 118649082669206862293918981)
    ·
      refine ⟨22246703000476286680109809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118649082669206862293918981 22246703000476286680109809)
      ·
        refine ⟨16685027250357215010082357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22246703000476286680109809 16685027250357215010082357)
        ·
          refine ⟨1564221304720988907195221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16685027250357215010082357 1564221304720988907195221)
          ·
            refine ⟨9165359207349544378097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1564221304720988907195221 9165359207349544378097)
            ·
              rfl

theorem cell22_2168711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 9].length) (baseStart_2168711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168711 prefixEnd_2168711 := by exact prefixLift 2168711
  have htrace : WordTrace (prefixWord ++ tailWord_2168711) baseStart_2168711 baseEnd_2168711 := by
    simpa [prefixWord, tailWord_2168711, baseEnd_2168711] using wordTrace_append hprefix tailTrace_2168711
  have hstable : (prefixWord ++ tailWord_2168711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168711).length < 2 ^ (prefixWord ++ tailWord_2168711).sum := by decide
  have hdescent : baseEnd_2168711 < baseStart_2168711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168739 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 9]
def baseStart_2168739 : Nat := 118140960795 + 2168739 * 2 ^ 59
def prefixEnd_2168739 : Nat := 4983230072969 + 3 ^ 40 * 2168739 * 2
def baseEnd_2168739 : Nat := 247467893589176784975257

theorem tailTrace_2168739 : CollatzResearch.WordTrace tailWord_2168739 prefixEnd_2168739 247467893589176784975257 := by
  unfold tailWord_2168739
  simp only [CollatzResearch.WordTrace]
  refine ⟨79100409690036468977965271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52733606460024312651976847 79100409690036468977965271)
  ·
    refine ⟨118650614535054703466947907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79100409690036468977965271 118650614535054703466947907)
    ·
      refine ⟨177975921802582055200421861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118650614535054703466947907 177975921802582055200421861)
      ·
        refine ⟨33370485337984135350079099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 177975921802582055200421861 33370485337984135350079099)
        ·
          refine ⟨50055728006976203025118649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33370485337984135350079099 50055728006976203025118649)
          ·
            refine ⟨37541796005232152268838987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50055728006976203025118649 37541796005232152268838987)
            ·
              refine ⟨56312694007848228403258481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37541796005232152268838987 56312694007848228403258481)
              ·
                refine ⟨42234520505886171302443861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56312694007848228403258481 42234520505886171302443861)
                ·
                  refine ⟨247467893589176784975257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42234520505886171302443861 247467893589176784975257)
                  ·
                    rfl

theorem cell22_2168739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 9].length) (baseStart_2168739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168739 prefixEnd_2168739 := by exact prefixLift 2168739
  have htrace : WordTrace (prefixWord ++ tailWord_2168739) baseStart_2168739 baseEnd_2168739 := by
    simpa [prefixWord, tailWord_2168739, baseEnd_2168739] using wordTrace_append hprefix tailTrace_2168739
  have hstable : (prefixWord ++ tailWord_2168739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168739).length < 2 ^ (prefixWord ++ tailWord_2168739).sum := by decide
  have hdescent : baseEnd_2168739 < baseStart_2168739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168743 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 5, 3]
def baseStart_2168743 : Nat := 118140960795 + 2168743 * 2 ^ 59
def prefixEnd_2168743 : Nat := 4983230072969 + 3 ^ 40 * 2168743 * 2
def baseEnd_2168743 : Nat := 742405050049275677825759

theorem tailTrace_2168743 : CollatzResearch.WordTrace tailWord_2168743 prefixEnd_2168743 742405050049275677825759 := by
  unfold tailWord_2168743
  simp only [CollatzResearch.WordTrace]
  refine ⟨79100555582021977661110883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52733703721347985107407255 79100555582021977661110883)
  ·
    refine ⟨118650833373032966491666325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79100555582021977661110883 118650833373032966491666325)
    ·
      refine ⟨5561757814360920304296859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 118650833373032966491666325 5561757814360920304296859)
      ·
        refine ⟨8342636721541380456445289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5561757814360920304296859 8342636721541380456445289)
        ·
          refine ⟨6256977541156035342333967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8342636721541380456445289 6256977541156035342333967)
          ·
            refine ⟨9385466311734053013500951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6256977541156035342333967 9385466311734053013500951)
            ·
              refine ⟨14078199467601079520251427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9385466311734053013500951 14078199467601079520251427)
              ·
                refine ⟨21117299201401619280377141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14078199467601079520251427 21117299201401619280377141)
                ·
                  refine ⟨1979746800131401807535357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21117299201401619280377141 1979746800131401807535357)
                  ·
                    refine ⟨742405050049275677825759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1979746800131401807535357 742405050049275677825759)
                    ·
                      rfl

theorem cell22_2168743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_2168743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168743 prefixEnd_2168743 := by exact prefixLift 2168743
  have htrace : WordTrace (prefixWord ++ tailWord_2168743) baseStart_2168743 baseEnd_2168743 := by
    simpa [prefixWord, tailWord_2168743, baseEnd_2168743] using wordTrace_append hprefix tailTrace_2168743
  have hstable : (prefixWord ++ tailWord_2168743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168743).length < 2 ^ (prefixWord ++ tailWord_2168743).sum := by decide
  have hdescent : baseEnd_2168743 < baseStart_2168743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168760 : List Nat := [2, 1, 2, 1, 2, 3, 4, 3, 1, 3]
def baseStart_2168760 : Nat := 118140960795 + 2168760 * 2 ^ 59
def prefixEnd_2168760 : Nat := 4983230072969 + 3 ^ 40 * 2168760 * 2
def baseEnd_2168760 : Nat := 742410869496693300150707

theorem tailTrace_2168760 : CollatzResearch.WordTrace tailWord_2168760 prefixEnd_2168760 742410869496693300150707 := by
  unfold tailWord_2168760
  simp only [CollatzResearch.WordTrace]
  refine ⟨39550587811480194782239867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52734117081973593042986489 39550587811480194782239867)
  ·
    refine ⟨59325881717220292173359801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39550587811480194782239867 59325881717220292173359801)
    ·
      refine ⟨44494411287915219130019851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59325881717220292173359801 44494411287915219130019851)
      ·
        refine ⟨66741616931872828695029777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44494411287915219130019851 66741616931872828695029777)
        ·
          refine ⟨50056212698904621521272333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66741616931872828695029777 50056212698904621521272333)
          ·
            refine ⟨18771079762089233070477125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50056212698904621521272333 18771079762089233070477125)
            ·
              refine ⟨3519577455391731200714461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18771079762089233070477125 3519577455391731200714461)
              ·
                refine ⟨1319841545771899200267923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3519577455391731200714461 1319841545771899200267923)
                ·
                  refine ⟨1979762318657848800401885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1319841545771899200267923 1979762318657848800401885)
                  ·
                    refine ⟨742410869496693300150707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1979762318657848800401885 742410869496693300150707)
                    ·
                      rfl

theorem cell22_2168760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3, 1, 3].length) (baseStart_2168760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168760 prefixEnd_2168760 := by exact prefixLift 2168760
  have htrace : WordTrace (prefixWord ++ tailWord_2168760) baseStart_2168760 baseEnd_2168760 := by
    simpa [prefixWord, tailWord_2168760, baseEnd_2168760] using wordTrace_append hprefix tailTrace_2168760
  have hstable : (prefixWord ++ tailWord_2168760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168760).length < 2 ^ (prefixWord ++ tailWord_2168760).sum := by decide
  have hdescent : baseEnd_2168760 < baseStart_2168760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168801 : List Nat := [1, 2, 3, 1, 2, 1, 4, 2, 6]
def baseStart_2168801 : Nat := 118140960795 + 2168801 * 2 ^ 59
def prefixEnd_2168801 : Nat := 4983230072969 + 3 ^ 40 * 2168801 * 2
def baseEnd_2168801 : Nat := 247474968211527619958527

theorem tailTrace_2168801 : CollatzResearch.WordTrace tailWord_2168801 prefixEnd_2168801 247474968211527619958527 := by
  unfold tailWord_2168801
  simp only [CollatzResearch.WordTrace]
  refine ⟨79102671015811853566722257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52735114010541235711148171 79102671015811853566722257)
  ·
    refine ⟨59327003261858890175041693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79102671015811853566722257 59327003261858890175041693)
    ·
      refine ⟨22247626223197083815640635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59327003261858890175041693 22247626223197083815640635)
      ·
        refine ⟨33371439334795625723460953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22247626223197083815640635 33371439334795625723460953)
        ·
          refine ⟨25028579501096719292595715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33371439334795625723460953 25028579501096719292595715)
          ·
            refine ⟨37542869251645078938893573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25028579501096719292595715 37542869251645078938893573)
            ·
              refine ⟨7039287984683452301042545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37542869251645078938893573 7039287984683452301042545)
              ·
                refine ⟨5279465988512589225781909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7039287984683452301042545 5279465988512589225781909)
                ·
                  refine ⟨247474968211527619958527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5279465988512589225781909 247474968211527619958527)
                  ·
                    rfl

theorem cell22_2168801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 6].length) (baseStart_2168801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168801 prefixEnd_2168801 := by exact prefixLift 2168801
  have htrace : WordTrace (prefixWord ++ tailWord_2168801) baseStart_2168801 baseEnd_2168801 := by
    simpa [prefixWord, tailWord_2168801, baseEnd_2168801] using wordTrace_append hprefix tailTrace_2168801
  have hstable : (prefixWord ++ tailWord_2168801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168801).length < 2 ^ (prefixWord ++ tailWord_2168801).sum := by decide
  have hdescent : baseEnd_2168801 < baseStart_2168801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168803 : List Nat := [1, 1, 1, 6, 1, 2, 1, 4, 1, 4]
def baseStart_2168803 : Nat := 118140960795 + 2168803 * 2 ^ 59
def prefixEnd_2168803 : Nat := 4983230072969 + 3 ^ 40 * 2168803 * 2
def baseEnd_2168803 : Nat := 742425589275455521325575

theorem tailTrace_2168803 : CollatzResearch.WordTrace tailWord_2168803 prefixEnd_2168803 742425589275455521325575 := by
  unfold tailWord_2168803
  simp only [CollatzResearch.WordTrace]
  refine ⟨79102743961804607908295063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52735162641203071938863375 79102743961804607908295063)
  ·
    refine ⟨118654115942706911862442595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79102743961804607908295063 118654115942706911862442595)
    ·
      refine ⟨177981173914060367793663893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118654115942706911862442595 177981173914060367793663893)
      ·
        refine ⟨8342867527221579740327995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 177981173914060367793663893 8342867527221579740327995)
        ·
          refine ⟨12514301290832369610491993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8342867527221579740327995 12514301290832369610491993)
          ·
            refine ⟨9385725968124277207868995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12514301290832369610491993 9385725968124277207868995)
            ·
              refine ⟨14078588952186415811803493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9385725968124277207868995 14078588952186415811803493)
              ·
                refine ⟨2639735428534952964713155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14078588952186415811803493 2639735428534952964713155)
                ·
                  refine ⟨3959603142802429447069733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2639735428534952964713155 3959603142802429447069733)
                  ·
                    refine ⟨742425589275455521325575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3959603142802429447069733 742425589275455521325575)
                    ·
                      rfl

theorem cell22_2168803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 4].length) (baseStart_2168803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168803 prefixEnd_2168803 := by exact prefixLift 2168803
  have htrace : WordTrace (prefixWord ++ tailWord_2168803) baseStart_2168803 baseEnd_2168803 := by
    simpa [prefixWord, tailWord_2168803, baseEnd_2168803] using wordTrace_append hprefix tailTrace_2168803
  have hstable : (prefixWord ++ tailWord_2168803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168803).length < 2 ^ (prefixWord ++ tailWord_2168803).sum := by decide
  have hdescent : baseEnd_2168803 < baseStart_2168803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168816 : List Nat := [2, 1, 1, 1, 3, 2, 2, 4, 1, 5]
def baseStart_2168816 : Nat := 118140960795 + 2168816 * 2 ^ 59
def prefixEnd_2168816 : Nat := 4983230072969 + 3 ^ 40 * 2168816 * 2
def baseEnd_2168816 : Nat := 742430039441127820750535

theorem tailTrace_2168816 : CollatzResearch.WordTrace tailWord_2168816 prefixEnd_2168816 742430039441127820750535 := by
  unfold tailWord_2168816
  simp only [CollatzResearch.WordTrace]
  refine ⟨39551609055378755564259151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52735478740505007419012201 39551609055378755564259151)
  ·
    refine ⟨59327413583068133346388727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39551609055378755564259151 59327413583068133346388727)
    ·
      refine ⟨88991120374602200019583091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59327413583068133346388727 88991120374602200019583091)
      ·
        refine ⟨133486680561903300029374637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88991120374602200019583091 133486680561903300029374637)
        ·
          refine ⟨50057505210713737511015489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133486680561903300029374637 50057505210713737511015489)
          ·
            refine ⟨37543128908035303133261617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50057505210713737511015489 37543128908035303133261617)
            ·
              refine ⟨28157346681026477349946213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37543128908035303133261617 28157346681026477349946213)
              ·
                refine ⟨5279502502692464503114915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28157346681026477349946213 5279502502692464503114915)
                ·
                  refine ⟨7919253754038696754672373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5279502502692464503114915 7919253754038696754672373)
                  ·
                    refine ⟨742430039441127820750535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7919253754038696754672373 742430039441127820750535)
                    ·
                      rfl

theorem cell22_2168816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 1, 5].length) (baseStart_2168816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168816 prefixEnd_2168816 := by exact prefixLift 2168816
  have htrace : WordTrace (prefixWord ++ tailWord_2168816) baseStart_2168816 baseEnd_2168816 := by
    simpa [prefixWord, tailWord_2168816, baseEnd_2168816] using wordTrace_append hprefix tailTrace_2168816
  have hstable : (prefixWord ++ tailWord_2168816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168816).length < 2 ^ (prefixWord ++ tailWord_2168816).sum := by decide
  have hdescent : baseEnd_2168816 < baseStart_2168816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168833 : List Nat := [1, 2, 4, 1, 2, 1, 1, 3, 4, 3]
def baseStart_2168833 : Nat := 118140960795 + 2168833 * 2 ^ 59
def prefixEnd_2168833 : Nat := 4983230072969 + 3 ^ 40 * 2168833 * 2
def baseEnd_2168833 : Nat := 742435858888545443075483

theorem tailTrace_2168833 : CollatzResearch.WordTrace tailWord_2168833 prefixEnd_2168833 742435858888545443075483 := by
  unfold tailWord_2168833
  simp only [CollatzResearch.WordTrace]
  refine ⟨79103838151695923031887153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52735892101130615354591435 79103838151695923031887153)
  ·
    refine ⟨59327878613771942273915365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79103838151695923031887153 59327878613771942273915365)
    ·
      refine ⟨11123977240082239176359131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59327878613771942273915365 11123977240082239176359131)
      ·
        refine ⟨16685965860123358764538697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11123977240082239176359131 16685965860123358764538697)
        ·
          refine ⟨12514474395092519073404023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16685965860123358764538697 12514474395092519073404023)
          ·
            refine ⟨18771711592638778610106035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12514474395092519073404023 18771711592638778610106035)
            ·
              refine ⟨28157567388958167915159053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18771711592638778610106035 28157567388958167915159053)
              ·
                refine ⟨10559087770859312968184645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28157567388958167915159053 10559087770859312968184645)
                ·
                  refine ⟨1979828957036121181534621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10559087770859312968184645 1979828957036121181534621)
                  ·
                    refine ⟨742435858888545443075483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1979828957036121181534621 742435858888545443075483)
                    ·
                      rfl

theorem cell22_2168833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_2168833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168833 prefixEnd_2168833 := by exact prefixLift 2168833
  have htrace : WordTrace (prefixWord ++ tailWord_2168833) baseStart_2168833 baseEnd_2168833 := by
    simpa [prefixWord, tailWord_2168833, baseEnd_2168833] using wordTrace_append hprefix tailTrace_2168833
  have hstable : (prefixWord ++ tailWord_2168833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168833).length < 2 ^ (prefixWord ++ tailWord_2168833).sum := by decide
  have hdescent : baseEnd_2168833 < baseStart_2168833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168865 : List Nat := [1, 2, 3, 2, 4, 1, 2, 1, 2, 4]
def baseStart_2168865 : Nat := 118140960795 + 2168865 * 2 ^ 59
def prefixEnd_2168865 : Nat := 4983230072969 + 3 ^ 40 * 2168865 * 2
def baseEnd_2168865 : Nat := 742446813142508026275385

theorem tailTrace_2168865 : CollatzResearch.WordTrace tailWord_2168865 prefixEnd_2168865 742446813142508026275385 := by
  unfold tailWord_2168865
  simp only [CollatzResearch.WordTrace]
  refine ⟨79105005287579992497052049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52736670191719994998034699 79105005287579992497052049)
  ·
    refine ⟨59328753965684994372789037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79105005287579992497052049 59328753965684994372789037)
    ·
      refine ⟨22248282737131872889795889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59328753965684994372789037 22248282737131872889795889)
      ·
        refine ⟨16686212052848904667346917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22248282737131872889795889 16686212052848904667346917)
        ·
          refine ⟨3128664759909169625127547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16686212052848904667346917 3128664759909169625127547)
          ·
            refine ⟨4692997139863754437691321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3128664759909169625127547 4692997139863754437691321)
            ·
              refine ⟨3519747854897815828268491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4692997139863754437691321 3519747854897815828268491)
              ·
                refine ⟨5279621782346723742402737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3519747854897815828268491 5279621782346723742402737)
                ·
                  refine ⟨3959716336760042806802053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5279621782346723742402737 3959716336760042806802053)
                  ·
                    refine ⟨742446813142508026275385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3959716336760042806802053 742446813142508026275385)
                    ·
                      rfl

theorem cell22_2168865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_2168865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168865 prefixEnd_2168865 := by exact prefixLift 2168865
  have htrace : WordTrace (prefixWord ++ tailWord_2168865) baseStart_2168865 baseEnd_2168865 := by
    simpa [prefixWord, tailWord_2168865, baseEnd_2168865] using wordTrace_append hprefix tailTrace_2168865
  have hstable : (prefixWord ++ tailWord_2168865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168865).length < 2 ^ (prefixWord ++ tailWord_2168865).sum := by decide
  have hdescent : baseEnd_2168865 < baseStart_2168865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168884 : List Nat := [2, 5, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_2168884 : Nat := 118140960795 + 2168884 * 2 ^ 59
def prefixEnd_2168884 : Nat := 4983230072969 + 3 ^ 40 * 2168884 * 2
def baseEnd_2168884 : Nat := 742453317230798310050327

theorem tailTrace_2168884 : CollatzResearch.WordTrace tailWord_2168884 prefixEnd_2168884 742453317230798310050327 := by
  unfold tailWord_2168884
  simp only [CollatzResearch.WordTrace]
  refine ⟨39552849137255579370996853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52737132183007439161329137 39552849137255579370996853)
  ·
    refine ⟨3708079606617710566030955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39552849137255579370996853 3708079606617710566030955)
    ·
      refine ⟨5562119409926565849046433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3708079606617710566030955 5562119409926565849046433)
      ·
        refine ⟨4171589557444924386784825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5562119409926565849046433 4171589557444924386784825)
        ·
          refine ⟨3128692168083693290088619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4171589557444924386784825 3128692168083693290088619)
          ·
            refine ⟨4693038252125539935132929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3128692168083693290088619 4693038252125539935132929)
            ·
              refine ⟨3519778689094154951349697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4693038252125539935132929 3519778689094154951349697)
              ·
                refine ⟨2639834016820616213512273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3519778689094154951349697 2639834016820616213512273)
                ·
                  refine ⟨1979875512615462160134205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2639834016820616213512273 1979875512615462160134205)
                  ·
                    refine ⟨742453317230798310050327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1979875512615462160134205 742453317230798310050327)
                    ·
                      rfl

theorem cell22_2168884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_2168884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168884 prefixEnd_2168884 := by exact prefixLift 2168884
  have htrace : WordTrace (prefixWord ++ tailWord_2168884) baseStart_2168884 baseEnd_2168884 := by
    simpa [prefixWord, tailWord_2168884, baseEnd_2168884] using wordTrace_append hprefix tailTrace_2168884
  have hstable : (prefixWord ++ tailWord_2168884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168884).length < 2 ^ (prefixWord ++ tailWord_2168884).sum := by decide
  have hdescent : baseEnd_2168884 < baseStart_2168884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168908 : List Nat := [2, 2, 1, 3, 1, 1, 4, 3, 5]
def baseStart_2168908 : Nat := 118140960795 + 2168908 * 2 ^ 59
def prefixEnd_2168908 : Nat := 4983230072969 + 3 ^ 40 * 2168908 * 2
def baseEnd_2168908 : Nat := 247487177640423415816751

theorem tailTrace_2168908 : CollatzResearch.WordTrace tailWord_2168908 prefixEnd_2168908 247487177640423415816751 := by
  unfold tailWord_2168908
  simp only [CollatzResearch.WordTrace]
  refine ⟨39553286813212105420433689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52737715750949473893911585 39553286813212105420433689)
  ·
    refine ⟨29664965109909079065325267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39553286813212105420433689 29664965109909079065325267)
    ·
      refine ⟨44497447664863618597987901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29664965109909079065325267 44497447664863618597987901)
      ·
        refine ⟨16686542874323856974245463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44497447664863618597987901 16686542874323856974245463)
        ·
          refine ⟨25029814311485785461368195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16686542874323856974245463 25029814311485785461368195)
          ·
            refine ⟨37544721467228678192052293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25029814311485785461368195 37544721467228678192052293)
            ·
              refine ⟨7039635275105377161009805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37544721467228678192052293 7039635275105377161009805)
              ·
                refine ⟨2639863228164516435378677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7039635275105377161009805 2639863228164516435378677)
                ·
                  refine ⟨247487177640423415816751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2639863228164516435378677 247487177640423415816751)
                  ·
                    rfl

theorem cell22_2168908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 5].length) (baseStart_2168908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168908 prefixEnd_2168908 := by exact prefixLift 2168908
  have htrace : WordTrace (prefixWord ++ tailWord_2168908) baseStart_2168908 baseEnd_2168908 := by
    simpa [prefixWord, tailWord_2168908, baseEnd_2168908] using wordTrace_append hprefix tailTrace_2168908
  have hstable : (prefixWord ++ tailWord_2168908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168908).length < 2 ^ (prefixWord ++ tailWord_2168908).sum := by decide
  have hdescent : baseEnd_2168908 < baseStart_2168908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2168953 : List Nat := [1, 2, 1, 3, 4, 1, 1, 3, 6]
def baseStart_2168953 : Nat := 118140960795 + 2168953 * 2 ^ 59
def prefixEnd_2168953 : Nat := 4983230072969 + 3 ^ 40 * 2168953 * 2
def baseEnd_2168953 : Nat := 247492312446968376691705

theorem tailTrace_2168953 : CollatzResearch.WordTrace tailWord_2168953 prefixEnd_2168953 247492312446968376691705 := by
  unfold tailWord_2168953
  simp only [CollatzResearch.WordTrace]
  refine ⟨79108214911261183526255513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52738809940840789017503675 79108214911261183526255513)
  ·
    refine ⟨59331161183445887644691635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79108214911261183526255513 59331161183445887644691635)
    ·
      refine ⟨88996741775168831467037453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59331161183445887644691635 88996741775168831467037453)
      ·
        refine ⟨33373778165688311800139045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88996741775168831467037453 33373778165688311800139045)
        ·
          refine ⟨6257583406066558462526071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33373778165688311800139045 6257583406066558462526071)
          ·
            refine ⟨9386375109099837693789107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6257583406066558462526071 9386375109099837693789107)
            ·
              refine ⟨14079562663649756540683661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9386375109099837693789107 14079562663649756540683661)
              ·
                refine ⟨5279835998868658702756373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14079562663649756540683661 5279835998868658702756373)
                ·
                  refine ⟨247492312446968376691705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5279835998868658702756373 247492312446968376691705)
                  ·
                    rfl

theorem cell22_2168953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 6].length) (baseStart_2168953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2168953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2168953 prefixEnd_2168953 := by exact prefixLift 2168953
  have htrace : WordTrace (prefixWord ++ tailWord_2168953) baseStart_2168953 baseEnd_2168953 := by
    simpa [prefixWord, tailWord_2168953, baseEnd_2168953] using wordTrace_append hprefix tailTrace_2168953
  have hstable : (prefixWord ++ tailWord_2168953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2168953).length < 2 ^ (prefixWord ++ tailWord_2168953).sum := by decide
  have hdescent : baseEnd_2168953 < baseStart_2168953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2168953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169047 : List Nat := [1, 1, 3, 2, 1, 2, 1, 7, 1, 3]
def baseStart_2169047 : Nat := 118140960795 + 2169047 * 2 ^ 59
def prefixEnd_2169047 : Nat := 4983230072969 + 3 ^ 40 * 2169047 * 2
def baseEnd_2169047 : Nat := 742509115461920218224827

theorem tailTrace_2169047 : CollatzResearch.WordTrace tailWord_2169047 prefixEnd_2169047 742509115461920218224827 := by
  unfold tailWord_2169047
  simp only [CollatzResearch.WordTrace]
  refine ⟨79111643372920637580177395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52741095581947091720118263 79111643372920637580177395)
  ·
    refine ⟨118667465059380956370266093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79111643372920637580177395 118667465059380956370266093)
    ·
      refine ⟨44500299397267858638849785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118667465059380956370266093 44500299397267858638849785)
      ·
        refine ⟨33375224547950893979137339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44500299397267858638849785 33375224547950893979137339)
        ·
          refine ⟨50062836821926340968706009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33375224547950893979137339 50062836821926340968706009)
          ·
            refine ⟨37547127616444755726529507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50062836821926340968706009 37547127616444755726529507)
            ·
              refine ⟨56320691424667133589794261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37547127616444755726529507 56320691424667133589794261)
              ·
                refine ⟨1320016205265635943510803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 56320691424667133589794261 1320016205265635943510803)
                ·
                  refine ⟨1980024307898453915266205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1320016205265635943510803 1980024307898453915266205)
                  ·
                    refine ⟨742509115461920218224827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1980024307898453915266205 742509115461920218224827)
                    ·
                      rfl

theorem cell22_2169047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7, 1, 3].length) (baseStart_2169047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169047 prefixEnd_2169047 := by exact prefixLift 2169047
  have htrace : WordTrace (prefixWord ++ tailWord_2169047) baseStart_2169047 baseEnd_2169047 := by
    simpa [prefixWord, tailWord_2169047, baseEnd_2169047] using wordTrace_append hprefix tailTrace_2169047
  have hstable : (prefixWord ++ tailWord_2169047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169047).length < 2 ^ (prefixWord ++ tailWord_2169047).sum := by decide
  have hdescent : baseEnd_2169047 < baseStart_2169047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169064 : List Nat := [2, 1, 4, 1, 2, 3, 1, 4, 1, 3]
def baseStart_2169064 : Nat := 118140960795 + 2169064 * 2 ^ 59
def prefixEnd_2169064 : Nat := 4983230072969 + 3 ^ 40 * 2169064 * 2
def baseEnd_2169064 : Nat := 742514934909337840549775

theorem tailTrace_2169064 : CollatzResearch.WordTrace tailWord_2169064 prefixEnd_2169064 742514934909337840549775 := by
  unfold tailWord_2169064
  simp only [CollatzResearch.WordTrace]
  refine ⟨39556131706929524741773123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52741508942572699655697497 39556131706929524741773123)
  ·
    refine ⟨59334197560394287112659685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39556131706929524741773123 59334197560394287112659685)
    ·
      refine ⟨11125162042573928833623691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59334197560394287112659685 11125162042573928833623691)
      ·
        refine ⟨16687743063860893250435537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11125162042573928833623691 16687743063860893250435537)
        ·
          refine ⟨12515807297895669937826653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16687743063860893250435537 12515807297895669937826653)
          ·
            refine ⟨4693427736710876226684995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12515807297895669937826653 4693427736710876226684995)
            ·
              refine ⟨7040141605066314340027493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4693427736710876226684995 7040141605066314340027493)
              ·
                refine ⟨1320026550949933938755155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7040141605066314340027493 1320026550949933938755155)
                ·
                  refine ⟨1980039826424900908132733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1320026550949933938755155 1980039826424900908132733)
                  ·
                    refine ⟨742514934909337840549775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1980039826424900908132733 742514934909337840549775)
                    ·
                      rfl

theorem cell22_2169064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_2169064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169064 prefixEnd_2169064 := by exact prefixLift 2169064
  have htrace : WordTrace (prefixWord ++ tailWord_2169064) baseStart_2169064 baseEnd_2169064 := by
    simpa [prefixWord, tailWord_2169064, baseEnd_2169064] using wordTrace_append hprefix tailTrace_2169064
  have hstable : (prefixWord ++ tailWord_2169064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169064).length < 2 ^ (prefixWord ++ tailWord_2169064).sum := by decide
  have hdescent : baseEnd_2169064 < baseStart_2169064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169088 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 8]
def baseStart_2169088 : Nat := 118140960795 + 2169088 * 2 ^ 59
def prefixEnd_2169088 : Nat := 4983230072969 + 3 ^ 40 * 2169088 * 2
def baseEnd_2169088 : Nat := 247507716866603259316567

theorem tailTrace_2169088 : CollatzResearch.WordTrace tailWord_2169088 prefixEnd_2169088 247507716866603259316567 := by
  unfold tailWord_2169088
  simp only [CollatzResearch.WordTrace]
  refine ⟨39556569382886050791209959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52742092510514734388279945 39556569382886050791209959)
  ·
    refine ⟨59334854074329076186814939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39556569382886050791209959 59334854074329076186814939)
    ·
      refine ⟨89002281111493614280222409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59334854074329076186814939 89002281111493614280222409)
      ·
        refine ⟨66751710833620210710166807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89002281111493614280222409 66751710833620210710166807)
        ·
          refine ⟨100127566250430316065250211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66751710833620210710166807 100127566250430316065250211)
          ·
            refine ⟨150191349375645474097875317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100127566250430316065250211 150191349375645474097875317)
            ·
              refine ⟨14080439003966763196675811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 150191349375645474097875317 14080439003966763196675811)
              ·
                refine ⟨21120658505950144795013717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14080439003966763196675811 21120658505950144795013717)
                ·
                  refine ⟨247507716866603259316567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21120658505950144795013717 247507716866603259316567)
                  ·
                    rfl

theorem cell22_2169088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 8].length) (baseStart_2169088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169088 prefixEnd_2169088 := by exact prefixLift 2169088
  have htrace : WordTrace (prefixWord ++ tailWord_2169088) baseStart_2169088 baseEnd_2169088 := by
    simpa [prefixWord, tailWord_2169088, baseEnd_2169088] using wordTrace_append hprefix tailTrace_2169088
  have hstable : (prefixWord ++ tailWord_2169088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169088).length < 2 ^ (prefixWord ++ tailWord_2169088).sum := by decide
  have hdescent : baseEnd_2169088 < baseStart_2169088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169122 : List Nat := [3, 3, 1, 1, 3, 2, 2, 1, 6]
def baseStart_2169122 : Nat := 118140960795 + 2169122 * 2 ^ 59
def prefixEnd_2169122 : Nat := 4983230072969 + 3 ^ 40 * 2169122 * 2
def baseEnd_2169122 : Nat := 247511596498215007533199

theorem tailTrace_2169122 : CollatzResearch.WordTrace tailWord_2169122 prefixEnd_2169122 247511596498215007533199 := by
  unfold tailWord_2169122
  simp only [CollatzResearch.WordTrace]
  refine ⟨19778594711912231347289405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52742919231765950259438413 19778594711912231347289405)
  ·
    refine ⟨7416973016967086755233527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19778594711912231347289405 7416973016967086755233527)
    ·
      refine ⟨11125459525450630132850291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7416973016967086755233527 11125459525450630132850291)
      ·
        refine ⟨16688189288175945199275437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11125459525450630132850291 16688189288175945199275437)
        ·
          refine ⟨6258070983065979449728289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16688189288175945199275437 6258070983065979449728289)
          ·
            refine ⟨4693553237299484587296217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6258070983065979449728289 4693553237299484587296217)
            ·
              refine ⟨3520164927974613440472163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4693553237299484587296217 3520164927974613440472163)
              ·
                refine ⟨5280247391961920160708245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3520164927974613440472163 5280247391961920160708245)
                ·
                  refine ⟨247511596498215007533199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5280247391961920160708245 247511596498215007533199)
                  ·
                    rfl

theorem cell22_2169122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_2169122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169122 prefixEnd_2169122 := by exact prefixLift 2169122
  have htrace : WordTrace (prefixWord ++ tailWord_2169122) baseStart_2169122 baseEnd_2169122 := by
    simpa [prefixWord, tailWord_2169122, baseEnd_2169122] using wordTrace_append hprefix tailTrace_2169122
  have hstable : (prefixWord ++ tailWord_2169122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169122).length < 2 ^ (prefixWord ++ tailWord_2169122).sum := by decide
  have hdescent : baseEnd_2169122 < baseStart_2169122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169195 : List Nat := [1, 1, 1, 1, 2, 2, 2, 7, 5]
def baseStart_2169195 : Nat := 118140960795 + 2169195 * 2 ^ 59
def prefixEnd_2169195 : Nat := 4983230072969 + 3 ^ 40 * 2169195 * 2
def baseEnd_2169195 : Nat := 247519926295499055174791

theorem tailTrace_2169195 : CollatzResearch.WordTrace tailWord_2169195 prefixEnd_2169195 247519926295499055174791 := by
  unfold tailWord_2169195
  simp only [CollatzResearch.WordTrace]
  refine ⟨79117041376384458856565039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52744694250922972571043359 79117041376384458856565039)
  ·
    refine ⟨118675562064576688284847559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79117041376384458856565039 118675562064576688284847559)
    ·
      refine ⟨178013343096865032427271339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118675562064576688284847559 178013343096865032427271339)
      ·
        refine ⟨267020014645297548640907009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178013343096865032427271339 267020014645297548640907009)
        ·
          refine ⟨200265010983973161480680257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267020014645297548640907009 200265010983973161480680257)
          ·
            refine ⟨150198758237979871110510193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200265010983973161480680257 150198758237979871110510193)
            ·
              refine ⟨112649068678484903332882645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150198758237979871110510193 112649068678484903332882645)
              ·
                refine ⟨2640212547151989921864437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 112649068678484903332882645 2640212547151989921864437)
                ·
                  refine ⟨247519926295499055174791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2640212547151989921864437 247519926295499055174791)
                  ·
                    rfl

theorem cell22_2169195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 5].length) (baseStart_2169195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169195 prefixEnd_2169195 := by exact prefixLift 2169195
  have htrace : WordTrace (prefixWord ++ tailWord_2169195) baseStart_2169195 baseEnd_2169195 := by
    simpa [prefixWord, tailWord_2169195, baseEnd_2169195] using wordTrace_append hprefix tailTrace_2169195
  have hstable : (prefixWord ++ tailWord_2169195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169195).length < 2 ^ (prefixWord ++ tailWord_2169195).sum := by decide
  have hdescent : baseEnd_2169195 < baseStart_2169195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169242 : List Nat := [3, 1, 1, 4, 1, 2, 1, 2, 3, 4]
def baseStart_2169242 : Nat := 118140960795 + 2169242 * 2 ^ 59
def prefixEnd_2169242 : Nat := 4983230072969 + 3 ^ 40 * 2169242 * 2
def baseEnd_2169242 : Nat := 742575867947004709599229

theorem tailTrace_2169242 : CollatzResearch.WordTrace tailWord_2169242 prefixEnd_2169242 742575867947004709599229 := by
  unfold tailWord_2169242
  simp only [CollatzResearch.WordTrace]
  refine ⟨19779688901803546470881495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52745837071476123922350653 19779688901803546470881495)
  ·
    refine ⟨29669533352705319706322243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19779688901803546470881495 29669533352705319706322243)
    ·
      refine ⟨44504300029057979559483365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29669533352705319706322243 44504300029057979559483365)
      ·
        refine ⟨8344556255448371167403131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44504300029057979559483365 8344556255448371167403131)
        ·
          refine ⟨12516834383172556751104697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8344556255448371167403131 12516834383172556751104697)
          ·
            refine ⟨9387625787379417563328523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12516834383172556751104697 9387625787379417563328523)
            ·
              refine ⟨14081438681069126344992785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9387625787379417563328523 14081438681069126344992785)
              ·
                refine ⟨10561079010801844758744589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14081438681069126344992785 10561079010801844758744589)
                ·
                  refine ⟨3960404629050691784529221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10561079010801844758744589 3960404629050691784529221)
                  ·
                    refine ⟨742575867947004709599229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3960404629050691784529221 742575867947004709599229)
                    ·
                      rfl

theorem cell22_2169242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_2169242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169242 prefixEnd_2169242 := by exact prefixLift 2169242
  have htrace : WordTrace (prefixWord ++ tailWord_2169242) baseStart_2169242 baseEnd_2169242 := by
    simpa [prefixWord, tailWord_2169242, baseEnd_2169242] using wordTrace_append hprefix tailTrace_2169242
  have hstable : (prefixWord ++ tailWord_2169242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169242).length < 2 ^ (prefixWord ++ tailWord_2169242).sum := by decide
  have hdescent : baseEnd_2169242 < baseStart_2169242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169272 : List Nat := [2, 1, 2, 1, 2, 2, 1, 4, 4, 3]
def baseStart_2169272 : Nat := 118140960795 + 2169272 * 2 ^ 59
def prefixEnd_2169272 : Nat := 4983230072969 + 3 ^ 40 * 2169272 * 2
def baseEnd_2169272 : Nat := 742586137560094631349137

theorem tailTrace_2169272 : CollatzResearch.WordTrace tailWord_2169272 prefixEnd_2169272 742586137560094631349137 := by
  unfold tailWord_2169272
  simp only [CollatzResearch.WordTrace]
  refine ⟨39559924898552750503559035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52746566531403667338078713 39559924898552750503559035)
  ·
    refine ⟨59339887347829125755338553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39559924898552750503559035 59339887347829125755338553)
    ·
      refine ⟨44504915510871844316503915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59339887347829125755338553 44504915510871844316503915)
      ·
        refine ⟨66757373266307766474755873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44504915510871844316503915 66757373266307766474755873)
        ·
          refine ⟨50068029949730824856066905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66757373266307766474755873 50068029949730824856066905)
          ·
            refine ⟨37551022462298118642050179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50068029949730824856066905 37551022462298118642050179)
            ·
              refine ⟨56326533693447177963075269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37551022462298118642050179 56326533693447177963075269)
              ·
                refine ⟨10561225067521345868076613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56326533693447177963075269 10561225067521345868076613)
                ·
                  refine ⟨1980229700160252350264365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10561225067521345868076613 1980229700160252350264365)
                  ·
                    refine ⟨742586137560094631349137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1980229700160252350264365 742586137560094631349137)
                    ·
                      rfl

theorem cell22_2169272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 4, 3].length) (baseStart_2169272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169272 prefixEnd_2169272 := by exact prefixLift 2169272
  have htrace : WordTrace (prefixWord ++ tailWord_2169272) baseStart_2169272 baseEnd_2169272 := by
    simpa [prefixWord, tailWord_2169272, baseEnd_2169272] using wordTrace_append hprefix tailTrace_2169272
  have hstable : (prefixWord ++ tailWord_2169272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169272).length < 2 ^ (prefixWord ++ tailWord_2169272).sum := by decide
  have hdescent : baseEnd_2169272 < baseStart_2169272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169276 : List Nat := [2, 2, 2, 4, 1, 1, 4, 1, 1, 4]
def baseStart_2169276 : Nat := 118140960795 + 2169276 * 2 ^ 59
def prefixEnd_2169276 : Nat := 4983230072969 + 3 ^ 40 * 2169276 * 2
def baseEnd_2169276 : Nat := 742587506841839954249125

theorem tailTrace_2169276 : CollatzResearch.WordTrace tailWord_2169276 prefixEnd_2169276 742587506841839954249125 := by
  unfold tailWord_2169276
  simp only [CollatzResearch.WordTrace]
  refine ⟨39559997844545504845131841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52746663792727339793509121 39559997844545504845131841)
  ·
    refine ⟨29669998383409128633848881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39559997844545504845131841 29669998383409128633848881)
    ·
      refine ⟨22252498787556846475386661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29669998383409128633848881 22252498787556846475386661)
      ·
        refine ⟨4172343522666908714134999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22252498787556846475386661 4172343522666908714134999)
        ·
          refine ⟨6258515284000363071202499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4172343522666908714134999 6258515284000363071202499)
          ·
            refine ⟨9387772926000544606803749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6258515284000363071202499 9387772926000544606803749)
            ·
              refine ⟨1760207423625102113775703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9387772926000544606803749 1760207423625102113775703)
              ·
                refine ⟨2640311135437653170663555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1760207423625102113775703 2640311135437653170663555)
                ·
                  refine ⟨3960466703156479755995333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2640311135437653170663555 3960466703156479755995333)
                  ·
                    refine ⟨742587506841839954249125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3960466703156479755995333 742587506841839954249125)
                    ·
                      rfl

theorem cell22_2169276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_2169276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169276 prefixEnd_2169276 := by exact prefixLift 2169276
  have htrace : WordTrace (prefixWord ++ tailWord_2169276) baseStart_2169276 baseEnd_2169276 := by
    simpa [prefixWord, tailWord_2169276, baseEnd_2169276] using wordTrace_append hprefix tailTrace_2169276
  have hstable : (prefixWord ++ tailWord_2169276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169276).length < 2 ^ (prefixWord ++ tailWord_2169276).sum := by decide
  have hdescent : baseEnd_2169276 < baseStart_2169276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169289 : List Nat := [1, 2, 1, 1, 2, 1, 7, 2, 2, 3]
def baseStart_2169289 : Nat := 118140960795 + 2169289 * 2 ^ 59
def prefixEnd_2169289 : Nat := 4983230072969 + 3 ^ 40 * 2169289 * 2
def baseEnd_2169289 : Nat := 742591957007512253674085

theorem tailTrace_2169289 : CollatzResearch.WordTrace tailWord_2169289 prefixEnd_2169289 742591957007512253674085 := by
  unfold tailWord_2169289
  simp only [CollatzResearch.WordTrace]
  refine ⟨79120469838043912910486921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52746979892029275273657947 79120469838043912910486921)
  ·
    refine ⟨59340352378532934682865191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79120469838043912910486921 59340352378532934682865191)
    ·
      refine ⟨89010528567799402024297787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59340352378532934682865191 89010528567799402024297787)
      ·
        refine ⟨133515792851699103036446681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89010528567799402024297787 133515792851699103036446681)
        ·
          refine ⟨100136844638774327277335011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133515792851699103036446681 100136844638774327277335011)
          ·
            refine ⟨150205266958161490916002517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100136844638774327277335011 150205266958161490916002517)
            ·
              refine ⟨3520435944331909943343809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 150205266958161490916002517 3520435944331909943343809)
              ·
                refine ⟨2640326958248932457507857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3520435944331909943343809 2640326958248932457507857)
                ·
                  refine ⟨1980245218686699343130893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2640326958248932457507857 1980245218686699343130893)
                  ·
                    refine ⟨742591957007512253674085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1980245218686699343130893 742591957007512253674085)
                    ·
                      rfl

theorem cell22_2169289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 2, 3].length) (baseStart_2169289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169289 prefixEnd_2169289 := by exact prefixLift 2169289
  have htrace : WordTrace (prefixWord ++ tailWord_2169289) baseStart_2169289 baseEnd_2169289 := by
    simpa [prefixWord, tailWord_2169289, baseEnd_2169289] using wordTrace_append hprefix tailTrace_2169289
  have hstable : (prefixWord ++ tailWord_2169289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169289).length < 2 ^ (prefixWord ++ tailWord_2169289).sum := by decide
  have hdescent : baseEnd_2169289 < baseStart_2169289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169306 : List Nat := [3, 1, 1, 2, 3, 1, 5, 1, 2, 3]
def baseStart_2169306 : Nat := 118140960795 + 2169306 * 2 ^ 59
def prefixEnd_2169306 : Nat := 4983230072969 + 3 ^ 40 * 2169306 * 2
def baseEnd_2169306 : Nat := 742597776454929875999033

theorem tailTrace_2169306 : CollatzResearch.WordTrace tailWord_2169306 prefixEnd_2169306 742597776454929875999033 := by
  unfold tailWord_2169306
  simp only [CollatzResearch.WordTrace]
  refine ⟨19780272469745581203463943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52747393252654883209237181 19780272469745581203463943)
  ·
    refine ⟨29670408704618371805195915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19780272469745581203463943 29670408704618371805195915)
    ·
      refine ⟨44505613056927557707793873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29670408704618371805195915 44505613056927557707793873)
      ·
        refine ⟨33379209792695668280845405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44505613056927557707793873 33379209792695668280845405)
        ·
          refine ⟨12517203672260875605317027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33379209792695668280845405 12517203672260875605317027)
          ·
            refine ⟨18775805508391313407975541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12517203672260875605317027 18775805508391313407975541)
            ·
              refine ⟨1760231766411685631997707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18775805508391313407975541 1760231766411685631997707)
              ·
                refine ⟨2640347649617528447996561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1760231766411685631997707 2640347649617528447996561)
                ·
                  refine ⟨1980260737213146335997421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2640347649617528447996561 1980260737213146335997421)
                  ·
                    refine ⟨742597776454929875999033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1980260737213146335997421 742597776454929875999033)
                    ·
                      rfl

theorem cell22_2169306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 2, 3].length) (baseStart_2169306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169306 prefixEnd_2169306 := by exact prefixLift 2169306
  have htrace : WordTrace (prefixWord ++ tailWord_2169306) baseStart_2169306 baseEnd_2169306 := by
    simpa [prefixWord, tailWord_2169306, baseEnd_2169306] using wordTrace_append hprefix tailTrace_2169306
  have hstable : (prefixWord ++ tailWord_2169306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169306).length < 2 ^ (prefixWord ++ tailWord_2169306).sum := by decide
  have hdescent : baseEnd_2169306 < baseStart_2169306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169347 : List Nat := [1, 1, 1, 3, 2, 1, 4, 4, 5]
def baseStart_2169347 : Nat := 118140960795 + 2169347 * 2 ^ 59
def prefixEnd_2169347 : Nat := 4983230072969 + 3 ^ 40 * 2169347 * 2
def baseEnd_2169347 : Nat := 247537270530939811907969

theorem tailTrace_2169347 : CollatzResearch.WordTrace tailWord_2169347 prefixEnd_2169347 247537270530939811907969 := by
  unfold tailWord_2169347
  simp only [CollatzResearch.WordTrace]
  refine ⟨79122585271833788816098295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52748390181222525877398863 79122585271833788816098295)
  ·
    refine ⟨118683877907750683224147443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79122585271833788816098295 118683877907750683224147443)
    ·
      refine ⟨178025816861626024836221165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118683877907750683224147443 178025816861626024836221165)
      ·
        refine ⟨66759681323109759313582937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178025816861626024836221165 66759681323109759313582937)
        ·
          refine ⟨50069760992332319485187203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66759681323109759313582937 50069760992332319485187203)
          ·
            refine ⟨75104641488498479227780805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50069760992332319485187203 75104641488498479227780805)
            ·
              refine ⟨14082120279093464855208901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75104641488498479227780805 14082120279093464855208901)
              ·
                refine ⟨2640397552330024660351669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14082120279093464855208901 2640397552330024660351669)
                ·
                  refine ⟨247537270530939811907969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2640397552330024660351669 247537270530939811907969)
                  ·
                    rfl

theorem cell22_2169347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 5].length) (baseStart_2169347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169347 prefixEnd_2169347 := by exact prefixLift 2169347
  have htrace : WordTrace (prefixWord ++ tailWord_2169347) baseStart_2169347 baseEnd_2169347 := by
    simpa [prefixWord, tailWord_2169347, baseEnd_2169347] using wordTrace_append hprefix tailTrace_2169347
  have hstable : (prefixWord ++ tailWord_2169347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169347).length < 2 ^ (prefixWord ++ tailWord_2169347).sum := by decide
  have hdescent : baseEnd_2169347 < baseStart_2169347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169357 : List Nat := [1, 7, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_2169357 : Nat := 118140960795 + 2169357 * 2 ^ 59
def prefixEnd_2169357 : Nat := 4983230072969 + 3 ^ 40 * 2169357 * 2
def baseEnd_2169357 : Nat := 742615234797182742973877

theorem tailTrace_2169357 : CollatzResearch.WordTrace tailWord_2169357 prefixEnd_2169357 742615234797182742973877 := by
  unfold tailWord_2169357
  simp only [CollatzResearch.WordTrace]
  refine ⟨79122950001797560523962325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52748633334531707015974883 79122950001797560523962325)
  ·
    refine ⟨1854444140667130324780367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 79122950001797560523962325 1854444140667130324780367)
    ·
      refine ⟨2781666211000695487170551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1854444140667130324780367 2781666211000695487170551)
      ·
        refine ⟨4172499316501043230755827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2781666211000695487170551 4172499316501043230755827)
        ·
          refine ⟨6258748974751564846133741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4172499316501043230755827 6258748974751564846133741)
          ·
            refine ⟨2347030865531836817300153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6258748974751564846133741 2347030865531836817300153)
            ·
              refine ⟨1760273149148877612975115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2347030865531836817300153 1760273149148877612975115)
              ·
                refine ⟨2640409723723316419462673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1760273149148877612975115 2640409723723316419462673)
                ·
                  refine ⟨1980307292792487314597005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2640409723723316419462673 1980307292792487314597005)
                  ·
                    refine ⟨742615234797182742973877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1980307292792487314597005 742615234797182742973877)
                    ·
                      rfl

theorem cell22_2169357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_2169357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169357 prefixEnd_2169357 := by exact prefixLift 2169357
  have htrace : WordTrace (prefixWord ++ tailWord_2169357) baseStart_2169357 baseEnd_2169357 := by
    simpa [prefixWord, tailWord_2169357, baseEnd_2169357] using wordTrace_append hprefix tailTrace_2169357
  have hstable : (prefixWord ++ tailWord_2169357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169357).length < 2 ^ (prefixWord ++ tailWord_2169357).sum := by decide
  have hdescent : baseEnd_2169357 < baseStart_2169357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169394 : List Nat := [3, 2, 1, 1, 2, 1, 2, 5, 1, 4]
def baseStart_2169394 : Nat := 118140960795 + 2169394 * 2 ^ 59
def prefixEnd_2169394 : Nat := 4983230072969 + 3 ^ 40 * 2169394 * 2
def baseEnd_2169394 : Nat := 742627900653326979798763

theorem tailTrace_2169394 : CollatzResearch.WordTrace tailWord_2169394 prefixEnd_2169394 742627900653326979798763 := by
  unfold tailWord_2169394
  simp only [CollatzResearch.WordTrace]
  refine ⟨19781074875665878960764809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52749533001775677228706157 19781074875665878960764809)
  ·
    refine ⟨14835806156749409220573607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19781074875665878960764809 14835806156749409220573607)
    ·
      refine ⟨22253709235124113830860411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14835806156749409220573607 22253709235124113830860411)
      ·
        refine ⟨33380563852686170746290617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22253709235124113830860411 33380563852686170746290617)
        ·
          refine ⟨25035422889514628059717963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33380563852686170746290617 25035422889514628059717963)
          ·
            refine ⟨37553134334271942089576945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25035422889514628059717963 37553134334271942089576945)
            ·
              refine ⟨28164850750703956567182709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37553134334271942089576945 28164850750703956567182709)
              ·
                refine ⟨2640454757878495928173379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28164850750703956567182709 2640454757878495928173379)
                ·
                  refine ⟨3960682136817743892260069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2640454757878495928173379 3960682136817743892260069)
                  ·
                    refine ⟨742627900653326979798763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3960682136817743892260069 742627900653326979798763)
                    ·
                      rfl

theorem cell22_2169394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_2169394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169394 prefixEnd_2169394 := by exact prefixLift 2169394
  have htrace : WordTrace (prefixWord ++ tailWord_2169394) baseStart_2169394 baseEnd_2169394 := by
    simpa [prefixWord, tailWord_2169394, baseEnd_2169394] using wordTrace_append hprefix tailTrace_2169394
  have hstable : (prefixWord ++ tailWord_2169394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169394).length < 2 ^ (prefixWord ++ tailWord_2169394).sum := by decide
  have hdescent : baseEnd_2169394 < baseStart_2169394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169407 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 3, 5]
def baseStart_2169407 : Nat := 118140960795 + 2169407 * 2 ^ 59
def prefixEnd_2169407 : Nat := 4983230072969 + 3 ^ 40 * 2169407 * 2
def baseEnd_2169407 : Nat := 742632350818999279223723

theorem tailTrace_2169407 : CollatzResearch.WordTrace tailWord_2169407 prefixEnd_2169407 742632350818999279223723 := by
  unfold tailWord_2169407
  simp only [CollatzResearch.WordTrace]
  refine ⟨79124773651616419063282475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52749849101077612708854983 79124773651616419063282475)
  ·
    refine ⟨118687160477424628594923713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79124773651616419063282475 118687160477424628594923713)
    ·
      refine ⟨89015370358068471446192785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118687160477424628594923713 89015370358068471446192785)
      ·
        refine ⟨66761527768551353584644589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89015370358068471446192785 66761527768551353584644589)
        ·
          refine ⟨25035572913206757594241721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66761527768551353584644589 25035572913206757594241721)
          ·
            refine ⟨18776679684905068195681291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25035572913206757594241721 18776679684905068195681291)
            ·
              refine ⟨28165019527357602293521937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18776679684905068195681291 28165019527357602293521937)
              ·
                refine ⟨21123764645518201720141453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28165019527357602293521937 21123764645518201720141453)
                ·
                  refine ⟨7921411742069325645053045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21123764645518201720141453 7921411742069325645053045)
                  ·
                    refine ⟨742632350818999279223723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7921411742069325645053045 742632350818999279223723)
                    ·
                      rfl

theorem cell22_2169407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 5].length) (baseStart_2169407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169407 prefixEnd_2169407 := by exact prefixLift 2169407
  have htrace : WordTrace (prefixWord ++ tailWord_2169407) baseStart_2169407 baseEnd_2169407 := by
    simpa [prefixWord, tailWord_2169407, baseEnd_2169407] using wordTrace_append hprefix tailTrace_2169407
  have hstable : (prefixWord ++ tailWord_2169407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169407).length < 2 ^ (prefixWord ++ tailWord_2169407).sum := by decide
  have hdescent : baseEnd_2169407 < baseStart_2169407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169445 : List Nat := [1, 3, 1, 3, 5, 1, 2, 1, 1, 4]
def baseStart_2169445 : Nat := 118140960795 + 2169445 * 2 ^ 59
def prefixEnd_2169445 : Nat := 4983230072969 + 3 ^ 40 * 2169445 * 2
def baseEnd_2169445 : Nat := 742645358995579846773607

theorem tailTrace_2169445 : CollatzResearch.WordTrace tailWord_2169445 prefixEnd_2169445 742645358995579846773607 := by
  unfold tailWord_2169445
  simp only [CollatzResearch.WordTrace]
  refine ⟨79126159625478751553165789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52750773083652501035443859 79126159625478751553165789)
  ·
    refine ⟨29672309859554531832437171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79126159625478751553165789 29672309859554531832437171)
    ·
      refine ⟨44508464789331797748655757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29672309859554531832437171 44508464789331797748655757)
      ·
        refine ⟨16690674295999424155745909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44508464789331797748655757 16690674295999424155745909)
        ·
          refine ⟨1564750715249946014601179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16690674295999424155745909 1564750715249946014601179)
          ·
            refine ⟨2347126072874919021901769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1564750715249946014601179 2347126072874919021901769)
            ·
              refine ⟨1760344554656189266426327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2347126072874919021901769 1760344554656189266426327)
              ·
                refine ⟨2640516831984283899639491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1760344554656189266426327 2640516831984283899639491)
                ·
                  refine ⟨3960775247976425849459237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2640516831984283899639491 3960775247976425849459237)
                  ·
                    refine ⟨742645358995579846773607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3960775247976425849459237 742645358995579846773607)
                    ·
                      rfl

theorem cell22_2169445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 1, 4].length) (baseStart_2169445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169445 prefixEnd_2169445 := by exact prefixLift 2169445
  have htrace : WordTrace (prefixWord ++ tailWord_2169445) baseStart_2169445 baseEnd_2169445 := by
    simpa [prefixWord, tailWord_2169445, baseEnd_2169445] using wordTrace_append hprefix tailTrace_2169445
  have hstable : (prefixWord ++ tailWord_2169445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169445).length < 2 ^ (prefixWord ++ tailWord_2169445).sum := by decide
  have hdescent : baseEnd_2169445 < baseStart_2169445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169454 : List Nat := [4, 1, 2, 2, 2, 2, 9]
def baseStart_2169454 : Nat := 118140960795 + 2169454 * 2 ^ 59
def prefixEnd_2169454 : Nat := 4983230072969 + 3 ^ 40 * 2169454 * 2
def baseEnd_2169454 : Nat := 27505497773315067529577

theorem tailTrace_2169454 : CollatzResearch.WordTrace tailWord_2169454 prefixEnd_2169454 27505497773315067529577 := by
  unfold tailWord_2169454
  simp only [CollatzResearch.WordTrace]
  refine ⟨9890810985305768261280427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52750991921630764060162277 9890810985305768261280427)
  ·
    refine ⟨14836216477958652391920641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9890810985305768261280427 14836216477958652391920641)
    ·
      refine ⟨11127162358468989293940481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14836216477958652391920641 11127162358468989293940481)
      ·
        refine ⟨8345371768851741970455361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11127162358468989293940481 8345371768851741970455361)
        ·
          refine ⟨6259028826638806477841521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8345371768851741970455361 6259028826638806477841521)
          ·
            refine ⟨4694271619979104858381141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6259028826638806477841521 4694271619979104858381141)
            ·
              refine ⟨27505497773315067529577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4694271619979104858381141 27505497773315067529577)
              ·
                rfl

theorem cell22_2169454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 9].length) (baseStart_2169454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169454 prefixEnd_2169454 := by exact prefixLift 2169454
  have htrace : WordTrace (prefixWord ++ tailWord_2169454) baseStart_2169454 baseEnd_2169454 := by
    simpa [prefixWord, tailWord_2169454, baseEnd_2169454] using wordTrace_append hprefix tailTrace_2169454
  have hstable : (prefixWord ++ tailWord_2169454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169454).length < 2 ^ (prefixWord ++ tailWord_2169454).sum := by decide
  have hdescent : baseEnd_2169454 < baseStart_2169454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169467 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 2, 6]
def baseStart_2169467 : Nat := 118140960795 + 2169467 * 2 ^ 59
def prefixEnd_2169467 : Nat := 4983230072969 + 3 ^ 40 * 2169467 * 2
def baseEnd_2169467 : Nat := 742652890045179122723539

theorem tailTrace_2169467 : CollatzResearch.WordTrace tailWord_2169467 prefixEnd_2169467 742652890045179122723539 := by
  unfold tailWord_2169467
  simp only [CollatzResearch.WordTrace]
  refine ⟨79126962031399049310466655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52751308020932699540311103 79126962031399049310466655)
  ·
    refine ⟨118690443047098573965699983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79126962031399049310466655 118690443047098573965699983)
    ·
      refine ⟨178035664570647860948549975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118690443047098573965699983 178035664570647860948549975)
      ·
        refine ⟨267053496855971791422824963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178035664570647860948549975 267053496855971791422824963)
        ·
          refine ⟨400580245283957687134237445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267053496855971791422824963 400580245283957687134237445)
          ·
            refine ⟨75108795990742066337669521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 400580245283957687134237445 75108795990742066337669521)
            ·
              refine ⟨56331596993056549753252141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75108795990742066337669521 56331596993056549753252141)
              ·
                refine ⟨21124348872396206157469553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56331596993056549753252141 21124348872396206157469553)
                ·
                  refine ⟨15843261654297154618102165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21124348872396206157469553 15843261654297154618102165)
                  ·
                    refine ⟨742652890045179122723539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15843261654297154618102165 742652890045179122723539)
                    ·
                      rfl

theorem cell22_2169467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 6].length) (baseStart_2169467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169467 prefixEnd_2169467 := by exact prefixLift 2169467
  have htrace : WordTrace (prefixWord ++ tailWord_2169467) baseStart_2169467 baseEnd_2169467 := by
    simpa [prefixWord, tailWord_2169467, baseEnd_2169467] using wordTrace_append hprefix tailTrace_2169467
  have hstable : (prefixWord ++ tailWord_2169467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169467).length < 2 ^ (prefixWord ++ tailWord_2169467).sum := by decide
  have hdescent : baseEnd_2169467 < baseStart_2169467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169486 : List Nat := [4, 1, 1, 3, 1, 1, 1, 4, 3, 3]
def baseStart_2169486 : Nat := 118140960795 + 2169486 * 2 ^ 59
def prefixEnd_2169486 : Nat := 4983230072969 + 3 ^ 40 * 2169486 * 2
def baseEnd_2169486 : Nat := 742659394133469406498481

theorem tailTrace_2169486 : CollatzResearch.WordTrace tailWord_2169486 prefixEnd_2169486 742659394133469406498481 := by
  unfold tailWord_2169486
  simp only [CollatzResearch.WordTrace]
  refine ⟨9890956877291276944426039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52751770012220143703605541 9890956877291276944426039)
  ·
    refine ⟨14836435315936915416639059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9890956877291276944426039 14836435315936915416639059)
    ·
      refine ⟨22254652973905373124958589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14836435315936915416639059 22254652973905373124958589)
      ·
        refine ⟨8345494865214514921859471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22254652973905373124958589 8345494865214514921859471)
        ·
          refine ⟨12518242297821772382789207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8345494865214514921859471 12518242297821772382789207)
          ·
            refine ⟨18777363446732658574183811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12518242297821772382789207 18777363446732658574183811)
            ·
              refine ⟨28166045170098987861275717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18777363446732658574183811 28166045170098987861275717)
              ·
                refine ⟨5281133469393560223989197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28166045170098987861275717 5281133469393560223989197)
                ·
                  refine ⟨1980425051022585083995949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5281133469393560223989197 1980425051022585083995949)
                  ·
                    refine ⟨742659394133469406498481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1980425051022585083995949 742659394133469406498481)
                    ·
                      rfl

theorem cell22_2169486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_2169486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169486 prefixEnd_2169486 := by exact prefixLift 2169486
  have htrace : WordTrace (prefixWord ++ tailWord_2169486) baseStart_2169486 baseEnd_2169486 := by
    simpa [prefixWord, tailWord_2169486, baseEnd_2169486] using wordTrace_append hprefix tailTrace_2169486
  have hstable : (prefixWord ++ tailWord_2169486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169486).length < 2 ^ (prefixWord ++ tailWord_2169486).sum := by decide
  have hdescent : baseEnd_2169486 < baseStart_2169486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169529 : List Nat := [1, 2, 1, 4, 1, 1, 1, 4, 3, 4]
def baseStart_2169529 : Nat := 118140960795 + 2169529 * 2 ^ 59
def prefixEnd_2169529 : Nat := 4983230072969 + 3 ^ 40 * 2169529 * 2
def baseEnd_2169529 : Nat := 742674113912231627673349

theorem tailTrace_2169529 : CollatzResearch.WordTrace tailWord_2169529 prefixEnd_2169529 742674113912231627673349 := by
  unfold tailWord_2169529
  simp only [CollatzResearch.WordTrace]
  refine ⟨79129223357174433899223641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52752815571449622599482427 79129223357174433899223641)
  ·
    refine ⟨59346917517880825424417731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79129223357174433899223641 59346917517880825424417731)
    ·
      refine ⟨89020376276821238136626597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59346917517880825424417731 89020376276821238136626597)
      ·
        refine ⟨16691320551903982150617487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89020376276821238136626597 16691320551903982150617487)
        ·
          refine ⟨25036980827855973225926231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16691320551903982150617487 25036980827855973225926231)
          ·
            refine ⟨37555471241783959838889347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25036980827855973225926231 37555471241783959838889347)
            ·
              refine ⟨56333206862675939758334021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37555471241783959838889347 56333206862675939758334021)
              ·
                refine ⟨10562476286751738704687629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56333206862675939758334021 10562476286751738704687629)
                ·
                  refine ⟨3960928607531902014257861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10562476286751738704687629 3960928607531902014257861)
                  ·
                    refine ⟨742674113912231627673349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3960928607531902014257861 742674113912231627673349)
                    ·
                      rfl

theorem cell22_2169529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 3, 4].length) (baseStart_2169529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169529 prefixEnd_2169529 := by exact prefixLift 2169529
  have htrace : WordTrace (prefixWord ++ tailWord_2169529) baseStart_2169529 baseEnd_2169529 := by
    simpa [prefixWord, tailWord_2169529, baseEnd_2169529] using wordTrace_append hprefix tailTrace_2169529
  have hstable : (prefixWord ++ tailWord_2169529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169529).length < 2 ^ (prefixWord ++ tailWord_2169529).sum := by decide
  have hdescent : baseEnd_2169529 < baseStart_2169529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169533 : List Nat := [1, 4, 1, 2, 1, 5, 2, 1, 5]
def baseStart_2169533 : Nat := 118140960795 + 2169533 * 2 ^ 59
def prefixEnd_2169533 : Nat := 4983230072969 + 3 ^ 40 * 2169533 * 2
def baseEnd_2169533 : Nat := 247558494397992316857779

theorem tailTrace_2169533 : CollatzResearch.WordTrace tailWord_2169533 prefixEnd_2169533 247558494397992316857779 := by
  unfold tailWord_2169533
  simp only [CollatzResearch.WordTrace]
  refine ⟨79129369249159942582369253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52752912832773295054912835 79129369249159942582369253)
  ·
    refine ⟨14836756734217489234194235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79129369249159942582369253 14836756734217489234194235)
    ·
      refine ⟨22255135101326233851291353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14836756734217489234194235 22255135101326233851291353)
      ·
        refine ⟨16691351325994675388468515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22255135101326233851291353 16691351325994675388468515)
        ·
          refine ⟨25037026988992013082702773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16691351325994675388468515 25037026988992013082702773)
          ·
            refine ⟨2347221280218001226503385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25037026988992013082702773 2347221280218001226503385)
            ·
              refine ⟨1760415960163500919877539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2347221280218001226503385 1760415960163500919877539)
              ·
                refine ⟨2640623940245251379816309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1760415960163500919877539 2640623940245251379816309)
                ·
                  refine ⟨247558494397992316857779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2640623940245251379816309 247558494397992316857779)
                  ·
                    rfl

theorem cell22_2169533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_2169533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169533 prefixEnd_2169533 := by exact prefixLift 2169533
  have htrace : WordTrace (prefixWord ++ tailWord_2169533) baseStart_2169533 baseEnd_2169533 := by
    simpa [prefixWord, tailWord_2169533, baseEnd_2169533] using wordTrace_append hprefix tailTrace_2169533
  have hstable : (prefixWord ++ tailWord_2169533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169533).length < 2 ^ (prefixWord ++ tailWord_2169533).sum := by decide
  have hdescent : baseEnd_2169533 < baseStart_2169533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169546 : List Nat := [3, 1, 2, 1, 4, 2, 1, 1, 3, 4]
def baseStart_2169546 : Nat := 118140960795 + 2169546 * 2 ^ 59
def prefixEnd_2169546 : Nat := 4983230072969 + 3 ^ 40 * 2169546 * 2
def baseEnd_2169546 : Nat := 742679933359649249998297

theorem tailTrace_2169546 : CollatzResearch.WordTrace tailWord_2169546 prefixEnd_2169546 742679933359649249998297 := by
  unfold tailWord_2169546
  simp only [CollatzResearch.WordTrace]
  refine ⟨19782460849528211450648123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52753228932075230535061661 19782460849528211450648123)
  ·
    refine ⟨29673691274292317175972185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19782460849528211450648123 29673691274292317175972185)
    ·
      refine ⟨22255268455719237881979139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29673691274292317175972185 22255268455719237881979139)
      ·
        refine ⟨33382902683578856822968709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22255268455719237881979139 33382902683578856822968709)
        ·
          refine ⟨6259294253171035654306633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33382902683578856822968709 6259294253171035654306633)
          ·
            refine ⟨4694470689878276740729975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6259294253171035654306633 4694470689878276740729975)
            ·
              refine ⟨7041706034817415111094963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4694470689878276740729975 7041706034817415111094963)
              ·
                refine ⟨10562559052226122666642445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7041706034817415111094963 10562559052226122666642445)
                ·
                  refine ⟨3960959644584795999990917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10562559052226122666642445 3960959644584795999990917)
                  ·
                    refine ⟨742679933359649249998297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3960959644584795999990917 742679933359649249998297)
                    ·
                      rfl

theorem cell22_2169546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_2169546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169546 prefixEnd_2169546 := by exact prefixLift 2169546
  have htrace : WordTrace (prefixWord ++ tailWord_2169546) baseStart_2169546 baseEnd_2169546 := by
    simpa [prefixWord, tailWord_2169546, baseEnd_2169546] using wordTrace_append hprefix tailTrace_2169546
  have hstable : (prefixWord ++ tailWord_2169546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169546).length < 2 ^ (prefixWord ++ tailWord_2169546).sum := by decide
  have hdescent : baseEnd_2169546 < baseStart_2169546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169559 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 3, 5]
def baseStart_2169559 : Nat := 118140960795 + 2169559 * 2 ^ 59
def prefixEnd_2169559 : Nat := 4983230072969 + 3 ^ 40 * 2169559 * 2
def baseEnd_2169559 : Nat := 742684383525321549423257

theorem tailTrace_2169559 : CollatzResearch.WordTrace tailWord_2169559 prefixEnd_2169559 742684383525321549423257 := by
  unfold tailWord_2169559
  simp only [CollatzResearch.WordTrace]
  refine ⟨79130317547065749022815731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52753545031377166015210487 79130317547065749022815731)
  ·
    refine ⟨118695476320598623534223597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79130317547065749022815731 118695476320598623534223597)
    ·
      refine ⟨44510803620224483825333849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118695476320598623534223597 44510803620224483825333849)
      ·
        refine ⟨33383102715168362869000387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44510803620224483825333849 33383102715168362869000387)
        ·
          refine ⟨50074654072752544303500581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33383102715168362869000387 50074654072752544303500581)
          ·
            refine ⟨9388997638641102056906359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50074654072752544303500581 9388997638641102056906359)
            ·
              refine ⟨14083496457961653085359539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9388997638641102056906359 14083496457961653085359539)
              ·
                refine ⟨21125244686942479628039309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14083496457961653085359539 21125244686942479628039309)
                ·
                  refine ⟨7921966757603429860514741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21125244686942479628039309 7921966757603429860514741)
                  ·
                    refine ⟨742684383525321549423257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7921966757603429860514741 742684383525321549423257)
                    ·
                      rfl

theorem cell22_2169559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_2169559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169559 prefixEnd_2169559 := by exact prefixLift 2169559
  have htrace : WordTrace (prefixWord ++ tailWord_2169559) baseStart_2169559 baseEnd_2169559 := by
    simpa [prefixWord, tailWord_2169559, baseEnd_2169559] using wordTrace_append hprefix tailTrace_2169559
  have hstable : (prefixWord ++ tailWord_2169559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169559).length < 2 ^ (prefixWord ++ tailWord_2169559).sum := by decide
  have hdescent : baseEnd_2169559 < baseStart_2169559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169561 : List Nat := [1, 2, 1, 2, 3, 2, 2, 5, 4]
def baseStart_2169561 : Nat := 118140960795 + 2169561 * 2 ^ 59
def prefixEnd_2169561 : Nat := 4983230072969 + 3 ^ 40 * 2169561 * 2
def baseEnd_2169561 : Nat := 247561689388731403624417

theorem tailTrace_2169561 : CollatzResearch.WordTrace tailWord_2169561 prefixEnd_2169561 247561689388731403624417 := by
  unfold tailWord_2169561
  simp only [CollatzResearch.WordTrace]
  refine ⟨79130390493058503364388537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52753593662039002242925691 79130390493058503364388537)
  ·
    refine ⟨59347792869793877523291403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79130390493058503364388537 59347792869793877523291403)
    ·
      refine ⟨89021689304690816284937105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59347792869793877523291403 89021689304690816284937105)
      ·
        refine ⟨66766266978518112213702829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89021689304690816284937105 66766266978518112213702829)
        ·
          refine ⟨25037350116944292080138561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66766266978518112213702829 25037350116944292080138561)
          ·
            refine ⟨18778012587708219060103921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25037350116944292080138561 18778012587708219060103921)
            ·
              refine ⟨14083509440781164295077941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18778012587708219060103921 14083509440781164295077941)
              ·
                refine ⟨1320329010073234152663557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14083509440781164295077941 1320329010073234152663557)
                ·
                  refine ⟨247561689388731403624417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1320329010073234152663557 247561689388731403624417)
                  ·
                    rfl

theorem cell22_2169561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 5, 4].length) (baseStart_2169561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169561 prefixEnd_2169561 := by exact prefixLift 2169561
  have htrace : WordTrace (prefixWord ++ tailWord_2169561) baseStart_2169561 baseEnd_2169561 := by
    simpa [prefixWord, tailWord_2169561, baseEnd_2169561] using wordTrace_append hprefix tailTrace_2169561
  have hstable : (prefixWord ++ tailWord_2169561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169561).length < 2 ^ (prefixWord ++ tailWord_2169561).sum := by decide
  have hdescent : baseEnd_2169561 < baseStart_2169561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169608 : List Nat := [2, 1, 3, 2, 2, 4, 1, 1, 2, 4]
def baseStart_2169608 : Nat := 118140960795 + 2169608 * 2 ^ 59
def prefixEnd_2169608 : Nat := 4983230072969 + 3 ^ 40 * 2169608 * 2
def baseEnd_2169608 : Nat := 742701157226701754948107

theorem tailTrace_2169608 : CollatzResearch.WordTrace tailWord_2169608 prefixEnd_2169608 742701157226701754948107 := by
  unfold tailWord_2169608
  simp only [CollatzResearch.WordTrace]
  refine ⟨39566052361944115195674739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52754736482592153594232985 39566052361944115195674739)
  ·
    refine ⟨59349078542916172793512109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39566052361944115195674739 59349078542916172793512109)
    ·
      refine ⟨22255904453593564797567041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59349078542916172793512109 22255904453593564797567041)
      ·
        refine ⟨16691928340195173598175281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22255904453593564797567041 16691928340195173598175281)
        ·
          refine ⟨12518946255146380198631461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16691928340195173598175281 12518946255146380198631461)
          ·
            refine ⟨2347302422839946287243399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12518946255146380198631461 2347302422839946287243399)
            ·
              refine ⟨3520953634259919430865099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2347302422839946287243399 3520953634259919430865099)
              ·
                refine ⟨5281430451389879146297649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3520953634259919430865099 5281430451389879146297649)
                ·
                  refine ⟨3961072838542409359723237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5281430451389879146297649 3961072838542409359723237)
                  ·
                    refine ⟨742701157226701754948107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3961072838542409359723237 742701157226701754948107)
                    ·
                      rfl

theorem cell22_2169608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_2169608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169608 prefixEnd_2169608 := by exact prefixLift 2169608
  have htrace : WordTrace (prefixWord ++ tailWord_2169608) baseStart_2169608 baseEnd_2169608 := by
    simpa [prefixWord, tailWord_2169608, baseEnd_2169608] using wordTrace_append hprefix tailTrace_2169608
  have hstable : (prefixWord ++ tailWord_2169608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169608).length < 2 ^ (prefixWord ++ tailWord_2169608).sum := by decide
  have hdescent : baseEnd_2169608 < baseStart_2169608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169621 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 5, 3]
def baseStart_2169621 : Nat := 118140960795 + 2169621 * 2 ^ 59
def prefixEnd_2169621 : Nat := 4983230072969 + 3 ^ 40 * 2169621 * 2
def baseEnd_2169621 : Nat := 742705607392374054373067

theorem tailTrace_2169621 : CollatzResearch.WordTrace tailWord_2169621 prefixEnd_2169621 742705607392374054373067 := by
  unfold tailWord_2169621
  simp only [CollatzResearch.WordTrace]
  refine ⟨79132578872841133611572717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52755052581894089074381811 79132578872841133611572717)
  ·
    refine ⟨29674717077315425104339769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79132578872841133611572717 29674717077315425104339769)
    ·
      refine ⟨22256037807986568828254827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29674717077315425104339769 22256037807986568828254827)
      ·
        refine ⟨33384056711979853242382241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22256037807986568828254827 33384056711979853242382241)
        ·
          refine ⟨25038042533984889931786681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33384056711979853242382241 25038042533984889931786681)
          ·
            refine ⟨18778531900488667448840011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25038042533984889931786681 18778531900488667448840011)
            ·
              refine ⟨28167797850733001173260017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18778531900488667448840011 28167797850733001173260017)
              ·
                refine ⟨21125848388049750879945013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28167797850733001173260017 21125848388049750879945013)
                ·
                  refine ⟨1980548286379664144994845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21125848388049750879945013 1980548286379664144994845)
                  ·
                    refine ⟨742705607392374054373067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1980548286379664144994845 742705607392374054373067)
                    ·
                      rfl

theorem cell22_2169621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_2169621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169621 prefixEnd_2169621 := by exact prefixLift 2169621
  have htrace : WordTrace (prefixWord ++ tailWord_2169621) baseStart_2169621 baseEnd_2169621 := by
    simpa [prefixWord, tailWord_2169621, baseEnd_2169621] using wordTrace_append hprefix tailTrace_2169621
  have hstable : (prefixWord ++ tailWord_2169621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169621).length < 2 ^ (prefixWord ++ tailWord_2169621).sum := by decide
  have hdescent : baseEnd_2169621 < baseStart_2169621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169664 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 2, 8]
def baseStart_2169664 : Nat := 118140960795 + 2169664 * 2 ^ 59
def prefixEnd_2169664 : Nat := 4983230072969 + 3 ^ 40 * 2169664 * 2
def baseEnd_2169664 : Nat := 742720327171136275547935

theorem tailTrace_2169664 : CollatzResearch.WordTrace tailWord_2169664 prefixEnd_2169664 742720327171136275547935 := by
  unfold tailWord_2169664
  simp only [CollatzResearch.WordTrace]
  refine ⟨39567073605842675977694023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52756098141123567970258697 39567073605842675977694023)
  ·
    refine ⟨59350610408764013966541035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39567073605842675977694023 59350610408764013966541035)
    ·
      refine ⟨89025915613146020949811553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59350610408764013966541035 89025915613146020949811553)
      ·
        refine ⟨66769436709859515712358665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89025915613146020949811553 66769436709859515712358665)
        ·
          refine ⟨50077077532394636784268999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66769436709859515712358665 50077077532394636784268999)
          ·
            refine ⟨75115616298591955176403499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50077077532394636784268999 75115616298591955176403499)
            ·
              refine ⟨112673424447887932764605249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75115616298591955176403499 112673424447887932764605249)
              ·
                refine ⟨84505068335915949573453937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112673424447887932764605249 84505068335915949573453937)
                ·
                  refine ⟨63378801251936962180090453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84505068335915949573453937 63378801251936962180090453)
                  ·
                    refine ⟨742720327171136275547935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63378801251936962180090453 742720327171136275547935)
                    ·
                      rfl

theorem cell22_2169664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_2169664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169664 prefixEnd_2169664 := by exact prefixLift 2169664
  have htrace : WordTrace (prefixWord ++ tailWord_2169664) baseStart_2169664 baseEnd_2169664 := by
    simpa [prefixWord, tailWord_2169664, baseEnd_2169664] using wordTrace_append hprefix tailTrace_2169664
  have hstable : (prefixWord ++ tailWord_2169664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169664).length < 2 ^ (prefixWord ++ tailWord_2169664).sum := by decide
  have hdescent : baseEnd_2169664 < baseStart_2169664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169777 : List Nat := [1, 2, 2, 4, 4, 1, 1, 1, 2, 4]
def baseStart_2169777 : Nat := 118140960795 + 2169777 * 2 ^ 59
def prefixEnd_2169777 : Nat := 4983230072969 + 3 ^ 40 * 2169777 * 2
def baseEnd_2169777 : Nat := 742759009380441647472589

theorem tailTrace_2169777 : CollatzResearch.WordTrace tailWord_2169777 prefixEnd_2169777 742759009380441647472589 := by
  unfold tailWord_2169777
  simp only [CollatzResearch.WordTrace]
  refine ⟨79138268660275972254251585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52758845773517314836167723 79138268660275972254251585)
  ·
    refine ⟨59353701495206979190688689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79138268660275972254251585 59353701495206979190688689)
    ·
      refine ⟨44515276121405234393016517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59353701495206979190688689 44515276121405234393016517)
      ·
        refine ⟨8346614272763481448690597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44515276121405234393016517 8346614272763481448690597)
        ·
          refine ⟨1564990176143152771629487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8346614272763481448690597 1564990176143152771629487)
          ·
            refine ⟨2347485264214729157444231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1564990176143152771629487 2347485264214729157444231)
            ·
              refine ⟨3521227896322093736166347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2347485264214729157444231 3521227896322093736166347)
              ·
                refine ⟨5281841844483140604249521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3521227896322093736166347 5281841844483140604249521)
                ·
                  refine ⟨3961381383362355453187141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5281841844483140604249521 3961381383362355453187141)
                  ·
                    refine ⟨742759009380441647472589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3961381383362355453187141 742759009380441647472589)
                    ·
                      rfl

theorem cell22_2169777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 2, 4].length) (baseStart_2169777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169777 prefixEnd_2169777 := by exact prefixLift 2169777
  have htrace : WordTrace (prefixWord ++ tailWord_2169777) baseStart_2169777 baseEnd_2169777 := by
    simpa [prefixWord, tailWord_2169777, baseEnd_2169777] using wordTrace_append hprefix tailTrace_2169777
  have hstable : (prefixWord ++ tailWord_2169777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169777).length < 2 ^ (prefixWord ++ tailWord_2169777).sum := by decide
  have hdescent : baseEnd_2169777 < baseStart_2169777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169786 : List Nat := [3, 1, 1, 1, 2, 1, 4, 2, 7]
def baseStart_2169786 : Nat := 118140960795 + 2169786 * 2 ^ 59
def prefixEnd_2169786 : Nat := 4983230072969 + 3 ^ 40 * 2169786 * 2
def baseEnd_2169786 : Nat := 247587363421456207999187

theorem tailTrace_2169786 : CollatzResearch.WordTrace tailWord_2169786 prefixEnd_2169786 247587363421456207999187 := by
  unfold tailWord_2169786
  simp only [CollatzResearch.WordTrace]
  refine ⟨19784649229310841697832303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52759064611495577860886141 19784649229310841697832303)
  ·
    refine ⟨29676973843966262546748455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19784649229310841697832303 29676973843966262546748455)
    ·
      refine ⟨44515460765949393820122683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29676973843966262546748455 44515460765949393820122683)
      ·
        refine ⟨66773191148924090730184025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44515460765949393820122683 66773191148924090730184025)
        ·
          refine ⟨50079893361693068047638019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66773191148924090730184025 50079893361693068047638019)
          ·
            refine ⟨75119840042539602071457029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50079893361693068047638019 75119840042539602071457029)
            ·
              refine ⟨14084970007976175388398193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75119840042539602071457029 14084970007976175388398193)
              ·
                refine ⟨10563727505982131541298645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14084970007976175388398193 10563727505982131541298645)
                ·
                  refine ⟨247587363421456207999187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10563727505982131541298645 247587363421456207999187)
                  ·
                    rfl

theorem cell22_2169786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_2169786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169786 prefixEnd_2169786 := by exact prefixLift 2169786
  have htrace : WordTrace (prefixWord ++ tailWord_2169786) baseStart_2169786 baseEnd_2169786 := by
    simpa [prefixWord, tailWord_2169786, baseEnd_2169786] using wordTrace_append hprefix tailTrace_2169786
  have hstable : (prefixWord ++ tailWord_2169786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169786).length < 2 ^ (prefixWord ++ tailWord_2169786).sum := by decide
  have hdescent : baseEnd_2169786 < baseStart_2169786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169796 : List Nat := [2, 3, 3, 3, 2, 1, 1, 2, 2, 3]
def baseStart_2169796 : Nat := 118140960795 + 2169796 * 2 ^ 59
def prefixEnd_2169796 : Nat := 4983230072969 + 3 ^ 40 * 2169796 * 2
def baseEnd_2169796 : Nat := 742765513468731931247531

theorem tailTrace_2169796 : CollatzResearch.WordTrace tailWord_2169796 prefixEnd_2169796 742765513468731931247531 := by
  unfold tailWord_2169796
  simp only [CollatzResearch.WordTrace]
  refine ⟨39569480823603569249596621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52759307764804758999462161 39569480823603569249596621)
  ·
    refine ⟨14838555308851338468598733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39569480823603569249596621 14838555308851338468598733)
    ·
      refine ⟨5564458240819251925724525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14838555308851338468598733 5564458240819251925724525)
      ·
        refine ⟨2086671840307219472146697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5564458240819251925724525 2086671840307219472146697)
        ·
          refine ⟨1565003880230414604110023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2086671840307219472146697 1565003880230414604110023)
          ·
            refine ⟨2347505820345621906165035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1565003880230414604110023 2347505820345621906165035)
            ·
              refine ⟨3521258730518432859247553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2347505820345621906165035 3521258730518432859247553)
              ·
                refine ⟨2640944047888824644435665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3521258730518432859247553 2640944047888824644435665)
                ·
                  refine ⟨1980708035916618483326749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2640944047888824644435665 1980708035916618483326749)
                  ·
                    refine ⟨742765513468731931247531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1980708035916618483326749 742765513468731931247531)
                    ·
                      rfl

theorem cell22_2169796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_2169796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169796 prefixEnd_2169796 := by exact prefixLift 2169796
  have htrace : WordTrace (prefixWord ++ tailWord_2169796) baseStart_2169796 baseEnd_2169796 := by
    simpa [prefixWord, tailWord_2169796, baseEnd_2169796] using wordTrace_append hprefix tailTrace_2169796
  have hstable : (prefixWord ++ tailWord_2169796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169796).length < 2 ^ (prefixWord ++ tailWord_2169796).sum := by decide
  have hdescent : baseEnd_2169796 < baseStart_2169796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169803 : List Nat := [1, 1, 1, 1, 3, 5, 3, 2, 5]
def baseStart_2169803 : Nat := 118140960795 + 2169803 * 2 ^ 59
def prefixEnd_2169803 : Nat := 4983230072969 + 3 ^ 40 * 2169803 * 2
def baseEnd_2169803 : Nat := 247589303237262082107503

theorem tailTrace_2169803 : CollatzResearch.WordTrace tailWord_2169803 prefixEnd_2169803 247589303237262082107503 := by
  unfold tailWord_2169803
  simp only [CollatzResearch.WordTrace]
  refine ⟨79139216958181778694698063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52759477972121185796465375 79139216958181778694698063)
  ·
    refine ⟨118708825437272668042047095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79139216958181778694698063 118708825437272668042047095)
    ·
      refine ⟨178063238155909002063070643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118708825437272668042047095 178063238155909002063070643)
      ·
        refine ⟨267094857233863503094605965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178063238155909002063070643 267094857233863503094605965)
        ·
          refine ⟨100160571462698813660477237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 267094857233863503094605965 100160571462698813660477237)
          ·
            refine ⟨9390053574628013780669741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100160571462698813660477237 9390053574628013780669741)
            ·
              refine ⟨3521270090485505167751153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9390053574628013780669741 3521270090485505167751153)
              ·
                refine ⟨2640952567864128875813365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3521270090485505167751153 2640952567864128875813365)
                ·
                  refine ⟨247589303237262082107503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2640952567864128875813365 247589303237262082107503)
                  ·
                    rfl

theorem cell22_2169803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 5].length) (baseStart_2169803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169803 prefixEnd_2169803 := by exact prefixLift 2169803
  have htrace : WordTrace (prefixWord ++ tailWord_2169803) baseStart_2169803 baseEnd_2169803 := by
    simpa [prefixWord, tailWord_2169803, baseEnd_2169803] using wordTrace_append hprefix tailTrace_2169803
  have hstable : (prefixWord ++ tailWord_2169803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169803).length < 2 ^ (prefixWord ++ tailWord_2169803).sum := by decide
  have hdescent : baseEnd_2169803 < baseStart_2169803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169818 : List Nat := [3, 1, 1, 2, 4, 1, 2, 1, 2, 5]
def baseStart_2169818 : Nat := 118140960795 + 2169818 * 2 ^ 59
def prefixEnd_2169818 : Nat := 4983230072969 + 3 ^ 40 * 2169818 * 2
def baseEnd_2169818 : Nat := 742773044518331207197463

theorem tailTrace_2169818 : CollatzResearch.WordTrace tailWord_2169818 prefixEnd_2169818 742773044518331207197463 := by
  unfold tailWord_2169818
  simp only [CollatzResearch.WordTrace]
  refine ⟨19784941013281859064123527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52759842702084957504329405 19784941013281859064123527)
  ·
    refine ⟨29677411519922788596185291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19784941013281859064123527 29677411519922788596185291)
    ·
      refine ⟨44516117279884182894277937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29677411519922788596185291 44516117279884182894277937)
      ·
        refine ⟨33387087959913137170708453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44516117279884182894277937 33387087959913137170708453)
        ·
          refine ⟨6260078992483713219507835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33387087959913137170708453 6260078992483713219507835)
          ·
            refine ⟨9390118488725569829261753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6260078992483713219507835 9390118488725569829261753)
            ·
              refine ⟨7042588866544177371946315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9390118488725569829261753 7042588866544177371946315)
              ·
                refine ⟨10563883299816266057919473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7042588866544177371946315 10563883299816266057919473)
                ·
                  refine ⟨7922912474862199543439605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10563883299816266057919473 7922912474862199543439605)
                  ·
                    refine ⟨742773044518331207197463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7922912474862199543439605 742773044518331207197463)
                    ·
                      rfl

theorem cell22_2169818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_2169818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169818 prefixEnd_2169818 := by exact prefixLift 2169818
  have htrace : WordTrace (prefixWord ++ tailWord_2169818) baseStart_2169818 baseEnd_2169818 := by
    simpa [prefixWord, tailWord_2169818, baseEnd_2169818] using wordTrace_append hprefix tailTrace_2169818
  have hstable : (prefixWord ++ tailWord_2169818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169818).length < 2 ^ (prefixWord ++ tailWord_2169818).sum := by decide
  have hdescent : baseEnd_2169818 < baseStart_2169818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169858 : List Nat := [3, 4, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_2169858 : Nat := 118140960795 + 2169858 * 2 ^ 59
def prefixEnd_2169858 : Nat := 4983230072969 + 3 ^ 40 * 2169858 * 2
def baseEnd_2169858 : Nat := 742786737335784436197341

theorem tailTrace_2169858 : CollatzResearch.WordTrace tailWord_2169858 prefixEnd_2169858 742786737335784436197341 := by
  unfold tailWord_2169858
  simp only [CollatzResearch.WordTrace]
  refine ⟨19785305743245630771987557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52760815315321682058633485 19785305743245630771987557)
  ·
    refine ⟨3709744826858555769747667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19785305743245630771987557 3709744826858555769747667)
    ·
      refine ⟨5564617240287833654621501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3709744826858555769747667 5564617240287833654621501)
      ·
        refine ⟨2086731465107937620483063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5564617240287833654621501 2086731465107937620483063)
        ·
          refine ⟨3130097197661906430724595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2086731465107937620483063 3130097197661906430724595)
          ·
            refine ⟨4695145796492859646086893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3130097197661906430724595 4695145796492859646086893)
            ·
              refine ⟨1760679673684822367282585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4695145796492859646086893 1760679673684822367282585)
              ·
                refine ⟨1320509755263616775461939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1760679673684822367282585 1320509755263616775461939)
                ·
                  refine ⟨1980764632895425163192909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1320509755263616775461939 1980764632895425163192909)
                  ·
                    refine ⟨742786737335784436197341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1980764632895425163192909 742786737335784436197341)
                    ·
                      rfl

theorem cell22_2169858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_2169858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169858 prefixEnd_2169858 := by exact prefixLift 2169858
  have htrace : WordTrace (prefixWord ++ tailWord_2169858) baseStart_2169858 baseEnd_2169858 := by
    simpa [prefixWord, tailWord_2169858, baseEnd_2169858] using wordTrace_append hprefix tailTrace_2169858
  have hstable : (prefixWord ++ tailWord_2169858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169858).length < 2 ^ (prefixWord ++ tailWord_2169858).sum := by decide
  have hdescent : baseEnd_2169858 < baseStart_2169858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169884 : List Nat := [2, 2, 3, 1, 5, 1, 1, 2, 1, 4]
def baseStart_2169884 : Nat := 118140960795 + 2169884 * 2 ^ 59
def prefixEnd_2169884 : Nat := 4983230072969 + 3 ^ 40 * 2169884 * 2
def baseEnd_2169884 : Nat := 742795637667129035047261

theorem tailTrace_2169884 : CollatzResearch.WordTrace tailWord_2169884 prefixEnd_2169884 742795637667129035047261 := by
  unfold tailWord_2169884
  simp only [CollatzResearch.WordTrace]
  refine ⟨39571085635444164764198353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52761447513925553018931137 39571085635444164764198353)
  ·
    refine ⟨29678314226583123573148765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39571085635444164764198353 29678314226583123573148765)
    ·
      refine ⟨11129367834968671339930787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29678314226583123573148765 11129367834968671339930787)
      ·
        refine ⟨16694051752453007009896181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11129367834968671339930787 16694051752453007009896181)
        ·
          refine ⟨1565067351792469407177767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16694051752453007009896181 1565067351792469407177767)
          ·
            refine ⟨2347601027688704110766651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1565067351792469407177767 2347601027688704110766651)
            ·
              refine ⟨3521401541533056166149977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2347601027688704110766651 3521401541533056166149977)
              ·
                refine ⟨2641051156149792124612483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3521401541533056166149977 2641051156149792124612483)
                ·
                  refine ⟨3961576734224688186918725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2641051156149792124612483 3961576734224688186918725)
                  ·
                    refine ⟨742795637667129035047261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3961576734224688186918725 742795637667129035047261)
                    ·
                      rfl

theorem cell22_2169884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_2169884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169884 prefixEnd_2169884 := by exact prefixLift 2169884
  have htrace : WordTrace (prefixWord ++ tailWord_2169884) baseStart_2169884 baseEnd_2169884 := by
    simpa [prefixWord, tailWord_2169884, baseEnd_2169884] using wordTrace_append hprefix tailTrace_2169884
  have hstable : (prefixWord ++ tailWord_2169884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169884).length < 2 ^ (prefixWord ++ tailWord_2169884).sum := by decide
  have hdescent : baseEnd_2169884 < baseStart_2169884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2169959 : List Nat := [1, 1, 5, 1, 1, 4, 2, 3, 1, 3]
def baseStart_2169959 : Nat := 118140960795 + 2169959 * 2 ^ 59
def prefixEnd_2169959 : Nat := 4983230072969 + 3 ^ 40 * 2169959 * 2
def baseEnd_2169959 : Nat := 742821311699853839422031

theorem tailTrace_2169959 : CollatzResearch.WordTrace tailWord_2169959 prefixEnd_2169959 742821311699853839422031 := by
  unfold tailWord_2169959
  simp only [CollatzResearch.WordTrace]
  refine ⟨79144906745616617337376931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52763271163744411558251287 79144906745616617337376931)
  ·
    refine ⟨118717360118424926006065397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79144906745616617337376931 118717360118424926006065397)
    ·
      refine ⟨11129752511102336813068631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118717360118424926006065397 11129752511102336813068631)
      ·
        refine ⟨16694628766653505219602947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11129752511102336813068631 16694628766653505219602947)
        ·
          refine ⟨25041943149980257829404421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16694628766653505219602947 25041943149980257829404421)
          ·
            refine ⟨4695364340621298343013329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25041943149980257829404421 4695364340621298343013329)
            ·
              refine ⟨3521523255465973757259997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4695364340621298343013329 3521523255465973757259997)
              ·
                refine ⟨1320571220799740158972499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3521523255465973757259997 1320571220799740158972499)
                ·
                  refine ⟨1980856831199610238458749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1320571220799740158972499 1980856831199610238458749)
                  ·
                    refine ⟨742821311699853839422031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1980856831199610238458749 742821311699853839422031)
                    ·
                      rfl

theorem cell22_2169959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_2169959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2169959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2169959 prefixEnd_2169959 := by exact prefixLift 2169959
  have htrace : WordTrace (prefixWord ++ tailWord_2169959) baseStart_2169959 baseEnd_2169959 := by
    simpa [prefixWord, tailWord_2169959, baseEnd_2169959] using wordTrace_append hprefix tailTrace_2169959
  have hstable : (prefixWord ++ tailWord_2169959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2169959).length < 2 ^ (prefixWord ++ tailWord_2169959).sum := by decide
  have hdescent : baseEnd_2169959 < baseStart_2169959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2169959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170002 : List Nat := [3, 2, 3, 1, 1, 2, 1, 4, 1, 4]
def baseStart_2170002 : Nat := 118140960795 + 2170002 * 2 ^ 59
def prefixEnd_2170002 : Nat := 4983230072969 + 3 ^ 40 * 2170002 * 2
def baseEnd_2170002 : Nat := 742836031478616060596899

theorem tailTrace_2170002 : CollatzResearch.WordTrace tailWord_2170002 prefixEnd_2170002 742836031478616060596899 := by
  unfold tailWord_2170002
  simp only [CollatzResearch.WordTrace]
  refine ⟨19786618771115208920298065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52764316722973890454128173 19786618771115208920298065)
  ·
    refine ⟨14839964078336406690223549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19786618771115208920298065 14839964078336406690223549)
    ·
      refine ⟨5564986529376152508833831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14839964078336406690223549 5564986529376152508833831)
      ·
        refine ⟨8347479794064228763250747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5564986529376152508833831 8347479794064228763250747)
        ·
          refine ⟨12521219691096343144876121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8347479794064228763250747 12521219691096343144876121)
          ·
            refine ⟨9390914768322257358657091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12521219691096343144876121 9390914768322257358657091)
            ·
              refine ⟨14086372152483386037985637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9390914768322257358657091 14086372152483386037985637)
              ·
                refine ⟨2641194778590634882122307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14086372152483386037985637 2641194778590634882122307)
                ·
                  refine ⟨3961792167885952323183461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2641194778590634882122307 3961792167885952323183461)
                  ·
                    refine ⟨742836031478616060596899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3961792167885952323183461 742836031478616060596899)
                    ·
                      rfl

theorem cell22_2170002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_2170002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170002 prefixEnd_2170002 := by exact prefixLift 2170002
  have htrace : WordTrace (prefixWord ++ tailWord_2170002) baseStart_2170002 baseEnd_2170002 := by
    simpa [prefixWord, tailWord_2170002, baseEnd_2170002] using wordTrace_append hprefix tailTrace_2170002
  have hstable : (prefixWord ++ tailWord_2170002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170002).length < 2 ^ (prefixWord ++ tailWord_2170002).sum := by decide
  have hdescent : baseEnd_2170002 < baseStart_2170002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170034 : List Nat := [3, 2, 1, 1, 1, 5, 3, 2, 4]
def baseStart_2170034 : Nat := 118140960795 + 2170034 * 2 ^ 59
def prefixEnd_2170034 : Nat := 4983230072969 + 3 ^ 40 * 2170034 * 2
def baseEnd_2170034 : Nat := 247615661910859547932267

theorem tailTrace_2170034 : CollatzResearch.WordTrace tailWord_2170034 prefixEnd_2170034 247615661910859547932267 := by
  unfold tailWord_2170034
  simp only [CollatzResearch.WordTrace]
  refine ⟨19786910555086226286589289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52765094813563270097571437 19786910555086226286589289)
  ·
    refine ⟨14840182916314669714941967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19786910555086226286589289 14840182916314669714941967)
    ·
      refine ⟨22260274374472004572412951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14840182916314669714941967 22260274374472004572412951)
      ·
        refine ⟨33390411561708006858619427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22260274374472004572412951 33390411561708006858619427)
        ·
          refine ⟨50085617342562010287929141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33390411561708006858619427 50085617342562010287929141)
          ·
            refine ⟨4695526625865188464493357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50085617342562010287929141 4695526625865188464493357)
            ·
              refine ⟨1760822484699445674185009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4695526625865188464493357 1760822484699445674185009)
              ·
                refine ⟨1320616863524584255638757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1760822484699445674185009 1320616863524584255638757)
                ·
                  refine ⟨247615661910859547932267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1320616863524584255638757 247615661910859547932267)
                  ·
                    rfl

theorem cell22_2170034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_2170034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170034 prefixEnd_2170034 := by exact prefixLift 2170034
  have htrace : WordTrace (prefixWord ++ tailWord_2170034) baseStart_2170034 baseEnd_2170034 := by
    simpa [prefixWord, tailWord_2170034, baseEnd_2170034] using wordTrace_append hprefix tailTrace_2170034
  have hstable : (prefixWord ++ tailWord_2170034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170034).length < 2 ^ (prefixWord ++ tailWord_2170034).sum := by decide
  have hdescent : baseEnd_2170034 < baseStart_2170034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170043 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 2, 7]
def baseStart_2170043 : Nat := 118140960795 + 2170043 * 2 ^ 59
def prefixEnd_2170043 : Nat := 4983230072969 + 3 ^ 40 * 2170043 * 2
def baseEnd_2170043 : Nat := 742850066616505620321773

theorem tailTrace_2170043 : CollatzResearch.WordTrace tailWord_2170043 prefixEnd_2170043 742850066616505620321773 := by
  unfold tailWord_2170043
  simp only [CollatzResearch.WordTrace]
  refine ⟨79147970477312299683434783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52765313651541533122289855 79147970477312299683434783)
  ·
    refine ⟨118721955715968449525152175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79147970477312299683434783 118721955715968449525152175)
    ·
      refine ⟨178082933573952674287728263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118721955715968449525152175 178082933573952674287728263)
      ·
        refine ⟨267124400360929011431592395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178082933573952674287728263 267124400360929011431592395)
        ·
          refine ⟨400686600541393517147388593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267124400360929011431592395 400686600541393517147388593)
          ·
            refine ⟨300514950406045137860541445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 400686600541393517147388593 300514950406045137860541445)
            ·
              refine ⟨56346553201133463348851521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 300514950406045137860541445 56346553201133463348851521)
              ·
                refine ⟨42259914900850097511638641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56346553201133463348851521 42259914900850097511638641)
                ·
                  refine ⟨31694936175637573133728981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42259914900850097511638641 31694936175637573133728981)
                  ·
                    refine ⟨742850066616505620321773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31694936175637573133728981 742850066616505620321773)
                    ·
                      rfl

theorem cell22_2170043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 7].length) (baseStart_2170043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170043 prefixEnd_2170043 := by exact prefixLift 2170043
  have htrace : WordTrace (prefixWord ++ tailWord_2170043) baseStart_2170043 baseEnd_2170043 := by
    simpa [prefixWord, tailWord_2170043, baseEnd_2170043] using wordTrace_append hprefix tailTrace_2170043
  have hstable : (prefixWord ++ tailWord_2170043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170043).length < 2 ^ (prefixWord ++ tailWord_2170043).sum := by decide
  have hdescent : baseEnd_2170043 < baseStart_2170043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170105 : List Nat := [1, 2, 1, 3, 1, 1, 5, 1, 2, 5]
def baseStart_2170105 : Nat := 118140960795 + 2170105 * 2 ^ 59
def prefixEnd_2170105 : Nat := 4983230072969 + 3 ^ 40 * 2170105 * 2
def baseEnd_2170105 : Nat := 742871290483558125271583

theorem tailTrace_2170105 : CollatzResearch.WordTrace tailWord_2170105 prefixEnd_2170105 742871290483558125271583 := by
  unfold tailWord_2170105
  simp only [CollatzResearch.WordTrace]
  refine ⟨79150231803087684272191769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52766821202058456181461179 79150231803087684272191769)
  ·
    refine ⟨59362673852315763204143827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79150231803087684272191769 59362673852315763204143827)
    ·
      refine ⟨89044010778473644806215741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59362673852315763204143827 89044010778473644806215741)
      ·
        refine ⟨33391504041927616802330903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89044010778473644806215741 33391504041927616802330903)
        ·
          refine ⟨50087256062891425203496355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33391504041927616802330903 50087256062891425203496355)
          ·
            refine ⟨75130884094337137805244533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50087256062891425203496355 75130884094337137805244533)
            ·
              refine ⟨7043520383844106669241675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75130884094337137805244533 7043520383844106669241675)
              ·
                refine ⟨10565280575766160003862513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7043520383844106669241675 10565280575766160003862513)
                ·
                  refine ⟨7923960431824620002896885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10565280575766160003862513 7923960431824620002896885)
                  ·
                    refine ⟨742871290483558125271583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7923960431824620002896885 742871290483558125271583)
                    ·
                      rfl

theorem cell22_2170105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 2, 5].length) (baseStart_2170105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170105 prefixEnd_2170105 := by exact prefixLift 2170105
  have htrace : WordTrace (prefixWord ++ tailWord_2170105) baseStart_2170105 baseEnd_2170105 := by
    simpa [prefixWord, tailWord_2170105, baseEnd_2170105] using wordTrace_append hprefix tailTrace_2170105
  have hstable : (prefixWord ++ tailWord_2170105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170105).length < 2 ^ (prefixWord ++ tailWord_2170105).sum := by decide
  have hdescent : baseEnd_2170105 < baseStart_2170105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170135 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 8]
def baseStart_2170135 : Nat := 118140960795 + 2170135 * 2 ^ 59
def prefixEnd_2170135 : Nat := 4983230072969 + 3 ^ 40 * 2170135 * 2
def baseEnd_2170135 : Nat := 247627186698882682340497

theorem tailTrace_2170135 : CollatzResearch.WordTrace tailWord_2170135 prefixEnd_2170135 247627186698882682340497 := by
  unfold tailWord_2170135
  simp only [CollatzResearch.WordTrace]
  refine ⟨79151325992978999395783859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52767550661985999597189239 79151325992978999395783859)
  ·
    refine ⟨118726988989468499093675789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79151325992978999395783859 118726988989468499093675789)
    ·
      refine ⟨44522620871050687160128421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118726988989468499093675789 44522620871050687160128421)
      ·
        refine ⟨8347991413322003842524079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44522620871050687160128421 8347991413322003842524079)
        ·
          refine ⟨12521987119983005763786119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8347991413322003842524079 12521987119983005763786119)
          ·
            refine ⟨18782980679974508645679179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12521987119983005763786119 18782980679974508645679179)
            ·
              refine ⟨28174471019961762968518769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18782980679974508645679179 28174471019961762968518769)
              ·
                refine ⟨21130853264971322226389077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28174471019961762968518769 21130853264971322226389077)
                ·
                  refine ⟨247627186698882682340497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21130853264971322226389077 247627186698882682340497)
                  ·
                    rfl

theorem cell22_2170135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 8].length) (baseStart_2170135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170135 prefixEnd_2170135 := by exact prefixLift 2170135
  have htrace : WordTrace (prefixWord ++ tailWord_2170135) baseStart_2170135 baseEnd_2170135 := by
    simpa [prefixWord, tailWord_2170135, baseEnd_2170135] using wordTrace_append hprefix tailTrace_2170135
  have hstable : (prefixWord ++ tailWord_2170135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170135).length < 2 ^ (prefixWord ++ tailWord_2170135).sum := by decide
  have hdescent : baseEnd_2170135 < baseStart_2170135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170152 : List Nat := [2, 1, 5, 1, 2, 1, 1, 3, 6]
def baseStart_2170152 : Nat := 118140960795 + 2170152 * 2 ^ 59
def prefixEnd_2170152 : Nat := 4983230072969 + 3 ^ 40 * 2170152 * 2
def baseEnd_2170152 : Nat := 247629126514688556448813

theorem tailTrace_2170152 : CollatzResearch.WordTrace tailWord_2170152 prefixEnd_2170152 247629126514688556448813 := by
  unfold tailWord_2170152
  simp only [CollatzResearch.WordTrace]
  refine ⟨39575973016958705649576355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52767964022611607532768473 39575973016958705649576355)
  ·
    refine ⟨59363959525438058474364533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39575973016958705649576355 59363959525438058474364533)
    ·
      refine ⟨5565371205509817981971675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59363959525438058474364533 5565371205509817981971675)
      ·
        refine ⟨8348056808264726972957513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5565371205509817981971675 8348056808264726972957513)
        ·
          refine ⟨6261042606198545229718135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8348056808264726972957513 6261042606198545229718135)
          ·
            refine ⟨9391563909297817844577203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6261042606198545229718135 9391563909297817844577203)
            ·
              refine ⟨14087345863946726766865805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9391563909297817844577203 14087345863946726766865805)
              ·
                refine ⟨5282754698980022537574677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14087345863946726766865805 5282754698980022537574677)
                ·
                  refine ⟨247629126514688556448813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5282754698980022537574677 247629126514688556448813)
                  ·
                    rfl

theorem cell22_2170152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 6].length) (baseStart_2170152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170152 prefixEnd_2170152 := by exact prefixLift 2170152
  have htrace : WordTrace (prefixWord ++ tailWord_2170152) baseStart_2170152 baseEnd_2170152 := by
    simpa [prefixWord, tailWord_2170152, baseEnd_2170152] using wordTrace_append hprefix tailTrace_2170152
  have hstable : (prefixWord ++ tailWord_2170152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170152).length < 2 ^ (prefixWord ++ tailWord_2170152).sum := by decide
  have hdescent : baseEnd_2170152 < baseStart_2170152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170197 : List Nat := [1, 3, 2, 2, 3, 3, 8]
def baseStart_2170197 : Nat := 118140960795 + 2170197 * 2 ^ 59
def prefixEnd_2170197 : Nat := 4983230072969 + 3 ^ 40 * 2170197 * 2
def baseEnd_2170197 : Nat := 27514917924581501924863

theorem tailTrace_2170197 : CollatzResearch.WordTrace tailWord_2170197 prefixEnd_2170197 27514917924581501924863 := by
  unfold tailWord_2170197
  simp only [CollatzResearch.WordTrace]
  refine ⟨79153587318754383984540845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52769058212502922656360563 79153587318754383984540845)
  ·
    refine ⟨29682595244532893994202817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79153587318754383984540845 29682595244532893994202817)
    ·
      refine ⟨22261946433399670495652113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29682595244532893994202817 22261946433399670495652113)
      ·
        refine ⟨16696459825049752871739085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22261946433399670495652113 16696459825049752871739085)
        ·
          refine ⟨6261172434393657326902157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16696459825049752871739085 6261172434393657326902157)
          ·
            refine ⟨2347939662897621497588309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6261172434393657326902157 2347939662897621497588309)
            ·
              refine ⟨27514917924581501924863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2347939662897621497588309 27514917924581501924863)
              ·
                rfl

theorem cell22_2170197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 8].length) (baseStart_2170197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170197 prefixEnd_2170197 := by exact prefixLift 2170197
  have htrace : WordTrace (prefixWord ++ tailWord_2170197) baseStart_2170197 baseEnd_2170197 := by
    simpa [prefixWord, tailWord_2170197, baseEnd_2170197] using wordTrace_append hprefix tailTrace_2170197
  have hstable : (prefixWord ++ tailWord_2170197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170197).length < 2 ^ (prefixWord ++ tailWord_2170197).sum := by decide
  have hdescent : baseEnd_2170197 < baseStart_2170197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170272 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 5, 4]
def baseStart_2170272 : Nat := 118140960795 + 2170272 * 2 ^ 59
def prefixEnd_2170272 : Nat := 4983230072969 + 3 ^ 40 * 2170272 * 2
def baseEnd_2170272 : Nat := 742928457996425356346071

theorem tailTrace_2170272 : CollatzResearch.WordTrace tailWord_2170272 prefixEnd_2170272 742928457996425356346071 := by
  unfold tailWord_2170272
  simp only [CollatzResearch.WordTrace]
  refine ⟨39578161396741335896760535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52770881862321781195680713 39578161396741335896760535)
  ·
    refine ⟨59367242095112003845140803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39578161396741335896760535 59367242095112003845140803)
    ·
      refine ⟨89050863142668005767711205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59367242095112003845140803 89050863142668005767711205)
      ·
        refine ⟨16697036839250251081445851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89050863142668005767711205 16697036839250251081445851)
        ·
          refine ⟨25045555258875376622168777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16697036839250251081445851 25045555258875376622168777)
          ·
            refine ⟨18784166444156532466626583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25045555258875376622168777 18784166444156532466626583)
            ·
              refine ⟨28176249666234798699939875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18784166444156532466626583 28176249666234798699939875)
              ·
                refine ⟨42264374499352198049909813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28176249666234798699939875 42264374499352198049909813)
                ·
                  refine ⟨3962285109314268567179045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42264374499352198049909813 3962285109314268567179045)
                  ·
                    refine ⟨742928457996425356346071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3962285109314268567179045 742928457996425356346071)
                    ·
                      rfl

theorem cell22_2170272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 5, 4].length) (baseStart_2170272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170272 prefixEnd_2170272 := by exact prefixLift 2170272
  have htrace : WordTrace (prefixWord ++ tailWord_2170272) baseStart_2170272 baseEnd_2170272 := by
    simpa [prefixWord, tailWord_2170272, baseEnd_2170272] using wordTrace_append hprefix tailTrace_2170272
  have hstable : (prefixWord ++ tailWord_2170272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170272).length < 2 ^ (prefixWord ++ tailWord_2170272).sum := by decide
  have hdescent : baseEnd_2170272 < baseStart_2170272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170274 : List Nat := [3, 3, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_2170274 : Nat := 118140960795 + 2170274 * 2 ^ 59
def prefixEnd_2170274 : Nat := 4983230072969 + 3 ^ 40 * 2170274 * 2
def baseEnd_2170274 : Nat := 742929142637298017796065

theorem tailTrace_2170274 : CollatzResearch.WordTrace tailWord_2170274 prefixEnd_2170274 742929142637298017796065 := by
  unfold tailWord_2170274
  simp only [CollatzResearch.WordTrace]
  refine ⟨19789098934868856533773469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52770930492983617423395917 19789098934868856533773469)
  ·
    refine ⟨7420912100575821200165051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19789098934868856533773469 7420912100575821200165051)
    ·
      refine ⟨11131368150863731800247577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7420912100575821200165051 11131368150863731800247577)
      ·
        refine ⟨8348526113147798850185683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11131368150863731800247577 8348526113147798850185683)
        ·
          refine ⟨12522789169721698275278525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8348526113147798850185683 12522789169721698275278525)
          ·
            refine ⟨4696045938645636853229447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12522789169721698275278525 4696045938645636853229447)
            ·
              refine ⟨7044068907968455279844171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4696045938645636853229447 7044068907968455279844171)
              ·
                refine ⟨10566103361952682919766257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7044068907968455279844171 10566103361952682919766257)
                ·
                  refine ⟨7924577521464512189824693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10566103361952682919766257 7924577521464512189824693)
                  ·
                    refine ⟨742929142637298017796065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7924577521464512189824693 742929142637298017796065)
                    ·
                      rfl

theorem cell22_2170274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_2170274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170274 prefixEnd_2170274 := by exact prefixLift 2170274
  have htrace : WordTrace (prefixWord ++ tailWord_2170274) baseStart_2170274 baseEnd_2170274 := by
    simpa [prefixWord, tailWord_2170274, baseEnd_2170274] using wordTrace_append hprefix tailTrace_2170274
  have hstable : (prefixWord ++ tailWord_2170274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170274).length < 2 ^ (prefixWord ++ tailWord_2170274).sum := by decide
  have hdescent : baseEnd_2170274 < baseStart_2170274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170289 : List Nat := [1, 2, 2, 4, 1, 1, 2, 4, 1, 4]
def baseStart_2170289 : Nat := 118140960795 + 2170289 * 2 ^ 59
def prefixEnd_2170289 : Nat := 4983230072969 + 3 ^ 40 * 2170289 * 2
def baseEnd_2170289 : Nat := 742934277443842978671019

theorem tailTrace_2170289 : CollatzResearch.WordTrace tailWord_2170289 prefixEnd_2170289 742934277443842978671019 := by
  unfold tailWord_2170289
  simp only [CollatzResearch.WordTrace]
  refine ⟨79156942834421083696889921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52771295222947389131259947 79156942834421083696889921)
  ·
    refine ⟨59367707125815812772667441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79156942834421083696889921 59367707125815812772667441)
    ·
      refine ⟨44525780344361859579500581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59367707125815812772667441 44525780344361859579500581)
      ·
        refine ⟨8348583814567848671156359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44525780344361859579500581 8348583814567848671156359)
        ·
          refine ⟨12522875721851773006734539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8348583814567848671156359 12522875721851773006734539)
          ·
            refine ⟨18784313582777659510101809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12522875721851773006734539 18784313582777659510101809)
            ·
              refine ⟨14088235187083244632576357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18784313582777659510101809 14088235187083244632576357)
              ·
                refine ⟨2641544097578108368608067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14088235187083244632576357 2641544097578108368608067)
                ·
                  refine ⟨3962316146367162552912101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2641544097578108368608067 3962316146367162552912101)
                  ·
                    refine ⟨742934277443842978671019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3962316146367162552912101 742934277443842978671019)
                    ·
                      rfl

theorem cell22_2170289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_2170289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170289 prefixEnd_2170289 := by exact prefixLift 2170289
  have htrace : WordTrace (prefixWord ++ tailWord_2170289) baseStart_2170289 baseEnd_2170289 := by
    simpa [prefixWord, tailWord_2170289, baseEnd_2170289] using wordTrace_append hprefix tailTrace_2170289
  have hstable : (prefixWord ++ tailWord_2170289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170289).length < 2 ^ (prefixWord ++ tailWord_2170289).sum := by decide
  have hdescent : baseEnd_2170289 < baseStart_2170289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170304 : List Nat := [2, 1, 1, 2, 3, 1, 3, 5, 4]
def baseStart_2170304 : Nat := 118140960795 + 2170304 * 2 ^ 59
def prefixEnd_2170304 : Nat := 4983230072969 + 3 ^ 40 * 2170304 * 2
def baseEnd_2170304 : Nat := 247646470750129313181991

theorem tailTrace_2170304 : CollatzResearch.WordTrace tailWord_2170304 prefixEnd_2170304 247646470750129313181991 := by
  unfold tailWord_2170304
  simp only [CollatzResearch.WordTrace]
  refine ⟨39578744964683370629342983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52771659952911160839123977 39578744964683370629342983)
  ·
    refine ⟨59368117447025055944014475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39578744964683370629342983 59368117447025055944014475)
    ·
      refine ⟨89052176170537583916021713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59368117447025055944014475 89052176170537583916021713)
      ·
        refine ⟨66789132127903187937016285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89052176170537583916021713 66789132127903187937016285)
        ·
          refine ⟨25045924547963695476381107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66789132127903187937016285 25045924547963695476381107)
          ·
            refine ⟨37568886821945543214571661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25045924547963695476381107 37568886821945543214571661)
            ·
              refine ⟨14088332558229578705464373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37568886821945543214571661 14088332558229578705464373)
              ·
                refine ⟨1320781177334023003637285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14088332558229578705464373 1320781177334023003637285)
                ·
                  refine ⟨247646470750129313181991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1320781177334023003637285 247646470750129313181991)
                  ·
                    rfl

theorem cell22_2170304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 5, 4].length) (baseStart_2170304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170304 prefixEnd_2170304 := by exact prefixLift 2170304
  have htrace : WordTrace (prefixWord ++ tailWord_2170304) baseStart_2170304 baseEnd_2170304 := by
    simpa [prefixWord, tailWord_2170304, baseEnd_2170304] using wordTrace_append hprefix tailTrace_2170304
  have hstable : (prefixWord ++ tailWord_2170304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170304).length < 2 ^ (prefixWord ++ tailWord_2170304).sum := by decide
  have hdescent : baseEnd_2170304 < baseStart_2170304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170364 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 5, 3]
def baseStart_2170364 : Nat := 118140960795 + 2170364 * 2 ^ 59
def prefixEnd_2170364 : Nat := 4983230072969 + 3 ^ 40 * 2170364 * 2
def baseEnd_2170364 : Nat := 742959951476567783045789

theorem tailTrace_2170364 : CollatzResearch.WordTrace tailWord_2170364 prefixEnd_2170364 742959951476567783045789 := by
  unfold tailWord_2170364
  simp only [CollatzResearch.WordTrace]
  refine ⟨39579839154574685752935073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52773118872766247670580097 39579839154574685752935073)
  ·
    refine ⟨29684879365931014314701305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39579839154574685752935073 29684879365931014314701305)
    ·
      refine ⟨22263659524448260736025979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29684879365931014314701305 22263659524448260736025979)
      ·
        refine ⟨33395489286672391104038969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22263659524448260736025979 33395489286672391104038969)
        ·
          refine ⟨25046616965004293328029227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33395489286672391104038969 25046616965004293328029227)
          ·
            refine ⟨37569925447506439992043841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25046616965004293328029227 37569925447506439992043841)
            ·
              refine ⟨28177444085629829994032881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37569925447506439992043841 28177444085629829994032881)
              ·
                refine ⟨21133083064222372495524661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28177444085629829994032881 21133083064222372495524661)
                ·
                  refine ⟨1981226537270847421455437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21133083064222372495524661 1981226537270847421455437)
                  ·
                    refine ⟨742959951476567783045789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1981226537270847421455437 742959951476567783045789)
                    ·
                      rfl

theorem cell22_2170364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_2170364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170364 prefixEnd_2170364 := by exact prefixLift 2170364
  have htrace : WordTrace (prefixWord ++ tailWord_2170364) baseStart_2170364 baseEnd_2170364 := by
    simpa [prefixWord, tailWord_2170364, baseEnd_2170364] using wordTrace_append hprefix tailTrace_2170364
  have hstable : (prefixWord ++ tailWord_2170364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170364).length < 2 ^ (prefixWord ++ tailWord_2170364).sum := by decide
  have hdescent : baseEnd_2170364 < baseStart_2170364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170377 : List Nat := [1, 2, 1, 1, 3, 1, 3, 3, 7]
def baseStart_2170377 : Nat := 118140960795 + 2170377 * 2 ^ 59
def prefixEnd_2170377 : Nat := 4983230072969 + 3 ^ 40 * 2170377 * 2
def baseEnd_2170377 : Nat := 247654800547413360823583

theorem tailTrace_2170377 : CollatzResearch.WordTrace tailWord_2170377 prefixEnd_2170377 247654800547413360823583 := by
  unfold tailWord_2170377
  simp only [CollatzResearch.WordTrace]
  refine ⟨79160152458102274726093385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52773434972068183150728923 79160152458102274726093385)
  ·
    refine ⟨59370114343576706044570039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79160152458102274726093385 59370114343576706044570039)
    ·
      refine ⟨89055171515365059066855059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59370114343576706044570039 89055171515365059066855059)
      ·
        refine ⟨133582757273047588600282589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89055171515365059066855059 133582757273047588600282589)
        ·
          refine ⟨50093533977392845725105971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133582757273047588600282589 50093533977392845725105971)
          ·
            refine ⟨75140300966089268587658957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50093533977392845725105971 75140300966089268587658957)
            ·
              refine ⟨28177612862283475720372109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75140300966089268587658957 28177612862283475720372109)
              ·
                refine ⟨10566604823356303395139541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28177612862283475720372109 10566604823356303395139541)
                ·
                  refine ⟨247654800547413360823583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10566604823356303395139541 247654800547413360823583)
                  ·
                    rfl

theorem cell22_2170377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 7].length) (baseStart_2170377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170377 prefixEnd_2170377 := by exact prefixLift 2170377
  have htrace : WordTrace (prefixWord ++ tailWord_2170377) baseStart_2170377 baseEnd_2170377 := by
    simpa [prefixWord, tailWord_2170377, baseEnd_2170377] using wordTrace_append hprefix tailTrace_2170377
  have hstable : (prefixWord ++ tailWord_2170377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170377).length < 2 ^ (prefixWord ++ tailWord_2170377).sum := by decide
  have hdescent : baseEnd_2170377 < baseStart_2170377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170544 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 4, 5]
def baseStart_2170544 : Nat := 118140960795 + 2170544 * 2 ^ 59
def prefixEnd_2170544 : Nat := 4983230072969 + 3 ^ 40 * 2170544 * 2
def baseEnd_2170544 : Nat := 743021569155107313545237

theorem tailTrace_2170544 : CollatzResearch.WordTrace tailWord_2170544 prefixEnd_2170544 743021569155107313545237 := by
  unfold tailWord_2170544
  simp only [CollatzResearch.WordTrace]
  refine ⟨39583121724248631123711343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52777495632331508164948457 39583121724248631123711343)
  ·
    refine ⟨59374682586372946685567015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39583121724248631123711343 59374682586372946685567015)
    ·
      refine ⟨89062023879559420028350523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59374682586372946685567015 89062023879559420028350523)
      ·
        refine ⟨133593035819339130042525785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89062023879559420028350523 133593035819339130042525785)
        ·
          refine ⟨100194776864504347531894339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133593035819339130042525785 100194776864504347531894339)
          ·
            refine ⟨150292165296756521297841509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100194776864504347531894339 150292165296756521297841509)
            ·
              refine ⟨28179780993141847743345283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 150292165296756521297841509 28179780993141847743345283)
              ·
                refine ⟨42269671489712771615017925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28179780993141847743345283 42269671489712771615017925)
                ·
                  refine ⟨7925563404321144677815861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42269671489712771615017925 7925563404321144677815861)
                  ·
                    refine ⟨743021569155107313545237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7925563404321144677815861 743021569155107313545237)
                    ·
                      rfl

theorem cell22_2170544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 4, 5].length) (baseStart_2170544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170544 prefixEnd_2170544 := by exact prefixLift 2170544
  have htrace : WordTrace (prefixWord ++ tailWord_2170544) baseStart_2170544 baseEnd_2170544 := by
    simpa [prefixWord, tailWord_2170544, baseEnd_2170544] using wordTrace_append hprefix tailTrace_2170544
  have hstable : (prefixWord ++ tailWord_2170544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170544).length < 2 ^ (prefixWord ++ tailWord_2170544).sum := by decide
  have hdescent : baseEnd_2170544 < baseStart_2170544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170576 : List Nat := [2, 1, 1, 1, 1, 2, 1, 8, 1, 4]
def baseStart_2170576 : Nat := 118140960795 + 2170576 * 2 ^ 59
def prefixEnd_2170576 : Nat := 4983230072969 + 3 ^ 40 * 2170576 * 2
def baseEnd_2170576 : Nat := 743032523409069896745139

theorem tailTrace_2170576 : CollatzResearch.WordTrace tailWord_2170576 prefixEnd_2170576 743032523409069896745139 := by
  unfold tailWord_2170576
  simp only [CollatzResearch.WordTrace]
  refine ⟨39583705292190665856293791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52778273722920887808391721 39583705292190665856293791)
  ·
    refine ⟨59375557938285998784440687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39583705292190665856293791 59375557938285998784440687)
    ·
      refine ⟨89063336907428998176661031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59375557938285998784440687 89063336907428998176661031)
      ·
        refine ⟨133595005361143497264991547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89063336907428998176661031 133595005361143497264991547)
        ·
          refine ⟨200392508041715245897487321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133595005361143497264991547 200392508041715245897487321)
          ·
            refine ⟨150294381031286434423115491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200392508041715245897487321 150294381031286434423115491)
            ·
              refine ⟨225441571546929651634673237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150294381031286434423115491 225441571546929651634673237)
              ·
                refine ⟨2641893416565581855093827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 225441571546929651634673237 2641893416565581855093827)
                ·
                  refine ⟨3962840124848372782640741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2641893416565581855093827 3962840124848372782640741)
                  ·
                    refine ⟨743032523409069896745139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3962840124848372782640741 743032523409069896745139)
                    ·
                      rfl

theorem cell22_2170576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 1, 4].length) (baseStart_2170576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170576 prefixEnd_2170576 := by exact prefixLift 2170576
  have htrace : WordTrace (prefixWord ++ tailWord_2170576) baseStart_2170576 baseEnd_2170576 := by
    simpa [prefixWord, tailWord_2170576, baseEnd_2170576] using wordTrace_append hprefix tailTrace_2170576
  have hstable : (prefixWord ++ tailWord_2170576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170576).length < 2 ^ (prefixWord ++ tailWord_2170576).sum := by decide
  have hdescent : baseEnd_2170576 < baseStart_2170576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170606 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 3, 5]
def baseStart_2170606 : Nat := 118140960795 + 2170606 * 2 ^ 59
def prefixEnd_2170606 : Nat := 4983230072969 + 3 ^ 40 * 2170606 * 2
def baseEnd_2170606 : Nat := 743042793022159818495047

theorem tailTrace_2170606 : CollatzResearch.WordTrace tailWord_2170606 prefixEnd_2170606 743042793022159818495047 := by
  unfold tailWord_2170606
  simp only [CollatzResearch.WordTrace]
  refine ⟨9896063096784080854522459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52779003182848431224119781 9896063096784080854522459)
  ·
    refine ⟨14844094645176121281783689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9896063096784080854522459 14844094645176121281783689)
    ·
      refine ⟨11133070983882090961337767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14844094645176121281783689 11133070983882090961337767)
      ·
        refine ⟨16699606475823136442006651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11133070983882090961337767 16699606475823136442006651)
        ·
          refine ⟨25049409713734704663009977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16699606475823136442006651 25049409713734704663009977)
          ·
            refine ⟨18787057285301028497257483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25049409713734704663009977 18787057285301028497257483)
            ·
              refine ⟨28180585927951542745886225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18787057285301028497257483 28180585927951542745886225)
              ·
                refine ⟨21135439445963657059414669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28180585927951542745886225 21135439445963657059414669)
                ·
                  refine ⟨7925789792236371397280501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21135439445963657059414669 7925789792236371397280501)
                  ·
                    refine ⟨743042793022159818495047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7925789792236371397280501 743042793022159818495047)
                    ·
                      rfl

theorem cell22_2170606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_2170606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170606 prefixEnd_2170606 := by exact prefixLift 2170606
  have htrace : WordTrace (prefixWord ++ tailWord_2170606) baseStart_2170606 baseEnd_2170606 := by
    simpa [prefixWord, tailWord_2170606, baseEnd_2170606] using wordTrace_append hprefix tailTrace_2170606
  have hstable : (prefixWord ++ tailWord_2170606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170606).length < 2 ^ (prefixWord ++ tailWord_2170606).sum := by decide
  have hdescent : baseEnd_2170606 < baseStart_2170606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170619 : List Nat := [1, 1, 1, 1, 1, 3, 1, 13]
def baseStart_2170619 : Nat := 118140960795 + 2170619 * 2 ^ 59
def prefixEnd_2170619 : Nat := 4983230072969 + 3 ^ 40 * 2170619 * 2
def baseEnd_2170619 : Nat := 82560804798648013102223

theorem tailTrace_2170619 : CollatzResearch.WordTrace tailWord_2170619 prefixEnd_2170619 82560804798648013102223 := by
  unfold tailWord_2170619
  simp only [CollatzResearch.WordTrace]
  refine ⟨79168978923225550056402911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52779319282150366704268607 79168978923225550056402911)
  ·
    refine ⟨118753468384838325084604367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79168978923225550056402911 118753468384838325084604367)
    ·
      refine ⟨178130202577257487626906551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118753468384838325084604367 178130202577257487626906551)
      ·
        refine ⟨267195303865886231440359827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178130202577257487626906551 267195303865886231440359827)
        ·
          refine ⟨400792955798829347160539741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267195303865886231440359827 400792955798829347160539741)
          ·
            refine ⟨150297358424561005185202403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 400792955798829347160539741 150297358424561005185202403)
            ·
              refine ⟨225446037636841507777803605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150297358424561005185202403 225446037636841507777803605)
              ·
                refine ⟨82560804798648013102223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 225446037636841507777803605 82560804798648013102223)
                ·
                  rfl

theorem cell22_2170619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 13].length) (baseStart_2170619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170619 prefixEnd_2170619 := by exact prefixLift 2170619
  have htrace : WordTrace (prefixWord ++ tailWord_2170619) baseStart_2170619 baseEnd_2170619 := by
    simpa [prefixWord, tailWord_2170619, baseEnd_2170619] using wordTrace_append hprefix tailTrace_2170619
  have hstable : (prefixWord ++ tailWord_2170619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170619).length < 2 ^ (prefixWord ++ tailWord_2170619).sum := by decide
  have hdescent : baseEnd_2170619 < baseStart_2170619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170623 : List Nat := [1, 1, 2, 2, 1, 3, 4, 3, 2, 3]
def baseStart_2170623 : Nat := 118140960795 + 2170623 * 2 ^ 59
def prefixEnd_2170623 : Nat := 4983230072969 + 3 ^ 40 * 2170623 * 2
def baseEnd_2170623 : Nat := 743048612469577440819995

theorem tailTrace_2170623 : CollatzResearch.WordTrace tailWord_2170623 prefixEnd_2170623 743048612469577440819995 := by
  unfold tailWord_2170623
  simp only [CollatzResearch.WordTrace]
  refine ⟨79169124815211058739548523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52779416543474039159699015 79169124815211058739548523)
  ·
    refine ⟨118753687222816588109322785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79169124815211058739548523 118753687222816588109322785)
    ·
      refine ⟨89065265417112441081992089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118753687222816588109322785 89065265417112441081992089)
      ·
        refine ⟨66798949062834330811494067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89065265417112441081992089 66798949062834330811494067)
        ·
          refine ⟨100198423594251496217241101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66798949062834330811494067 100198423594251496217241101)
          ·
            refine ⟨37574408847844311081465413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100198423594251496217241101 37574408847844311081465413)
            ·
              refine ⟨7045201658970808327774765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37574408847844311081465413 7045201658970808327774765)
              ·
                refine ⟨2641950622114053122915537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7045201658970808327774765 2641950622114053122915537)
                ·
                  refine ⟨1981462966585539842186653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2641950622114053122915537 1981462966585539842186653)
                  ·
                    refine ⟨743048612469577440819995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1981462966585539842186653 743048612469577440819995)
                    ·
                      rfl

theorem cell22_2170623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 3, 2, 3].length) (baseStart_2170623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170623 prefixEnd_2170623 := by exact prefixLift 2170623
  have htrace : WordTrace (prefixWord ++ tailWord_2170623) baseStart_2170623 baseEnd_2170623 := by
    simpa [prefixWord, tailWord_2170623, baseEnd_2170623] using wordTrace_append hprefix tailTrace_2170623
  have hstable : (prefixWord ++ tailWord_2170623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170623).length < 2 ^ (prefixWord ++ tailWord_2170623).sum := by decide
  have hdescent : baseEnd_2170623 < baseStart_2170623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170638 : List Nat := [4, 1, 1, 2, 1, 1, 5, 1, 2, 4]
def baseStart_2170638 : Nat := 118140960795 + 2170638 * 2 ^ 59
def prefixEnd_2170638 : Nat := 4983230072969 + 3 ^ 40 * 2170638 * 2
def baseEnd_2170638 : Nat := 743053747276122401694949

theorem tailTrace_2170638 : CollatzResearch.WordTrace tailWord_2170638 prefixEnd_2170638 743053747276122401694949 := by
  unfold tailWord_2170638
  simp only [CollatzResearch.WordTrace]
  refine ⟨9896208988769589537668071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52779781273437810867563045 9896208988769589537668071)
  ·
    refine ⟨14844313483154384306502107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9896208988769589537668071 14844313483154384306502107)
    ·
      refine ⟨22266470224731576459753161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14844313483154384306502107 22266470224731576459753161)
      ·
        refine ⟨16699852668548682344814871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22266470224731576459753161 16699852668548682344814871)
        ·
          refine ⟨25049779002823023517222307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16699852668548682344814871 25049779002823023517222307)
          ·
            refine ⟨37574668504234535275833461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25049779002823023517222307 37574668504234535275833461)
            ·
              refine ⟨3522625172271987682109387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37574668504234535275833461 3522625172271987682109387)
              ·
                refine ⟨5283937758407981523164081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3522625172271987682109387 5283937758407981523164081)
                ·
                  refine ⟨3962953318805986142373061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5283937758407981523164081 3962953318805986142373061)
                  ·
                    refine ⟨743053747276122401694949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3962953318805986142373061 743053747276122401694949)
                    ·
                      rfl

theorem cell22_2170638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_2170638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170638 prefixEnd_2170638 := by exact prefixLift 2170638
  have htrace : WordTrace (prefixWord ++ tailWord_2170638) baseStart_2170638 baseEnd_2170638 := by
    simpa [prefixWord, tailWord_2170638, baseEnd_2170638] using wordTrace_append hprefix tailTrace_2170638
  have hstable : (prefixWord ++ tailWord_2170638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170638).length < 2 ^ (prefixWord ++ tailWord_2170638).sum := by decide
  have hdescent : baseEnd_2170638 < baseStart_2170638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170642 : List Nat := [3, 2, 4, 1, 1, 2, 2, 3, 4]
def baseStart_2170642 : Nat := 118140960795 + 2170642 * 2 ^ 59
def prefixEnd_2170642 : Nat := 4983230072969 + 3 ^ 40 * 2170642 * 2
def baseEnd_2170642 : Nat := 247685038852622574864979

theorem tailTrace_2170642 : CollatzResearch.WordTrace tailWord_2170642 prefixEnd_2170642 247685038852622574864979 := by
  unfold tailWord_2170642
  simp only [CollatzResearch.WordTrace]
  refine ⟨19792454450535556246122545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52779878534761483322993453 19792454450535556246122545)
  ·
    refine ⟨14844340837901667184591909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19792454450535556246122545 14844340837901667184591909)
    ·
      refine ⟨2783313907106562597110983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14844340837901667184591909 2783313907106562597110983)
      ·
        refine ⟨4174970860659843895666475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2783313907106562597110983 4174970860659843895666475)
        ·
          refine ⟨6262456290989765843499713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4174970860659843895666475 6262456290989765843499713)
          ·
            refine ⟨4696842218242324382624785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6262456290989765843499713 4696842218242324382624785)
            ·
              refine ⟨3522631663681743286968589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4696842218242324382624785 3522631663681743286968589)
              ·
                refine ⟨1320986873880653732613221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3522631663681743286968589 1320986873880653732613221)
                ·
                  refine ⟨247685038852622574864979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1320986873880653732613221 247685038852622574864979)
                  ·
                    rfl

theorem cell22_2170642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_2170642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170642 prefixEnd_2170642 := by exact prefixLift 2170642
  have htrace : WordTrace (prefixWord ++ tailWord_2170642) baseStart_2170642 baseEnd_2170642 := by
    simpa [prefixWord, tailWord_2170642, baseEnd_2170642] using wordTrace_append hprefix tailTrace_2170642
  have hstable : (prefixWord ++ tailWord_2170642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170642).length < 2 ^ (prefixWord ++ tailWord_2170642).sum := by decide
  have hdescent : baseEnd_2170642 < baseStart_2170642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170644 : List Nat := [2, 4, 4, 1, 1, 1, 1, 3, 1, 4]
def baseStart_2170644 : Nat := 118140960795 + 2170644 * 2 ^ 59
def prefixEnd_2170644 : Nat := 4983230072969 + 3 ^ 40 * 2170644 * 2
def baseEnd_2170644 : Nat := 743055801198740386044931

theorem tailTrace_2170644 : CollatzResearch.WordTrace tailWord_2170644 prefixEnd_2170644 743055801198740386044931 := by
  unfold tailWord_2170644
  simp only [CollatzResearch.WordTrace]
  refine ⟨39584945374067489663031493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52779927165423319550708657 39584945374067489663031493)
  ·
    refine ⟨7422177257637654311818405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39584945374067489663031493 7422177257637654311818405)
    ·
      refine ⟨1391658235807060183465951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7422177257637654311818405 1391658235807060183465951)
      ·
        refine ⟨2087487353710590275198927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1391658235807060183465951 2087487353710590275198927)
        ·
          refine ⟨3131231030565885412798391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2087487353710590275198927 3131231030565885412798391)
          ·
            refine ⟨4696846545848828119197587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3131231030565885412798391 4696846545848828119197587)
            ·
              refine ⟨7045269818773242178796381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4696846545848828119197587 7045269818773242178796381)
              ·
                refine ⟨2641976182039965817048643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7045269818773242178796381 2641976182039965817048643)
                ·
                  refine ⟨3962964273059948725572965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2641976182039965817048643 3962964273059948725572965)
                  ·
                    refine ⟨743055801198740386044931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3962964273059948725572965 743055801198740386044931)
                    ·
                      rfl

theorem cell22_2170644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_2170644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170644 prefixEnd_2170644 := by exact prefixLift 2170644
  have htrace : WordTrace (prefixWord ++ tailWord_2170644) baseStart_2170644 baseEnd_2170644 := by
    simpa [prefixWord, tailWord_2170644, baseEnd_2170644] using wordTrace_append hprefix tailTrace_2170644
  have hstable : (prefixWord ++ tailWord_2170644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170644).length < 2 ^ (prefixWord ++ tailWord_2170644).sum := by decide
  have hdescent : baseEnd_2170644 < baseStart_2170644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170668 : List Nat := [2, 2, 1, 1, 1, 5, 1, 3, 3, 3]
def baseStart_2170668 : Nat := 118140960795 + 2170668 * 2 ^ 59
def prefixEnd_2170668 : Nat := 4983230072969 + 3 ^ 40 * 2170668 * 2
def baseEnd_2170668 : Nat := 743064016889212323444857

theorem tailTrace_2170668 : CollatzResearch.WordTrace tailWord_2170668 prefixEnd_2170668 743064016889212323444857 := by
  unfold tailWord_2170668
  simp only [CollatzResearch.WordTrace]
  refine ⟨39585383050024015712468329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52780510733365354283291105 39585383050024015712468329)
  ·
    refine ⟨29689037287518011784351247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39585383050024015712468329 29689037287518011784351247)
    ·
      refine ⟨44533555931277017676526871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29689037287518011784351247 44533555931277017676526871)
      ·
        refine ⟨66800333896915526514790307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44533555931277017676526871 66800333896915526514790307)
        ·
          refine ⟨100200500845373289772185461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66800333896915526514790307 100200500845373289772185461)
          ·
            refine ⟨9393796954253745916142387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100200500845373289772185461 9393796954253745916142387)
            ·
              refine ⟨14090695431380618874213581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9393796954253745916142387 14090695431380618874213581)
              ·
                refine ⟨5284010786767732077830093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14090695431380618874213581 5284010786767732077830093)
                ·
                  refine ⟨1981504045037899529186285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5284010786767732077830093 1981504045037899529186285)
                  ·
                    refine ⟨743064016889212323444857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1981504045037899529186285 743064016889212323444857)
                    ·
                      rfl

theorem cell22_2170668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 3].length) (baseStart_2170668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170668 prefixEnd_2170668 := by exact prefixLift 2170668
  have htrace : WordTrace (prefixWord ++ tailWord_2170668) baseStart_2170668 baseEnd_2170668 := by
    simpa [prefixWord, tailWord_2170668, baseEnd_2170668] using wordTrace_append hprefix tailTrace_2170668
  have hstable : (prefixWord ++ tailWord_2170668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170668).length < 2 ^ (prefixWord ++ tailWord_2170668).sum := by decide
  have hdescent : baseEnd_2170668 < baseStart_2170668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170685 : List Nat := [1, 4, 1, 4, 1, 1, 2, 2, 3, 3]
def baseStart_2170685 : Nat := 118140960795 + 2170685 * 2 ^ 59
def prefixEnd_2170685 : Nat := 4983230072969 + 3 ^ 40 * 2170685 * 2
def baseEnd_2170685 : Nat := 743069836336629945769805

theorem tailTrace_2170685 : CollatzResearch.WordTrace tailWord_2170685 prefixEnd_2170685 743069836336629945769805 := by
  unfold tailWord_2170685
  simp only [CollatzResearch.WordTrace]
  refine ⟨79171386140986443328305509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52780924093990962218870339 79171386140986443328305509)
  ·
    refine ⟨14844634901434958124057283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79171386140986443328305509 14844634901434958124057283)
    ·
      refine ⟨22266952352152437186085925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14844634901434958124057283 22266952352152437186085925)
      ·
        refine ⟨4175053566028581972391111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22266952352152437186085925 4175053566028581972391111)
        ·
          refine ⟨6262580349042872958586667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4175053566028581972391111 6262580349042872958586667)
          ·
            refine ⟨9393870523564309437880001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6262580349042872958586667 9393870523564309437880001)
            ·
              refine ⟨7045402892673232078410001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9393870523564309437880001 7045402892673232078410001)
              ·
                refine ⟨5284052169504924058807501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7045402892673232078410001 5284052169504924058807501)
                ·
                  refine ⟨1981519563564346522052813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5284052169504924058807501 1981519563564346522052813)
                  ·
                    refine ⟨743069836336629945769805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1981519563564346522052813 743069836336629945769805)
                    ·
                      rfl

theorem cell22_2170685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_2170685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170685 prefixEnd_2170685 := by exact prefixLift 2170685
  have htrace : WordTrace (prefixWord ++ tailWord_2170685) baseStart_2170685 baseEnd_2170685 := by
    simpa [prefixWord, tailWord_2170685, baseEnd_2170685] using wordTrace_append hprefix tailTrace_2170685
  have hstable : (prefixWord ++ tailWord_2170685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170685).length < 2 ^ (prefixWord ++ tailWord_2170685).sum := by decide
  have hdescent : baseEnd_2170685 < baseStart_2170685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170728 : List Nat := [2, 1, 4, 2, 1, 1, 2, 2, 3, 4]
def baseStart_2170728 : Nat := 118140960795 + 2170728 * 2 ^ 59
def prefixEnd_2170728 : Nat := 4983230072969 + 3 ^ 40 * 2170728 * 2
def baseEnd_2170728 : Nat := 743084556115392166944673

theorem tailTrace_2170728 : CollatzResearch.WordTrace tailWord_2170728 prefixEnd_2170728 743084556115392166944673 := by
  unfold tailWord_2170728
  simp only [CollatzResearch.WordTrace]
  refine ⟨39586477239915330836060419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52781969653220441114747225 39586477239915330836060419)
  ·
    refine ⟨59379715859872996254090629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39586477239915330836060419 59379715859872996254090629)
    ·
      refine ⟨11133696723726186797641993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59379715859872996254090629 11133696723726186797641993)
      ·
        refine ⟨8350272542794640098231495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11133696723726186797641993 8350272542794640098231495)
        ·
          refine ⟨12525408814191960147347243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8350272542794640098231495 12525408814191960147347243)
          ·
            refine ⟨18788113221287940221020865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12525408814191960147347243 18788113221287940221020865)
            ·
              refine ⟨14091084915965955165765649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18788113221287940221020865 14091084915965955165765649)
              ·
                refine ⟨10568313686974466374324237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14091084915965955165765649 10568313686974466374324237)
                ·
                  refine ⟨3963117632615424890371589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10568313686974466374324237 3963117632615424890371589)
                  ·
                    refine ⟨743084556115392166944673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3963117632615424890371589 743084556115392166944673)
                    ·
                      rfl

theorem cell22_2170728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_2170728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170728 prefixEnd_2170728 := by exact prefixLift 2170728
  have htrace : WordTrace (prefixWord ++ tailWord_2170728) baseStart_2170728 baseEnd_2170728 := by
    simpa [prefixWord, tailWord_2170728, baseEnd_2170728] using wordTrace_append hprefix tailTrace_2170728
  have hstable : (prefixWord ++ tailWord_2170728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170728).length < 2 ^ (prefixWord ++ tailWord_2170728).sum := by decide
  have hdescent : baseEnd_2170728 < baseStart_2170728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170773 : List Nat := [1, 3, 2, 1, 1, 3, 1, 4, 2, 4]
def baseStart_2170773 : Nat := 118140960795 + 2170773 * 2 ^ 59
def prefixEnd_2170773 : Nat := 4983230072969 + 3 ^ 40 * 2170773 * 2
def baseEnd_2170773 : Nat := 743099960535027049569535

theorem tailTrace_2170773 : CollatzResearch.WordTrace tailWord_2170773 prefixEnd_2170773 743099960535027049569535 := by
  unfold tailWord_2170773
  simp only [CollatzResearch.WordTrace]
  refine ⟨79174595764667634357508973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52783063843111756238339315 79174595764667634357508973)
  ·
    refine ⟨29690473411750362884065865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79174595764667634357508973 29690473411750362884065865)
    ·
      refine ⟨22267855058812772163049399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29690473411750362884065865 22267855058812772163049399)
      ·
        refine ⟨33401782588219158244574099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22267855058812772163049399 33401782588219158244574099)
        ·
          refine ⟨50102673882328737366861149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33401782588219158244574099 50102673882328737366861149)
          ·
            refine ⟨18788502705873276512572931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50102673882328737366861149 18788502705873276512572931)
            ·
              refine ⟨28182754058809914768859397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18788502705873276512572931 28182754058809914768859397)
              ·
                refine ⟨5284266386026859019161137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28182754058809914768859397 5284266386026859019161137)
                ·
                  refine ⟨3963199789520144264370853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5284266386026859019161137 3963199789520144264370853)
                  ·
                    refine ⟨743099960535027049569535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3963199789520144264370853 743099960535027049569535)
                    ·
                      rfl

theorem cell22_2170773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_2170773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170773 prefixEnd_2170773 := by exact prefixLift 2170773
  have htrace : WordTrace (prefixWord ++ tailWord_2170773) baseStart_2170773 baseEnd_2170773 := by
    simpa [prefixWord, tailWord_2170773, baseEnd_2170773] using wordTrace_append hprefix tailTrace_2170773
  have hstable : (prefixWord ++ tailWord_2170773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170773).length < 2 ^ (prefixWord ++ tailWord_2170773).sum := by decide
  have hdescent : baseEnd_2170773 < baseStart_2170773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170775 : List Nat := [1, 1, 3, 3, 1, 3, 1, 4, 2, 3]
def baseStart_2170775 : Nat := 118140960795 + 2170775 * 2 ^ 59
def prefixEnd_2170775 : Nat := 4983230072969 + 3 ^ 40 * 2170775 * 2
def baseEnd_2170775 : Nat := 743100645175899711019529

theorem tailTrace_2170775 : CollatzResearch.WordTrace tailWord_2170775 prefixEnd_2170775 743100645175899711019529 := by
  unfold tailWord_2170775
  simp only [CollatzResearch.WordTrace]
  refine ⟨79174668710660388699081779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52783112473773592466054519 79174668710660388699081779)
  ·
    refine ⟨118762003065990583048622669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79174668710660388699081779 118762003065990583048622669)
    ·
      refine ⟨44535751149746468643233501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118762003065990583048622669 44535751149746468643233501)
      ·
        refine ⟨16700906681154925741212563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44535751149746468643233501 16700906681154925741212563)
        ·
          refine ⟨25051360021732388611818845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16700906681154925741212563 25051360021732388611818845)
          ·
            refine ⟨9394260008149645729432067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25051360021732388611818845 9394260008149645729432067)
            ·
              refine ⟨14091390012224468594148101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9394260008149645729432067 14091390012224468594148101)
              ·
                refine ⟨2642135627292087861402769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14091390012224468594148101 2642135627292087861402769)
                ·
                  refine ⟨1981601720469065896052077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2642135627292087861402769 1981601720469065896052077)
                  ·
                    refine ⟨743100645175899711019529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1981601720469065896052077 743100645175899711019529)
                    ·
                      rfl

theorem cell22_2170775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2, 3].length) (baseStart_2170775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170775 prefixEnd_2170775 := by exact prefixLift 2170775
  have htrace : WordTrace (prefixWord ++ tailWord_2170775) baseStart_2170775 baseEnd_2170775 := by
    simpa [prefixWord, tailWord_2170775, baseEnd_2170775] using wordTrace_append hprefix tailTrace_2170775
  have hstable : (prefixWord ++ tailWord_2170775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170775).length < 2 ^ (prefixWord ++ tailWord_2170775).sum := by decide
  have hdescent : baseEnd_2170775 < baseStart_2170775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170788 : List Nat := [2, 3, 1, 2, 1, 3, 3, 7]
def baseStart_2170788 : Nat := 118140960795 + 2170788 * 2 ^ 59
def prefixEnd_2170788 : Nat := 4983230072969 + 3 ^ 40 * 2170788 * 2
def baseEnd_2170788 : Nat := 82567232815730223382721

theorem tailTrace_2170788 : CollatzResearch.WordTrace tailWord_2170788 prefixEnd_2170788 82567232815730223382721 := by
  unfold tailWord_2170788
  simp only [CollatzResearch.WordTrace]
  refine ⟨39587571429806645959652509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52783428573075527946203345 39587571429806645959652509)
  ·
    refine ⟨14845339286177492234869691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39587571429806645959652509 14845339286177492234869691)
    ·
      refine ⟨22268008929266238352304537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14845339286177492234869691 22268008929266238352304537)
      ·
        refine ⟨16701006696949678764228403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22268008929266238352304537 16701006696949678764228403)
        ·
          refine ⟨25051510045424518146342605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16701006696949678764228403 25051510045424518146342605)
          ·
            refine ⟨9394316267034194304878477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25051510045424518146342605 9394316267034194304878477)
            ·
              refine ⟨3522868600137822864329429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9394316267034194304878477 3522868600137822864329429)
              ·
                refine ⟨82567232815730223382721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3522868600137822864329429 82567232815730223382721)
                ·
                  rfl

theorem cell22_2170788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 7].length) (baseStart_2170788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170788 prefixEnd_2170788 := by exact prefixLift 2170788
  have htrace : WordTrace (prefixWord ++ tailWord_2170788) baseStart_2170788 baseEnd_2170788 := by
    simpa [prefixWord, tailWord_2170788, baseEnd_2170788] using wordTrace_append hprefix tailTrace_2170788
  have hstable : (prefixWord ++ tailWord_2170788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170788).length < 2 ^ (prefixWord ++ tailWord_2170788).sum := by decide
  have hdescent : baseEnd_2170788 < baseStart_2170788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170805 : List Nat := [1, 3, 3, 2, 1, 3, 3, 6]
def baseStart_2170805 : Nat := 118140960795 + 2170805 * 2 ^ 59
def prefixEnd_2170805 : Nat := 4983230072969 + 3 ^ 40 * 2170805 * 2
def baseEnd_2170805 : Nat := 82567879420998848085493

theorem tailTrace_2170805 : CollatzResearch.WordTrace tailWord_2170805 prefixEnd_2170805 82567879420998848085493 := by
  unfold tailWord_2170805
  simp only [CollatzResearch.WordTrace]
  refine ⟨79175762900551703822673869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52783841933701135881782579 79175762900551703822673869)
  ·
    refine ⟨29690911087706888933502701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79175762900551703822673869 29690911087706888933502701)
    ·
      refine ⟨11134091657890083350063513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29690911087706888933502701 11134091657890083350063513)
      ·
        refine ⟨8350568743417562512547635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11134091657890083350063513 8350568743417562512547635)
        ·
          refine ⟨12525853115126343768821453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8350568743417562512547635 12525853115126343768821453)
          ·
            refine ⟨4697194918172378913308045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12525853115126343768821453 4697194918172378913308045)
            ·
              refine ⟨1761448094314642092490517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4697194918172378913308045 1761448094314642092490517)
              ·
                refine ⟨82567879420998848085493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1761448094314642092490517 82567879420998848085493)
                ·
                  rfl

theorem cell22_2170805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 6].length) (baseStart_2170805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170805 prefixEnd_2170805 := by exact prefixLift 2170805
  have htrace : WordTrace (prefixWord ++ tailWord_2170805) baseStart_2170805 baseEnd_2170805 := by
    simpa [prefixWord, tailWord_2170805, baseEnd_2170805] using wordTrace_append hprefix tailTrace_2170805
  have hstable : (prefixWord ++ tailWord_2170805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170805).length < 2 ^ (prefixWord ++ tailWord_2170805).sum := by decide
  have hdescent : baseEnd_2170805 < baseStart_2170805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170833 : List Nat := [1, 2, 2, 1, 2, 1, 2, 6, 5]
def baseStart_2170833 : Nat := 118140960795 + 2170833 * 2 ^ 59
def prefixEnd_2170833 : Nat := 4983230072969 + 3 ^ 40 * 2170833 * 2
def baseEnd_2170833 : Nat := 247706833253735631023117

theorem tailTrace_2170833 : CollatzResearch.WordTrace tailWord_2170833 prefixEnd_2170833 247706833253735631023117 := by
  unfold tailWord_2170833
  simp only [CollatzResearch.WordTrace]
  refine ⟨79176784144450264604693153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52784522762966843069795435 79176784144450264604693153)
  ·
    refine ⟨59382588108337698453519865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79176784144450264604693153 59382588108337698453519865)
    ·
      refine ⟨44536941081253273840139899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59382588108337698453519865 44536941081253273840139899)
      ·
        refine ⟨66805411621879910760209849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44536941081253273840139899 66805411621879910760209849)
        ·
          refine ⟨50104058716409933070157387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66805411621879910760209849 50104058716409933070157387)
          ·
            refine ⟨75156088074614899605236081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50104058716409933070157387 75156088074614899605236081)
            ·
              refine ⟨56367066055961174703927061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75156088074614899605236081 56367066055961174703927061)
              ·
                refine ⟨2642206221373180064246581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56367066055961174703927061 2642206221373180064246581)
                ·
                  refine ⟨247706833253735631023117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2642206221373180064246581 247706833253735631023117)
                  ·
                    rfl

theorem cell22_2170833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 5].length) (baseStart_2170833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170833 prefixEnd_2170833 := by exact prefixLift 2170833
  have htrace : WordTrace (prefixWord ++ tailWord_2170833) baseStart_2170833 baseEnd_2170833 := by
    simpa [prefixWord, tailWord_2170833, baseEnd_2170833] using wordTrace_append hprefix tailTrace_2170833
  have hstable : (prefixWord ++ tailWord_2170833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170833).length < 2 ^ (prefixWord ++ tailWord_2170833).sum := by decide
  have hdescent : baseEnd_2170833 < baseStart_2170833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170837 : List Nat := [1, 3, 2, 3, 2, 2, 2, 1, 3, 3]
def baseStart_2170837 : Nat := 118140960795 + 2170837 * 2 ^ 59
def prefixEnd_2170837 : Nat := 4983230072969 + 3 ^ 40 * 2170837 * 2
def baseEnd_2170837 : Nat := 743121869042952215969339

theorem tailTrace_2170837 : CollatzResearch.WordTrace tailWord_2170837 prefixEnd_2170837 743121869042952215969339 := by
  unfold tailWord_2170837
  simp only [CollatzResearch.WordTrace]
  refine ⟨79176930036435773287838765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52784620024290515525225843 79176930036435773287838765)
  ·
    refine ⟨29691348763663414982939537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79176930036435773287838765 29691348763663414982939537)
    ·
      refine ⟨22268511572747561237204653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29691348763663414982939537 22268511572747561237204653)
      ·
        refine ⟨8350691839780335463951745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22268511572747561237204653 8350691839780335463951745)
        ·
          refine ⟨6263018879835251597963809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8350691839780335463951745 6263018879835251597963809)
          ·
            refine ⟨4697264159876438698472857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6263018879835251597963809 4697264159876438698472857)
            ·
              refine ⟨3522948119907329023854643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4697264159876438698472857 3522948119907329023854643)
              ·
                refine ⟨5284422179860993535781965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3522948119907329023854643 5284422179860993535781965)
                ·
                  refine ⟨1981658317447872575918237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5284422179860993535781965 1981658317447872575918237)
                  ·
                    refine ⟨743121869042952215969339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1981658317447872575918237 743121869042952215969339)
                    ·
                      rfl

theorem cell22_2170837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_2170837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170837 prefixEnd_2170837 := by exact prefixLift 2170837
  have htrace : WordTrace (prefixWord ++ tailWord_2170837) baseStart_2170837 baseEnd_2170837 := by
    simpa [prefixWord, tailWord_2170837, baseEnd_2170837] using wordTrace_append hprefix tailTrace_2170837
  have hstable : (prefixWord ++ tailWord_2170837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170837).length < 2 ^ (prefixWord ++ tailWord_2170837).sum := by decide
  have hdescent : baseEnd_2170837 < baseStart_2170837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170953 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 1, 8]
def baseStart_2170953 : Nat := 118140960795 + 2170953 * 2 ^ 59
def prefixEnd_2170953 : Nat := 4983230072969 + 3 ^ 40 * 2170953 * 2
def baseEnd_2170953 : Nat := 743161578213566580068983

theorem tailTrace_2170953 : CollatzResearch.WordTrace tailWord_2170953 prefixEnd_2170953 743161578213566580068983 := by
  unfold tailWord_2170953
  simp only [CollatzResearch.WordTrace]
  refine ⟨79181160904015525099061513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52787440602677016732707675 79181160904015525099061513)
  ·
    refine ⟨59385870678011643824296135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79181160904015525099061513 59385870678011643824296135)
    ·
      refine ⟨89078806017017465736444203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59385870678011643824296135 89078806017017465736444203)
      ·
        refine ⟨133618209025526198604666305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89078806017017465736444203 133618209025526198604666305)
        ·
          refine ⟨100213656769144648953499729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133618209025526198604666305 100213656769144648953499729)
          ·
            refine ⟨75160242576858486715124797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100213656769144648953499729 75160242576858486715124797)
            ·
              refine ⟨28185090966321932518171799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75160242576858486715124797 28185090966321932518171799)
              ·
                refine ⟨42277636449482898777257699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28185090966321932518171799 42277636449482898777257699)
                ·
                  refine ⟨63416454674224348165886549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42277636449482898777257699 63416454674224348165886549)
                  ·
                    refine ⟨743161578213566580068983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63416454674224348165886549 743161578213566580068983)
                    ·
                      rfl

theorem cell22_2170953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_2170953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170953 prefixEnd_2170953 := by exact prefixLift 2170953
  have htrace : WordTrace (prefixWord ++ tailWord_2170953) baseStart_2170953 baseEnd_2170953 := by
    simpa [prefixWord, tailWord_2170953, baseEnd_2170953] using wordTrace_append hprefix tailTrace_2170953
  have hstable : (prefixWord ++ tailWord_2170953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170953).length < 2 ^ (prefixWord ++ tailWord_2170953).sum := by decide
  have hdescent : baseEnd_2170953 < baseStart_2170953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2170972 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 5, 3]
def baseStart_2170972 : Nat := 118140960795 + 2170972 * 2 ^ 59
def prefixEnd_2170972 : Nat := 4983230072969 + 3 ^ 40 * 2170972 * 2
def baseEnd_2170972 : Nat := 743168082301856863843925

theorem tailTrace_2170972 : CollatzResearch.WordTrace tailWord_2170972 prefixEnd_2170972 743168082301856863843925 := by
  unfold tailWord_2170972
  simp only [CollatzResearch.WordTrace]
  refine ⟨39590926945473345672001585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52787902593964460896002113 39590926945473345672001585)
  ·
    refine ⟨29693195209105009254001189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39590926945473345672001585 29693195209105009254001189)
    ·
      refine ⟨5567474101707189235125223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29693195209105009254001189 5567474101707189235125223)
      ·
        refine ⟨8351211152560783852687835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5567474101707189235125223 8351211152560783852687835)
        ·
          refine ⟨12526816728841175779031753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8351211152560783852687835 12526816728841175779031753)
          ·
            refine ⟨9395112546630881834273815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12526816728841175779031753 9395112546630881834273815)
            ·
              refine ⟨14092668819946322751410723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9395112546630881834273815 14092668819946322751410723)
              ·
                refine ⟨21139003229919484127116085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14092668819946322751410723 21139003229919484127116085)
                ·
                  refine ⟨1981781552804951636917133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21139003229919484127116085 1981781552804951636917133)
                  ·
                    refine ⟨743168082301856863843925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1981781552804951636917133 743168082301856863843925)
                    ·
                      rfl

theorem cell22_2170972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_2170972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2170972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2170972 prefixEnd_2170972 := by exact prefixLift 2170972
  have htrace : WordTrace (prefixWord ++ tailWord_2170972) baseStart_2170972 baseEnd_2170972 := by
    simpa [prefixWord, tailWord_2170972, baseEnd_2170972] using wordTrace_append hprefix tailTrace_2170972
  have hstable : (prefixWord ++ tailWord_2170972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2170972).length < 2 ^ (prefixWord ++ tailWord_2170972).sum := by decide
  have hdescent : baseEnd_2170972 < baseStart_2170972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2170972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171015 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 5, 4]
def baseStart_2171015 : Nat := 118140960795 + 2171015 * 2 ^ 59
def prefixEnd_2171015 : Nat := 4983230072969 + 3 ^ 40 * 2171015 * 2
def baseEnd_2171015 : Nat := 743182802080619085018793

theorem tailTrace_2171015 : CollatzResearch.WordTrace tailWord_2171015 prefixEnd_2171015 743182802080619085018793 := by
  unfold tailWord_2171015
  simp only [CollatzResearch.WordTrace]
  refine ⟨79183422229790909687818499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52788948153193939791878999 79183422229790909687818499)
  ·
    refine ⟨118775133344686364531727749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79183422229790909687818499 118775133344686364531727749)
    ·
      refine ⟨22270337502128693349698953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118775133344686364531727749 22270337502128693349698953)
      ·
        refine ⟨16702753126596520012274215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22270337502128693349698953 16702753126596520012274215)
        ·
          refine ⟨25054129689894780018411323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16702753126596520012274215 25054129689894780018411323)
          ·
            refine ⟨37581194534842170027616985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25054129689894780018411323 37581194534842170027616985)
            ·
              refine ⟨28185895901131627520712739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37581194534842170027616985 28185895901131627520712739)
              ·
                refine ⟨42278843851697441281069109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28185895901131627520712739 42278843851697441281069109)
                ·
                  refine ⟨3963641611096635120100229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42278843851697441281069109 3963641611096635120100229)
                  ·
                    refine ⟨743182802080619085018793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3963641611096635120100229 743182802080619085018793)
                    ·
                      rfl

theorem cell22_2171015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_2171015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2171015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2171015 prefixEnd_2171015 := by exact prefixLift 2171015
  have htrace : WordTrace (prefixWord ++ tailWord_2171015) baseStart_2171015 baseEnd_2171015 := by
    simpa [prefixWord, tailWord_2171015, baseEnd_2171015] using wordTrace_append hprefix tailTrace_2171015
  have hstable : (prefixWord ++ tailWord_2171015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171015).length < 2 ^ (prefixWord ++ tailWord_2171015).sum := by decide
  have hdescent : baseEnd_2171015 < baseStart_2171015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171045 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 3, 5]
def baseStart_2171045 : Nat := 118140960795 + 2171045 * 2 ^ 59
def prefixEnd_2171045 : Nat := 4983230072969 + 3 ^ 40 * 2171045 * 2
def baseEnd_2171045 : Nat := 743193071693709006768701

theorem tailTrace_2171045 : CollatzResearch.WordTrace tailWord_2171045 prefixEnd_2171045 743193071693709006768701 := by
  unfold tailWord_2171045
  simp only [CollatzResearch.WordTrace]
  refine ⟨79184516419682224811410589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52789677613121483207607059 79184516419682224811410589)
  ·
    refine ⟨29694193657380834304278971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79184516419682224811410589 29694193657380834304278971)
    ·
      refine ⟨44541290486071251456418457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29694193657380834304278971 44541290486071251456418457)
      ·
        refine ⟨33405967864553438592313843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44541290486071251456418457 33405967864553438592313843)
        ·
          refine ⟨50108951796830157888470765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33405967864553438592313843 50108951796830157888470765)
          ·
            refine ⟨18790856923811309208176537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50108951796830157888470765 18790856923811309208176537)
            ·
              refine ⟨14093142692858481906132403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18790856923811309208176537 14093142692858481906132403)
              ·
                refine ⟨21139714039287722859198605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14093142692858481906132403 21139714039287722859198605)
                ·
                  refine ⟨7927392764732896072199477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21139714039287722859198605 7927392764732896072199477)
                  ·
                    refine ⟨743193071693709006768701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7927392764732896072199477 743193071693709006768701)
                    ·
                      rfl

theorem cell22_2171045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_2171045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2171045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2171045 prefixEnd_2171045 := by exact prefixLift 2171045
  have htrace : WordTrace (prefixWord ++ tailWord_2171045) baseStart_2171045 baseEnd_2171045 := by
    simpa [prefixWord, tailWord_2171045, baseEnd_2171045] using wordTrace_append hprefix tailTrace_2171045
  have hstable : (prefixWord ++ tailWord_2171045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171045).length < 2 ^ (prefixWord ++ tailWord_2171045).sum := by decide
  have hdescent : baseEnd_2171045 < baseStart_2171045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171064 : List Nat := [2, 1, 2, 1, 2, 1, 7, 2, 4]
def baseStart_2171064 : Nat := 118140960795 + 2171064 * 2 ^ 59
def prefixEnd_2171064 : Nat := 4983230072969 + 3 ^ 40 * 2171064 * 2
def baseEnd_2171064 : Nat := 247733191927333096847881

theorem tailTrace_2171064 : CollatzResearch.WordTrace tailWord_2171064 prefixEnd_2171064 247733191927333096847881 := by
  unfold tailWord_2171064
  simp only [CollatzResearch.WordTrace]
  refine ⟨39592604703306695528176123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52790139604408927370901497 39592604703306695528176123)
  ·
    refine ⟨59388907054960043292264185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39592604703306695528176123 59388907054960043292264185)
    ·
      refine ⟨44541680291220032469198139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59388907054960043292264185 44541680291220032469198139)
      ·
        refine ⟨66812520436830048703797209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44541680291220032469198139 66812520436830048703797209)
        ·
          refine ⟨50109390327622536527847907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66812520436830048703797209 50109390327622536527847907)
          ·
            refine ⟨75164085491433804791771861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50109390327622536527847907 75164085491433804791771861)
            ·
              refine ⟨1761658253705479799807153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 75164085491433804791771861 1761658253705479799807153)
              ·
                refine ⟨1321243690279109849855365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1761658253705479799807153 1321243690279109849855365)
                ·
                  refine ⟨247733191927333096847881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1321243690279109849855365 247733191927333096847881)
                  ·
                    rfl

theorem cell22_2171064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 2, 4].length) (baseStart_2171064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2171064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2171064 prefixEnd_2171064 := by exact prefixLift 2171064
  have htrace : WordTrace (prefixWord ++ tailWord_2171064) baseStart_2171064 baseEnd_2171064 := by
    simpa [prefixWord, tailWord_2171064, baseEnd_2171064] using wordTrace_append hprefix tailTrace_2171064
  have hstable : (prefixWord ++ tailWord_2171064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171064).length < 2 ^ (prefixWord ++ tailWord_2171064).sum := by decide
  have hdescent : baseEnd_2171064 < baseStart_2171064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171120 : List Nat := [2, 1, 1, 1, 3, 1, 1, 5, 7]
def baseStart_2171120 : Nat := 118140960795 + 2171120 * 2 ^ 59
def prefixEnd_2171120 : Nat := 4983230072969 + 3 ^ 40 * 2171120 * 2
def baseEnd_2171120 : Nat := 247739581908811270381157

theorem tailTrace_2171120 : CollatzResearch.WordTrace tailWord_2171120 prefixEnd_2171120 247739581908811270381157 := by
  unfold tailWord_2171120
  simp only [CollatzResearch.WordTrace]
  refine ⟨39593625947205256310195407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52791501262940341746927209 39593625947205256310195407)
  ·
    refine ⟨59390438920807884465293111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39593625947205256310195407 59390438920807884465293111)
    ·
      refine ⟨89085658381211826697939667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59390438920807884465293111 89085658381211826697939667)
      ·
        refine ⟨133628487571817740046909501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89085658381211826697939667 133628487571817740046909501)
        ·
          refine ⟨50110682839431652517591063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133628487571817740046909501 50110682839431652517591063)
          ·
            refine ⟨75166024259147478776386595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50110682839431652517591063 75166024259147478776386595)
            ·
              refine ⟨112749036388721218164579893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75166024259147478776386595 112749036388721218164579893)
              ·
                refine ⟨10570222161442614202929365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 112749036388721218164579893 10570222161442614202929365)
                ·
                  refine ⟨247739581908811270381157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10570222161442614202929365 247739581908811270381157)
                  ·
                    rfl

theorem cell22_2171120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 7].length) (baseStart_2171120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2171120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2171120 prefixEnd_2171120 := by exact prefixLift 2171120
  have htrace : WordTrace (prefixWord ++ tailWord_2171120) baseStart_2171120 baseEnd_2171120 := by
    simpa [prefixWord, tailWord_2171120, baseEnd_2171120] using wordTrace_append hprefix tailTrace_2171120
  have hstable : (prefixWord ++ tailWord_2171120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171120).length < 2 ^ (prefixWord ++ tailWord_2171120).sum := by decide
  have hdescent : baseEnd_2171120 < baseStart_2171120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171122 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 2, 6]
def baseStart_2171122 : Nat := 118140960795 + 2171122 * 2 ^ 59
def prefixEnd_2171122 : Nat := 4983230072969 + 3 ^ 40 * 2171122 * 2
def baseEnd_2171122 : Nat := 743219430367306472593465

theorem tailTrace_2171122 : CollatzResearch.WordTrace tailWord_2171122 prefixEnd_2171122 743219430367306472593465 := by
  unfold tailWord_2171122
  simp only [CollatzResearch.WordTrace]
  refine ⟨19796831210100816740490905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52791549893602177974642413 19796831210100816740490905)
  ·
    refine ⟨14847623407575612555368179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19796831210100816740490905 14847623407575612555368179)
    ·
      refine ⟨22271435111363418833052269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14847623407575612555368179 22271435111363418833052269)
      ·
        refine ⟨8351788166761282062394601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22271435111363418833052269 8351788166761282062394601)
        ·
          refine ⟨6263841125070961546795951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8351788166761282062394601 6263841125070961546795951)
          ·
            refine ⟨9395761687606442320193927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6263841125070961546795951 9395761687606442320193927)
            ·
              refine ⟨14093642531409663480290891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9395761687606442320193927 14093642531409663480290891)
              ·
                refine ⟨21140463797114495220436337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14093642531409663480290891 21140463797114495220436337)
                ·
                  refine ⟨15855347847835871415327253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21140463797114495220436337 15855347847835871415327253)
                  ·
                    refine ⟨743219430367306472593465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15855347847835871415327253 743219430367306472593465)
                    ·
                      rfl

theorem cell22_2171122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_2171122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2171122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2171122 prefixEnd_2171122 := by exact prefixLift 2171122
  have htrace : WordTrace (prefixWord ++ tailWord_2171122) baseStart_2171122 baseEnd_2171122 := by
    simpa [prefixWord, tailWord_2171122, baseEnd_2171122] using wordTrace_append hprefix tailTrace_2171122
  have hstable : (prefixWord ++ tailWord_2171122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171122).length < 2 ^ (prefixWord ++ tailWord_2171122).sum := by decide
  have hdescent : baseEnd_2171122 < baseStart_2171122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171137 : List Nat := [1, 2, 4, 1, 1, 2, 1, 5, 5]
def baseStart_2171137 : Nat := 118140960795 + 2171137 * 2 ^ 59
def prefixEnd_2171137 : Nat := 4983230072969 + 3 ^ 40 * 2171137 * 2
def baseEnd_2171137 : Nat := 247741521724617144489473

theorem tailTrace_2171137 : CollatzResearch.WordTrace tailWord_2171137 prefixEnd_2171137 247741521724617144489473 := by
  unfold tailWord_2171137
  simp only [CollatzResearch.WordTrace]
  refine ⟨79187871935348924523759665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52791914623565949682506443 79187871935348924523759665)
  ·
    refine ⟨59390903951511693392819749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79187871935348924523759665 59390903951511693392819749)
    ·
      refine ⟨11135794490908442511153703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59390903951511693392819749 11135794490908442511153703)
      ·
        refine ⟨16703691736362663766730555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11135794490908442511153703 16703691736362663766730555)
        ·
          refine ⟨25055537604543995650095833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16703691736362663766730555 25055537604543995650095833)
          ·
            refine ⟨18791653203407996737571875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25055537604543995650095833 18791653203407996737571875)
            ·
              refine ⟨28187479805111995106357813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18791653203407996737571875 28187479805111995106357813)
              ·
                refine ⟨2642576231729249541221045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28187479805111995106357813 2642576231729249541221045)
                ·
                  refine ⟨247741521724617144489473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2642576231729249541221045 247741521724617144489473)
                  ·
                    rfl

theorem cell22_2171137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 5].length) (baseStart_2171137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2171137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2171137 prefixEnd_2171137 := by exact prefixLift 2171137
  have htrace : WordTrace (prefixWord ++ tailWord_2171137) baseStart_2171137 baseEnd_2171137 := by
    simpa [prefixWord, tailWord_2171137, baseEnd_2171137] using wordTrace_append hprefix tailTrace_2171137
  have hstable : (prefixWord ++ tailWord_2171137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171137).length < 2 ^ (prefixWord ++ tailWord_2171137).sum := by decide
  have hdescent : baseEnd_2171137 < baseStart_2171137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171175 : List Nat := [1, 1, 8, 1, 1, 1, 2, 1, 3, 3]
def baseStart_2171175 : Nat := 118140960795 + 2171175 * 2 ^ 59
def prefixEnd_2171175 : Nat := 4983230072969 + 3 ^ 40 * 2171175 * 2
def baseEnd_2171175 : Nat := 743237573350432001018303

theorem tailTrace_2171175 : CollatzResearch.WordTrace tailWord_2171175 prefixEnd_2171175 743237573350432001018303 := by
  unfold tailWord_2171175
  simp only [CollatzResearch.WordTrace]
  refine ⟨79189257909211257013642979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52792838606140838009095319 79189257909211257013642979)
  ·
    refine ⟨118783886863816885520464469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79189257909211257013642979 118783886863816885520464469)
    ·
      refine ⟨1391998674185354127192943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 118783886863816885520464469 1391998674185354127192943)
      ·
        refine ⟨2087998011278031190789415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1391998674185354127192943 2087998011278031190789415)
        ·
          refine ⟨3131997016917046786184123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2087998011278031190789415 3131997016917046786184123)
          ·
            refine ⟨4697995525375570179276185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3131997016917046786184123 4697995525375570179276185)
            ·
              refine ⟨3523496644031677634457139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4697995525375570179276185 3523496644031677634457139)
              ·
                refine ⟨5285244966047516451685709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3523496644031677634457139 5285244966047516451685709)
                ·
                  refine ⟨1981966862267818669382141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5285244966047516451685709 1981966862267818669382141)
                  ·
                    refine ⟨743237573350432001018303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1981966862267818669382141 743237573350432001018303)
                    ·
                      rfl

theorem cell22_2171175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_2171175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2171175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2171175 prefixEnd_2171175 := by exact prefixLift 2171175
  have htrace : WordTrace (prefixWord ++ tailWord_2171175) baseStart_2171175 baseEnd_2171175 := by
    simpa [prefixWord, tailWord_2171175, baseEnd_2171175] using wordTrace_append hprefix tailTrace_2171175
  have hstable : (prefixWord ++ tailWord_2171175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171175).length < 2 ^ (prefixWord ++ tailWord_2171175).sum := by decide
  have hdescent : baseEnd_2171175 < baseStart_2171175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171212 : List Nat := [2, 2, 1, 3, 2, 1, 1, 3, 1, 6]
def baseStart_2171212 : Nat := 118140960795 + 2171212 * 2 ^ 59
def prefixEnd_2171212 : Nat := 4983230072969 + 3 ^ 40 * 2171212 * 2
def baseEnd_2171212 : Nat := 743250239206576237843189

theorem tailTrace_2171212 : CollatzResearch.WordTrace tailWord_2171212 prefixEnd_2171212 743250239206576237843189 := by
  unfold tailWord_2171212
  simp only [CollatzResearch.WordTrace]
  refine ⟨39595303705038606166369945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52793738273384808221826593 39595303705038606166369945)
  ·
    refine ⟨29696477778778954624777459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39595303705038606166369945 29696477778778954624777459)
    ·
      refine ⟨44544716668168431937166189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29696477778778954624777459 44544716668168431937166189)
      ·
        refine ⟨16704268750563161976437321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44544716668168431937166189 16704268750563161976437321)
        ·
          refine ⟨12528201562922371482327991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16704268750563161976437321 12528201562922371482327991)
          ·
            refine ⟨18792302344383557223491987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12528201562922371482327991 18792302344383557223491987)
            ·
              refine ⟨28188453516575335835237981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18792302344383557223491987 28188453516575335835237981)
              ·
                refine ⟨10570670068715750938214243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28188453516575335835237981 10570670068715750938214243)
                ·
                  refine ⟨15856005103073626407321365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10570670068715750938214243 15856005103073626407321365)
                  ·
                    refine ⟨743250239206576237843189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15856005103073626407321365 743250239206576237843189)
                    ·
                      rfl

theorem cell22_2171212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_2171212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2171212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2171212 prefixEnd_2171212 := by exact prefixLift 2171212
  have htrace : WordTrace (prefixWord ++ tailWord_2171212) baseStart_2171212 baseEnd_2171212 := by
    simpa [prefixWord, tailWord_2171212, baseEnd_2171212] using wordTrace_append hprefix tailTrace_2171212
  have hstable : (prefixWord ++ tailWord_2171212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171212).length < 2 ^ (prefixWord ++ tailWord_2171212).sum := by decide
  have hdescent : baseEnd_2171212 < baseStart_2171212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171216 : List Nat := [2, 1, 1, 1, 1, 8, 1, 3, 4]
def baseStart_2171216 : Nat := 118140960795 + 2171216 * 2 ^ 59
def prefixEnd_2171216 : Nat := 4983230072969 + 3 ^ 40 * 2171216 * 2
def baseEnd_2171216 : Nat := 247750536162773853581059

theorem tailTrace_2171216 : CollatzResearch.WordTrace tailWord_2171216 prefixEnd_2171216 247750536162773853581059 := by
  unfold tailWord_2171216
  simp only [CollatzResearch.WordTrace]
  refine ⟨39595376651031360507942751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52793835534708480677257001 39595376651031360507942751)
  ·
    refine ⟨59393064976547040761914127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39595376651031360507942751 59393064976547040761914127)
    ·
      refine ⟨89089597464820561142871191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59393064976547040761914127 89089597464820561142871191)
      ·
        refine ⟨133634396197230841714306787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89089597464820561142871191 133634396197230841714306787)
        ·
          refine ⟨200451594295846262571460181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133634396197230841714306787 200451594295846262571460181)
          ·
            refine ⟨2349042120654448389509299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 200451594295846262571460181 2349042120654448389509299)
            ·
              refine ⟨3523563180981672584263949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2349042120654448389509299 3523563180981672584263949)
              ·
                refine ⟨1321336192868127219098981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3523563180981672584263949 1321336192868127219098981)
                ·
                  refine ⟨247750536162773853581059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1321336192868127219098981 247750536162773853581059)
                  ·
                    rfl

theorem cell22_2171216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3, 4].length) (baseStart_2171216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2171216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2171216 prefixEnd_2171216 := by exact prefixLift 2171216
  have htrace : WordTrace (prefixWord ++ tailWord_2171216) baseStart_2171216 baseEnd_2171216 := by
    simpa [prefixWord, tailWord_2171216, baseEnd_2171216] using wordTrace_append hprefix tailTrace_2171216
  have hstable : (prefixWord ++ tailWord_2171216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171216).length < 2 ^ (prefixWord ++ tailWord_2171216).sum := by decide
  have hdescent : baseEnd_2171216 < baseStart_2171216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171244 : List Nat := [2, 2, 1, 1, 6, 1, 2, 7]
def baseStart_2171244 : Nat := 118140960795 + 2171244 * 2 ^ 59
def prefixEnd_2171244 : Nat := 4983230072969 + 3 ^ 40 * 2171244 * 2
def baseEnd_2171244 : Nat := 82584577051170980115899

theorem tailTrace_2171244 : CollatzResearch.WordTrace tailWord_2171244 prefixEnd_2171244 82584577051170980115899 := by
  unfold tailWord_2171244
  simp only [CollatzResearch.WordTrace]
  refine ⟨39595887272980640898952393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52794516363974187865269857 39595887272980640898952393)
  ·
    refine ⟨29696915454735480674214295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39595887272980640898952393 29696915454735480674214295)
    ·
      refine ⟨44545373182103221011321443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29696915454735480674214295 44545373182103221011321443)
      ·
        refine ⟨66818059773154831516982165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44545373182103221011321443 66818059773154831516982165)
        ·
          refine ⟨3132096551866632727358539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 66818059773154831516982165 3132096551866632727358539)
          ·
            refine ⟨4698144827799949091037809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3132096551866632727358539 4698144827799949091037809)
            ·
              refine ⟨3523608620849961818278357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4698144827799949091037809 3523608620849961818278357)
              ·
                refine ⟨82584577051170980115899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3523608620849961818278357 82584577051170980115899)
                ·
                  rfl

theorem cell22_2171244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 7].length) (baseStart_2171244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2171244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2171244 prefixEnd_2171244 := by exact prefixLift 2171244
  have htrace : WordTrace (prefixWord ++ tailWord_2171244) baseStart_2171244 baseEnd_2171244 := by
    simpa [prefixWord, tailWord_2171244, baseEnd_2171244] using wordTrace_append hprefix tailTrace_2171244
  have hstable : (prefixWord ++ tailWord_2171244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171244).length < 2 ^ (prefixWord ++ tailWord_2171244).sum := by decide
  have hdescent : baseEnd_2171244 < baseStart_2171244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171248 : List Nat := [2, 1, 1, 1, 4, 5, 2, 1, 2, 3]
def baseStart_2171248 : Nat := 118140960795 + 2171248 * 2 ^ 59
def prefixEnd_2171248 : Nat := 4983230072969 + 3 ^ 40 * 2171248 * 2
def baseEnd_2171248 : Nat := 743262562742284143943079

theorem tailTrace_2171248 : CollatzResearch.WordTrace tailWord_2171248 prefixEnd_2171248 743262562742284143943079 := by
  unfold tailWord_2171248
  simp only [CollatzResearch.WordTrace]
  refine ⟨39595960218973395240525199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52794613625297860320700265 39595960218973395240525199)
  ·
    refine ⟨59393940328460092860787799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39595960218973395240525199 59393940328460092860787799)
    ·
      refine ⟨89090910492690139291181699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59393940328460092860787799 89090910492690139291181699)
      ·
        refine ⟨133636365739035208936772549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89090910492690139291181699 133636365739035208936772549)
        ·
          refine ⟨25056818576069101675644853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133636365739035208936772549 25056818576069101675644853)
          ·
            refine ⟨2349076741506478282091705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25056818576069101675644853 2349076741506478282091705)
            ·
              refine ⟨1761807556129858711568779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2349076741506478282091705 1761807556129858711568779)
              ·
                refine ⟨2642711334194788067353169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1761807556129858711568779 2642711334194788067353169)
                ·
                  refine ⟨1982033500646091050514877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2642711334194788067353169 1982033500646091050514877)
                  ·
                    refine ⟨743262562742284143943079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1982033500646091050514877 743262562742284143943079)
                    ·
                      rfl

theorem cell22_2171248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 2, 3].length) (baseStart_2171248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2171248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2171248 prefixEnd_2171248 := by exact prefixLift 2171248
  have htrace : WordTrace (prefixWord ++ tailWord_2171248) baseStart_2171248 baseEnd_2171248 := by
    simpa [prefixWord, tailWord_2171248, baseEnd_2171248] using wordTrace_append hprefix tailTrace_2171248
  have hstable : (prefixWord ++ tailWord_2171248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171248).length < 2 ^ (prefixWord ++ tailWord_2171248).sum := by decide
  have hdescent : baseEnd_2171248 < baseStart_2171248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171289 : List Nat := [1, 2, 1, 2, 1, 4, 4, 2, 5]
def baseStart_2171289 : Nat := 118140960795 + 2171289 * 2 ^ 59
def prefixEnd_2171289 : Nat := 4983230072969 + 3 ^ 40 * 2171289 * 2
def baseEnd_2171289 : Nat := 247758865960057901222651

theorem tailTrace_2171289 : CollatzResearch.WordTrace tailWord_2171289 prefixEnd_2171289 247758865960057901222651 := by
  unfold tailWord_2171289
  simp only [CollatzResearch.WordTrace]
  refine ⟨79193415830798254483292921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52795610553865502988861947 79193415830798254483292921)
  ·
    refine ⟨59395061873098690862469691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79193415830798254483292921 59395061873098690862469691)
    ·
      refine ⟨89092592809648036293704537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59395061873098690862469691 89092592809648036293704537)
      ·
        refine ⟨66819444607236027220278403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89092592809648036293704537 66819444607236027220278403)
        ·
          refine ⟨100229166910854040830417605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66819444607236027220278403 100229166910854040830417605)
          ·
            refine ⟨18792968795785132655703301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100229166910854040830417605 18792968795785132655703301)
            ·
              refine ⟨3523681649209712372944369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18792968795785132655703301 3523681649209712372944369)
              ·
                refine ⟨2642761236907284279708277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3523681649209712372944369 2642761236907284279708277)
                ·
                  refine ⟨247758865960057901222651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2642761236907284279708277 247758865960057901222651)
                  ·
                    rfl

theorem cell22_2171289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 5].length) (baseStart_2171289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2171289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2171289 prefixEnd_2171289 := by exact prefixLift 2171289
  have htrace : WordTrace (prefixWord ++ tailWord_2171289) baseStart_2171289 baseEnd_2171289 := by
    simpa [prefixWord, tailWord_2171289, baseEnd_2171289] using wordTrace_append hprefix tailTrace_2171289
  have hstable : (prefixWord ++ tailWord_2171289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171289).length < 2 ^ (prefixWord ++ tailWord_2171289).sum := by decide
  have hdescent : baseEnd_2171289 < baseStart_2171289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171319 : List Nat := [1, 1, 3, 1, 3, 3, 2, 1, 3, 4]
def baseStart_2171319 : Nat := 118140960795 + 2171319 * 2 ^ 59
def prefixEnd_2171319 : Nat := 4983230072969 + 3 ^ 40 * 2171319 * 2
def baseEnd_2171319 : Nat := 743286867493263625417861

theorem tailTrace_2171319 : CollatzResearch.WordTrace tailWord_2171319 prefixEnd_2171319 743286867493263625417861 := by
  unfold tailWord_2171319
  simp only [CollatzResearch.WordTrace]
  refine ⟨79194510020689569606885011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52796340013793046404590007 79194510020689569606885011)
  ·
    refine ⟨118791765031034354410327517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79194510020689569606885011 118791765031034354410327517)
    ·
      refine ⟨44546911886637882903872819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118791765031034354410327517 44546911886637882903872819)
      ·
        refine ⟨66820367829956824355809229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44546911886637882903872819 66820367829956824355809229)
        ·
          refine ⟨25057637936233809133428461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66820367829956824355809229 25057637936233809133428461)
          ·
            refine ⟨9396614226087678425035673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25057637936233809133428461 9396614226087678425035673)
            ·
              refine ⟨7047460669565758818776755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9396614226087678425035673 7047460669565758818776755)
              ·
                refine ⟨10571191004348638228165133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7047460669565758818776755 10571191004348638228165133)
                ·
                  refine ⟨3964196626630739335561925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10571191004348638228165133 3964196626630739335561925)
                  ·
                    refine ⟨743286867493263625417861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3964196626630739335561925 743286867493263625417861)
                    ·
                      rfl

theorem cell22_2171319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_2171319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2171319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2171319 prefixEnd_2171319 := by exact prefixLift 2171319
  have htrace : WordTrace (prefixWord ++ tailWord_2171319) baseStart_2171319 baseEnd_2171319 := by
    simpa [prefixWord, tailWord_2171319, baseEnd_2171319] using wordTrace_append hprefix tailTrace_2171319
  have hstable : (prefixWord ++ tailWord_2171319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171319).length < 2 ^ (prefixWord ++ tailWord_2171319).sum := by decide
  have hdescent : baseEnd_2171319 < baseStart_2171319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171336 : List Nat := [2, 1, 3, 1, 3, 3, 1, 3, 1, 4]
def baseStart_2171336 : Nat := 118140960795 + 2171336 * 2 ^ 59
def prefixEnd_2171336 : Nat := 4983230072969 + 3 ^ 40 * 2171336 * 2
def baseEnd_2171336 : Nat := 743292686940681247742809

theorem tailTrace_2171336 : CollatzResearch.WordTrace tailWord_2171336 prefixEnd_2171336 743292686940681247742809 := by
  unfold tailWord_2171336
  simp only [CollatzResearch.WordTrace]
  refine ⟨39597565030813990755126931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52796753374418654340169241 39597565030813990755126931)
  ·
    refine ⟨59396347546220986132690397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39597565030813990755126931 59396347546220986132690397)
    ·
      refine ⟨22273630329832869799758899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59396347546220986132690397 22273630329832869799758899)
      ·
        refine ⟨33410445494749304699638349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22273630329832869799758899 33410445494749304699638349)
        ·
          refine ⟨12528917060530989262364381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33410445494749304699638349 12528917060530989262364381)
          ·
            refine ⟨4698343897699120973386643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12528917060530989262364381 4698343897699120973386643)
            ·
              refine ⟨7047515846548681460079965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4698343897699120973386643 7047515846548681460079965)
              ·
                refine ⟨2642818442455755547529987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7047515846548681460079965 2642818442455755547529987)
                ·
                  refine ⟨3964227663683633321294981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2642818442455755547529987 3964227663683633321294981)
                  ·
                    refine ⟨743292686940681247742809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3964227663683633321294981 743292686940681247742809)
                    ·
                      rfl

theorem cell22_2171336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_2171336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2171336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2171336 prefixEnd_2171336 := by exact prefixLift 2171336
  have htrace : WordTrace (prefixWord ++ tailWord_2171336) baseStart_2171336 baseEnd_2171336 := by
    simpa [prefixWord, tailWord_2171336, baseEnd_2171336] using wordTrace_append hprefix tailTrace_2171336
  have hstable : (prefixWord ++ tailWord_2171336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171336).length < 2 ^ (prefixWord ++ tailWord_2171336).sum := by decide
  have hdescent : baseEnd_2171336 < baseStart_2171336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171396 : List Nat := [2, 3, 2, 3, 1, 3, 8]
def baseStart_2171396 : Nat := 118140960795 + 2171396 * 2 ^ 59
def prefixEnd_2171396 : Nat := 4983230072969 + 3 ^ 40 * 2171396 * 2
def baseEnd_2171396 : Nat := 27530119487661521897875

theorem tailTrace_2171396 : CollatzResearch.WordTrace tailWord_2171396 prefixEnd_2171396 27530119487661521897875 := by
  unfold tailWord_2171396
  simp only [CollatzResearch.WordTrace]
  refine ⟨39598659220705305878719021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52798212294273741171625361 39598659220705305878719021)
  ·
    refine ⟨14849497207764489704519633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39598659220705305878719021 14849497207764489704519633)
    ·
      refine ⟨11137122905823367278389725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14849497207764489704519633 11137122905823367278389725)
      ·
        refine ⟨4176421089683762729396147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11137122905823367278389725 4176421089683762729396147)
        ·
          refine ⟨6264631634525644094094221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4176421089683762729396147 6264631634525644094094221)
          ·
            refine ⟨2349236862947116535285333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6264631634525644094094221 2349236862947116535285333)
            ·
              refine ⟨27530119487661521897875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2349236862947116535285333 27530119487661521897875)
              ·
                rfl

theorem cell22_2171396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 8].length) (baseStart_2171396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2171396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2171396 prefixEnd_2171396 := by exact prefixLift 2171396
  have htrace : WordTrace (prefixWord ++ tailWord_2171396) baseStart_2171396 baseEnd_2171396 := by
    simpa [prefixWord, tailWord_2171396, baseEnd_2171396] using wordTrace_append hprefix tailTrace_2171396
  have hstable : (prefixWord ++ tailWord_2171396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171396).length < 2 ^ (prefixWord ++ tailWord_2171396).sum := by decide
  have hdescent : baseEnd_2171396 < baseStart_2171396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171516 : List Nat := [2, 2, 2, 1, 1, 2, 2, 4, 2, 4]
def baseStart_2171516 : Nat := 118140960795 + 2171516 * 2 ^ 59
def prefixEnd_2171516 : Nat := 4983230072969 + 3 ^ 40 * 2171516 * 2
def baseEnd_2171516 : Nat := 743354304619220778242257

theorem tailTrace_2171516 : CollatzResearch.WordTrace tailWord_2171516 prefixEnd_2171516 743354304619220778242257 := by
  unfold tailWord_2171516
  simp only [CollatzResearch.WordTrace]
  refine ⟨39600847600487936125903201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52801130133983914834537601 39600847600487936125903201)
  ·
    refine ⟨29700635700365952094427401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39600847600487936125903201 29700635700365952094427401)
    ·
      refine ⟨22275476775274464070820551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29700635700365952094427401 22275476775274464070820551)
      ·
        refine ⟨33413215162911696106230827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22275476775274464070820551 33413215162911696106230827)
        ·
          refine ⟨50119822744367544159346241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33413215162911696106230827 50119822744367544159346241)
          ·
            refine ⟨37589867058275658119509681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50119822744367544159346241 37589867058275658119509681)
            ·
              refine ⟨28192400293706743589632261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37589867058275658119509681 28192400293706743589632261)
              ·
                refine ⟨5286075055070014423056049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28192400293706743589632261 5286075055070014423056049)
                ·
                  refine ⟨3964556291302510817292037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5286075055070014423056049 3964556291302510817292037)
                  ·
                    refine ⟨743354304619220778242257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3964556291302510817292037 743354304619220778242257)
                    ·
                      rfl

theorem cell22_2171516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_2171516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2171516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2171516 prefixEnd_2171516 := by exact prefixLift 2171516
  have htrace : WordTrace (prefixWord ++ tailWord_2171516) baseStart_2171516 baseEnd_2171516 := by
    simpa [prefixWord, tailWord_2171516, baseEnd_2171516] using wordTrace_append hprefix tailTrace_2171516
  have hstable : (prefixWord ++ tailWord_2171516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171516).length < 2 ^ (prefixWord ++ tailWord_2171516).sum := by decide
  have hdescent : baseEnd_2171516 < baseStart_2171516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171548 : List Nat := [2, 2, 3, 2, 2, 1, 4, 6]
def baseStart_2171548 : Nat := 118140960795 + 2171548 * 2 ^ 59
def prefixEnd_2171548 : Nat := 4983230072969 + 3 ^ 40 * 2171548 * 2
def baseEnd_2171548 : Nat := 82596139874798151271351

theorem tailTrace_2171548 : CollatzResearch.WordTrace tailWord_2171548 prefixEnd_2171548 82596139874798151271351 := by
  unfold tailWord_2171548
  simp only [CollatzResearch.WordTrace]
  refine ⟨39601431168429970858485649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52801908224573294477980865 39601431168429970858485649)
  ·
    refine ⟨29701073376322478143864237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39601431168429970858485649 29701073376322478143864237)
    ·
      refine ⟨11137902516120929303949089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29701073376322478143864237 11137902516120929303949089)
      ·
        refine ⟨8353426887090696977961817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11137902516120929303949089 8353426887090696977961817)
        ·
          refine ⟨6265070165318022733471363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8353426887090696977961817 6265070165318022733471363)
          ·
            refine ⟨9397605247977034100207045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6265070165318022733471363 9397605247977034100207045)
            ·
              refine ⟨1762050983995693893788821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9397605247977034100207045 1762050983995693893788821)
              ·
                refine ⟨82596139874798151271351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1762050983995693893788821 82596139874798151271351)
                ·
                  rfl

theorem cell22_2171548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 6].length) (baseStart_2171548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2171548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2171548 prefixEnd_2171548 := by exact prefixLift 2171548
  have htrace : WordTrace (prefixWord ++ tailWord_2171548) baseStart_2171548 baseEnd_2171548 := by
    simpa [prefixWord, tailWord_2171548, baseEnd_2171548] using wordTrace_append hprefix tailTrace_2171548
  have hstable : (prefixWord ++ tailWord_2171548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171548).length < 2 ^ (prefixWord ++ tailWord_2171548).sum := by decide
  have hdescent : baseEnd_2171548 < baseStart_2171548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171638 : List Nat := [5, 1, 1, 1, 1, 2, 2, 3, 6]
def baseStart_2171638 : Nat := 118140960795 + 2171638 * 2 ^ 59
def prefixEnd_2171638 : Nat := 4983230072969 + 3 ^ 40 * 2171638 * 2
def baseEnd_2171638 : Nat := 247798689237484375563961

theorem tailTrace_2171638 : CollatzResearch.WordTrace tailWord_2171638 prefixEnd_2171638 247798689237484375563961 := by
  unfold tailWord_2171638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4950384056658367942984223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52804096604355924725165045 4950384056658367942984223)
  ·
    refine ⟨7425576084987551914476335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4950384056658367942984223 7425576084987551914476335)
    ·
      refine ⟨11138364127481327871714503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7425576084987551914476335 11138364127481327871714503)
      ·
        refine ⟨16707546191221991807571755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11138364127481327871714503 16707546191221991807571755)
        ·
          refine ⟨25061319286832987711357633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16707546191221991807571755 25061319286832987711357633)
          ·
            refine ⟨18795989465124740783518225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25061319286832987711357633 18795989465124740783518225)
            ·
              refine ⟨14096992098843555587638669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18795989465124740783518225 14096992098843555587638669)
              ·
                refine ⟨5286372037066333345364501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14096992098843555587638669 5286372037066333345364501)
                ·
                  refine ⟨247798689237484375563961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5286372037066333345364501 247798689237484375563961)
                  ·
                    rfl

theorem cell22_2171638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_2171638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2171638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2171638 prefixEnd_2171638 := by exact prefixLift 2171638
  have htrace : WordTrace (prefixWord ++ tailWord_2171638) baseStart_2171638 baseEnd_2171638 := by
    simpa [prefixWord, tailWord_2171638, baseEnd_2171638] using wordTrace_append hprefix tailTrace_2171638
  have hstable : (prefixWord ++ tailWord_2171638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171638).length < 2 ^ (prefixWord ++ tailWord_2171638).sum := by decide
  have hdescent : baseEnd_2171638 < baseStart_2171638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171651 : List Nat := [1, 1, 1, 3, 2, 2, 1, 4, 1, 6]
def baseStart_2171651 : Nat := 118140960795 + 2171651 * 2 ^ 59
def prefixEnd_2171651 : Nat := 4983230072969 + 3 ^ 40 * 2171651 * 2
def baseEnd_2171651 : Nat := 743400517878125426116843

theorem tailTrace_2171651 : CollatzResearch.WordTrace tailWord_2171651 prefixEnd_2171651 743400517878125426116843 := by
  unfold tailWord_2171651
  simp only [CollatzResearch.WordTrace]
  refine ⟨79206619055486790307970807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52804412703657860205313871 79206619055486790307970807)
  ·
    refine ⟨118809928583230185461956211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79206619055486790307970807 118809928583230185461956211)
    ·
      refine ⟨178214892874845278192934317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118809928583230185461956211 178214892874845278192934317)
      ·
        refine ⟨66830584828066979322350369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178214892874845278192934317 66830584828066979322350369)
        ·
          refine ⟨50122938621050234491762777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66830584828066979322350369 50122938621050234491762777)
          ·
            refine ⟨37592203965787675868822083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50122938621050234491762777 37592203965787675868822083)
            ·
              refine ⟨56388305948681513803233125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37592203965787675868822083 56388305948681513803233125)
              ·
                refine ⟨10572807365377783838106211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56388305948681513803233125 10572807365377783838106211)
                ·
                  refine ⟨15859211048066675757159317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10572807365377783838106211 15859211048066675757159317)
                  ·
                    refine ⟨743400517878125426116843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15859211048066675757159317 743400517878125426116843)
                    ·
                      rfl

theorem cell22_2171651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 6].length) (baseStart_2171651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2171651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2171651 prefixEnd_2171651 := by exact prefixLift 2171651
  have htrace : WordTrace (prefixWord ++ tailWord_2171651) baseStart_2171651 baseEnd_2171651 := by
    simpa [prefixWord, tailWord_2171651, baseEnd_2171651] using wordTrace_append hprefix tailTrace_2171651
  have hstable : (prefixWord ++ tailWord_2171651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171651).length < 2 ^ (prefixWord ++ tailWord_2171651).sum := by decide
  have hdescent : baseEnd_2171651 < baseStart_2171651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171696 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 1, 8]
def baseStart_2171696 : Nat := 118140960795 + 2171696 * 2 ^ 59
def prefixEnd_2171696 : Nat := 4983230072969 + 3 ^ 40 * 2171696 * 2
def baseEnd_2171696 : Nat := 743415922297760308741705

theorem tailTrace_2171696 : CollatzResearch.WordTrace tailWord_2171696 prefixEnd_2171696 743415922297760308741705 := by
  unfold tailWord_2171696
  simp only [CollatzResearch.WordTrace]
  refine ⟨39604130170161881496679471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52805506893549175328905961 39604130170161881496679471)
  ·
    refine ⟨59406195255242822245019207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39604130170161881496679471 59406195255242822245019207)
    ·
      refine ⟨89109292882864233367528811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59406195255242822245019207 89109292882864233367528811)
      ·
        refine ⟨133663939324296350051293217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89109292882864233367528811 133663939324296350051293217)
        ·
          refine ⟨100247954493222262538469913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133663939324296350051293217 100247954493222262538469913)
          ·
            refine ⟨75185965869916696903852435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100247954493222262538469913 75185965869916696903852435)
            ·
              refine ⟨112778948804875045355778653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75185965869916696903852435 112778948804875045355778653)
              ·
                refine ⟨42292105801828142008416995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112778948804875045355778653 42292105801828142008416995)
                ·
                  refine ⟨63438158702742213012625493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42292105801828142008416995 63438158702742213012625493)
                  ·
                    refine ⟨743415922297760308741705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 63438158702742213012625493 743415922297760308741705)
                    ·
                      rfl

theorem cell22_2171696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_2171696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2171696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2171696 prefixEnd_2171696 := by exact prefixLift 2171696
  have htrace : WordTrace (prefixWord ++ tailWord_2171696) baseStart_2171696 baseEnd_2171696 := by
    simpa [prefixWord, tailWord_2171696, baseEnd_2171696] using wordTrace_append hprefix tailTrace_2171696
  have hstable : (prefixWord ++ tailWord_2171696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171696).length < 2 ^ (prefixWord ++ tailWord_2171696).sum := by decide
  have hdescent : baseEnd_2171696 < baseStart_2171696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171773 : List Nat := [1, 4, 1, 1, 2, 1, 2, 4, 6]
def baseStart_2171773 : Nat := 118140960795 + 2171773 * 2 ^ 59
def prefixEnd_2171773 : Nat := 4983230072969 + 3 ^ 40 * 2171773 * 2
def baseEnd_2171773 : Nat := 247814093657119258188823

theorem tailTrace_2171773 : CollatzResearch.WordTrace tailWord_2171773 prefixEnd_2171773 247814093657119258188823 := by
  unfold tailWord_2171773
  simp only [CollatzResearch.WordTrace]
  refine ⟨79211068761044805143911973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52807379174029870095941315 79211068761044805143911973)
  ·
    refine ⟨14852075392695900964483495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79211068761044805143911973 14852075392695900964483495)
    ·
      refine ⟨22278113089043851446725243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14852075392695900964483495 22278113089043851446725243)
      ·
        refine ⟨33417169633565777170087865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22278113089043851446725243 33417169633565777170087865)
        ·
          refine ⟨25062877225174332877565899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33417169633565777170087865 25062877225174332877565899)
          ·
            refine ⟨37594315837761499316348849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25062877225174332877565899 37594315837761499316348849)
            ·
              refine ⟨28195736878321124487261637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37594315837761499316348849 28195736878321124487261637)
              ·
                refine ⟨5286700664685210841361557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28195736878321124487261637 5286700664685210841361557)
                ·
                  refine ⟨247814093657119258188823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5286700664685210841361557 247814093657119258188823)
                  ·
                    rfl

theorem cell22_2171773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_2171773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2171773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2171773 prefixEnd_2171773 := by exact prefixLift 2171773
  have htrace : WordTrace (prefixWord ++ tailWord_2171773) baseStart_2171773 baseEnd_2171773 := by
    simpa [prefixWord, tailWord_2171773, baseEnd_2171773] using wordTrace_append hprefix tailTrace_2171773
  have hstable : (prefixWord ++ tailWord_2171773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171773).length < 2 ^ (prefixWord ++ tailWord_2171773).sum := by decide
  have hdescent : baseEnd_2171773 < baseStart_2171773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171775 : List Nat := [1, 1, 2, 2, 1, 1, 7, 2, 1, 4]
def baseStart_2171775 : Nat := 118140960795 + 2171775 * 2 ^ 59
def prefixEnd_2171775 : Nat := 4983230072969 + 3 ^ 40 * 2171775 * 2
def baseEnd_2171775 : Nat := 743442965612230436016463

theorem tailTrace_2171775 : CollatzResearch.WordTrace tailWord_2171775 prefixEnd_2171775 743442965612230436016463 := by
  unfold tailWord_2171775
  simp only [CollatzResearch.WordTrace]
  refine ⟨79211141707037559485484779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52807427804691706323656519 79211141707037559485484779)
  ·
    refine ⟨118816712560556339228227169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79211141707037559485484779 118816712560556339228227169)
    ·
      refine ⟨89112534420417254421170377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118816712560556339228227169 89112534420417254421170377)
      ·
        refine ⟨66834400815312940815877783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89112534420417254421170377 66834400815312940815877783)
        ·
          refine ⟨100251601222969411223816675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66834400815312940815877783 100251601222969411223816675)
          ·
            refine ⟨150377401834454116835725013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100251601222969411223816675 150377401834454116835725013)
            ·
              refine ⟨3524470355495018363337305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 150377401834454116835725013 3524470355495018363337305)
              ·
                refine ⟨2643352766621263772502979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3524470355495018363337305 2643352766621263772502979)
                ·
                  refine ⟨3965029149931895658754469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2643352766621263772502979 3965029149931895658754469)
                  ·
                    refine ⟨743442965612230436016463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3965029149931895658754469 743442965612230436016463)
                    ·
                      rfl

theorem cell22_2171775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 1, 4].length) (baseStart_2171775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2171775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2171775 prefixEnd_2171775 := by exact prefixLift 2171775
  have htrace : WordTrace (prefixWord ++ tailWord_2171775) baseStart_2171775 baseEnd_2171775 := by
    simpa [prefixWord, tailWord_2171775, baseEnd_2171775] using wordTrace_append hprefix tailTrace_2171775
  have hstable : (prefixWord ++ tailWord_2171775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171775).length < 2 ^ (prefixWord ++ tailWord_2171775).sum := by decide
  have hdescent : baseEnd_2171775 < baseStart_2171775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171788 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 3, 5]
def baseStart_2171788 : Nat := 118140960795 + 2171788 * 2 ^ 59
def prefixEnd_2171788 : Nat := 4983230072969 + 3 ^ 40 * 2171788 * 2
def baseEnd_2171788 : Nat := 743447415777902735441423

theorem tailTrace_2171788 : CollatzResearch.WordTrace tailWord_2171788 prefixEnd_2171788 743447415777902735441423 := by
  unfold tailWord_2171788
  simp only [CollatzResearch.WordTrace]
  refine ⟨39605807927995231352854009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52807743903993641803805345 39605807927995231352854009)
  ·
    refine ⟨29704355945996423514640507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39605807927995231352854009 29704355945996423514640507)
    ·
      refine ⟨44556533918994635271960761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29704355945996423514640507 44556533918994635271960761)
      ·
        refine ⟨33417400439245976453970571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44556533918994635271960761 33417400439245976453970571)
        ·
          refine ⟨50126100658868964680955857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33417400439245976453970571 50126100658868964680955857)
          ·
            refine ⟨37594575494151723510716893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50126100658868964680955857 37594575494151723510716893)
            ·
              refine ⟨14097965810306896316518835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37594575494151723510716893 14097965810306896316518835)
              ·
                refine ⟨21146948715460344474778253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14097965810306896316518835 21146948715460344474778253)
                ·
                  refine ⟨7930105768297629178041845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21146948715460344474778253 7930105768297629178041845)
                  ·
                    refine ⟨743447415777902735441423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7930105768297629178041845 743447415777902735441423)
                    ·
                      rfl

theorem cell22_2171788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_2171788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2171788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2171788 prefixEnd_2171788 := by exact prefixLift 2171788
  have htrace : WordTrace (prefixWord ++ tailWord_2171788) baseStart_2171788 baseEnd_2171788 := by
    simpa [prefixWord, tailWord_2171788, baseEnd_2171788] using wordTrace_append hprefix tailTrace_2171788
  have hstable : (prefixWord ++ tailWord_2171788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171788).length < 2 ^ (prefixWord ++ tailWord_2171788).sum := by decide
  have hdescent : baseEnd_2171788 < baseStart_2171788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171807 : List Nat := [1, 1, 2, 5, 2, 2, 1, 4, 4]
def baseStart_2171807 : Nat := 118140960795 + 2171807 * 2 ^ 59
def prefixEnd_2171807 : Nat := 4983230072969 + 3 ^ 40 * 2171807 * 2
def baseEnd_2171807 : Nat := 247817973288731006405455

theorem tailTrace_2171807 : CollatzResearch.WordTrace tailWord_2171807 prefixEnd_2171807 247817973288731006405455 := by
  unfold tailWord_2171807
  simp only [CollatzResearch.WordTrace]
  refine ⟨79212308842921628950649675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52808205895281085967099783 79212308842921628950649675)
  ·
    refine ⟨118818463264382443425974513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79212308842921628950649675 118818463264382443425974513)
    ·
      refine ⟨89113847448286832569480885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118818463264382443425974513 89113847448286832569480885)
      ·
        refine ⟨8354423198276890553388833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89113847448286832569480885 8354423198276890553388833)
        ·
          refine ⟨6265817398707667915041625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8354423198276890553388833 6265817398707667915041625)
          ·
            refine ⟨4699363049030750936281219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6265817398707667915041625 4699363049030750936281219)
            ·
              refine ⟨7049044573546126404421829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4699363049030750936281219 7049044573546126404421829)
              ·
                refine ⟨1321695857539898700829093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7049044573546126404421829 1321695857539898700829093)
                ·
                  refine ⟨247817973288731006405455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1321695857539898700829093 247817973288731006405455)
                  ·
                    rfl

theorem cell22_2171807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4, 4].length) (baseStart_2171807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2171807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2171807 prefixEnd_2171807 := by exact prefixLift 2171807
  have htrace : WordTrace (prefixWord ++ tailWord_2171807) baseStart_2171807 baseEnd_2171807 := by
    simpa [prefixWord, tailWord_2171807, baseEnd_2171807] using wordTrace_append hprefix tailTrace_2171807
  have hstable : (prefixWord ++ tailWord_2171807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171807).length < 2 ^ (prefixWord ++ tailWord_2171807).sum := by decide
  have hdescent : baseEnd_2171807 < baseStart_2171807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171850 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 7, 3]
def baseStart_2171850 : Nat := 118140960795 + 2171850 * 2 ^ 59
def prefixEnd_2171850 : Nat := 4983230072969 + 3 ^ 40 * 2171850 * 2
def baseEnd_2171850 : Nat := 743468639644955240391233

theorem tailTrace_2171850 : CollatzResearch.WordTrace tailWord_2171850 prefixEnd_2171850 743468639644955240391233 := by
  unfold tailWord_2171850
  simp only [CollatzResearch.WordTrace]
  refine ⟨19803469295441461823616251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52809251454510564862976669 19803469295441461823616251)
  ·
    refine ⟨29705203943162192735424377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19803469295441461823616251 29705203943162192735424377)
    ·
      refine ⟨22278902957371644551568283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29705203943162192735424377 22278902957371644551568283)
      ·
        refine ⟨33418354436057466827352425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22278902957371644551568283 33418354436057466827352425)
        ·
          refine ⟨25063765827043100120514319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33418354436057466827352425 25063765827043100120514319)
          ·
            refine ⟨37595648740564650180771479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25063765827043100120514319 37595648740564650180771479)
            ·
              refine ⟨56393473110846975271157219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37595648740564650180771479 56393473110846975271157219)
              ·
                refine ⟨84590209666270462906735829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56393473110846975271157219 84590209666270462906735829)
                ·
                  refine ⟨1982583039053213974376621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 84590209666270462906735829 1982583039053213974376621)
                  ·
                    refine ⟨743468639644955240391233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1982583039053213974376621 743468639644955240391233)
                    ·
                      rfl

theorem cell22_2171850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_2171850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2171850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2171850 prefixEnd_2171850 := by exact prefixLift 2171850
  have htrace : WordTrace (prefixWord ++ tailWord_2171850) baseStart_2171850 baseEnd_2171850 := by
    simpa [prefixWord, tailWord_2171850, baseEnd_2171850] using wordTrace_append hprefix tailTrace_2171850
  have hstable : (prefixWord ++ tailWord_2171850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171850).length < 2 ^ (prefixWord ++ tailWord_2171850).sum := by decide
  have hdescent : baseEnd_2171850 < baseStart_2171850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171880 : List Nat := [2, 1, 4, 1, 1, 1, 2, 5, 5]
def baseStart_2171880 : Nat := 118140960795 + 2171880 * 2 ^ 59
def prefixEnd_2171880 : Nat := 4983230072969 + 3 ^ 40 * 2171880 * 2
def baseEnd_2171880 : Nat := 247826303086015054047047

theorem tailTrace_2171880 : CollatzResearch.WordTrace tailWord_2171880 prefixEnd_2171880 247826303086015054047047 := by
  unfold tailWord_2171880
  simp only [CollatzResearch.WordTrace]
  refine ⟨39607485685828581209028547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52809980914438108278704729 39607485685828581209028547)
  ·
    refine ⟨59411228528742871813542821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39607485685828581209028547 59411228528742871813542821)
    ·
      refine ⟨11139605349139288465039279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59411228528742871813542821 11139605349139288465039279)
      ·
        refine ⟨16709408023708932697558919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11139605349139288465039279 16709408023708932697558919)
        ·
          refine ⟨25064112035563399046338379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16709408023708932697558919 25064112035563399046338379)
          ·
            refine ⟨37596168053345098569507569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25064112035563399046338379 37596168053345098569507569)
            ·
              refine ⟨28197126040008823927130677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37596168053345098569507569 28197126040008823927130677)
              ·
                refine ⟨2643480566250827243168501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28197126040008823927130677 2643480566250827243168501)
                ·
                  refine ⟨247826303086015054047047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2643480566250827243168501 247826303086015054047047)
                  ·
                    rfl

theorem cell22_2171880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 5].length) (baseStart_2171880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2171880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2171880 prefixEnd_2171880 := by exact prefixLift 2171880
  have htrace : WordTrace (prefixWord ++ tailWord_2171880) baseStart_2171880 baseEnd_2171880 := by
    simpa [prefixWord, tailWord_2171880, baseEnd_2171880] using wordTrace_append hprefix tailTrace_2171880
  have hstable : (prefixWord ++ tailWord_2171880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171880).length < 2 ^ (prefixWord ++ tailWord_2171880).sum := by decide
  have hdescent : baseEnd_2171880 < baseStart_2171880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2171892 : List Nat := [2, 6, 2, 1, 2, 1, 1, 3, 4]
def baseStart_2171892 : Nat := 118140960795 + 2171892 * 2 ^ 59
def prefixEnd_2171892 : Nat := 4983230072969 + 3 ^ 40 * 2171892 * 2
def baseEnd_2171892 : Nat := 247827672367760376947035

theorem tailTrace_2171892 : CollatzResearch.WordTrace tailWord_2171892 prefixEnd_2171892 247827672367760376947035 := by
  unfold tailWord_2171892
  simp only [CollatzResearch.WordTrace]
  refine ⟨39607704523806844233746965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52810272698409125644995953 39607704523806844233746965)
  ·
    refine ⟨1856611149553445823456889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 39607704523806844233746965 1856611149553445823456889)
    ·
      refine ⟨1392458362165084367592667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1856611149553445823456889 1392458362165084367592667)
      ·
        refine ⟨2088687543247626551389001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1392458362165084367592667 2088687543247626551389001)
        ·
          refine ⟨1566515657435719913541751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2088687543247626551389001 1566515657435719913541751)
          ·
            refine ⟨2349773486153579870312627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1566515657435719913541751 2349773486153579870312627)
            ·
              refine ⟨3524660229230369805468941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2349773486153579870312627 3524660229230369805468941)
              ·
                refine ⟨1321747585961388677050853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3524660229230369805468941 1321747585961388677050853)
                ·
                  refine ⟨247827672367760376947035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1321747585961388677050853 247827672367760376947035)
                  ·
                    rfl

theorem cell22_2171892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_2171892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2171892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2171892 prefixEnd_2171892 := by exact prefixLift 2171892
  have htrace : WordTrace (prefixWord ++ tailWord_2171892) baseStart_2171892 baseEnd_2171892 := by
    simpa [prefixWord, tailWord_2171892, baseEnd_2171892] using wordTrace_append hprefix tailTrace_2171892
  have hstable : (prefixWord ++ tailWord_2171892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2171892).length < 2 ^ (prefixWord ++ tailWord_2171892).sum := by decide
  have hdescent : baseEnd_2171892 < baseStart_2171892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2171892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172000 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 2, 6]
def baseStart_2172000 : Nat := 118140960795 + 2172000 * 2 ^ 59
def prefixEnd_2172000 : Nat := 4983230072969 + 3 ^ 40 * 2172000 * 2
def baseEnd_2172000 : Nat := 743519987710404849140773

theorem tailTrace_2172000 : CollatzResearch.WordTrace tailWord_2172000 prefixEnd_2172000 743519987710404849140773 := by
  unfold tailWord_2172000
  simp only [CollatzResearch.WordTrace]
  refine ⟨39609674065611211456212727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52812898754148281941616969 39609674065611211456212727)
  ·
    refine ⟨59414511098416817184319091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39609674065611211456212727 59414511098416817184319091)
    ·
      refine ⟨89121766647625225776478637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59414511098416817184319091 89121766647625225776478637)
      ·
        refine ⟨33420662492859459666179489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89121766647625225776478637 33420662492859459666179489)
        ·
          refine ⟨25065496869644594749634617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33420662492859459666179489 25065496869644594749634617)
          ·
            refine ⟨18799122652233446062225963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25065496869644594749634617 18799122652233446062225963)
            ·
              refine ⟨28198683978350169093338945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18799122652233446062225963 28198683978350169093338945)
              ·
                refine ⟨21149012983762626820004209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28198683978350169093338945 21149012983762626820004209)
                ·
                  refine ⟨15861759737821970115003157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21149012983762626820004209 15861759737821970115003157)
                  ·
                    refine ⟨743519987710404849140773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15861759737821970115003157 743519987710404849140773)
                    ·
                      rfl

theorem cell22_2172000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 2, 6].length) (baseStart_2172000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172000 prefixEnd_2172000 := by exact prefixLift 2172000
  have htrace : WordTrace (prefixWord ++ tailWord_2172000) baseStart_2172000 baseEnd_2172000 := by
    simpa [prefixWord, tailWord_2172000, baseEnd_2172000] using wordTrace_append hprefix tailTrace_2172000
  have hstable : (prefixWord ++ tailWord_2172000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172000).length < 2 ^ (prefixWord ++ tailWord_2172000).sum := by decide
  have hdescent : baseEnd_2172000 < baseStart_2172000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172015 : List Nat := [1, 1, 2, 1, 3, 3, 2, 2, 7]
def baseStart_2172015 : Nat := 118140960795 + 2172015 * 2 ^ 59
def prefixEnd_2172015 : Nat := 4983230072969 + 3 ^ 40 * 2172015 * 2
def baseEnd_2172015 : Nat := 247841707505649936671909

theorem tailTrace_2172015 : CollatzResearch.WordTrace tailWord_2172015 prefixEnd_2172015 247841707505649936671909 := by
  unfold tailWord_2172015
  simp only [CollatzResearch.WordTrace]
  refine ⟨79219895226168080474221499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52813263484112053649480999 79219895226168080474221499)
  ·
    refine ⟨118829842839252120711332249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79219895226168080474221499 118829842839252120711332249)
    ·
      refine ⟨89122382129439090533499187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118829842839252120711332249 89122382129439090533499187)
      ·
        refine ⟨133683573194158635800248781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89122382129439090533499187 133683573194158635800248781)
        ·
          refine ⟨50131339947809488425093293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133683573194158635800248781 50131339947809488425093293)
          ·
            refine ⟨18799252480428558159409985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50131339947809488425093293 18799252480428558159409985)
            ·
              refine ⟨14099439360321418619557489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18799252480428558159409985 14099439360321418619557489)
              ·
                refine ⟨10574579520241063964668117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14099439360321418619557489 10574579520241063964668117)
                ·
                  refine ⟨247841707505649936671909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10574579520241063964668117 247841707505649936671909)
                  ·
                    rfl

theorem cell22_2172015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 7].length) (baseStart_2172015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172015 prefixEnd_2172015 := by exact prefixLift 2172015
  have htrace : WordTrace (prefixWord ++ tailWord_2172015) baseStart_2172015 baseEnd_2172015 := by
    simpa [prefixWord, tailWord_2172015, baseEnd_2172015] using wordTrace_append hprefix tailTrace_2172015
  have hstable : (prefixWord ++ tailWord_2172015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172015).length < 2 ^ (prefixWord ++ tailWord_2172015).sum := by decide
  have hdescent : baseEnd_2172015 < baseStart_2172015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172032 : List Nat := [2, 1, 1, 2, 1, 3, 5, 2, 5]
def baseStart_2172032 : Nat := 118140960795 + 2172032 * 2 ^ 59
def prefixEnd_2172032 : Nat := 4983230072969 + 3 ^ 40 * 2172032 * 2
def baseEnd_2172032 : Nat := 247843647321455810780225

theorem tailTrace_2172032 : CollatzResearch.WordTrace tailWord_2172032 prefixEnd_2172032 247843647321455810780225 := by
  unfold tailWord_2172032
  simp only [CollatzResearch.WordTrace]
  refine ⟨39610257633553246188795175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52813676844737661585060233 39610257633553246188795175)
  ·
    refine ⟨59415386450329869283192763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39610257633553246188795175 59415386450329869283192763)
    ·
      refine ⟨89123079675494803924789145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59415386450329869283192763 89123079675494803924789145)
      ·
        refine ⟨66842309756621102943591859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89123079675494803924789145 66842309756621102943591859)
        ·
          refine ⟨100263464634931654415387789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66842309756621102943591859 100263464634931654415387789)
          ·
            refine ⟨37598799238099370405770421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100263464634931654415387789 37598799238099370405770421)
            ·
              refine ⟨3524887428571815975540977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37598799238099370405770421 3524887428571815975540977)
              ·
                refine ⟨2643665571428861981655733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3524887428571815975540977 2643665571428861981655733)
                ·
                  refine ⟨247843647321455810780225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2643665571428861981655733 247843647321455810780225)
                  ·
                    rfl

theorem cell22_2172032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 5].length) (baseStart_2172032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172032 prefixEnd_2172032 := by exact prefixLift 2172032
  have htrace : WordTrace (prefixWord ++ tailWord_2172032) baseStart_2172032 baseEnd_2172032 := by
    simpa [prefixWord, tailWord_2172032, baseEnd_2172032] using wordTrace_append hprefix tailTrace_2172032
  have hstable : (prefixWord ++ tailWord_2172032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172032).length < 2 ^ (prefixWord ++ tailWord_2172032).sum := by decide
  have hdescent : baseEnd_2172032 < baseStart_2172032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172036 : List Nat := [2, 3, 2, 1, 2, 2, 2, 4, 1, 3]
def baseStart_2172036 : Nat := 118140960795 + 2172036 * 2 ^ 59
def prefixEnd_2172036 : Nat := 4983230072969 + 3 ^ 40 * 2172036 * 2
def baseEnd_2172036 : Nat := 743532311246112755240663

theorem tailTrace_2172036 : CollatzResearch.WordTrace tailWord_2172036 prefixEnd_2172036 743532311246112755240663 := by
  unfold tailWord_2172036
  simp only [CollatzResearch.WordTrace]
  refine ⟨39610330579546000530367981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52813774106061334040490641 39610330579546000530367981)
  ·
    refine ⟨14853873967329750198887993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39610330579546000530367981 14853873967329750198887993)
    ·
      refine ⟨11140405475497312649165995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14853873967329750198887993 11140405475497312649165995)
      ·
        refine ⟨16710608213245968973748993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11140405475497312649165995 16710608213245968973748993)
        ·
          refine ⟨12532956159934476730311745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16710608213245968973748993 12532956159934476730311745)
          ·
            refine ⟨9399717119950857547733809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12532956159934476730311745 9399717119950857547733809)
            ·
              refine ⟨7049787839963143160800357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9399717119950857547733809 7049787839963143160800357)
              ·
                refine ⟨1321835219993089342650067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7049787839963143160800357 1321835219993089342650067)
                ·
                  refine ⟨1982752829989634013975101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1321835219993089342650067 1982752829989634013975101)
                  ·
                    refine ⟨743532311246112755240663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1982752829989634013975101 743532311246112755240663)
                    ·
                      rfl

theorem cell22_2172036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_2172036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172036 prefixEnd_2172036 := by exact prefixLift 2172036
  have htrace : WordTrace (prefixWord ++ tailWord_2172036) baseStart_2172036 baseEnd_2172036 := by
    simpa [prefixWord, tailWord_2172036, baseEnd_2172036] using wordTrace_append hprefix tailTrace_2172036
  have hstable : (prefixWord ++ tailWord_2172036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172036).length < 2 ^ (prefixWord ++ tailWord_2172036).sum := by decide
  have hdescent : baseEnd_2172036 < baseStart_2172036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172094 : List Nat := [4, 2, 1, 1, 3, 1, 3, 1, 6]
def baseStart_2172094 : Nat := 118140960795 + 2172094 * 2 ^ 59
def prefixEnd_2172094 : Nat := 4983230072969 + 3 ^ 40 * 2172094 * 2
def baseEnd_2172094 : Nat := 247850721943806645763495

theorem tailTrace_2172094 : CollatzResearch.WordTrace tailWord_2172094 prefixEnd_2172094 247850721943806645763495 := by
  unfold tailWord_2172094
  simp only [CollatzResearch.WordTrace]
  refine ⟨9902847074110234620793417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52815184395254584644231557 9902847074110234620793417)
  ·
    refine ⟨7427135305582675965595063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9902847074110234620793417 7427135305582675965595063)
    ·
      refine ⟨11140702958374013948392595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7427135305582675965595063 11140702958374013948392595)
      ·
        refine ⟨16711054437561020922588893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11140702958374013948392595 16711054437561020922588893)
        ·
          refine ⟨6266645414085382845970835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16711054437561020922588893 6266645414085382845970835)
          ·
            refine ⟨9399968121128074268956253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6266645414085382845970835 9399968121128074268956253)
            ·
              refine ⟨3524988045423027850858595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9399968121128074268956253 3524988045423027850858595)
              ·
                refine ⟨5287482068134541776287893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3524988045423027850858595 5287482068134541776287893)
                ·
                  refine ⟨247850721943806645763495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5287482068134541776287893 247850721943806645763495)
                  ·
                    rfl

theorem cell22_2172094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_2172094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172094 prefixEnd_2172094 := by exact prefixLift 2172094
  have htrace : WordTrace (prefixWord ++ tailWord_2172094) baseStart_2172094 baseEnd_2172094 := by
    simpa [prefixWord, tailWord_2172094, baseEnd_2172094] using wordTrace_append hprefix tailTrace_2172094
  have hstable : (prefixWord ++ tailWord_2172094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172094).length < 2 ^ (prefixWord ++ tailWord_2172094).sum := by decide
  have hdescent : baseEnd_2172094 < baseStart_2172094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172154 : List Nat := [3, 1, 1, 1, 1, 4, 2, 3, 3, 3]
def baseStart_2172154 : Nat := 118140960795 + 2172154 * 2 ^ 59
def prefixEnd_2172154 : Nat := 4983230072969 + 3 ^ 40 * 2172154 * 2
def baseEnd_2172154 : Nat := 743572705057599780790301

theorem tailTrace_2172154 : CollatzResearch.WordTrace tailWord_2172154 prefixEnd_2172154 743572705057599780790301 := by
  unfold tailWord_2172154
  simp only [CollatzResearch.WordTrace]
  refine ⟨19806241243166126803382879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52816643315109671475687677 19806241243166126803382879)
  ·
    refine ⟨29709361864749190205074319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19806241243166126803382879 29709361864749190205074319)
    ·
      refine ⟨44564042797123785307611479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29709361864749190205074319 44564042797123785307611479)
      ·
        refine ⟨66846064195685677961417219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44564042797123785307611479 66846064195685677961417219)
        ·
          refine ⟨100269096293528516942125829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66846064195685677961417219 100269096293528516942125829)
          ·
            refine ⟨18800455555036596926648593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100269096293528516942125829 18800455555036596926648593)
            ·
              refine ⟨14100341666277447694986445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18800455555036596926648593 14100341666277447694986445)
              ·
                refine ⟨5287628124854042885619917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14100341666277447694986445 5287628124854042885619917)
                ·
                  refine ⟨1982860546820266082107469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5287628124854042885619917 1982860546820266082107469)
                  ·
                    refine ⟨743572705057599780790301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1982860546820266082107469 743572705057599780790301)
                    ·
                      rfl

theorem cell22_2172154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 3, 3].length) (baseStart_2172154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172154 prefixEnd_2172154 := by exact prefixLift 2172154
  have htrace : WordTrace (prefixWord ++ tailWord_2172154) baseStart_2172154 baseEnd_2172154 := by
    simpa [prefixWord, tailWord_2172154, baseEnd_2172154] using wordTrace_append hprefix tailTrace_2172154
  have hstable : (prefixWord ++ tailWord_2172154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172154).length < 2 ^ (prefixWord ++ tailWord_2172154).sum := by decide
  have hdescent : baseEnd_2172154 < baseStart_2172154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172156 : List Nat := [2, 2, 2, 1, 6, 1, 1, 7]
def baseStart_2172156 : Nat := 118140960795 + 2172156 * 2 ^ 59
def prefixEnd_2172156 : Nat := 4983230072969 + 3 ^ 40 * 2172156 * 2
def baseEnd_2172156 : Nat := 82619265522052493582255

theorem tailTrace_2172156 : CollatzResearch.WordTrace tailWord_2172156 prefixEnd_2172156 82619265522052493582255 := by
  unfold tailWord_2172156
  simp only [CollatzResearch.WordTrace]
  refine ⟨39612518959328630777552161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52816691945771507703402881 39612518959328630777552161)
  ·
    refine ⟨29709389219496473083164121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39612518959328630777552161 29709389219496473083164121)
    ·
      refine ⟨22282041914622354812373091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29709389219496473083164121 22282041914622354812373091)
      ·
        refine ⟨33423062871933532218559637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22282041914622354812373091 33423062871933532218559637)
        ·
          refine ⟨1566706072121884322744983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33423062871933532218559637 1566706072121884322744983)
          ·
            refine ⟨2350059108182826484117475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1566706072121884322744983 2350059108182826484117475)
            ·
              refine ⟨3525088662274239726176213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2350059108182826484117475 3525088662274239726176213)
              ·
                refine ⟨82619265522052493582255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3525088662274239726176213 82619265522052493582255)
                ·
                  rfl

theorem cell22_2172156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 7].length) (baseStart_2172156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172156 prefixEnd_2172156 := by exact prefixLift 2172156
  have htrace : WordTrace (prefixWord ++ tailWord_2172156) baseStart_2172156 baseEnd_2172156 := by
    simpa [prefixWord, tailWord_2172156, baseEnd_2172156] using wordTrace_append hprefix tailTrace_2172156
  have hstable : (prefixWord ++ tailWord_2172156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172156).length < 2 ^ (prefixWord ++ tailWord_2172156).sum := by decide
  have hdescent : baseEnd_2172156 < baseStart_2172156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172205 : List Nat := [1, 5, 3, 1, 1, 1, 2, 4, 1, 3]
def baseStart_2172205 : Nat := 118140960795 + 2172205 * 2 ^ 59
def prefixEnd_2172205 : Nat := 4983230072969 + 3 ^ 40 * 2172205 * 2
def baseEnd_2172205 : Nat := 743590163399852647765145

theorem tailTrace_2172205 : CollatzResearch.WordTrace tailWord_2172205 prefixEnd_2172205 743590163399852647765145 := by
  unfold tailWord_2172205
  simp only [CollatzResearch.WordTrace]
  refine ⟨79226825095479742923638069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52817883396986495282425379 79226825095479742923638069)
  ·
    refine ⟨7427514852701225899091069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79226825095479742923638069 7427514852701225899091069)
    ·
      refine ⟨2785318069762959712159151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7427514852701225899091069 2785318069762959712159151)
      ·
        refine ⟨4177977104644439568238727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2785318069762959712159151 4177977104644439568238727)
        ·
          refine ⟨6266965656966659352358091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4177977104644439568238727 6266965656966659352358091)
          ·
            refine ⟨9400448485449989028537137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6266965656966659352358091 9400448485449989028537137)
            ·
              refine ⟨7050336364087491771402853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9400448485449989028537137 7050336364087491771402853)
              ·
                refine ⟨1321938068266404707138035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7050336364087491771402853 1321938068266404707138035)
                ·
                  refine ⟨1982907102399607060707053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1321938068266404707138035 1982907102399607060707053)
                  ·
                    refine ⟨743590163399852647765145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1982907102399607060707053 743590163399852647765145)
                    ·
                      rfl

theorem cell22_2172205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_2172205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172205 prefixEnd_2172205 := by exact prefixLift 2172205
  have htrace : WordTrace (prefixWord ++ tailWord_2172205) baseStart_2172205 baseEnd_2172205 := by
    simpa [prefixWord, tailWord_2172205, baseEnd_2172205] using wordTrace_append hprefix tailTrace_2172205
  have hstable : (prefixWord ++ tailWord_2172205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172205).length < 2 ^ (prefixWord ++ tailWord_2172205).sum := by decide
  have hdescent : baseEnd_2172205 < baseStart_2172205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172231 : List Nat := [1, 1, 4, 1, 2, 4, 2, 2, 1, 4]
def baseStart_2172231 : Nat := 118140960795 + 2172231 * 2 ^ 59
def prefixEnd_2172231 : Nat := 4983230072969 + 3 ^ 40 * 2172231 * 2
def baseEnd_2172231 : Nat := 743599063731197246615065

theorem tailTrace_2172231 : CollatzResearch.WordTrace tailWord_2172231 prefixEnd_2172231 743599063731197246615065 := by
  unfold tailWord_2172231
  simp only [CollatzResearch.WordTrace]
  refine ⟨79227773393385549364084547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52818515595590366242723031 79227773393385549364084547)
  ·
    refine ⟨118841660090078324046126821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79227773393385549364084547 118841660090078324046126821)
    ·
      refine ⟨22282811266889685758648779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118841660090078324046126821 22282811266889685758648779)
      ·
        refine ⟨33424216900334528637973169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22282811266889685758648779 33424216900334528637973169)
        ·
          refine ⟨25068162675250896478479877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33424216900334528637973169 25068162675250896478479877)
          ·
            refine ⟨4700280501609543089714977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25068162675250896478479877 4700280501609543089714977)
            ·
              refine ⟨3525210376207157317286233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4700280501609543089714977 3525210376207157317286233)
              ·
                refine ⟨2643907782155367987964675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3525210376207157317286233 2643907782155367987964675)
                ·
                  refine ⟨3965861673233051981947013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2643907782155367987964675 3965861673233051981947013)
                  ·
                    refine ⟨743599063731197246615065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3965861673233051981947013 743599063731197246615065)
                    ·
                      rfl

theorem cell22_2172231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_2172231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172231 prefixEnd_2172231 := by exact prefixLift 2172231
  have htrace : WordTrace (prefixWord ++ tailWord_2172231) baseStart_2172231 baseEnd_2172231 := by
    simpa [prefixWord, tailWord_2172231, baseEnd_2172231] using wordTrace_append hprefix tailTrace_2172231
  have hstable : (prefixWord ++ tailWord_2172231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172231).length < 2 ^ (prefixWord ++ tailWord_2172231).sum := by decide
  have hdescent : baseEnd_2172231 < baseStart_2172231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172244 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_2172244 : Nat := 118140960795 + 2172244 * 2 ^ 59
def prefixEnd_2172244 : Nat := 4983230072969 + 3 ^ 40 * 2172244 * 2
def baseEnd_2172244 : Nat := 743603513896869546040025

theorem tailTrace_2172244 : CollatzResearch.WordTrace tailWord_2172244 prefixEnd_2172244 743603513896869546040025 := by
  unfold tailWord_2172244
  simp only [CollatzResearch.WordTrace]
  refine ⟨39614123771169226292153893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52818831694892301722871857 39614123771169226292153893)
  ·
    refine ⟨7427648207094229929778855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39614123771169226292153893 7427648207094229929778855)
    ·
      refine ⟨11141472310641344894668283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7427648207094229929778855 11141472310641344894668283)
      ·
        refine ⟨16712208465962017342002425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11141472310641344894668283 16712208465962017342002425)
        ·
          refine ⟨12534156349471513006501819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16712208465962017342002425 12534156349471513006501819)
          ·
            refine ⟨18801234524207269509752729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12534156349471513006501819 18801234524207269509752729)
            ·
              refine ⟨14100925893155452132314547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18801234524207269509752729 14100925893155452132314547)
              ·
                refine ⟨21151388839733178198471821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14100925893155452132314547 21151388839733178198471821)
                ·
                  refine ⟨7931770814899941824426933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21151388839733178198471821 7931770814899941824426933)
                  ·
                    refine ⟨743603513896869546040025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7931770814899941824426933 743603513896869546040025)
                    ·
                      rfl

theorem cell22_2172244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_2172244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172244 prefixEnd_2172244 := by exact prefixLift 2172244
  have htrace : WordTrace (prefixWord ++ tailWord_2172244) baseStart_2172244 baseEnd_2172244 := by
    simpa [prefixWord, tailWord_2172244, baseEnd_2172244] using wordTrace_append hprefix tailTrace_2172244
  have hstable : (prefixWord ++ tailWord_2172244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172244).length < 2 ^ (prefixWord ++ tailWord_2172244).sum := by decide
  have hdescent : baseEnd_2172244 < baseStart_2172244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172259 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 4, 4]
def baseStart_2172259 : Nat := 118140960795 + 2172259 * 2 ^ 59
def prefixEnd_2172259 : Nat := 4983230072969 + 3 ^ 40 * 2172259 * 2
def baseEnd_2172259 : Nat := 743608648703414506914979

theorem tailTrace_2172259 : CollatzResearch.WordTrace tailWord_2172259 prefixEnd_2172259 743608648703414506914979 := by
  unfold tailWord_2172259
  simp only [CollatzResearch.WordTrace]
  refine ⟨79228794637284110146103831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52819196424856073430735887 79228794637284110146103831)
  ·
    refine ⟨118843191955926165219155747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79228794637284110146103831 118843191955926165219155747)
    ·
      refine ⟨178264787933889247828733621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118843191955926165219155747 178264787933889247828733621)
      ·
        refine ⟨16712323868802116983943777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 178264787933889247828733621 16712323868802116983943777)
        ·
          refine ⟨12534242901601587737957833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16712323868802116983943777 12534242901601587737957833)
          ·
            refine ⟨9400682176201190803468375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12534242901601587737957833 9400682176201190803468375)
            ·
              refine ⟨14101023264301786205202563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9400682176201190803468375 14101023264301786205202563)
              ·
                refine ⟨21151534896452679307803845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14101023264301786205202563 21151534896452679307803845)
                ·
                  refine ⟨3965912793084877370213221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21151534896452679307803845 3965912793084877370213221)
                  ·
                    refine ⟨743608648703414506914979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3965912793084877370213221 743608648703414506914979)
                    ·
                      rfl

theorem cell22_2172259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 4, 4].length) (baseStart_2172259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172259 prefixEnd_2172259 := by exact prefixLift 2172259
  have htrace : WordTrace (prefixWord ++ tailWord_2172259) baseStart_2172259 baseEnd_2172259 := by
    simpa [prefixWord, tailWord_2172259, baseEnd_2172259] using wordTrace_append hprefix tailTrace_2172259
  have hstable : (prefixWord ++ tailWord_2172259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172259).length < 2 ^ (prefixWord ++ tailWord_2172259).sum := by decide
  have hdescent : baseEnd_2172259 < baseStart_2172259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172261 : List Nat := [1, 3, 1, 3, 1, 2, 2, 4, 2, 3]
def baseStart_2172261 : Nat := 118140960795 + 2172261 * 2 ^ 59
def prefixEnd_2172261 : Nat := 4983230072969 + 3 ^ 40 * 2172261 * 2
def baseEnd_2172261 : Nat := 743609333344287168364973

theorem tailTrace_2172261 : CollatzResearch.WordTrace tailWord_2172261 prefixEnd_2172261 743609333344287168364973 := by
  unfold tailWord_2172261
  simp only [CollatzResearch.WordTrace]
  refine ⟨79228867583276864487676637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52819245055517909658451091 79228867583276864487676637)
  ·
    refine ⟨29710825343728824182878739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79228867583276864487676637 29710825343728824182878739)
    ·
      refine ⟨44566238015593236274318109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29710825343728824182878739 44566238015593236274318109)
      ·
        refine ⟨16712339255847463602869291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44566238015593236274318109 16712339255847463602869291)
        ·
          refine ⟨25068508883771195404303937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16712339255847463602869291 25068508883771195404303937)
          ·
            refine ⟨18801381662828396553227953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25068508883771195404303937 18801381662828396553227953)
            ·
              refine ⟨14101036247121297414920965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18801381662828396553227953 14101036247121297414920965)
              ·
                refine ⟨2643944296335243265297681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14101036247121297414920965 2643944296335243265297681)
                ·
                  refine ⟨1982958222251432448973261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2643944296335243265297681 1982958222251432448973261)
                  ·
                    refine ⟨743609333344287168364973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1982958222251432448973261 743609333344287168364973)
                    ·
                      rfl

theorem cell22_2172261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 2, 3].length) (baseStart_2172261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172261 prefixEnd_2172261 := by exact prefixLift 2172261
  have htrace : WordTrace (prefixWord ++ tailWord_2172261) baseStart_2172261 baseEnd_2172261 := by
    simpa [prefixWord, tailWord_2172261, baseEnd_2172261] using wordTrace_append hprefix tailTrace_2172261
  have hstable : (prefixWord ++ tailWord_2172261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172261).length < 2 ^ (prefixWord ++ tailWord_2172261).sum := by decide
  have hdescent : baseEnd_2172261 < baseStart_2172261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172263 : List Nat := [1, 1, 5, 1, 5, 1, 1, 1, 6]
def baseStart_2172263 : Nat := 118140960795 + 2172263 * 2 ^ 59
def prefixEnd_2172263 : Nat := 4983230072969 + 3 ^ 40 * 2172263 * 2
def baseEnd_2172263 : Nat := 247870005995053276604989

theorem tailTrace_2172263 : CollatzResearch.WordTrace tailWord_2172263 prefixEnd_2172263 247870005995053276604989 := by
  unfold tailWord_2172263
  simp only [CollatzResearch.WordTrace]
  refine ⟨79228940529269618829249443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52819293686179745886166295 79228940529269618829249443)
  ·
    refine ⟨118843410793904428243874165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79228940529269618829249443 118843410793904428243874165)
    ·
      refine ⟨11141569761928540147863203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118843410793904428243874165 11141569761928540147863203)
      ·
        refine ⟨16712354642892810221794805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11141569761928540147863203 16712354642892810221794805)
        ·
          refine ⟨1566783247771200958293263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16712354642892810221794805 1566783247771200958293263)
          ·
            refine ⟨2350174871656801437439895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1566783247771200958293263 2350174871656801437439895)
            ·
              refine ⟨3525262307485202156159843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2350174871656801437439895 3525262307485202156159843)
              ·
                refine ⟨5287893461227803234239765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3525262307485202156159843 5287893461227803234239765)
                ·
                  refine ⟨247870005995053276604989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5287893461227803234239765 247870005995053276604989)
                  ·
                    rfl

theorem cell22_2172263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 6].length) (baseStart_2172263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172263 prefixEnd_2172263 := by exact prefixLift 2172263
  have htrace : WordTrace (prefixWord ++ tailWord_2172263) baseStart_2172263 baseEnd_2172263 := by
    simpa [prefixWord, tailWord_2172263, baseEnd_2172263] using wordTrace_append hprefix tailTrace_2172263
  have hstable : (prefixWord ++ tailWord_2172263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172263).length < 2 ^ (prefixWord ++ tailWord_2172263).sum := by decide
  have hdescent : baseEnd_2172263 < baseStart_2172263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172274 : List Nat := [3, 2, 1, 2, 1, 2, 4, 7]
def baseStart_2172274 : Nat := 118140960795 + 2172274 * 2 ^ 59
def prefixEnd_2172274 : Nat := 4983230072969 + 3 ^ 40 * 2172274 * 2
def baseEnd_2172274 : Nat := 82623753723328829754437

theorem tailTrace_2172274 : CollatzResearch.WordTrace tailWord_2172274 prefixEnd_2172274 82623753723328829754437 := by
  unfold tailWord_2172274
  simp only [CollatzResearch.WordTrace]
  refine ⟨19807335433057441926974969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52819561154819845138599917 19807335433057441926974969)
  ·
    refine ⟨14855501574793081445231227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19807335433057441926974969 14855501574793081445231227)
    ·
      refine ⟨22283252362189622167846841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14855501574793081445231227 22283252362189622167846841)
      ·
        refine ⟨16712439271642216625885131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22283252362189622167846841 16712439271642216625885131)
        ·
          refine ⟨25068658907463324938827697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16712439271642216625885131 25068658907463324938827697)
          ·
            refine ⟨18801494180597493704120773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25068658907463324938827697 18801494180597493704120773)
            ·
              refine ⟨3525280158862030069522645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18801494180597493704120773 3525280158862030069522645)
              ·
                refine ⟨82623753723328829754437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3525280158862030069522645 82623753723328829754437)
                ·
                  rfl

theorem cell22_2172274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 7].length) (baseStart_2172274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172274 prefixEnd_2172274 := by exact prefixLift 2172274
  have htrace : WordTrace (prefixWord ++ tailWord_2172274) baseStart_2172274 baseEnd_2172274 := by
    simpa [prefixWord, tailWord_2172274, baseEnd_2172274] using wordTrace_append hprefix tailTrace_2172274
  have hstable : (prefixWord ++ tailWord_2172274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172274).length < 2 ^ (prefixWord ++ tailWord_2172274).sum := by decide
  have hdescent : baseEnd_2172274 < baseStart_2172274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172323 : List Nat := [1, 1, 1, 4, 1, 3, 3, 4, 1, 3]
def baseStart_2172323 : Nat := 118140960795 + 2172323 * 2 ^ 59
def prefixEnd_2172323 : Nat := 4983230072969 + 3 ^ 40 * 2172323 * 2
def baseEnd_2172323 : Nat := 743630557211339673314783

theorem tailTrace_2172323 : CollatzResearch.WordTrace tailWord_2172323 prefixEnd_2172323 743630557211339673314783 := by
  unfold tailWord_2172323
  simp only [CollatzResearch.WordTrace]
  refine ⟨79231128909052249076433623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52820752606034832717622415 79231128909052249076433623)
  ·
    refine ⟨118846693363578373614650435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79231128909052249076433623 118846693363578373614650435)
    ·
      refine ⟨178270040045367560421975653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118846693363578373614650435 178270040045367560421975653)
      ·
        refine ⟨33425632508506417579120435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 178270040045367560421975653 33425632508506417579120435)
        ·
          refine ⟨50138448762759626368680653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33425632508506417579120435 50138448762759626368680653)
          ·
            refine ⟨18801918286034859888255245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50138448762759626368680653 18801918286034859888255245)
            ·
              refine ⟨7050719357263072458095717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18801918286034859888255245 7050719357263072458095717)
              ·
                refine ⟨1322009879486826085892947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7050719357263072458095717 1322009879486826085892947)
                ·
                  refine ⟨1983014819230239128839421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1322009879486826085892947 1983014819230239128839421)
                  ·
                    refine ⟨743630557211339673314783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1983014819230239128839421 743630557211339673314783)
                    ·
                      rfl

theorem cell22_2172323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 4, 1, 3].length) (baseStart_2172323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172323 prefixEnd_2172323 := by exact prefixLift 2172323
  have htrace : WordTrace (prefixWord ++ tailWord_2172323) baseStart_2172323 baseEnd_2172323 := by
    simpa [prefixWord, tailWord_2172323, baseEnd_2172323] using wordTrace_append hprefix tailTrace_2172323
  have hstable : (prefixWord ++ tailWord_2172323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172323).length < 2 ^ (prefixWord ++ tailWord_2172323).sum := by decide
  have hdescent : baseEnd_2172323 < baseStart_2172323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172381 : List Nat := [1, 4, 3, 1, 1, 2, 1, 3, 6]
def baseStart_2172381 : Nat := 118140960795 + 2172381 * 2 ^ 59
def prefixEnd_2172381 : Nat := 4983230072969 + 3 ^ 40 * 2172381 * 2
def baseEnd_2172381 : Nat := 247883470598882285121535

theorem tailTrace_2172381 : CollatzResearch.WordTrace tailWord_2172381 prefixEnd_2172381 247883470598882285121535 := by
  unfold tailWord_2172381
  simp only [CollatzResearch.WordTrace]
  refine ⟨79233244342842124982044997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52822162895228083321363331 79233244342842124982044997)
  ·
    refine ⟨14856233314282898434133437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79233244342842124982044997 14856233314282898434133437)
    ·
      refine ⟨5571087492856086912800039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14856233314282898434133437 5571087492856086912800039)
      ·
        refine ⟨8356631239284130369200059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5571087492856086912800039 8356631239284130369200059)
        ·
          refine ⟨12534946858926195553800089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8356631239284130369200059 12534946858926195553800089)
          ·
            refine ⟨9401210144194646665350067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12534946858926195553800089 9401210144194646665350067)
            ·
              refine ⟨14101815216291969998025101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9401210144194646665350067 14101815216291969998025101)
              ·
                refine ⟨5288180706109488749259413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14101815216291969998025101 5288180706109488749259413)
                ·
                  refine ⟨247883470598882285121535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5288180706109488749259413 247883470598882285121535)
                  ·
                    rfl

theorem cell22_2172381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_2172381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172381 prefixEnd_2172381 := by exact prefixLift 2172381
  have htrace : WordTrace (prefixWord ++ tailWord_2172381) baseStart_2172381 baseEnd_2172381 := by
    simpa [prefixWord, tailWord_2172381, baseEnd_2172381] using wordTrace_append hprefix tailTrace_2172381
  have hstable : (prefixWord ++ tailWord_2172381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172381).length < 2 ^ (prefixWord ++ tailWord_2172381).sum := by decide
  have hdescent : baseEnd_2172381 < baseStart_2172381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172426 : List Nat := [3, 1, 2, 2, 2, 4, 8]
def baseStart_2172426 : Nat := 118140960795 + 2172426 * 2 ^ 59
def prefixEnd_2172426 : Nat := 4983230072969 + 3 ^ 40 * 2172426 * 2
def baseEnd_2172426 : Nat := 27543178378380805110721

theorem tailTrace_2172426 : CollatzResearch.WordTrace tailWord_2172426 prefixEnd_2172426 27543178378380805110721 := by
  unfold tailWord_2172426
  simp only [CollatzResearch.WordTrace]
  refine ⟨19808721406919774416858283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52823257085119398444955421 19808721406919774416858283)
  ·
    refine ⟨29713082110379661625287425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19808721406919774416858283 29713082110379661625287425)
    ·
      refine ⟨22284811582784746218965569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29713082110379661625287425 22284811582784746218965569)
      ·
        refine ⟨16713608687088559664224177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22284811582784746218965569 16713608687088559664224177)
        ·
          refine ⟨12535206515316419748168133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16713608687088559664224177 12535206515316419748168133)
          ·
            refine ⟨2350351221621828702781525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12535206515316419748168133 2350351221621828702781525)
            ·
              refine ⟨27543178378380805110721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2350351221621828702781525 27543178378380805110721)
              ·
                rfl

theorem cell22_2172426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 8].length) (baseStart_2172426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172426 prefixEnd_2172426 := by exact prefixLift 2172426
  have htrace : WordTrace (prefixWord ++ tailWord_2172426) baseStart_2172426 baseEnd_2172426 := by
    simpa [prefixWord, tailWord_2172426, baseEnd_2172426] using wordTrace_append hprefix tailTrace_2172426
  have hstable : (prefixWord ++ tailWord_2172426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172426).length < 2 ^ (prefixWord ++ tailWord_2172426).sum := by decide
  have hdescent : baseEnd_2172426 < baseStart_2172426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172428 : List Nat := [2, 2, 1, 2, 5, 1, 1, 2, 2, 4]
def baseStart_2172428 : Nat := 118140960795 + 2172428 * 2 ^ 59
def prefixEnd_2172428 : Nat := 4983230072969 + 3 ^ 40 * 2172428 * 2
def baseEnd_2172428 : Nat := 743666500857154399439461

theorem tailTrace_2172428 : CollatzResearch.WordTrace tailWord_2172428 prefixEnd_2172428 743666500857154399439461 := by
  unfold tailWord_2172428
  simp only [CollatzResearch.WordTrace]
  refine ⟨39617479286835926004502969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52823305715781234672670625 39617479286835926004502969)
  ·
    refine ⟨29713109465126944503377227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39617479286835926004502969 29713109465126944503377227)
    ·
      refine ⟨44569664197690416755065841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29713109465126944503377227 44569664197690416755065841)
      ·
        refine ⟨33427248148267812566299381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44569664197690416755065841 33427248148267812566299381)
        ·
          refine ⟨3133804513900107428090567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33427248148267812566299381 3133804513900107428090567)
          ·
            refine ⟨4700706770850161142135851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3133804513900107428090567 4700706770850161142135851)
            ·
              refine ⟨7051060156275241713203777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4700706770850161142135851 7051060156275241713203777)
              ·
                refine ⟨5288295117206431284902833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7051060156275241713203777 5288295117206431284902833)
                ·
                  refine ⟨3966221337904823463677125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5288295117206431284902833 3966221337904823463677125)
                  ·
                    refine ⟨743666500857154399439461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3966221337904823463677125 743666500857154399439461)
                    ·
                      rfl

theorem cell22_2172428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_2172428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172428 prefixEnd_2172428 := by exact prefixLift 2172428
  have htrace : WordTrace (prefixWord ++ tailWord_2172428) baseStart_2172428 baseEnd_2172428 := by
    simpa [prefixWord, tailWord_2172428, baseEnd_2172428] using wordTrace_append hprefix tailTrace_2172428
  have hstable : (prefixWord ++ tailWord_2172428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172428).length < 2 ^ (prefixWord ++ tailWord_2172428).sum := by decide
  have hdescent : baseEnd_2172428 < baseStart_2172428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172458 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 5, 3]
def baseStart_2172458 : Nat := 118140960795 + 2172458 * 2 ^ 59
def prefixEnd_2172458 : Nat := 4983230072969 + 3 ^ 40 * 2172458 * 2
def baseEnd_2172458 : Nat := 743676770470244321189369

theorem tailTrace_2172458 : CollatzResearch.WordTrace tailWord_2172458 prefixEnd_2172458 743676770470244321189369 := by
  unfold tailWord_2172458
  simp only [CollatzResearch.WordTrace]
  refine ⟨19809013190890791783149507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52824035175708778088398685 19809013190890791783149507)
  ·
    refine ⟨29713519786336187674724261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19809013190890791783149507 29713519786336187674724261)
    ·
      refine ⟨5571284959938035189010799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29713519786336187674724261 5571284959938035189010799)
      ·
        refine ⟨8356927439907052783516199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5571284959938035189010799 8356927439907052783516199)
        ·
          refine ⟨12535391159860579175274299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8356927439907052783516199 12535391159860579175274299)
          ·
            refine ⟨18803086739790868762911449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12535391159860579175274299 18803086739790868762911449)
            ·
              refine ⟨14102315054843151572183587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18803086739790868762911449 14102315054843151572183587)
              ·
                refine ⟨21153472582264727358275381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14102315054843151572183587 21153472582264727358275381)
                ·
                  refine ⟨1983138054587318189838317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21153472582264727358275381 1983138054587318189838317)
                  ·
                    refine ⟨743676770470244321189369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1983138054587318189838317 743676770470244321189369)
                    ·
                      rfl

theorem cell22_2172458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_2172458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172458 prefixEnd_2172458 := by exact prefixLift 2172458
  have htrace : WordTrace (prefixWord ++ tailWord_2172458) baseStart_2172458 baseEnd_2172458 := by
    simpa [prefixWord, tailWord_2172458, baseEnd_2172458] using wordTrace_append hprefix tailTrace_2172458
  have hstable : (prefixWord ++ tailWord_2172458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172458).length < 2 ^ (prefixWord ++ tailWord_2172458).sum := by decide
  have hdescent : baseEnd_2172458 < baseStart_2172458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172492 : List Nat := [2, 2, 1, 3, 1, 3, 4, 2, 1, 3]
def baseStart_2172492 : Nat := 118140960795 + 2172492 * 2 ^ 59
def prefixEnd_2172492 : Nat := 4983230072969 + 3 ^ 40 * 2172492 * 2
def baseEnd_2172492 : Nat := 743688409365079565839265

theorem tailTrace_2172492 : CollatzResearch.WordTrace tailWord_2172492 prefixEnd_2172492 743688409365079565839265 := by
  unfold tailWord_2172492
  simp only [CollatzResearch.WordTrace]
  refine ⟨39618646422719995469667865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52824861896959993959557153 39618646422719995469667865)
  ·
    refine ⟨29713984817039996602250899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39618646422719995469667865 29713984817039996602250899)
    ·
      refine ⟨44570977225559994903376349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29713984817039996602250899 44570977225559994903376349)
      ·
        refine ⟨16714116459584998088766131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44570977225559994903376349 16714116459584998088766131)
        ·
          refine ⟨25071174689377497133149197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16714116459584998088766131 25071174689377497133149197)
          ·
            refine ⟨9401690508516561424930949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25071174689377497133149197 9401690508516561424930949)
            ·
              refine ⟨1762816970346855267174553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9401690508516561424930949 1762816970346855267174553)
              ·
                refine ⟨1322112727760141450380915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1762816970346855267174553 1322112727760141450380915)
                ·
                  refine ⟨1983169091640212175571373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1322112727760141450380915 1983169091640212175571373)
                  ·
                    refine ⟨743688409365079565839265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1983169091640212175571373 743688409365079565839265)
                    ·
                      rfl

theorem cell22_2172492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2, 1, 3].length) (baseStart_2172492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172492 prefixEnd_2172492 := by exact prefixLift 2172492
  have htrace : WordTrace (prefixWord ++ tailWord_2172492) baseStart_2172492 baseEnd_2172492 := by
    simpa [prefixWord, tailWord_2172492, baseEnd_2172492] using wordTrace_append hprefix tailTrace_2172492
  have hstable : (prefixWord ++ tailWord_2172492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172492).length < 2 ^ (prefixWord ++ tailWord_2172492).sum := by decide
  have hdescent : baseEnd_2172492 < baseStart_2172492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172516 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 8]
def baseStart_2172516 : Nat := 118140960795 + 2172516 * 2 ^ 59
def prefixEnd_2172516 : Nat := 4983230072969 + 3 ^ 40 * 2172516 * 2
def baseEnd_2172516 : Nat := 247898875018517167746397

theorem tailTrace_2172516 : CollatzResearch.WordTrace tailWord_2172516 prefixEnd_2172516 247898875018517167746397 := by
  unfold tailWord_2172516
  simp only [CollatzResearch.WordTrace]
  refine ⟨39619084098676521519104701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52825445464902028692139601 39619084098676521519104701)
  ·
    refine ⟨14857156537003695569664263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39619084098676521519104701 14857156537003695569664263)
    ·
      refine ⟨22285734805505543354496395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14857156537003695569664263 22285734805505543354496395)
      ·
        refine ⟨33428602208258315031744593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22285734805505543354496395 33428602208258315031744593)
        ·
          refine ⟨25071451656193736273808445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33428602208258315031744593 25071451656193736273808445)
          ·
            refine ⟨9401794371072651102678167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25071451656193736273808445 9401794371072651102678167)
            ·
              refine ⟨14102691556608976654017251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9401794371072651102678167 14102691556608976654017251)
              ·
                refine ⟨21154037334913464981025877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14102691556608976654017251 21154037334913464981025877)
                ·
                  refine ⟨247898875018517167746397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21154037334913464981025877 247898875018517167746397)
                  ·
                    rfl

theorem cell22_2172516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_2172516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172516 prefixEnd_2172516 := by exact prefixLift 2172516
  have htrace : WordTrace (prefixWord ++ tailWord_2172516) baseStart_2172516 baseEnd_2172516 := by
    simpa [prefixWord, tailWord_2172516, baseEnd_2172516] using wordTrace_append hprefix tailTrace_2172516
  have hstable : (prefixWord ++ tailWord_2172516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172516).length < 2 ^ (prefixWord ++ tailWord_2172516).sum := by decide
  have hdescent : baseEnd_2172516 < baseStart_2172516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172668 : List Nat := [2, 2, 2, 1, 3, 1, 2, 3, 6]
def baseStart_2172668 : Nat := 118140960795 + 2172668 * 2 ^ 59
def prefixEnd_2172668 : Nat := 4983230072969 + 3 ^ 40 * 2172668 * 2
def baseEnd_2172668 : Nat := 247916219253957924479575

theorem tailTrace_2172668 : CollatzResearch.WordTrace tailWord_2172668 prefixEnd_2172668 247916219253957924479575 := by
  unfold tailWord_2172668
  simp only [CollatzResearch.WordTrace]
  refine ⟨39621856046401186498871329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52829141395201581998495105 39621856046401186498871329)
  ·
    refine ⟨29716392034800889874153497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39621856046401186498871329 29716392034800889874153497)
    ·
      refine ⟨22287294026100667405615123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29716392034800889874153497 22287294026100667405615123)
      ·
        refine ⟨33430941039151001108422685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22287294026100667405615123 33430941039151001108422685)
        ·
          refine ⟨12536602889681625415658507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33430941039151001108422685 12536602889681625415658507)
          ·
            refine ⟨18804904334522438123487761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12536602889681625415658507 18804904334522438123487761)
            ·
              refine ⟨14103678250891828592615821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18804904334522438123487761 14103678250891828592615821)
              ·
                refine ⟨5288879344084435722230933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14103678250891828592615821 5288879344084435722230933)
                ·
                  refine ⟨247916219253957924479575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5288879344084435722230933 247916219253957924479575)
                  ·
                    rfl

theorem cell22_2172668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 6].length) (baseStart_2172668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172668 prefixEnd_2172668 := by exact prefixLift 2172668
  have htrace : WordTrace (prefixWord ++ tailWord_2172668) baseStart_2172668 baseEnd_2172668 := by
    simpa [prefixWord, tailWord_2172668, baseEnd_2172668] using wordTrace_append hprefix tailTrace_2172668
  have hstable : (prefixWord ++ tailWord_2172668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172668).length < 2 ^ (prefixWord ++ tailWord_2172668).sum := by decide
  have hdescent : baseEnd_2172668 < baseStart_2172668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172683 : List Nat := [1, 1, 1, 1, 5, 1, 3, 3, 1, 5]
def baseStart_2172683 : Nat := 118140960795 + 2172683 * 2 ^ 59
def prefixEnd_2172683 : Nat := 4983230072969 + 3 ^ 40 * 2172683 * 2
def baseEnd_2172683 : Nat := 743753792568418734313679

theorem tailTrace_2172683 : CollatzResearch.WordTrace tailWord_2172683 prefixEnd_2172683 743753792568418734313679 := by
  unfold tailWord_2172683
  simp only [CollatzResearch.WordTrace]
  refine ⟨79244259187748030559538703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52829506125165353706359135 79244259187748030559538703)
  ·
    refine ⟨118866388781622045839308055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79244259187748030559538703 118866388781622045839308055)
    ·
      refine ⟨178299583172433068758962083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118866388781622045839308055 178299583172433068758962083)
      ·
        refine ⟨267449374758649603138443125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178299583172433068758962083 267449374758649603138443125)
        ·
          refine ⟨25073378883623400294229043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 267449374758649603138443125 25073378883623400294229043)
          ·
            refine ⟨37610068325435100441343565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25073378883623400294229043 37610068325435100441343565)
            ·
              refine ⟨14103775622038162665503837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37610068325435100441343565 14103775622038162665503837)
              ·
                refine ⟨5288915858264310999563939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14103775622038162665503837 5288915858264310999563939)
                ·
                  refine ⟨7933373787396466499345909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5288915858264310999563939 7933373787396466499345909)
                  ·
                    refine ⟨743753792568418734313679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7933373787396466499345909 743753792568418734313679)
                    ·
                      rfl

theorem cell22_2172683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 1, 5].length) (baseStart_2172683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172683 prefixEnd_2172683 := by exact prefixLift 2172683
  have htrace : WordTrace (prefixWord ++ tailWord_2172683) baseStart_2172683 baseEnd_2172683 := by
    simpa [prefixWord, tailWord_2172683, baseEnd_2172683] using wordTrace_append hprefix tailTrace_2172683
  have hstable : (prefixWord ++ tailWord_2172683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172683).length < 2 ^ (prefixWord ++ tailWord_2172683).sum := by decide
  have hdescent : baseEnd_2172683 < baseStart_2172683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172700 : List Nat := [2, 2, 3, 1, 1, 2, 2, 2, 4, 3]
def baseStart_2172700 : Nat := 118140960795 + 2172700 * 2 ^ 59
def prefixEnd_2172700 : Nat := 4983230072969 + 3 ^ 40 * 2172700 * 2
def baseEnd_2172700 : Nat := 743759612015836356638627

theorem tailTrace_2172700 : CollatzResearch.WordTrace tailWord_2172700 prefixEnd_2172700 743759612015836356638627 := by
  unfold tailWord_2172700
  simp only [CollatzResearch.WordTrace]
  refine ⟨39622439614343221231453777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52829919485790961641938369 39622439614343221231453777)
  ·
    refine ⟨29716829710757415923590333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39622439614343221231453777 29716829710757415923590333)
    ·
      refine ⟨11143811141534030971346375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29716829710757415923590333 11143811141534030971346375)
      ·
        refine ⟨16715716712301046457019563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11143811141534030971346375 16715716712301046457019563)
        ·
          refine ⟨25073575068451569685529345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16715716712301046457019563 25073575068451569685529345)
          ·
            refine ⟨18805181301338677264147009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25073575068451569685529345 18805181301338677264147009)
            ·
              refine ⟨14103885976004007948110257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18805181301338677264147009 14103885976004007948110257)
              ·
                refine ⟨10577914482003005961082693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14103885976004007948110257 10577914482003005961082693)
                ·
                  refine ⟨1983358965375563617703005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10577914482003005961082693 1983358965375563617703005)
                  ·
                    refine ⟨743759612015836356638627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1983358965375563617703005 743759612015836356638627)
                    ·
                      rfl

theorem cell22_2172700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_2172700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172700 prefixEnd_2172700 := by exact prefixLift 2172700
  have htrace : WordTrace (prefixWord ++ tailWord_2172700) baseStart_2172700 baseEnd_2172700 := by
    simpa [prefixWord, tailWord_2172700, baseEnd_2172700] using wordTrace_append hprefix tailTrace_2172700
  have hstable : (prefixWord ++ tailWord_2172700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172700).length < 2 ^ (prefixWord ++ tailWord_2172700).sum := by decide
  have hdescent : baseEnd_2172700 < baseStart_2172700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172743 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 2, 6]
def baseStart_2172743 : Nat := 118140960795 + 2172743 * 2 ^ 59
def prefixEnd_2172743 : Nat := 4983230072969 + 3 ^ 40 * 2172743 * 2
def baseEnd_2172743 : Nat := 743774331794598577813495

theorem tailTrace_2172743 : CollatzResearch.WordTrace tailWord_2172743 prefixEnd_2172743 743774331794598577813495 := by
  unfold tailWord_2172743
  simp only [CollatzResearch.WordTrace]
  refine ⟨79246447567530660806722883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52830965045020440537815255 79246447567530660806722883)
  ·
    refine ⟨118869671351295991210084325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79246447567530660806722883 118869671351295991210084325)
    ·
      refine ⟨22288063378367998351890811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118869671351295991210084325 22288063378367998351890811)
      ·
        refine ⟨33432095067551997527836217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22288063378367998351890811 33432095067551997527836217)
        ·
          refine ⟨25074071300663998145877163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33432095067551997527836217 25074071300663998145877163)
          ·
            refine ⟨37611106950995997218815745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25074071300663998145877163 37611106950995997218815745)
            ·
              refine ⟨28208330213246997914111809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37611106950995997218815745 28208330213246997914111809)
              ·
                refine ⟨21156247659935248435583857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28208330213246997914111809 21156247659935248435583857)
                ·
                  refine ⟨15867185744951436326687893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21156247659935248435583857 15867185744951436326687893)
                  ·
                    refine ⟨743774331794598577813495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15867185744951436326687893 743774331794598577813495)
                    ·
                      rfl

theorem cell22_2172743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_2172743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172743 prefixEnd_2172743 := by exact prefixLift 2172743
  have htrace : WordTrace (prefixWord ++ tailWord_2172743) baseStart_2172743 baseEnd_2172743 := by
    simpa [prefixWord, tailWord_2172743, baseEnd_2172743] using wordTrace_append hprefix tailTrace_2172743
  have hstable : (prefixWord ++ tailWord_2172743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172743).length < 2 ^ (prefixWord ++ tailWord_2172743).sum := by decide
  have hdescent : baseEnd_2172743 < baseStart_2172743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172745 : List Nat := [1, 2, 1, 1, 2, 4, 1, 4, 3, 3]
def baseStart_2172745 : Nat := 118140960795 + 2172745 * 2 ^ 59
def prefixEnd_2172745 : Nat := 4983230072969 + 3 ^ 40 * 2172745 * 2
def baseEnd_2172745 : Nat := 743775016435471239263489

theorem tailTrace_2172745 : CollatzResearch.WordTrace tailWord_2172745 prefixEnd_2172745 743775016435471239263489 := by
  unfold tailWord_2172745
  simp only [CollatzResearch.WordTrace]
  refine ⟨79246520513523415148295689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52831013675682276765530459 79246520513523415148295689)
  ·
    refine ⟨59434890385142561361221767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79246520513523415148295689 59434890385142561361221767)
    ·
      refine ⟨89152335577713842041832651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59434890385142561361221767 89152335577713842041832651)
      ·
        refine ⟨133728503366570763062748977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89152335577713842041832651 133728503366570763062748977)
        ·
          refine ⟨100296377524928072297061733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133728503366570763062748977 100296377524928072297061733)
          ·
            refine ⟨18805570785924013555699075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100296377524928072297061733 18805570785924013555699075)
            ·
              refine ⟨28208356178886020333548613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18805570785924013555699075 28208356178886020333548613)
              ·
                refine ⟨5289066783541128812540365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28208356178886020333548613 5289066783541128812540365)
                ·
                  refine ⟨1983400043827923304702637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5289066783541128812540365 1983400043827923304702637)
                  ·
                    refine ⟨743775016435471239263489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1983400043827923304702637 743775016435471239263489)
                    ·
                      rfl

theorem cell22_2172745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 3, 3].length) (baseStart_2172745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172745 prefixEnd_2172745 := by exact prefixLift 2172745
  have htrace : WordTrace (prefixWord ++ tailWord_2172745) baseStart_2172745 baseEnd_2172745 := by
    simpa [prefixWord, tailWord_2172745, baseEnd_2172745] using wordTrace_append hprefix tailTrace_2172745
  have hstable : (prefixWord ++ tailWord_2172745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172745).length < 2 ^ (prefixWord ++ tailWord_2172745).sum := by decide
  have hdescent : baseEnd_2172745 < baseStart_2172745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172775 : List Nat := [1, 1, 5, 1, 2, 1, 2, 4, 5]
def baseStart_2172775 : Nat := 118140960795 + 2172775 * 2 ^ 59
def prefixEnd_2172775 : Nat := 4983230072969 + 3 ^ 40 * 2172775 * 2
def baseEnd_2172775 : Nat := 247928428682853720337799

theorem tailTrace_2172775 : CollatzResearch.WordTrace tailWord_2172775 prefixEnd_2172775 247928428682853720337799 := by
  unfold tailWord_2172775
  simp only [CollatzResearch.WordTrace]
  refine ⟨79247614703414730271887779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52831743135609820181258519 79247614703414730271887779)
  ·
    refine ⟨118871422055122095407831669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79247614703414730271887779 118871422055122095407831669)
    ·
      refine ⟨11144195817667696444484219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118871422055122095407831669 11144195817667696444484219)
      ·
        refine ⟨16716293726501544666726329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11144195817667696444484219 16716293726501544666726329)
        ·
          refine ⟨12537220294876158500044747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16716293726501544666726329 12537220294876158500044747)
          ·
            refine ⟨18805830442314237750067121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12537220294876158500044747 18805830442314237750067121)
            ·
              refine ⟨14104372831735678312550341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18805830442314237750067121 14104372831735678312550341)
              ·
                refine ⟨2644569905950439683603189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14104372831735678312550341 2644569905950439683603189)
                ·
                  refine ⟨247928428682853720337799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2644569905950439683603189 247928428682853720337799)
                  ·
                    rfl

theorem cell22_2172775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 5].length) (baseStart_2172775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172775 prefixEnd_2172775 := by exact prefixLift 2172775
  have htrace : WordTrace (prefixWord ++ tailWord_2172775) baseStart_2172775 baseEnd_2172775 := by
    simpa [prefixWord, tailWord_2172775, baseEnd_2172775] using wordTrace_append hprefix tailTrace_2172775
  have hstable : (prefixWord ++ tailWord_2172775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172775).length < 2 ^ (prefixWord ++ tailWord_2172775).sum := by decide
  have hdescent : baseEnd_2172775 < baseStart_2172775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172805 : List Nat := [1, 3, 1, 1, 3, 2, 3, 1, 3, 4]
def baseStart_2172805 : Nat := 118140960795 + 2172805 * 2 ^ 59
def prefixEnd_2172805 : Nat := 4983230072969 + 3 ^ 40 * 2172805 * 2
def baseEnd_2172805 : Nat := 743795555661651082763305

theorem tailTrace_2172805 : CollatzResearch.WordTrace tailWord_2172805 prefixEnd_2172805 743795555661651082763305 := by
  unfold tailWord_2172805
  simp only [CollatzResearch.WordTrace]
  refine ⟨79248708893306045395479869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52832472595537363596986579 79248708893306045395479869)
  ·
    refine ⟨29718265834989767023304951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79248708893306045395479869 29718265834989767023304951)
    ·
      refine ⟨44577398752484650534957427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29718265834989767023304951 44577398752484650534957427)
      ·
        refine ⟨66866098128726975802436141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44577398752484650534957427 66866098128726975802436141)
        ·
          refine ⟨25074786798272615925913553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66866098128726975802436141 25074786798272615925913553)
          ·
            refine ⟨18806090098704461944435165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25074786798272615925913553 18806090098704461944435165)
            ·
              refine ⟨7052283787014173229163187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18806090098704461944435165 7052283787014173229163187)
              ·
                refine ⟨10578425680521259843744781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7052283787014173229163187 10578425680521259843744781)
                ·
                  refine ⟨3966909630195472441404293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10578425680521259843744781 3966909630195472441404293)
                  ·
                    refine ⟨743795555661651082763305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3966909630195472441404293 743795555661651082763305)
                    ·
                      rfl

theorem cell22_2172805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_2172805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172805 prefixEnd_2172805 := by exact prefixLift 2172805
  have htrace : WordTrace (prefixWord ++ tailWord_2172805) baseStart_2172805 baseEnd_2172805 := by
    simpa [prefixWord, tailWord_2172805, baseEnd_2172805] using wordTrace_append hprefix tailTrace_2172805
  have hstable : (prefixWord ++ tailWord_2172805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172805).length < 2 ^ (prefixWord ++ tailWord_2172805).sum := by decide
  have hdescent : baseEnd_2172805 < baseStart_2172805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172850 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 4, 4]
def baseStart_2172850 : Nat := 118140960795 + 2172850 * 2 ^ 59
def prefixEnd_2172850 : Nat := 4983230072969 + 3 ^ 40 * 2172850 * 2
def baseEnd_2172850 : Nat := 743810960081285965388167

theorem tailTrace_2172850 : CollatzResearch.WordTrace tailWord_2172850 prefixEnd_2172850 743810960081285965388167 := by
  unfold tailWord_2172850
  simp only [CollatzResearch.WordTrace]
  refine ⟨19812587544535754520217001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52833566785428678720578669 19812587544535754520217001)
  ·
    refine ⟨14859440658401815890162751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19812587544535754520217001 14859440658401815890162751)
    ·
      refine ⟨22289160987602723835244127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14859440658401815890162751 22289160987602723835244127)
      ·
        refine ⟨33433741481404085752866191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22289160987602723835244127 33433741481404085752866191)
        ·
          refine ⟨50150612222106128629299287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33433741481404085752866191 50150612222106128629299287)
          ·
            refine ⟨75225918333159192943948931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50150612222106128629299287 75225918333159192943948931)
            ·
              refine ⟨112838877499738789415923397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75225918333159192943948931 112838877499738789415923397)
              ·
                refine ⟨21157289531201023015485637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112838877499738789415923397 21157289531201023015485637)
                ·
                  refine ⟨3966991787100191815403557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21157289531201023015485637 3966991787100191815403557)
                  ·
                    refine ⟨743810960081285965388167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3966991787100191815403557 743810960081285965388167)
                    ·
                      rfl

theorem cell22_2172850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_2172850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172850 prefixEnd_2172850 := by exact prefixLift 2172850
  have htrace : WordTrace (prefixWord ++ tailWord_2172850) baseStart_2172850 baseEnd_2172850 := by
    simpa [prefixWord, tailWord_2172850, baseEnd_2172850] using wordTrace_append hprefix tailTrace_2172850
  have hstable : (prefixWord ++ tailWord_2172850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172850).length < 2 ^ (prefixWord ++ tailWord_2172850).sum := by decide
  have hdescent : baseEnd_2172850 < baseStart_2172850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172882 : List Nat := [3, 2, 2, 3, 2, 1, 9]
def baseStart_2172882 : Nat := 118140960795 + 2172882 * 2 ^ 59
def prefixEnd_2172882 : Nat := 4983230072969 + 3 ^ 40 * 2172882 * 2
def baseEnd_2172882 : Nat := 27548959790194390688447

theorem tailTrace_2172882 : CollatzResearch.WordTrace tailWord_2172882 prefixEnd_2172882 27548959790194390688447 := by
  unfold tailWord_2172882
  simp only [CollatzResearch.WordTrace]
  refine ⟨19812879328506771886508225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52834344876018058364021933 19812879328506771886508225)
  ·
    refine ⟨14859659496380078914881169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19812879328506771886508225 14859659496380078914881169)
    ·
      refine ⟨11144744622285059186160877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14859659496380078914881169 11144744622285059186160877)
      ·
        refine ⟨4179279233356897194810329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11144744622285059186160877 4179279233356897194810329)
        ·
          refine ⟨3134459425017672896107747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4179279233356897194810329 3134459425017672896107747)
          ·
            refine ⟨4701689137526509344161621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3134459425017672896107747 4701689137526509344161621)
            ·
              refine ⟨27548959790194390688447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4701689137526509344161621 27548959790194390688447)
              ·
                rfl

theorem cell22_2172882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 9].length) (baseStart_2172882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172882 prefixEnd_2172882 := by exact prefixLift 2172882
  have htrace : WordTrace (prefixWord ++ tailWord_2172882) baseStart_2172882 baseEnd_2172882 := by
    simpa [prefixWord, tailWord_2172882, baseEnd_2172882] using wordTrace_append hprefix tailTrace_2172882
  have hstable : (prefixWord ++ tailWord_2172882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172882).length < 2 ^ (prefixWord ++ tailWord_2172882).sum := by decide
  have hdescent : baseEnd_2172882 < baseStart_2172882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172886 : List Nat := [5, 2, 1, 1, 3, 1, 1, 1, 4, 3]
def baseStart_2172886 : Nat := 118140960795 + 2172886 * 2 ^ 59
def prefixEnd_2172886 : Nat := 4983230072969 + 3 ^ 40 * 2172886 * 2
def baseEnd_2172886 : Nat := 743823283616993871488057

theorem tailTrace_2172886 : CollatzResearch.WordTrace tailWord_2172886 prefixEnd_2172886 743823283616993871488057 := by
  unfold tailWord_2172886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4953228950375787264323657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52834442137341730819452341 4953228950375787264323657)
  ·
    refine ⟨3714921712781840448242743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4953228950375787264323657 3714921712781840448242743)
    ·
      refine ⟨5572382569172760672364115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3714921712781840448242743 5572382569172760672364115)
      ·
        refine ⟨8358573853759141008546173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5572382569172760672364115 8358573853759141008546173)
        ·
          refine ⟨3134465195159677878204815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8358573853759141008546173 3134465195159677878204815)
          ·
            refine ⟨4701697792739516817307223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3134465195159677878204815 4701697792739516817307223)
            ·
              refine ⟨7052546689109275225960835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4701697792739516817307223 7052546689109275225960835)
              ·
                refine ⟨10578820033663912838941253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7052546689109275225960835 10578820033663912838941253)
                ·
                  refine ⟨1983528756311983657301485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10578820033663912838941253 1983528756311983657301485)
                  ·
                    refine ⟨743823283616993871488057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1983528756311983657301485 743823283616993871488057)
                    ·
                      rfl

theorem cell22_2172886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_2172886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172886 prefixEnd_2172886 := by exact prefixLift 2172886
  have htrace : WordTrace (prefixWord ++ tailWord_2172886) baseStart_2172886 baseEnd_2172886 := by
    simpa [prefixWord, tailWord_2172886, baseEnd_2172886] using wordTrace_append hprefix tailTrace_2172886
  have hstable : (prefixWord ++ tailWord_2172886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172886).length < 2 ^ (prefixWord ++ tailWord_2172886).sum := by decide
  have hdescent : baseEnd_2172886 < baseStart_2172886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172897 : List Nat := [1, 2, 3, 1, 2, 1, 3, 3, 3, 3]
def baseStart_2172897 : Nat := 118140960795 + 2172897 * 2 ^ 59
def prefixEnd_2172897 : Nat := 4983230072969 + 3 ^ 40 * 2172897 * 2
def baseEnd_2172897 : Nat := 743827049141793509463023

theorem tailTrace_2172897 : CollatzResearch.WordTrace tailWord_2172897 prefixEnd_2172897 743827049141793509463023 := by
  unfold tailWord_2172897
  simp only [CollatzResearch.WordTrace]
  refine ⟨79252064408972745107828945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52834709605981830071885963 79252064408972745107828945)
  ·
    refine ⟨59439048306729558830871709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79252064408972745107828945 59439048306729558830871709)
    ·
      refine ⟨22289643115023584561576891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59439048306729558830871709 22289643115023584561576891)
      ·
        refine ⟨33434464672535376842365337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22289643115023584561576891 33434464672535376842365337)
        ·
          refine ⟨25075848504401532631774003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33434464672535376842365337 25075848504401532631774003)
          ·
            refine ⟨37613772756602298947661005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25075848504401532631774003 37613772756602298947661005)
            ·
              refine ⟨14105164783725862105372877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37613772756602298947661005 14105164783725862105372877)
              ·
                refine ⟨5289436793897198289514829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14105164783725862105372877 5289436793897198289514829)
                ·
                  refine ⟨1983538797711449358568061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5289436793897198289514829 1983538797711449358568061)
                  ·
                    refine ⟨743827049141793509463023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1983538797711449358568061 743827049141793509463023)
                    ·
                      rfl

theorem cell22_2172897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_2172897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172897 prefixEnd_2172897 := by exact prefixLift 2172897
  have htrace : WordTrace (prefixWord ++ tailWord_2172897) baseStart_2172897 baseEnd_2172897 := by
    simpa [prefixWord, tailWord_2172897, baseEnd_2172897] using wordTrace_append hprefix tailTrace_2172897
  have hstable : (prefixWord ++ tailWord_2172897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172897).length < 2 ^ (prefixWord ++ tailWord_2172897).sum := by decide
  have hdescent : baseEnd_2172897 < baseStart_2172897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172925 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 1, 7]
def baseStart_2172925 : Nat := 118140960795 + 2172925 * 2 ^ 59
def prefixEnd_2172925 : Nat := 4983230072969 + 3 ^ 40 * 2172925 * 2
def baseEnd_2172925 : Nat := 743836634114010769762937

theorem tailTrace_2172925 : CollatzResearch.WordTrace tailWord_2172925 prefixEnd_2172925 743836634114010769762937 := by
  unfold tailWord_2172925
  simp only [CollatzResearch.WordTrace]
  refine ⟨79253085652871305889848229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52835390435247537259898819 79253085652871305889848229)
  ·
    refine ⟨14859953559913369854346543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79253085652871305889848229 14859953559913369854346543)
    ·
      refine ⟨22289930339870054781519815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14859953559913369854346543 22289930339870054781519815)
      ·
        refine ⟨33434895509805082172279723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22289930339870054781519815 33434895509805082172279723)
        ·
          refine ⟨50152343264707623258419585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33434895509805082172279723 50152343264707623258419585)
          ·
            refine ⟨37614257448530717443814689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50152343264707623258419585 37614257448530717443814689)
            ·
              refine ⟨28210693086398038082861017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37614257448530717443814689 28210693086398038082861017)
              ·
                refine ⟨21158019814798528562145763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28210693086398038082861017 21158019814798528562145763)
                ·
                  refine ⟨31737029722197792843218645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21158019814798528562145763 31737029722197792843218645)
                  ·
                    refine ⟨743836634114010769762937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31737029722197792843218645 743836634114010769762937)
                    ·
                      rfl

theorem cell22_2172925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_2172925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172925 prefixEnd_2172925 := by exact prefixLift 2172925
  have htrace : WordTrace (prefixWord ++ tailWord_2172925) baseStart_2172925 baseEnd_2172925 := by
    simpa [prefixWord, tailWord_2172925, baseEnd_2172925] using wordTrace_append hprefix tailTrace_2172925
  have hstable : (prefixWord ++ tailWord_2172925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172925).length < 2 ^ (prefixWord ++ tailWord_2172925).sum := by decide
  have hdescent : baseEnd_2172925 < baseStart_2172925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172955 : List Nat := [1, 1, 1, 1, 1, 1, 3, 7, 6]
def baseStart_2172955 : Nat := 118140960795 + 2172955 * 2 ^ 59
def prefixEnd_2172955 : Nat := 4983230072969 + 3 ^ 40 * 2172955 * 2
def baseEnd_2172955 : Nat := 247948967909033563837615

theorem tailTrace_2172955 : CollatzResearch.WordTrace tailWord_2172955 prefixEnd_2172955 247948967909033563837615 := by
  unfold tailWord_2172955
  simp only [CollatzResearch.WordTrace]
  refine ⟨79254179842762621013440319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52836119895175080675626879 79254179842762621013440319)
  ·
    refine ⟨118881269764143931520160479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79254179842762621013440319 118881269764143931520160479)
    ·
      refine ⟨178321904646215897280240719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118881269764143931520160479 178321904646215897280240719)
      ·
        refine ⟨267482856969323845920361079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178321904646215897280240719 267482856969323845920361079)
        ·
          refine ⟨401224285453985768880541619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267482856969323845920361079 401224285453985768880541619)
          ·
            refine ⟨601836428180978653320812429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401224285453985768880541619 601836428180978653320812429)
            ·
              refine ⟨225688660567866994995304661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 601836428180978653320812429 225688660567866994995304661)
              ·
                refine ⟨5289577982059382695202453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 225688660567866994995304661 5289577982059382695202453)
                ·
                  refine ⟨247948967909033563837615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5289577982059382695202453 247948967909033563837615)
                  ·
                    rfl

theorem cell22_2172955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 6].length) (baseStart_2172955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172955 prefixEnd_2172955 := by exact prefixLift 2172955
  have htrace : WordTrace (prefixWord ++ tailWord_2172955) baseStart_2172955 baseEnd_2172955 := by
    simpa [prefixWord, tailWord_2172955, baseEnd_2172955] using wordTrace_append hprefix tailTrace_2172955
  have hstable : (prefixWord ++ tailWord_2172955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172955).length < 2 ^ (prefixWord ++ tailWord_2172955).sum := by decide
  have hdescent : baseEnd_2172955 < baseStart_2172955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172961 : List Nat := [1, 2, 3, 2, 4, 2, 2, 1, 5]
def baseStart_2172961 : Nat := 118140960795 + 2172961 * 2 ^ 59
def prefixEnd_2172961 : Nat := 4983230072969 + 3 ^ 40 * 2172961 * 2
def baseEnd_2172961 : Nat := 247949652549906225287609

theorem tailTrace_2172961 : CollatzResearch.WordTrace tailWord_2172961 prefixEnd_2172961 247949652549906225287609 := by
  unfold tailWord_2172961
  simp only [CollatzResearch.WordTrace]
  refine ⟨79254398680740884038158737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52836265787160589358772491 79254398680740884038158737)
  ·
    refine ⟨59440799010555663028619053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79254398680740884038158737 59440799010555663028619053)
    ·
      refine ⟨22290299628958373635732145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59440799010555663028619053 22290299628958373635732145)
      ·
        refine ⟨16717724721718780226799109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22290299628958373635732145 16717724721718780226799109)
        ·
          refine ⟨3134573385322271292524833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16717724721718780226799109 3134573385322271292524833)
          ·
            refine ⟨2350930038991703469393625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3134573385322271292524833 2350930038991703469393625)
            ·
              refine ⟨1763197529243777602045219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2350930038991703469393625 1763197529243777602045219)
              ·
                refine ⟨2644796293865666403067829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1763197529243777602045219 2644796293865666403067829)
                ·
                  refine ⟨247949652549906225287609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2644796293865666403067829 247949652549906225287609)
                  ·
                    rfl

theorem cell22_2172961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 5].length) (baseStart_2172961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172961 prefixEnd_2172961 := by exact prefixLift 2172961
  have htrace : WordTrace (prefixWord ++ tailWord_2172961) baseStart_2172961 baseEnd_2172961 := by
    simpa [prefixWord, tailWord_2172961, baseEnd_2172961] using wordTrace_append hprefix tailTrace_2172961
  have hstable : (prefixWord ++ tailWord_2172961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172961).length < 2 ^ (prefixWord ++ tailWord_2172961).sum := by decide
  have hdescent : baseEnd_2172961 < baseStart_2172961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172974 : List Nat := [4, 1, 3, 1, 1, 3, 1, 1, 3, 4]
def baseStart_2172974 : Nat := 118140960795 + 2172974 * 2 ^ 59
def prefixEnd_2172974 : Nat := 4983230072969 + 3 ^ 40 * 2172974 * 2
def baseEnd_2172974 : Nat := 743853407815390975287787

theorem tailTrace_2172974 : CollatzResearch.WordTrace tailWord_2172974 prefixEnd_2172974 743853407815390975287787 := by
  unfold tailWord_2172974
  simp only [CollatzResearch.WordTrace]
  refine ⟨9906859103711723407297747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52836581886462524838921317 9906859103711723407297747)
  ·
    refine ⟨14860288655567585110946621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9906859103711723407297747 14860288655567585110946621)
    ·
      refine ⟨5572608245837844416604983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14860288655567585110946621 5572608245837844416604983)
      ·
        refine ⟨8358912368756766624907475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5572608245837844416604983 8358912368756766624907475)
        ·
          refine ⟨12538368553135149937361213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8358912368756766624907475 12538368553135149937361213)
          ·
            refine ⟨4701888207425681226510455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12538368553135149937361213 4701888207425681226510455)
            ·
              refine ⟨7052832311138521839765683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4701888207425681226510455 7052832311138521839765683)
              ·
                refine ⟨10579248466707782759648525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7052832311138521839765683 10579248466707782759648525)
                ·
                  refine ⟨3967218175015418534868197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10579248466707782759648525 3967218175015418534868197)
                  ·
                    refine ⟨743853407815390975287787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3967218175015418534868197 743853407815390975287787)
                    ·
                      rfl

theorem cell22_2172974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_2172974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172974 prefixEnd_2172974 := by exact prefixLift 2172974
  have htrace : WordTrace (prefixWord ++ tailWord_2172974) baseStart_2172974 baseEnd_2172974 := by
    simpa [prefixWord, tailWord_2172974, baseEnd_2172974] using wordTrace_append hprefix tailTrace_2172974
  have hstable : (prefixWord ++ tailWord_2172974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172974).length < 2 ^ (prefixWord ++ tailWord_2172974).sum := by decide
  have hdescent : baseEnd_2172974 < baseStart_2172974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2172989 : List Nat := [1, 4, 1, 3, 1, 1, 2, 5, 4]
def baseStart_2172989 : Nat := 118140960795 + 2172989 * 2 ^ 59
def prefixEnd_2172989 : Nat := 4983230072969 + 3 ^ 40 * 2172989 * 2
def baseEnd_2172989 : Nat := 247952847540645312054247

theorem tailTrace_2172989 : CollatzResearch.WordTrace tailWord_2172989 prefixEnd_2172989 247952847540645312054247 := by
  unfold tailWord_2172989
  simp only [CollatzResearch.WordTrace]
  refine ⟨79255419924639444820178021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52836946616426296546785347 79255419924639444820178021)
  ·
    refine ⟨14860391235869895903783379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79255419924639444820178021 14860391235869895903783379)
    ·
      refine ⟨22290586853804843855675069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14860391235869895903783379 22290586853804843855675069)
      ·
        refine ⟨8358970070176816445878151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22290586853804843855675069 8358970070176816445878151)
        ·
          refine ⟨12538455105265224668817227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8358970070176816445878151 12538455105265224668817227)
          ·
            refine ⟨18807682657897837003225841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12538455105265224668817227 18807682657897837003225841)
            ·
              refine ⟨14105761993423377752419381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18807682657897837003225841 14105761993423377752419381)
              ·
                refine ⟨1322415186883441664289317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14105761993423377752419381 1322415186883441664289317)
                ·
                  refine ⟨247952847540645312054247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1322415186883441664289317 247952847540645312054247)
                  ·
                    rfl

theorem cell22_2172989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_2172989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2172989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2172989 prefixEnd_2172989 := by exact prefixLift 2172989
  have htrace : WordTrace (prefixWord ++ tailWord_2172989) baseStart_2172989 baseEnd_2172989 := by
    simpa [prefixWord, tailWord_2172989, baseEnd_2172989] using wordTrace_append hprefix tailTrace_2172989
  have hstable : (prefixWord ++ tailWord_2172989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2172989).length < 2 ^ (prefixWord ++ tailWord_2172989).sum := by decide
  have hdescent : baseEnd_2172989 < baseStart_2172989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2172989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173004 : List Nat := [2, 2, 1, 3, 1, 1, 3, 4, 2, 3]
def baseStart_2173004 : Nat := 118140960795 + 2173004 * 2 ^ 59
def prefixEnd_2173004 : Nat := 4983230072969 + 3 ^ 40 * 2173004 * 2
def baseEnd_2173004 : Nat := 743863677428480897037695

theorem tailTrace_2173004 : CollatzResearch.WordTrace tailWord_2173004 prefixEnd_2173004 743863677428480897037695 := by
  unfold tailWord_2173004
  simp only [CollatzResearch.WordTrace]
  refine ⟨39627983509792551190987033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52837311346390068254649377 39627983509792551190987033)
  ·
    refine ⟨29720987632344413393240275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39627983509792551190987033 29720987632344413393240275)
    ·
      refine ⟨44581481448516620089860413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29720987632344413393240275 44581481448516620089860413)
      ·
        refine ⟨16718055543193732533697655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44581481448516620089860413 16718055543193732533697655)
        ·
          refine ⟨25077083314790598800546483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16718055543193732533697655 25077083314790598800546483)
          ·
            refine ⟨37615624972185898200819725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25077083314790598800546483 37615624972185898200819725)
            ·
              refine ⟨14105859364569711825307397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37615624972185898200819725 14105859364569711825307397)
              ·
                refine ⟨2644848630856820967245137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14105859364569711825307397 2644848630856820967245137)
                ·
                  refine ⟨1983636473142615725433853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2644848630856820967245137 1983636473142615725433853)
                  ·
                    refine ⟨743863677428480897037695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1983636473142615725433853 743863677428480897037695)
                    ·
                      rfl

theorem cell22_2173004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 4, 2, 3].length) (baseStart_2173004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173004 prefixEnd_2173004 := by exact prefixLift 2173004
  have htrace : WordTrace (prefixWord ++ tailWord_2173004) baseStart_2173004 baseEnd_2173004 := by
    simpa [prefixWord, tailWord_2173004, baseEnd_2173004] using wordTrace_append hprefix tailTrace_2173004
  have hstable : (prefixWord ++ tailWord_2173004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173004).length < 2 ^ (prefixWord ++ tailWord_2173004).sum := by decide
  have hdescent : baseEnd_2173004 < baseStart_2173004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173006 : List Nat := [4, 1, 1, 1, 1, 4, 4, 2, 4]
def baseStart_2173006 : Nat := 118140960795 + 2173006 * 2 ^ 59
def prefixEnd_2173006 : Nat := 4983230072969 + 3 ^ 40 * 2173006 * 2
def baseEnd_2173006 : Nat := 247954787356451186162563

theorem tailTrace_2173006 : CollatzResearch.WordTrace tailWord_2173006 prefixEnd_2173006 247954787356451186162563 := by
  unfold tailWord_2173006
  simp only [CollatzResearch.WordTrace]
  refine ⟨9907004995697232090443359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52837359977051904482364581 9907004995697232090443359)
  ·
    refine ⟨14860507493545848135665039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9907004995697232090443359 14860507493545848135665039)
    ·
      refine ⟨22290761240318772203497559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14860507493545848135665039 22290761240318772203497559)
      ·
        refine ⟨33436141860478158305246339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22290761240318772203497559 33436141860478158305246339)
        ·
          refine ⟨50154212790717237457869509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33436141860478158305246339 50154212790717237457869509)
          ·
            refine ⟨9403914898259482023350533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50154212790717237457869509 9403914898259482023350533)
            ·
              refine ⟨1763234043423652879378225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9403914898259482023350533 1763234043423652879378225)
              ·
                refine ⟨1322425532567739659533669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1763234043423652879378225 1322425532567739659533669)
                ·
                  refine ⟨247954787356451186162563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1322425532567739659533669 247954787356451186162563)
                  ·
                    rfl

theorem cell22_2173006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_2173006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173006 prefixEnd_2173006 := by exact prefixLift 2173006
  have htrace : WordTrace (prefixWord ++ tailWord_2173006) baseStart_2173006 baseEnd_2173006 := by
    simpa [prefixWord, tailWord_2173006, baseEnd_2173006] using wordTrace_append hprefix tailTrace_2173006
  have hstable : (prefixWord ++ tailWord_2173006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173006).length < 2 ^ (prefixWord ++ tailWord_2173006).sum := by decide
  have hdescent : baseEnd_2173006 < baseStart_2173006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173021 : List Nat := [1, 4, 4, 1, 1, 2, 2, 1, 1, 5]
def baseStart_2173021 : Nat := 118140960795 + 2173021 * 2 ^ 59
def prefixEnd_2173021 : Nat := 4983230072969 + 3 ^ 40 * 2173021 * 2
def baseEnd_2173021 : Nat := 743869496875898519362643

theorem tailTrace_2173021 : CollatzResearch.WordTrace tailWord_2173021 prefixEnd_2173021 743869496875898519362643 := by
  unfold tailWord_2173021
  simp only [CollatzResearch.WordTrace]
  refine ⟨79256587060523514285342917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52837724707015676190228611 79256587060523514285342917)
  ·
    refine ⟨14860610073848158928501797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79256587060523514285342917 14860610073848158928501797)
    ·
      refine ⟨2786364388846529799094087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14860610073848158928501797 2786364388846529799094087)
      ·
        refine ⟨4179546583269794698641131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2786364388846529799094087 4179546583269794698641131)
        ·
          refine ⟨6269319874904692047961697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4179546583269794698641131 6269319874904692047961697)
          ·
            refine ⟨4701989906178519035971273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6269319874904692047961697 4701989906178519035971273)
            ·
              refine ⟨3526492429633889276978455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4701989906178519035971273 3526492429633889276978455)
              ·
                refine ⟨5289738644450833915467683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3526492429633889276978455 5289738644450833915467683)
                ·
                  refine ⟨7934607966676250873201525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5289738644450833915467683 7934607966676250873201525)
                  ·
                    refine ⟨743869496875898519362643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7934607966676250873201525 743869496875898519362643)
                    ·
                      rfl

theorem cell22_2173021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_2173021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173021 prefixEnd_2173021 := by exact prefixLift 2173021
  have htrace : WordTrace (prefixWord ++ tailWord_2173021) baseStart_2173021 baseEnd_2173021 := by
    simpa [prefixWord, tailWord_2173021, baseEnd_2173021] using wordTrace_append hprefix tailTrace_2173021
  have hstable : (prefixWord ++ tailWord_2173021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173021).length < 2 ^ (prefixWord ++ tailWord_2173021).sum := by decide
  have hdescent : baseEnd_2173021 < baseStart_2173021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173066 : List Nat := [3, 1, 2, 3, 1, 3, 2, 1, 3, 3]
def baseStart_2173066 : Nat := 118140960795 + 2173066 * 2 ^ 59
def prefixEnd_2173066 : Nat := 4983230072969 + 3 ^ 40 * 2173066 * 2
def baseEnd_2173066 : Nat := 743884901295533401987505

theorem tailTrace_2173066 : CollatzResearch.WordTrace tailWord_2173066 prefixEnd_2173066 743884901295533401987505 := by
  unfold tailWord_2173066
  simp only [CollatzResearch.WordTrace]
  refine ⟨19814557086340121742682763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52838818896906991313820701 19814557086340121742682763)
  ·
    refine ⟨29721835629510182614024145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19814557086340121742682763 29721835629510182614024145)
    ·
      refine ⟨22291376722132636960518109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29721835629510182614024145 22291376722132636960518109)
      ·
        refine ⟨8359266270799738860194291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22291376722132636960518109 8359266270799738860194291)
        ·
          refine ⟨12538899406199608290291437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8359266270799738860194291 12538899406199608290291437)
          ·
            refine ⟨4702087277324853108859289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12538899406199608290291437 4702087277324853108859289)
            ·
              refine ⟨3526565457993639831644467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4702087277324853108859289 3526565457993639831644467)
              ·
                refine ⟨5289848186990459747466701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3526565457993639831644467 5289848186990459747466701)
                ·
                  refine ⟨1983693070121422405300013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5289848186990459747466701 1983693070121422405300013)
                  ·
                    refine ⟨743884901295533401987505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1983693070121422405300013 743884901295533401987505)
                    ·
                      rfl

theorem cell22_2173066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_2173066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173066 prefixEnd_2173066 := by exact prefixLift 2173066
  have htrace : WordTrace (prefixWord ++ tailWord_2173066) baseStart_2173066 baseEnd_2173066 := by
    simpa [prefixWord, tailWord_2173066, baseEnd_2173066] using wordTrace_append hprefix tailTrace_2173066
  have hstable : (prefixWord ++ tailWord_2173066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173066).length < 2 ^ (prefixWord ++ tailWord_2173066).sum := by decide
  have hdescent : baseEnd_2173066 < baseStart_2173066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173077 : List Nat := [1, 3, 2, 1, 1, 1, 3, 3, 2, 5]
def baseStart_2173077 : Nat := 118140960795 + 2173077 * 2 ^ 59
def prefixEnd_2173077 : Nat := 4983230072969 + 3 ^ 40 * 2173077 * 2
def baseEnd_2173077 : Nat := 743888666820333039962471

theorem tailTrace_2173077 : CollatzResearch.WordTrace tailWord_2173077 prefixEnd_2173077 743888666820333039962471 := by
  unfold tailWord_2173077
  simp only [CollatzResearch.WordTrace]
  refine ⟨79258629548320635849381485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52839086365547090566254323 79258629548320635849381485)
  ·
    refine ⟨29721986080620238443518057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79258629548320635849381485 29721986080620238443518057)
    ·
      refine ⟨22291489560465178832638543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29721986080620238443518057 22291489560465178832638543)
      ·
        refine ⟨33437234340697768248957815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22291489560465178832638543 33437234340697768248957815)
        ·
          refine ⟨50155851511046652373436723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33437234340697768248957815 50155851511046652373436723)
          ·
            refine ⟨75233777266569978560155085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50155851511046652373436723 75233777266569978560155085)
            ·
              refine ⟨28212666474963741960058157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75233777266569978560155085 28212666474963741960058157)
              ·
                refine ⟨10579749928111403235021809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28212666474963741960058157 10579749928111403235021809)
                ·
                  refine ⟨7934812446083552426266357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10579749928111403235021809 7934812446083552426266357)
                  ·
                    refine ⟨743888666820333039962471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7934812446083552426266357 743888666820333039962471)
                    ·
                      rfl

theorem cell22_2173077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_2173077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173077 prefixEnd_2173077 := by exact prefixLift 2173077
  have htrace : WordTrace (prefixWord ++ tailWord_2173077) baseStart_2173077 baseEnd_2173077 := by
    simpa [prefixWord, tailWord_2173077, baseEnd_2173077] using wordTrace_append hprefix tailTrace_2173077
  have hstable : (prefixWord ++ tailWord_2173077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173077).length < 2 ^ (prefixWord ++ tailWord_2173077).sum := by decide
  have hdescent : baseEnd_2173077 < baseStart_2173077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173137 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 3, 6]
def baseStart_2173137 : Nat := 118140960795 + 2173137 * 2 ^ 59
def prefixEnd_2173137 : Nat := 4983230072969 + 3 ^ 40 * 2173137 * 2
def baseEnd_2173137 : Nat := 743909206046512883462287

theorem tailTrace_2173137 : CollatzResearch.WordTrace tailWord_2173137 prefixEnd_2173137 743909206046512883462287 := by
  unfold tailWord_2173137
  simp only [CollatzResearch.WordTrace]
  refine ⟨79260817928103266096565665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52840545285402177397710443 79260817928103266096565665)
  ·
    refine ⟨59445613446077449572424249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79260817928103266096565665 59445613446077449572424249)
    ·
      refine ⟨44584210084558087179318187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59445613446077449572424249 44584210084558087179318187)
      ·
        refine ⟨66876315126837130768977281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44584210084558087179318187 66876315126837130768977281)
        ·
          refine ⟨50157236345127848076732961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66876315126837130768977281 50157236345127848076732961)
          ·
            refine ⟨37617927258845886057549721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50157236345127848076732961 37617927258845886057549721)
            ·
              refine ⟨28213445444134414543162291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37617927258845886057549721 28213445444134414543162291)
              ·
                refine ⟨42320168166201621814743437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28213445444134414543162291 42320168166201621814743437)
                ·
                  refine ⟨15870063062325608180528789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42320168166201621814743437 15870063062325608180528789)
                  ·
                    refine ⟨743909206046512883462287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15870063062325608180528789 743909206046512883462287)
                    ·
                      rfl

theorem cell22_2173137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_2173137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173137 prefixEnd_2173137 := by exact prefixLift 2173137
  have htrace : WordTrace (prefixWord ++ tailWord_2173137) baseStart_2173137 baseEnd_2173137 := by
    simpa [prefixWord, tailWord_2173137, baseEnd_2173137] using wordTrace_append hprefix tailTrace_2173137
  have hstable : (prefixWord ++ tailWord_2173137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173137).length < 2 ^ (prefixWord ++ tailWord_2173137).sum := by decide
  have hdescent : baseEnd_2173137 < baseStart_2173137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173152 : List Nat := [2, 1, 1, 3, 1, 3, 1, 10]
def baseStart_2173152 : Nat := 118140960795 + 2173152 * 2 ^ 59
def prefixEnd_2173152 : Nat := 4983230072969 + 3 ^ 40 * 2173152 * 2
def baseEnd_2173152 : Nat := 82657148983673093815249

theorem tailTrace_2173152 : CollatzResearch.WordTrace tailWord_2173152 prefixEnd_2173152 82657148983673093815249 := by
  unfold tailWord_2173152
  simp only [CollatzResearch.WordTrace]
  refine ⟨39630682511524461829180855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52840910015365949105574473 39630682511524461829180855)
  ·
    refine ⟨59446023767286692743771283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39630682511524461829180855 59446023767286692743771283)
    ·
      refine ⟨89169035650930039115656925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59446023767286692743771283 89169035650930039115656925)
      ·
        refine ⟨33438388369098764668371347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89169035650930039115656925 33438388369098764668371347)
        ·
          refine ⟨50157582553648147002557021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33438388369098764668371347 50157582553648147002557021)
          ·
            refine ⟨18809093457618055125958883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50157582553648147002557021 18809093457618055125958883)
            ·
              refine ⟨28213640186427082688938325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18809093457618055125958883 28213640186427082688938325)
              ·
                refine ⟨82657148983673093815249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 28213640186427082688938325 82657148983673093815249)
                ·
                  rfl

theorem cell22_2173152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 10].length) (baseStart_2173152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173152 prefixEnd_2173152 := by exact prefixLift 2173152
  have htrace : WordTrace (prefixWord ++ tailWord_2173152) baseStart_2173152 baseEnd_2173152 := by
    simpa [prefixWord, tailWord_2173152, baseEnd_2173152] using wordTrace_append hprefix tailTrace_2173152
  have hstable : (prefixWord ++ tailWord_2173152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173152).length < 2 ^ (prefixWord ++ tailWord_2173152).sum := by decide
  have hdescent : baseEnd_2173152 < baseStart_2173152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173186 : List Nat := [3, 4, 1, 1, 2, 1, 3, 7]
def baseStart_2173186 : Nat := 118140960795 + 2173186 * 2 ^ 59
def prefixEnd_2173186 : Nat := 4983230072969 + 3 ^ 40 * 2173186 * 2
def baseEnd_2173186 : Nat := 82658442194210343220793

theorem tailTrace_2173186 : CollatzResearch.WordTrace tailWord_2173186 prefixEnd_2173186 82658442194210343220793 := by
  unfold tailWord_2173186
  simp only [CollatzResearch.WordTrace]
  refine ⟨19815651276231436866274853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52841736736617164976732941 19815651276231436866274853)
  ·
    refine ⟨3715434614293394412426535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19815651276231436866274853 3715434614293394412426535)
    ·
      refine ⟨5573151921440091618639803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3715434614293394412426535 5573151921440091618639803)
      ·
        refine ⟨8359727882160137427959705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5573151921440091618639803 8359727882160137427959705)
        ·
          refine ⟨6269795911620103070969779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8359727882160137427959705 6269795911620103070969779)
          ·
            refine ⟨9404693867430154606454669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6269795911620103070969779 9404693867430154606454669)
            ·
              refine ⟨3526760200286307977420501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9404693867430154606454669 3526760200286307977420501)
              ·
                refine ⟨82658442194210343220793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3526760200286307977420501 82658442194210343220793)
                ·
                  rfl

theorem cell22_2173186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 7].length) (baseStart_2173186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173186 prefixEnd_2173186 := by exact prefixLift 2173186
  have htrace : WordTrace (prefixWord ++ tailWord_2173186) baseStart_2173186 baseEnd_2173186 := by
    simpa [prefixWord, tailWord_2173186, baseEnd_2173186] using wordTrace_append hprefix tailTrace_2173186
  have hstable : (prefixWord ++ tailWord_2173186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173186).length < 2 ^ (prefixWord ++ tailWord_2173186).sum := by decide
  have hdescent : baseEnd_2173186 < baseStart_2173186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173201 : List Nat := [1, 2, 2, 1, 1, 6, 1, 2, 3, 3]
def baseStart_2173201 : Nat := 118140960795 + 2173201 * 2 ^ 59
def prefixEnd_2173201 : Nat := 4983230072969 + 3 ^ 40 * 2173201 * 2
def baseEnd_2173201 : Nat := 743931114554438049862091

theorem tailTrace_2173201 : CollatzResearch.WordTrace tailWord_2173201 prefixEnd_2173201 743931114554438049862091 := by
  unfold tailWord_2173201
  simp only [CollatzResearch.WordTrace]
  refine ⟨79263152199871405026895457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52842101466580936684596971 79263152199871405026895457)
  ·
    refine ⟨59447364149903553770171593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79263152199871405026895457 59447364149903553770171593)
    ·
      refine ⟨44585523112427665327628695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59447364149903553770171593 44585523112427665327628695)
      ·
        refine ⟨66878284668641497991443043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44585523112427665327628695 66878284668641497991443043)
        ·
          refine ⟨100317427002962246987164565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66878284668641497991443043 100317427002962246987164565)
          ·
            refine ⟨4702379390763855327523339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 100317427002962246987164565 4702379390763855327523339)
            ·
              refine ⟨7053569086145782991285009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4702379390763855327523339 7053569086145782991285009)
              ·
                refine ⟨5290176814609337243463757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7053569086145782991285009 5290176814609337243463757)
                ·
                  refine ⟨1983816305478501466298909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5290176814609337243463757 1983816305478501466298909)
                  ·
                    refine ⟨743931114554438049862091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1983816305478501466298909 743931114554438049862091)
                    ·
                      rfl

theorem cell22_2173201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 3, 3].length) (baseStart_2173201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173201 prefixEnd_2173201 := by exact prefixLift 2173201
  have htrace : WordTrace (prefixWord ++ tailWord_2173201) baseStart_2173201 baseEnd_2173201 := by
    simpa [prefixWord, tailWord_2173201, baseEnd_2173201] using wordTrace_append hprefix tailTrace_2173201
  have hstable : (prefixWord ++ tailWord_2173201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173201).length < 2 ^ (prefixWord ++ tailWord_2173201).sum := by decide
  have hdescent : baseEnd_2173201 < baseStart_2173201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173246 : List Nat := [4, 2, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_2173246 : Nat := 118140960795 + 2173246 * 2 ^ 59
def prefixEnd_2173246 : Nat := 4983230072969 + 3 ^ 40 * 2173246 * 2
def baseEnd_2173246 : Nat := 743946518974072932486953

theorem tailTrace_2173246 : CollatzResearch.WordTrace tailWord_2173246 prefixEnd_2173246 743946518974072932486953 := by
  unfold tailWord_2173246
  simp only [CollatzResearch.WordTrace]
  refine ⟨9908099185588547214035449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52843195656472251808189061 9908099185588547214035449)
  ·
    refine ⟨7431074389191410410526587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9908099185588547214035449 7431074389191410410526587)
    ·
      refine ⟨11146611583787115615789881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7431074389191410410526587 11146611583787115615789881)
      ·
        refine ⟨8359958687840336711842411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11146611583787115615789881 8359958687840336711842411)
        ·
          refine ⟨12539938031760505067763617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8359958687840336711842411 12539938031760505067763617)
          ·
            refine ⟨9404953523820378800822713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12539938031760505067763617 9404953523820378800822713)
            ·
              refine ⟨7053715142865284100617035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9404953523820378800822713 7053715142865284100617035)
              ·
                refine ⟨10580572714297926150925553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7053715142865284100617035 10580572714297926150925553)
                ·
                  refine ⟨7935429535723444613194165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10580572714297926150925553 7935429535723444613194165)
                  ·
                    refine ⟨743946518974072932486953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7935429535723444613194165 743946518974072932486953)
                    ·
                      rfl

theorem cell22_2173246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_2173246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173246 prefixEnd_2173246 := by exact prefixLift 2173246
  have htrace : WordTrace (prefixWord ++ tailWord_2173246) baseStart_2173246 baseEnd_2173246 := by
    simpa [prefixWord, tailWord_2173246, baseEnd_2173246] using wordTrace_append hprefix tailTrace_2173246
  have hstable : (prefixWord ++ tailWord_2173246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173246).length < 2 ^ (prefixWord ++ tailWord_2173246).sum := by decide
  have hdescent : baseEnd_2173246 < baseStart_2173246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173274 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 3, 5]
def baseStart_2173274 : Nat := 118140960795 + 2173274 * 2 ^ 59
def prefixEnd_2173274 : Nat := 4983230072969 + 3 ^ 40 * 2173274 * 2
def baseEnd_2173274 : Nat := 743956103946290192786867

theorem tailTrace_2173274 : CollatzResearch.WordTrace tailWord_2173274 prefixEnd_2173274 743956103946290192786867 := by
  unfold tailWord_2173274
  simp only [CollatzResearch.WordTrace]
  refine ⟨19816453682151734623575719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52843876485737958996201917 19816453682151734623575719)
  ·
    refine ⟨29724680523227601935363579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19816453682151734623575719 29724680523227601935363579)
    ·
      refine ⟨44587020784841402903045369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29724680523227601935363579 44587020784841402903045369)
      ·
        refine ⟨33440265588631052177284027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44587020784841402903045369 33440265588631052177284027)
        ·
          refine ⟨50160398382946578265926041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33440265588631052177284027 50160398382946578265926041)
          ·
            refine ⟨37620298787209933699444531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50160398382946578265926041 37620298787209933699444531)
            ·
              refine ⟨56430448180814900549166797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37620298787209933699444531 56430448180814900549166797)
              ·
                refine ⟨21161418067805587705937549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56430448180814900549166797 21161418067805587705937549)
                ·
                  refine ⟨7935531775427095389726581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21161418067805587705937549 7935531775427095389726581)
                  ·
                    refine ⟨743956103946290192786867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7935531775427095389726581 743956103946290192786867)
                    ·
                      rfl

theorem cell22_2173274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_2173274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173274 prefixEnd_2173274 := by exact prefixLift 2173274
  have htrace : WordTrace (prefixWord ++ tailWord_2173274) baseStart_2173274 baseEnd_2173274 := by
    simpa [prefixWord, tailWord_2173274, baseEnd_2173274] using wordTrace_append hprefix tailTrace_2173274
  have hstable : (prefixWord ++ tailWord_2173274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173274).length < 2 ^ (prefixWord ++ tailWord_2173274).sum := by decide
  have hdescent : baseEnd_2173274 < baseStart_2173274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173342 : List Nat := [4, 3, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_2173342 : Nat := 118140960795 + 2173342 * 2 ^ 59
def prefixEnd_2173342 : Nat := 4983230072969 + 3 ^ 40 * 2173342 * 2
def baseEnd_2173342 : Nat := 743979381735960682086659

theorem tailTrace_2173342 : CollatzResearch.WordTrace tailWord_2173342 prefixEnd_2173342 743979381735960682086659 := by
  unfold tailWord_2173342
  simp only [CollatzResearch.WordTrace]
  refine ⟨9908536861545073263472285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52845529928240390738518853 9908536861545073263472285)
  ·
    refine ⟨3715701323079402473802107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9908536861545073263472285 3715701323079402473802107)
    ·
      refine ⟨5573551984619103710703161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3715701323079402473802107 5573551984619103710703161)
      ·
        refine ⟨4180163988464327783027371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5573551984619103710703161 4180163988464327783027371)
        ·
          refine ⟨6270245982696491674541057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4180163988464327783027371 6270245982696491674541057)
          ·
            refine ⟨4702684487022368755905793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6270245982696491674541057 4702684487022368755905793)
            ·
              refine ⟨3527013365266776566929345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4702684487022368755905793 3527013365266776566929345)
              ·
                refine ⟨2645260023950082425197009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3527013365266776566929345 2645260023950082425197009)
                ·
                  refine ⟨1983945017962561818897757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2645260023950082425197009 1983945017962561818897757)
                  ·
                    refine ⟨743979381735960682086659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1983945017962561818897757 743979381735960682086659)
                    ·
                      rfl

theorem cell22_2173342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_2173342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173342 prefixEnd_2173342 := by exact prefixLift 2173342
  have htrace : WordTrace (prefixWord ++ tailWord_2173342) baseStart_2173342 baseEnd_2173342 := by
    simpa [prefixWord, tailWord_2173342, baseEnd_2173342] using wordTrace_append hprefix tailTrace_2173342
  have hstable : (prefixWord ++ tailWord_2173342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173342).length < 2 ^ (prefixWord ++ tailWord_2173342).sum := by decide
  have hdescent : baseEnd_2173342 < baseStart_2173342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173351 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 2, 6]
def baseStart_2173351 : Nat := 118140960795 + 2173351 * 2 ^ 59
def prefixEnd_2173351 : Nat := 4983230072969 + 3 ^ 40 * 2173351 * 2
def baseEnd_2173351 : Nat := 743982462619887658611631

theorem tailTrace_2173351 : CollatzResearch.WordTrace tailWord_2173351 prefixEnd_2173351 743982462619887658611631 := by
  unfold tailWord_2173351
  simp only [CollatzResearch.WordTrace]
  refine ⟨79268623149327980644855907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52845748766218653763237271 79268623149327980644855907)
  ·
    refine ⟨118902934723991970967283861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79268623149327980644855907 118902934723991970967283861)
    ·
      refine ⟨5573575065187123639091431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 118902934723991970967283861 5573575065187123639091431)
      ·
        refine ⟨8360362597780685458637147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5573575065187123639091431 8360362597780685458637147)
        ·
          refine ⟨12540543896671028187955721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8360362597780685458637147 12540543896671028187955721)
          ·
            refine ⟨9405407922503271140966791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12540543896671028187955721 9405407922503271140966791)
            ·
              refine ⟨14108111883754906711450187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9405407922503271140966791 14108111883754906711450187)
              ·
                refine ⟨21162167825632360067175281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14108111883754906711450187 21162167825632360067175281)
                ·
                  refine ⟨15871625869224270050381461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21162167825632360067175281 15871625869224270050381461)
                  ·
                    refine ⟨743982462619887658611631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15871625869224270050381461 743982462619887658611631)
                    ·
                      rfl

theorem cell22_2173351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_2173351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173351 prefixEnd_2173351 := by exact prefixLift 2173351
  have htrace : WordTrace (prefixWord ++ tailWord_2173351) baseStart_2173351 baseEnd_2173351 := by
    simpa [prefixWord, tailWord_2173351, baseEnd_2173351] using wordTrace_append hprefix tailTrace_2173351
  have hstable : (prefixWord ++ tailWord_2173351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173351).length < 2 ^ (prefixWord ++ tailWord_2173351).sum := by decide
  have hdescent : baseEnd_2173351 < baseStart_2173351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173398 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_2173398 : Nat := 118140960795 + 2173398 * 2 ^ 59
def prefixEnd_2173398 : Nat := 4983230072969 + 3 ^ 40 * 2173398 * 2
def baseEnd_2173398 : Nat := 743998551680395202686487

theorem tailTrace_2173398 : CollatzResearch.WordTrace tailWord_2173398 prefixEnd_2173398 743998551680395202686487 := by
  unfold tailWord_2173398
  simp only [CollatzResearch.WordTrace]
  refine ⟨4954396086259856729488553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52846891586771805114544565 4954396086259856729488553)
  ·
    refine ⟨3715797064694892547116415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4954396086259856729488553 3715797064694892547116415)
    ·
      refine ⟨5573695597042338820674623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3715797064694892547116415 5573695597042338820674623)
      ·
        refine ⟨8360543395563508231011935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5573695597042338820674623 8360543395563508231011935)
        ·
          refine ⟨12540815093345262346517903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8360543395563508231011935 12540815093345262346517903)
          ·
            refine ⟨18811222640017893519776855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12540815093345262346517903 18811222640017893519776855)
            ·
              refine ⟨28216833960026840279665283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18811222640017893519776855 28216833960026840279665283)
              ·
                refine ⟨42325250940040260419497925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28216833960026840279665283 42325250940040260419497925)
                ·
                  refine ⟨7935984551257548828655861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42325250940040260419497925 7935984551257548828655861)
                  ·
                    refine ⟨743998551680395202686487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7935984551257548828655861 743998551680395202686487)
                    ·
                      rfl

theorem cell22_2173398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_2173398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173398 prefixEnd_2173398 := by exact prefixLift 2173398
  have htrace : WordTrace (prefixWord ++ tailWord_2173398) baseStart_2173398 baseEnd_2173398 := by
    simpa [prefixWord, tailWord_2173398, baseEnd_2173398] using wordTrace_append hprefix tailTrace_2173398
  have hstable : (prefixWord ++ tailWord_2173398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173398).length < 2 ^ (prefixWord ++ tailWord_2173398).sum := by decide
  have hdescent : baseEnd_2173398 < baseStart_2173398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173430 : List Nat := [5, 1, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_2173430 : Nat := 118140960795 + 2173430 * 2 ^ 59
def prefixEnd_2173430 : Nat := 4983230072969 + 3 ^ 40 * 2173430 * 2
def baseEnd_2173430 : Nat := 744009505934357785886389

theorem tailTrace_2173430 : CollatzResearch.WordTrace tailWord_2173430 prefixEnd_2173430 744009505934357785886389 := by
  unfold tailWord_2173430
  simp only [CollatzResearch.WordTrace]
  refine ⟨4954469032252611071061359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 52847669677361184757987829 4954469032252611071061359)
  ·
    refine ⟨7431703548378916606592039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4954469032252611071061359 7431703548378916606592039)
    ·
      refine ⟨11147555322568374909888059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7431703548378916606592039 11147555322568374909888059)
      ·
        refine ⟨16721332983852562364832089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11147555322568374909888059 16721332983852562364832089)
        ·
          refine ⟨12540999737889421773624067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16721332983852562364832089 12540999737889421773624067)
          ·
            refine ⟨18811499606834132660436101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12540999737889421773624067 18811499606834132660436101)
            ·
              refine ⟨3527156176281399873831769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18811499606834132660436101 3527156176281399873831769)
              ·
                refine ⟨2645367132211049905373827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3527156176281399873831769 2645367132211049905373827)
                ·
                  refine ⟨3968050698316574858060741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2645367132211049905373827 3968050698316574858060741)
                  ·
                    refine ⟨744009505934357785886389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3968050698316574858060741 744009505934357785886389)
                    ·
                      rfl

theorem cell22_2173430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_2173430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173430 prefixEnd_2173430 := by exact prefixLift 2173430
  have htrace : WordTrace (prefixWord ++ tailWord_2173430) baseStart_2173430 baseEnd_2173430 := by
    simpa [prefixWord, tailWord_2173430, baseEnd_2173430] using wordTrace_append hprefix tailTrace_2173430
  have hstable : (prefixWord ++ tailWord_2173430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173430).length < 2 ^ (prefixWord ++ tailWord_2173430).sum := by decide
  have hdescent : baseEnd_2173430 < baseStart_2173430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173488 : List Nat := [2, 1, 1, 1, 2, 3, 2, 4, 3, 3]
def baseStart_2173488 : Nat := 118140960795 + 2173488 * 2 ^ 59
def prefixEnd_2173488 : Nat := 4983230072969 + 3 ^ 40 * 2173488 * 2
def baseEnd_2173488 : Nat := 744029360519664967936211

theorem tailTrace_2173488 : CollatzResearch.WordTrace tailWord_2173488 prefixEnd_2173488 744029360519664967936211 := by
  unfold tailWord_2173488
  simp only [CollatzResearch.WordTrace]
  refine ⟨39636809974915826521296559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52849079966554435361728745 39636809974915826521296559)
  ·
    refine ⟨59455214962373739781944839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39636809974915826521296559 59455214962373739781944839)
    ·
      refine ⟨89182822443560609672917259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59455214962373739781944839 89182822443560609672917259)
      ·
        refine ⟨133774233665340914509375889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89182822443560609672917259 133774233665340914509375889)
        ·
          refine ⟨100330675249005685882031917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133774233665340914509375889 100330675249005685882031917)
          ·
            refine ⟨37624003218377132205761969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100330675249005685882031917 37624003218377132205761969)
            ·
              refine ⟨28218002413782849154321477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37624003218377132205761969 28218002413782849154321477)
              ·
                refine ⟨5290875452584284216435277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28218002413782849154321477 5290875452584284216435277)
                ·
                  refine ⟨1984078294719106581163229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5290875452584284216435277 1984078294719106581163229)
                  ·
                    refine ⟨744029360519664967936211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1984078294719106581163229 744029360519664967936211)
                    ·
                      rfl

theorem cell22_2173488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 4, 3, 3].length) (baseStart_2173488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173488 prefixEnd_2173488 := by exact prefixLift 2173488
  have htrace : WordTrace (prefixWord ++ tailWord_2173488) baseStart_2173488 baseEnd_2173488 := by
    simpa [prefixWord, tailWord_2173488, baseEnd_2173488] using wordTrace_append hprefix tailTrace_2173488
  have hstable : (prefixWord ++ tailWord_2173488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173488).length < 2 ^ (prefixWord ++ tailWord_2173488).sum := by decide
  have hdescent : baseEnd_2173488 < baseStart_2173488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173518 : List Nat := [4, 1, 1, 1, 1, 2, 3, 4, 5]
def baseStart_2173518 : Nat := 118140960795 + 2173518 * 2 ^ 59
def prefixEnd_2173518 : Nat := 4983230072969 + 3 ^ 40 * 2173518 * 2
def baseEnd_2173518 : Nat := 248013210044251629895373

theorem tailTrace_2173518 : CollatzResearch.WordTrace tailWord_2173518 prefixEnd_2173518 248013210044251629895373 := by
  unfold tailWord_2173518
  simp only [CollatzResearch.WordTrace]
  refine ⟨9909339267465371020773151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52849809426481978777456805 9909339267465371020773151)
  ·
    refine ⟨14864008901198056531159727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9909339267465371020773151 14864008901198056531159727)
    ·
      refine ⟨22296013351797084796739591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14864008901198056531159727 22296013351797084796739591)
      ·
        refine ⟨33444020027695627195109387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22296013351797084796739591 33444020027695627195109387)
        ·
          refine ⟨50166030041543440792664081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33444020027695627195109387 50166030041543440792664081)
          ·
            refine ⟨37624522531157580594498061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50166030041543440792664081 37624522531157580594498061)
            ·
              refine ⟨14109195949184092722936773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37624522531157580594498061 14109195949184092722936773)
              ·
                refine ⟨2645474240472017385550645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14109195949184092722936773 2645474240472017385550645)
                ·
                  refine ⟨248013210044251629895373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2645474240472017385550645 248013210044251629895373)
                  ·
                    rfl

theorem cell22_2173518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_2173518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173518 prefixEnd_2173518 := by exact prefixLift 2173518
  have htrace : WordTrace (prefixWord ++ tailWord_2173518) baseStart_2173518 baseEnd_2173518 := by
    simpa [prefixWord, tailWord_2173518, baseEnd_2173518] using wordTrace_append hprefix tailTrace_2173518
  have hstable : (prefixWord ++ tailWord_2173518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173518).length < 2 ^ (prefixWord ++ tailWord_2173518).sum := by decide
  have hdescent : baseEnd_2173518 < baseStart_2173518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173522 : List Nat := [3, 2, 2, 1, 2, 1, 3, 4, 1, 3]
def baseStart_2173522 : Nat := 118140960795 + 2173522 * 2 ^ 59
def prefixEnd_2173522 : Nat := 4983230072969 + 3 ^ 40 * 2173522 * 2
def baseEnd_2173522 : Nat := 744040999414500212586107

theorem tailTrace_2173522 : CollatzResearch.WordTrace tailWord_2173522 prefixEnd_2173522 744040999414500212586107 := by
  unfold tailWord_2173522
  simp only [CollatzResearch.WordTrace]
  refine ⟨19818715007927119212332705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52849906687805651232887213 19818715007927119212332705)
  ·
    refine ⟨14864036255945339409249529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19818715007927119212332705 14864036255945339409249529)
    ·
      refine ⟨11148027191959004556937147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14864036255945339409249529 11148027191959004556937147)
      ·
        refine ⟨16722040787938506835405721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11148027191959004556937147 16722040787938506835405721)
        ·
          refine ⟨12541530590953880126554291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16722040787938506835405721 12541530590953880126554291)
          ·
            refine ⟨18812295886430820189831437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12541530590953880126554291 18812295886430820189831437)
            ·
              refine ⟨7054610957411557571186789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18812295886430820189831437 7054610957411557571186789)
              ·
                refine ⟨1322739554514667044597523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7054610957411557571186789 1322739554514667044597523)
                ·
                  refine ⟨1984109331772000566896285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1322739554514667044597523 1984109331772000566896285)
                  ·
                    refine ⟨744040999414500212586107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1984109331772000566896285 744040999414500212586107)
                    ·
                      rfl

theorem cell22_2173522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_2173522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173522 prefixEnd_2173522 := by exact prefixLift 2173522
  have htrace : WordTrace (prefixWord ++ tailWord_2173522) baseStart_2173522 baseEnd_2173522 := by
    simpa [prefixWord, tailWord_2173522, baseEnd_2173522] using wordTrace_append hprefix tailTrace_2173522
  have hstable : (prefixWord ++ tailWord_2173522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173522).length < 2 ^ (prefixWord ++ tailWord_2173522).sum := by decide
  have hdescent : baseEnd_2173522 < baseStart_2173522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173548 : List Nat := [2, 2, 1, 1, 3, 1, 4, 1, 3, 4]
def baseStart_2173548 : Nat := 118140960795 + 2173548 * 2 ^ 59
def prefixEnd_2173548 : Nat := 4983230072969 + 3 ^ 40 * 2173548 * 2
def baseEnd_2173548 : Nat := 744049899745844811436027

theorem tailTrace_2173548 : CollatzResearch.WordTrace tailWord_2173548 prefixEnd_2173548 744049899745844811436027 := by
  unfold tailWord_2173548
  simp only [CollatzResearch.WordTrace]
  refine ⟨39637904164807141644888649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52850538886409522193184865 39637904164807141644888649)
  ·
    refine ⟨29728428123605356233666487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39637904164807141644888649 29728428123605356233666487)
    ·
      refine ⟨44592642185408034350499731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29728428123605356233666487 44592642185408034350499731)
      ·
        refine ⟨66888963278112051525749597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44592642185408034350499731 66888963278112051525749597)
        ·
          refine ⟨25083361229292019322156099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66888963278112051525749597 25083361229292019322156099)
          ·
            refine ⟨37625041843938028983234149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25083361229292019322156099 37625041843938028983234149)
            ·
              refine ⟨7054695345738380434356403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37625041843938028983234149 7054695345738380434356403)
              ·
                refine ⟨10582043018607570651534605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7054695345738380434356403 10582043018607570651534605)
                ·
                  refine ⟨3968266131977838994325477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10582043018607570651534605 3968266131977838994325477)
                  ·
                    refine ⟨744049899745844811436027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3968266131977838994325477 744049899745844811436027)
                    ·
                      rfl

theorem cell22_2173548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_2173548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173548 prefixEnd_2173548 := by exact prefixLift 2173548
  have htrace : WordTrace (prefixWord ++ tailWord_2173548) baseStart_2173548 baseEnd_2173548 := by
    simpa [prefixWord, tailWord_2173548, baseEnd_2173548] using wordTrace_append hprefix tailTrace_2173548
  have hstable : (prefixWord ++ tailWord_2173548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173548).length < 2 ^ (prefixWord ++ tailWord_2173548).sum := by decide
  have hdescent : baseEnd_2173548 < baseStart_2173548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173614 : List Nat := [4, 1, 4, 1, 1, 1, 3, 3, 4]
def baseStart_2173614 : Nat := 118140960795 + 2173614 * 2 ^ 59
def prefixEnd_2173614 : Nat := 4983230072969 + 3 ^ 40 * 2173614 * 2
def baseEnd_2173614 : Nat := 248024164298214213095275

theorem tailTrace_2173614 : CollatzResearch.WordTrace tailWord_2173614 prefixEnd_2173614 248024164298214213095275 := by
  unfold tailWord_2173614
  simp only [CollatzResearch.WordTrace]
  refine ⟨9909776943421897070209987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52852143698250117707786597 9909776943421897070209987)
  ·
    refine ⟨14864665415132845605314981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9909776943421897070209987 14864665415132845605314981)
    ·
      refine ⟨2787124765337408550996559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14864665415132845605314981 2787124765337408550996559)
      ·
        refine ⟨4180687148006112826494839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2787124765337408550996559 4180687148006112826494839)
        ·
          refine ⟨6271030722009169239742259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4180687148006112826494839 6271030722009169239742259)
          ·
            refine ⟨9406546083013753859613389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6271030722009169239742259 9406546083013753859613389)
            ·
              refine ⟨3527454781130157697355021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9406546083013753859613389 3527454781130157697355021)
              ·
                refine ⟨1322795542923809136508133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3527454781130157697355021 1322795542923809136508133)
                ·
                  refine ⟨248024164298214213095275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1322795542923809136508133 248024164298214213095275)
                  ·
                    rfl

theorem cell22_2173614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_2173614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173614 prefixEnd_2173614 := by exact prefixLift 2173614
  have htrace : WordTrace (prefixWord ++ tailWord_2173614) baseStart_2173614 baseEnd_2173614 := by
    simpa [prefixWord, tailWord_2173614, baseEnd_2173614] using wordTrace_append hprefix tailTrace_2173614
  have hstable : (prefixWord ++ tailWord_2173614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173614).length < 2 ^ (prefixWord ++ tailWord_2173614).sum := by decide
  have hdescent : baseEnd_2173614 < baseStart_2173614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173700 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 5, 4]
def baseStart_2173700 : Nat := 118140960795 + 2173700 * 2 ^ 59
def prefixEnd_2173700 : Nat := 4983230072969 + 3 ^ 40 * 2173700 * 2
def baseEnd_2173700 : Nat := 744101932452167081635561

theorem tailTrace_2173700 : CollatzResearch.WordTrace tailWord_2173700 prefixEnd_2173700 744101932452167081635561 := by
  unfold tailWord_2173700
  simp only [CollatzResearch.WordTrace]
  refine ⟨39640676112531806624655277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52854234816709075499540369 39640676112531806624655277)
  ·
    refine ⟨14865253542199427484245729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39640676112531806624655277 14865253542199427484245729)
    ·
      refine ⟨11148940156649570613184297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14865253542199427484245729 11148940156649570613184297)
      ·
        refine ⟨8361705117487177959888223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11148940156649570613184297 8361705117487177959888223)
        ·
          refine ⟨12542557676230766939832335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8361705117487177959888223 12542557676230766939832335)
          ·
            refine ⟨18813836514346150409748503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12542557676230766939832335 18813836514346150409748503)
            ·
              refine ⟨28220754771519225614622755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18813836514346150409748503 28220754771519225614622755)
              ·
                refine ⟨42331132157278838421934133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28220754771519225614622755 42331132157278838421934133)
                ·
                  refine ⟨3968543639744891102056325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42331132157278838421934133 3968543639744891102056325)
                  ·
                    refine ⟨744101932452167081635561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3968543639744891102056325 744101932452167081635561)
                    ·
                      rfl

theorem cell22_2173700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_2173700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173700 prefixEnd_2173700 := by exact prefixLift 2173700
  have htrace : WordTrace (prefixWord ++ tailWord_2173700) baseStart_2173700 baseEnd_2173700 := by
    simpa [prefixWord, tailWord_2173700, baseEnd_2173700] using wordTrace_append hprefix tailTrace_2173700
  have hstable : (prefixWord ++ tailWord_2173700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173700).length < 2 ^ (prefixWord ++ tailWord_2173700).sum := by decide
  have hdescent : baseEnd_2173700 < baseStart_2173700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173745 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 4, 4]
def baseStart_2173745 : Nat := 118140960795 + 2173745 * 2 ^ 59
def prefixEnd_2173745 : Nat := 4983230072969 + 3 ^ 40 * 2173745 * 2
def baseEnd_2173745 : Nat := 744117336871801964260423

theorem tailTrace_2173745 : CollatzResearch.WordTrace tailWord_2173745 prefixEnd_2173745 744117336871801964260423 := by
  unfold tailWord_2173745
  simp only [CollatzResearch.WordTrace]
  refine ⟨79282993509900585934698689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52855329006600390623132459 79282993509900585934698689)
  ·
    refine ⟨59462245132425439451024017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79282993509900585934698689 59462245132425439451024017)
    ·
      refine ⟨44596683849319079588268013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59462245132425439451024017 44596683849319079588268013)
      ·
        refine ⟨16723756443494654845600505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44596683849319079588268013 16723756443494654845600505)
        ·
          refine ⟨12542817332620991134200379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16723756443494654845600505 12542817332620991134200379)
          ·
            refine ⟨18814225998931486701300569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12542817332620991134200379 18814225998931486701300569)
            ·
              refine ⟨14110669499198615025975427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18814225998931486701300569 14110669499198615025975427)
              ·
                refine ⟨21166004248797922538963141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14110669499198615025975427 21166004248797922538963141)
                ·
                  refine ⟨3968625796649610476055589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21166004248797922538963141 3968625796649610476055589)
                  ·
                    refine ⟨744117336871801964260423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3968625796649610476055589 744117336871801964260423)
                    ·
                      rfl

theorem cell22_2173745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_2173745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173745 prefixEnd_2173745 := by exact prefixLift 2173745
  have htrace : WordTrace (prefixWord ++ tailWord_2173745) baseStart_2173745 baseEnd_2173745 := by
    simpa [prefixWord, tailWord_2173745, baseEnd_2173745] using wordTrace_append hprefix tailTrace_2173745
  have hstable : (prefixWord ++ tailWord_2173745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173745).length < 2 ^ (prefixWord ++ tailWord_2173745).sum := by decide
  have hdescent : baseEnd_2173745 < baseStart_2173745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173747 : List Nat := [1, 1, 1, 2, 6, 2, 1, 1, 4, 3]
def baseStart_2173747 : Nat := 118140960795 + 2173747 * 2 ^ 59
def prefixEnd_2173747 : Nat := 4983230072969 + 3 ^ 40 * 2173747 * 2
def baseEnd_2173747 : Nat := 744118021512674625710417

theorem tailTrace_2173747 : CollatzResearch.WordTrace tailWord_2173747 prefixEnd_2173747 744118021512674625710417 := by
  unfold tailWord_2173747
  simp only [CollatzResearch.WordTrace]
  refine ⟨79283066455893340276271495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52855377637262226850847663 79283066455893340276271495)
  ·
    refine ⟨118924599683840010414407243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79283066455893340276271495 118924599683840010414407243)
    ·
      refine ⟨178386899525760015621610865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118924599683840010414407243 178386899525760015621610865)
      ·
        refine ⟨133790174644320011716208149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178386899525760015621610865 133790174644320011716208149)
        ·
          refine ⟨6271414436452500549197257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 133790174644320011716208149 6271414436452500549197257)
          ·
            refine ⟨4703560827339375411897943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6271414436452500549197257 4703560827339375411897943)
            ·
              refine ⟨7055341241009063117846915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4703560827339375411897943 7055341241009063117846915)
              ·
                refine ⟨10583011861513594676770373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7055341241009063117846915 10583011861513594676770373)
                ·
                  refine ⟨1984314724033799001894445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10583011861513594676770373 1984314724033799001894445)
                  ·
                    refine ⟨744118021512674625710417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1984314724033799001894445 744118021512674625710417)
                    ·
                      rfl

theorem cell22_2173747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 4, 3].length) (baseStart_2173747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173747 prefixEnd_2173747 := by exact prefixLift 2173747
  have htrace : WordTrace (prefixWord ++ tailWord_2173747) baseStart_2173747 baseEnd_2173747 := by
    simpa [prefixWord, tailWord_2173747, baseEnd_2173747] using wordTrace_append hprefix tailTrace_2173747
  have hstable : (prefixWord ++ tailWord_2173747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173747).length < 2 ^ (prefixWord ++ tailWord_2173747).sum := by decide
  have hdescent : baseEnd_2173747 < baseStart_2173747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173794 : List Nat := [3, 3, 2, 1, 4, 1, 8]
def baseStart_2173794 : Nat := 118140960795 + 2173794 * 2 ^ 59
def prefixEnd_2173794 : Nat := 4983230072969 + 3 ^ 40 * 2173794 * 2
def baseEnd_2173794 : Nat := 27560522613821561843899

theorem tailTrace_2173794 : CollatzResearch.WordTrace tailWord_2173794 prefixEnd_2173794 27560522613821561843899 := by
  unfold tailWord_2173794
  simp only [CollatzResearch.WordTrace]
  refine ⟨19821195171680766825808109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52856520457815378202154957 19821195171680766825808109)
  ·
    refine ⟨7432948189380287559678041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19821195171680766825808109 7432948189380287559678041)
    ·
      refine ⟨5574711142035215669758531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7432948189380287559678041 5574711142035215669758531)
      ·
        refine ⟨8362066713052823504637797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5574711142035215669758531 8362066713052823504637797)
        ·
          refine ⟨1567887508697404407119587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8362066713052823504637797 1567887508697404407119587)
          ·
            refine ⟨2351831263046106610679381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1567887508697404407119587 2351831263046106610679381)
            ·
              refine ⟨27560522613821561843899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2351831263046106610679381 27560522613821561843899)
              ·
                rfl

theorem cell22_2173794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 8].length) (baseStart_2173794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173794 prefixEnd_2173794 := by exact prefixLift 2173794
  have htrace : WordTrace (prefixWord ++ tailWord_2173794) baseStart_2173794 baseEnd_2173794 := by
    simpa [prefixWord, tailWord_2173794, baseEnd_2173794] using wordTrace_append hprefix tailTrace_2173794
  have hstable : (prefixWord ++ tailWord_2173794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173794).length < 2 ^ (prefixWord ++ tailWord_2173794).sum := by decide
  have hdescent : baseEnd_2173794 < baseStart_2173794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173809 : List Nat := [1, 2, 2, 2, 1, 6, 1, 1, 3, 3]
def baseStart_2173809 : Nat := 118140960795 + 2173809 * 2 ^ 59
def prefixEnd_2173809 : Nat := 4983230072969 + 3 ^ 40 * 2173809 * 2
def baseEnd_2173809 : Nat := 744139245379727130660227

theorem tailTrace_2173809 : CollatzResearch.WordTrace tailWord_2173809 prefixEnd_2173809 744139245379727130660227 := by
  unfold tailWord_2173809
  simp only [CollatzResearch.WordTrace]
  refine ⟨79285327781668724865028481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52856885187779149910018987 79285327781668724865028481)
  ·
    refine ⟨59463995836251543648771361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79285327781668724865028481 59463995836251543648771361)
    ·
      refine ⟨44597996877188657736578521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59463995836251543648771361 44597996877188657736578521)
      ·
        refine ⟨33448497657891493302433891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44597996877188657736578521 33448497657891493302433891)
        ·
          refine ⟨50172746486837239953650837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33448497657891493302433891 50172746486837239953650837)
          ·
            refine ⟨2351847491570495622827383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 50172746486837239953650837 2351847491570495622827383)
            ·
              refine ⟨3527771237355743434241075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2351847491570495622827383 3527771237355743434241075)
              ·
                refine ⟨5291656856033615151361613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3527771237355743434241075 5291656856033615151361613)
                ·
                  refine ⟨1984371321012605681760605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5291656856033615151361613 1984371321012605681760605)
                  ·
                    refine ⟨744139245379727130660227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1984371321012605681760605 744139245379727130660227)
                    ·
                      rfl

theorem cell22_2173809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 1, 3, 3].length) (baseStart_2173809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173809 prefixEnd_2173809 := by exact prefixLift 2173809
  have htrace : WordTrace (prefixWord ++ tailWord_2173809) baseStart_2173809 baseEnd_2173809 := by
    simpa [prefixWord, tailWord_2173809, baseEnd_2173809] using wordTrace_append hprefix tailTrace_2173809
  have hstable : (prefixWord ++ tailWord_2173809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173809).length < 2 ^ (prefixWord ++ tailWord_2173809).sum := by decide
  have hdescent : baseEnd_2173809 < baseStart_2173809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173820 : List Nat := [2, 2, 2, 1, 1, 1, 1, 5, 2, 5]
def baseStart_2173820 : Nat := 118140960795 + 2173820 * 2 ^ 59
def prefixEnd_2173820 : Nat := 4983230072969 + 3 ^ 40 * 2173820 * 2
def baseEnd_2173820 : Nat := 744143010904526768635193

theorem tailTrace_2173820 : CollatzResearch.WordTrace tailWord_2173820 prefixEnd_2173820 744143010904526768635193 := by
  unfold tailWord_2173820
  simp only [CollatzResearch.WordTrace]
  refine ⟨39642864492314436871839457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52857152656419249162452609 39642864492314436871839457)
  ·
    refine ⟨29732148369235827653879593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39642864492314436871839457 29732148369235827653879593)
    ·
      refine ⟨22299111276926870740409695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29732148369235827653879593 22299111276926870740409695)
      ·
        refine ⟨33448666915390306110614543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22299111276926870740409695 33448666915390306110614543)
        ·
          refine ⟨50173000373085459165921815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33448666915390306110614543 50173000373085459165921815)
          ·
            refine ⟨75259500559628188748882723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50173000373085459165921815 75259500559628188748882723)
            ·
              refine ⟨112889250839442283123324085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75259500559628188748882723 112889250839442283123324085)
              ·
                refine ⟨10583367266197714042811633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 112889250839442283123324085 10583367266197714042811633)
                ·
                  refine ⟨7937525449648285532108725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10583367266197714042811633 7937525449648285532108725)
                  ·
                    refine ⟨744143010904526768635193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7937525449648285532108725 744143010904526768635193)
                    ·
                      rfl

theorem cell22_2173820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_2173820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173820 prefixEnd_2173820 := by exact prefixLift 2173820
  have htrace : WordTrace (prefixWord ++ tailWord_2173820) baseStart_2173820 baseEnd_2173820 := by
    simpa [prefixWord, tailWord_2173820, baseEnd_2173820] using wordTrace_append hprefix tailTrace_2173820
  have hstable : (prefixWord ++ tailWord_2173820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173820).length < 2 ^ (prefixWord ++ tailWord_2173820).sum := by decide
  have hdescent : baseEnd_2173820 < baseStart_2173820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173865 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 3, 5]
def baseStart_2173865 : Nat := 118140960795 + 2173865 * 2 ^ 59
def prefixEnd_2173865 : Nat := 4983230072969 + 3 ^ 40 * 2173865 * 2
def baseEnd_2173865 : Nat := 744158415324161651260055

theorem tailTrace_2173865 : CollatzResearch.WordTrace tailWord_2173865 prefixEnd_2173865 744158415324161651260055 := by
  unfold tailWord_2173865
  simp only [CollatzResearch.WordTrace]
  refine ⟨79287370269465846429067049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52858246846310564286044699 79287370269465846429067049)
  ·
    refine ⟨59465527702099384821800287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79287370269465846429067049 59465527702099384821800287)
    ·
      refine ⟨89198291553149077232700431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59465527702099384821800287 89198291553149077232700431)
      ·
        refine ⟨133797437329723615849050647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89198291553149077232700431 133797437329723615849050647)
        ·
          refine ⟨200696155994585423773575971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133797437329723615849050647 200696155994585423773575971)
          ·
            refine ⟨301044233991878135660363957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200696155994585423773575971 301044233991878135660363957)
            ·
              refine ⟨28222896936738575218159121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 301044233991878135660363957 28222896936738575218159121)
              ·
                refine ⟨21167172702553931413619341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28222896936738575218159121 21167172702553931413619341)
                ·
                  refine ⟨7937689763457724280107253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21167172702553931413619341 7937689763457724280107253)
                  ·
                    refine ⟨744158415324161651260055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7937689763457724280107253 744158415324161651260055)
                    ·
                      rfl

theorem cell22_2173865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 5].length) (baseStart_2173865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173865 prefixEnd_2173865 := by exact prefixLift 2173865
  have htrace : WordTrace (prefixWord ++ tailWord_2173865) baseStart_2173865 baseEnd_2173865 := by
    simpa [prefixWord, tailWord_2173865, baseEnd_2173865] using wordTrace_append hprefix tailTrace_2173865
  have hstable : (prefixWord ++ tailWord_2173865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173865).length < 2 ^ (prefixWord ++ tailWord_2173865).sum := by decide
  have hdescent : baseEnd_2173865 < baseStart_2173865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173867 : List Nat := [1, 1, 1, 1, 2, 1, 1, 10, 4]
def baseStart_2173867 : Nat := 118140960795 + 2173867 * 2 ^ 59
def prefixEnd_2173867 : Nat := 4983230072969 + 3 ^ 40 * 2173867 * 2
def baseEnd_2173867 : Nat := 248053033321678104236683

theorem tailTrace_2173867 : CollatzResearch.WordTrace tailWord_2173867 prefixEnd_2173867 248053033321678104236683 := by
  unfold tailWord_2173867
  simp only [CollatzResearch.WordTrace]
  refine ⟨79287443215458600770639855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52858295476972400513759903 79287443215458600770639855)
  ·
    refine ⟨118931164823187901155959783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79287443215458600770639855 118931164823187901155959783)
    ·
      refine ⟨178396747234781851733939675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118931164823187901155959783 178396747234781851733939675)
      ·
        refine ⟨267595120852172777600909513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178396747234781851733939675 267595120852172777600909513)
        ·
          refine ⟨200696340639129583200682135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267595120852172777600909513 200696340639129583200682135)
          ·
            refine ⟨301044510958694374801023203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200696340639129583200682135 301044510958694374801023203)
            ·
              refine ⟨451566766438041562201534805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301044510958694374801023203 451566766438041562201534805)
              ·
                refine ⟨1322949511048949889262309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 451566766438041562201534805 1322949511048949889262309)
                ·
                  refine ⟨248053033321678104236683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1322949511048949889262309 248053033321678104236683)
                  ·
                    rfl

theorem cell22_2173867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10, 4].length) (baseStart_2173867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173867 prefixEnd_2173867 := by exact prefixLift 2173867
  have htrace : WordTrace (prefixWord ++ tailWord_2173867) baseStart_2173867 baseEnd_2173867 := by
    simpa [prefixWord, tailWord_2173867, baseEnd_2173867] using wordTrace_append hprefix tailTrace_2173867
  have hstable : (prefixWord ++ tailWord_2173867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173867).length < 2 ^ (prefixWord ++ tailWord_2173867).sum := by decide
  have hdescent : baseEnd_2173867 < baseStart_2173867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173882 : List Nat := [3, 1, 1, 1, 2, 1, 6, 1, 1, 5]
def baseStart_2173882 : Nat := 118140960795 + 2173882 * 2 ^ 59
def prefixEnd_2173882 : Nat := 4983230072969 + 3 ^ 40 * 2173882 * 2
def baseEnd_2173882 : Nat := 744164234771579273585003

theorem tailTrace_2173882 : CollatzResearch.WordTrace tailWord_2173882 prefixEnd_2173882 744164234771579273585003 := by
  unfold tailWord_2173882
  simp only [CollatzResearch.WordTrace]
  refine ⟨19821997577601064583108975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52858660206936172221623933 19821997577601064583108975)
  ·
    refine ⟨29732996366401596874663463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19821997577601064583108975 29732996366401596874663463)
    ·
      refine ⟨44599494549602395311995195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29732996366401596874663463 44599494549602395311995195)
      ·
        refine ⟨66899241824403592967992793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44599494549602395311995195 66899241824403592967992793)
        ·
          refine ⟨50174431368302694725994595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66899241824403592967992793 50174431368302694725994595)
          ·
            refine ⟨75261647052454042088991893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50174431368302694725994595 75261647052454042088991893)
            ·
              refine ⟨3527889705583783222921495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75261647052454042088991893 3527889705583783222921495)
              ·
                refine ⟨5291834558375674834382243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3527889705583783222921495 5291834558375674834382243)
                ·
                  refine ⟨7937751837563512251573365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5291834558375674834382243 7937751837563512251573365)
                  ·
                    refine ⟨744164234771579273585003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7937751837563512251573365 744164234771579273585003)
                    ·
                      rfl

theorem cell22_2173882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_2173882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173882 prefixEnd_2173882 := by exact prefixLift 2173882
  have htrace : WordTrace (prefixWord ++ tailWord_2173882) baseStart_2173882 baseEnd_2173882 := by
    simpa [prefixWord, tailWord_2173882, baseEnd_2173882] using wordTrace_append hprefix tailTrace_2173882
  have hstable : (prefixWord ++ tailWord_2173882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173882).length < 2 ^ (prefixWord ++ tailWord_2173882).sum := by decide
  have hdescent : baseEnd_2173882 < baseStart_2173882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173894 : List Nat := [6, 1, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_2173894 : Nat := 118140960795 + 2173894 * 2 ^ 59
def prefixEnd_2173894 : Nat := 4983230072969 + 3 ^ 40 * 2173894 * 2
def baseEnd_2173894 : Nat := 744168342616815242284967

theorem tailTrace_2173894 : CollatzResearch.WordTrace tailWord_2173894 prefixEnd_2173894 744168342616815242284967 := by
  unfold tailWord_2173894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2477763374573774511933523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 52858951990907189587915157 2477763374573774511933523)
  ·
    refine ⟨3716645061860661767900285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2477763374573774511933523 3716645061860661767900285)
    ·
      refine ⟨1393741898197748162962607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3716645061860661767900285 1393741898197748162962607)
      ·
        refine ⟨2090612847296622244443911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1393741898197748162962607 2090612847296622244443911)
        ·
          refine ⟨3135919270944933366665867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2090612847296622244443911 3135919270944933366665867)
          ·
            refine ⟨4703878906417400049998801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3135919270944933366665867 4703878906417400049998801)
            ·
              refine ⟨3527909179813050037499101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4703878906417400049998801 3527909179813050037499101)
              ·
                refine ⟨1322965942429893764062163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3527909179813050037499101 1322965942429893764062163)
                ·
                  refine ⟨1984448913644840646093245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1322965942429893764062163 1984448913644840646093245)
                  ·
                    refine ⟨744168342616815242284967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1984448913644840646093245 744168342616815242284967)
                    ·
                      rfl

theorem cell22_2173894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_2173894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173894 prefixEnd_2173894 := by exact prefixLift 2173894
  have htrace : WordTrace (prefixWord ++ tailWord_2173894) baseStart_2173894 baseEnd_2173894 := by
    simpa [prefixWord, tailWord_2173894, baseEnd_2173894] using wordTrace_append hprefix tailTrace_2173894
  have hstable : (prefixWord ++ tailWord_2173894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173894).length < 2 ^ (prefixWord ++ tailWord_2173894).sum := by decide
  have hdescent : baseEnd_2173894 < baseStart_2173894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173895 : List Nat := [1, 1, 4, 1, 1, 2, 2, 10]
def baseStart_2173895 : Nat := 118140960795 + 2173895 * 2 ^ 59
def prefixEnd_2173895 : Nat := 4983230072969 + 3 ^ 40 * 2173895 * 2
def baseEnd_2173895 : Nat := 82685409437472397001107

theorem tailTrace_2173895 : CollatzResearch.WordTrace tailWord_2173895 prefixEnd_2173895 82685409437472397001107 := by
  unfold tailWord_2173895
  simp only [CollatzResearch.WordTrace]
  refine ⟨79288464459357161552659139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52858976306238107701772759 79288464459357161552659139)
  ·
    refine ⟨118932696689035742328988709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79288464459357161552659139 118932696689035742328988709)
    ·
      refine ⟨22299880629194201686685383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118932696689035742328988709 22299880629194201686685383)
      ·
        refine ⟨33449820943791302530028075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22299880629194201686685383 33449820943791302530028075)
        ·
          refine ⟨50174731415686953795042113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33449820943791302530028075 50174731415686953795042113)
          ·
            refine ⟨37631048561765215346281585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50174731415686953795042113 37631048561765215346281585)
            ·
              refine ⟨28223286421323911509711189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37631048561765215346281585 28223286421323911509711189)
              ·
                refine ⟨82685409437472397001107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 28223286421323911509711189 82685409437472397001107)
                ·
                  rfl

theorem cell22_2173895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 10].length) (baseStart_2173895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173895 prefixEnd_2173895 := by exact prefixLift 2173895
  have htrace : WordTrace (prefixWord ++ tailWord_2173895) baseStart_2173895 baseEnd_2173895 := by
    simpa [prefixWord, tailWord_2173895, baseEnd_2173895] using wordTrace_append hprefix tailTrace_2173895
  have hstable : (prefixWord ++ tailWord_2173895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173895).length < 2 ^ (prefixWord ++ tailWord_2173895).sum := by decide
  have hdescent : baseEnd_2173895 < baseStart_2173895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173978 : List Nat := [3, 1, 1, 3, 1, 2, 5, 2, 1, 3]
def baseStart_2173978 : Nat := 118140960795 + 2173978 * 2 ^ 59
def prefixEnd_2173978 : Nat := 4983230072969 + 3 ^ 40 * 2173978 * 2
def baseEnd_2173978 : Nat := 744197097533467023184709

theorem tailTrace_2173978 : CollatzResearch.WordTrace tailWord_2173978 prefixEnd_2173978 744197097533467023184709 := by
  unfold tailWord_2173978
  simp only [CollatzResearch.WordTrace]
  refine ⟨19822872929514116681982647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52860994478704311151953725 19822872929514116681982647)
  ·
    refine ⟨29734309394271175022973971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19822872929514116681982647 29734309394271175022973971)
    ·
      refine ⟨44601464091406762534460957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29734309394271175022973971 44601464091406762534460957)
      ·
        refine ⟨16725549034277535950422859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44601464091406762534460957 16725549034277535950422859)
        ·
          refine ⟨25088323551416303925634289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16725549034277535950422859 25088323551416303925634289)
          ·
            refine ⟨18816242663562227944225717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25088323551416303925634289 18816242663562227944225717)
            ·
              refine ⟨1764022749708958869771161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18816242663562227944225717 1764022749708958869771161)
              ·
                refine ⟨1323017062281719152328371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1764022749708958869771161 1323017062281719152328371)
                ·
                  refine ⟨1984525593422578728492557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1323017062281719152328371 1984525593422578728492557)
                  ·
                    refine ⟨744197097533467023184709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1984525593422578728492557 744197097533467023184709)
                    ·
                      rfl

theorem cell22_2173978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2, 1, 3].length) (baseStart_2173978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173978 prefixEnd_2173978 := by exact prefixLift 2173978
  have htrace : WordTrace (prefixWord ++ tailWord_2173978) baseStart_2173978 baseEnd_2173978 := by
    simpa [prefixWord, tailWord_2173978, baseEnd_2173978] using wordTrace_append hprefix tailTrace_2173978
  have hstable : (prefixWord ++ tailWord_2173978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173978).length < 2 ^ (prefixWord ++ tailWord_2173978).sum := by decide
  have hdescent : baseEnd_2173978 < baseStart_2173978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2173991 : List Nat := [1, 1, 7, 1, 1, 2, 1, 3, 5]
def baseStart_2173991 : Nat := 118140960795 + 2173991 * 2 ^ 59
def prefixEnd_2173991 : Nat := 4983230072969 + 3 ^ 40 * 2173991 * 2
def baseEnd_2173991 : Nat := 248067182566379774203223

theorem tailTrace_2173991 : CollatzResearch.WordTrace tailWord_2173991 prefixEnd_2173991 248067182566379774203223 := by
  unfold tailWord_2173991
  simp only [CollatzResearch.WordTrace]
  refine ⟨79291965867009369948153827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52861310578006246632102551 79291965867009369948153827)
  ·
    refine ⟨118937948800514054922230741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79291965867009369948153827 118937948800514054922230741)
    ·
      refine ⟨2787608175012048162239783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 118937948800514054922230741 2787608175012048162239783)
      ·
        refine ⟨4181412262518072243359675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2787608175012048162239783 4181412262518072243359675)
        ·
          refine ⟨6272118393777108365039513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4181412262518072243359675 6272118393777108365039513)
          ·
            refine ⟨4704088795332831273779635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6272118393777108365039513 4704088795332831273779635)
            ·
              refine ⟨7056133192999246910669453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4704088795332831273779635 7056133192999246910669453)
              ·
                refine ⟨2646049947374717591501045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7056133192999246910669453 2646049947374717591501045)
                ·
                  refine ⟨248067182566379774203223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2646049947374717591501045 248067182566379774203223)
                  ·
                    rfl

theorem cell22_2173991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 5].length) (baseStart_2173991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2173991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2173991 prefixEnd_2173991 := by exact prefixLift 2173991
  have htrace : WordTrace (prefixWord ++ tailWord_2173991) baseStart_2173991 baseEnd_2173991 := by
    simpa [prefixWord, tailWord_2173991, baseEnd_2173991] using wordTrace_append hprefix tailTrace_2173991
  have hstable : (prefixWord ++ tailWord_2173991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2173991).length < 2 ^ (prefixWord ++ tailWord_2173991).sum := by decide
  have hdescent : baseEnd_2173991 < baseStart_2173991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2173991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174002 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 8]
def baseStart_2174002 : Nat := 118140960795 + 2174002 * 2 ^ 59
def prefixEnd_2174002 : Nat := 4983230072969 + 3 ^ 40 * 2174002 * 2
def baseEnd_2174002 : Nat := 248068437741312986861545

theorem tailTrace_2174002 : CollatzResearch.WordTrace tailWord_2174002 prefixEnd_2174002 248068437741312986861545 := by
  unfold tailWord_2174002
  simp only [CollatzResearch.WordTrace]
  refine ⟨19823091767492379706701065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52861578046646345884536173 19823091767492379706701065)
  ·
    refine ⟨14867318825619284780025799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19823091767492379706701065 14867318825619284780025799)
    ·
      refine ⟨22300978238428927170038699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14867318825619284780025799 22300978238428927170038699)
      ·
        refine ⟨33451467357643390755058049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22300978238428927170038699 33451467357643390755058049)
        ·
          refine ⟨25088600518232543066293537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33451467357643390755058049 25088600518232543066293537)
          ·
            refine ⟨18816450388674407299720153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25088600518232543066293537 18816450388674407299720153)
            ·
              refine ⟨14112337791505805474790115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18816450388674407299720153 14112337791505805474790115)
              ·
                refine ⟨21168506687258708212185173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14112337791505805474790115 21168506687258708212185173)
                ·
                  refine ⟨248068437741312986861545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21168506687258708212185173 248068437741312986861545)
                  ·
                    rfl

theorem cell22_2174002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_2174002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2174002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2174002 prefixEnd_2174002 := by exact prefixLift 2174002
  have htrace : WordTrace (prefixWord ++ tailWord_2174002) baseStart_2174002 baseEnd_2174002 := by
    simpa [prefixWord, tailWord_2174002, baseEnd_2174002] using wordTrace_append hprefix tailTrace_2174002
  have hstable : (prefixWord ++ tailWord_2174002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174002).length < 2 ^ (prefixWord ++ tailWord_2174002).sum := by decide
  have hdescent : baseEnd_2174002 < baseStart_2174002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174019 : List Nat := [1, 1, 1, 3, 1, 2, 4, 5, 4]
def baseStart_2174019 : Nat := 118140960795 + 2174019 * 2 ^ 59
def prefixEnd_2174019 : Nat := 4983230072969 + 3 ^ 40 * 2174019 * 2
def baseEnd_2174019 : Nat := 248070377557118860969861

theorem tailTrace_2174019 : CollatzResearch.WordTrace tailWord_2174019 prefixEnd_2174019 248070377557118860969861 := by
  unfold tailWord_2174019
  simp only [CollatzResearch.WordTrace]
  refine ⟨79292987110907930730173111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52861991407271953820115407 79292987110907930730173111)
  ·
    refine ⟨118939480666361896095259667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79292987110907930730173111 118939480666361896095259667)
    ·
      refine ⟨178409220999542844142889501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118939480666361896095259667 178409220999542844142889501)
      ·
        refine ⟨66903457874828566553583563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178409220999542844142889501 66903457874828566553583563)
        ·
          refine ⟨100355186812242849830375345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66903457874828566553583563 100355186812242849830375345)
          ·
            refine ⟨75266390109182137372781509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100355186812242849830375345 75266390109182137372781509)
            ·
              refine ⟨14112448145471650757396533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75266390109182137372781509 14112448145471650757396533)
              ·
                refine ⟨1323042013637967258505925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14112448145471650757396533 1323042013637967258505925)
                ·
                  refine ⟨248070377557118860969861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1323042013637967258505925 248070377557118860969861)
                  ·
                    rfl

theorem cell22_2174019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 5, 4].length) (baseStart_2174019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2174019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2174019 prefixEnd_2174019 := by exact prefixLift 2174019
  have htrace : WordTrace (prefixWord ++ tailWord_2174019) baseStart_2174019 baseEnd_2174019 := by
    simpa [prefixWord, tailWord_2174019, baseEnd_2174019] using wordTrace_append hprefix tailTrace_2174019
  have hstable : (prefixWord ++ tailWord_2174019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174019).length < 2 ^ (prefixWord ++ tailWord_2174019).sum := by decide
  have hdescent : baseEnd_2174019 < baseStart_2174019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174064 : List Nat := [2, 1, 1, 1, 5, 1, 5, 6]
def baseStart_2174064 : Nat := 118140960795 + 2174064 * 2 ^ 59
def prefixEnd_2174064 : Nat := 4983230072969 + 3 ^ 40 * 2174064 * 2
def baseEnd_2174064 : Nat := 82691837454554607281605

theorem tailTrace_2174064 : CollatzResearch.WordTrace tailWord_2174064 prefixEnd_2174064 82691837454554607281605 := by
  unfold tailWord_2174064
  simp only [CollatzResearch.WordTrace]
  refine ⟨39647314197872451707780623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52863085597163268943707497 39647314197872451707780623)
  ·
    refine ⟨59470971296808677561670935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39647314197872451707780623 59470971296808677561670935)
    ·
      refine ⟨89206456945213016342506403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59470971296808677561670935 89206456945213016342506403)
      ·
        refine ⟨133809685417819524513759605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89206456945213016342506403 133809685417819524513759605)
        ·
          refine ⟨12544658007920580423164963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 133809685417819524513759605 12544658007920580423164963)
          ·
            refine ⟨18816987011880870634747445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12544658007920580423164963 18816987011880870634747445)
            ·
              refine ⟨1764092532363831622007573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18816987011880870634747445 1764092532363831622007573)
              ·
                refine ⟨82691837454554607281605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1764092532363831622007573 82691837454554607281605)
                ·
                  rfl

theorem cell22_2174064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 6].length) (baseStart_2174064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2174064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2174064 prefixEnd_2174064 := by exact prefixLift 2174064
  have htrace : WordTrace (prefixWord ++ tailWord_2174064) baseStart_2174064 baseEnd_2174064 := by
    simpa [prefixWord, tailWord_2174064, baseEnd_2174064] using wordTrace_append hprefix tailTrace_2174064
  have hstable : (prefixWord ++ tailWord_2174064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174064).length < 2 ^ (prefixWord ++ tailWord_2174064).sum := by decide
  have hdescent : baseEnd_2174064 < baseStart_2174064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174085 : List Nat := [1, 3, 1, 1, 7, 1, 1, 2, 2, 3]
def baseStart_2174085 : Nat := 118140960795 + 2174085 * 2 ^ 59
def prefixEnd_2174085 : Nat := 4983230072969 + 3 ^ 40 * 2174085 * 2
def baseEnd_2174085 : Nat := 744233725820154410759381

theorem tailTrace_2174085 : CollatzResearch.WordTrace tailWord_2174085 prefixEnd_2174085 744233725820154410759381 := by
  unfold tailWord_2174085
  simp only [CollatzResearch.WordTrace]
  refine ⟨79295394328668824002075709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52863596219112549334717139 79295394328668824002075709)
  ·
    refine ⟨29735772873250809000778391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79295394328668824002075709 29735772873250809000778391)
    ·
      refine ⟨44603659309876213501167587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29735772873250809000778391 44603659309876213501167587)
      ·
        refine ⟨66905488964814320251751381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44603659309876213501167587 66905488964814320251751381)
        ·
          refine ⟨1568097397612835630900423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 66905488964814320251751381 1568097397612835630900423)
          ·
            refine ⟨2352146096419253446350635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1568097397612835630900423 2352146096419253446350635)
            ·
              refine ⟨3528219144628880169525953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2352146096419253446350635 3528219144628880169525953)
              ·
                refine ⟨2646164358471660127144465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3528219144628880169525953 2646164358471660127144465)
                ·
                  refine ⟨1984623268853745095358349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2646164358471660127144465 1984623268853745095358349)
                  ·
                    refine ⟨744233725820154410759381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1984623268853745095358349 744233725820154410759381)
                    ·
                      rfl

theorem cell22_2174085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 2, 3].length) (baseStart_2174085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2174085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2174085 prefixEnd_2174085 := by exact prefixLift 2174085
  have htrace : WordTrace (prefixWord ++ tailWord_2174085) baseStart_2174085 baseEnd_2174085 := by
    simpa [prefixWord, tailWord_2174085, baseEnd_2174085] using wordTrace_append hprefix tailTrace_2174085
  have hstable : (prefixWord ++ tailWord_2174085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174085).length < 2 ^ (prefixWord ++ tailWord_2174085).sum := by decide
  have hdescent : baseEnd_2174085 < baseStart_2174085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174130 : List Nat := [3, 2, 1, 1, 1, 6, 1, 3, 1, 3]
def baseStart_2174130 : Nat := 118140960795 + 2174130 * 2 ^ 59
def prefixEnd_2174130 : Nat := 4983230072969 + 3 ^ 40 * 2174130 * 2
def baseEnd_2174130 : Nat := 744249130239789293384243

theorem tailTrace_2174130 : CollatzResearch.WordTrace tailWord_2174130 prefixEnd_2174130 744249130239789293384243 := by
  unfold tailWord_2174130
  simp only [CollatzResearch.WordTrace]
  refine ⟨19824258903376449171865961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52864690409003864458309229 19824258903376449171865961)
  ·
    refine ⟨14868194177532336878899471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19824258903376449171865961 14868194177532336878899471)
    ·
      refine ⟨22302291266298505318349207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14868194177532336878899471 22302291266298505318349207)
      ·
        refine ⟨33453436899447757977523811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22302291266298505318349207 33453436899447757977523811)
        ·
          refine ⟨50180155349171636966285717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33453436899447757977523811 50180155349171636966285717)
          ·
            refine ⟨2352194781992420482794643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 50180155349171636966285717 2352194781992420482794643)
            ·
              refine ⟨3528292172988630724191965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2352194781992420482794643 3528292172988630724191965)
              ·
                refine ⟨1323109564870736521571987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3528292172988630724191965 1323109564870736521571987)
                ·
                  refine ⟨1984664347306104782357981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1323109564870736521571987 1984664347306104782357981)
                  ·
                    refine ⟨744249130239789293384243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1984664347306104782357981 744249130239789293384243)
                    ·
                      rfl

theorem cell22_2174130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_2174130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2174130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2174130 prefixEnd_2174130 := by exact prefixLift 2174130
  have htrace : WordTrace (prefixWord ++ tailWord_2174130) baseStart_2174130 baseEnd_2174130 := by
    simpa [prefixWord, tailWord_2174130, baseEnd_2174130] using wordTrace_append hprefix tailTrace_2174130
  have hstable : (prefixWord ++ tailWord_2174130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174130).length < 2 ^ (prefixWord ++ tailWord_2174130).sum := by decide
  have hdescent : baseEnd_2174130 < baseStart_2174130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174169 : List Nat := [1, 2, 1, 2, 3, 1, 1, 5, 1, 5]
def baseStart_2174169 : Nat := 118140960795 + 2174169 * 2 ^ 59
def prefixEnd_2174169 : Nat := 4983230072969 + 3 ^ 40 * 2174169 * 2
def baseEnd_2174169 : Nat := 744262480736806191659123

theorem tailTrace_2174169 : CollatzResearch.WordTrace tailWord_2174169 prefixEnd_2174169 744262480736806191659123 := by
  unfold tailWord_2174169
  simp only [CollatzResearch.WordTrace]
  refine ⟨79298458060364506348133561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52865638706909670898755707 79298458060364506348133561)
  ·
    refine ⟨59473843545273379761100171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79298458060364506348133561 59473843545273379761100171)
    ·
      refine ⟨89210765317910069641650257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59473843545273379761100171 89210765317910069641650257)
      ·
        refine ⟨66908073988432552231237693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89210765317910069641650257 66908073988432552231237693)
        ·
          refine ⟨25090527745662207086714135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66908073988432552231237693 25090527745662207086714135)
          ·
            refine ⟨37635791618493310630071203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25090527745662207086714135 37635791618493310630071203)
            ·
              refine ⟨56453687427739965945106805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37635791618493310630071203 56453687427739965945106805)
              ·
                refine ⟨5292533196350621807353763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56453687427739965945106805 5292533196350621807353763)
                ·
                  refine ⟨7938799794525932711030645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5292533196350621807353763 7938799794525932711030645)
                  ·
                    refine ⟨744262480736806191659123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7938799794525932711030645 744262480736806191659123)
                    ·
                      rfl

theorem cell22_2174169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 5].length) (baseStart_2174169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2174169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2174169 prefixEnd_2174169 := by exact prefixLift 2174169
  have htrace : WordTrace (prefixWord ++ tailWord_2174169) baseStart_2174169 baseEnd_2174169 := by
    simpa [prefixWord, tailWord_2174169, baseEnd_2174169] using wordTrace_append hprefix tailTrace_2174169
  have hstable : (prefixWord ++ tailWord_2174169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174169).length < 2 ^ (prefixWord ++ tailWord_2174169).sum := by decide
  have hdescent : baseEnd_2174169 < baseStart_2174169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174173 : List Nat := [1, 4, 3, 2, 2, 1, 1, 1, 3, 4]
def baseStart_2174173 : Nat := 118140960795 + 2174173 * 2 ^ 59
def prefixEnd_2174173 : Nat := 4983230072969 + 3 ^ 40 * 2174173 * 2
def baseEnd_2174173 : Nat := 744263850018551514559111

theorem tailTrace_2174173 : CollatzResearch.WordTrace tailWord_2174173 prefixEnd_2174173 744263850018551514559111 := by
  unfold tailWord_2174173
  simp only [CollatzResearch.WordTrace]
  refine ⟨79298603952350015031279173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52865735968233343354186115 79298603952350015031279173)
  ·
    refine ⟨14868488241065627818364845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79298603952350015031279173 14868488241065627818364845)
    ·
      refine ⟨5575683090399610431886817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14868488241065627818364845 5575683090399610431886817)
      ·
        refine ⟨4181762317799707823915113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5575683090399610431886817 4181762317799707823915113)
        ·
          refine ⟨3136321738349780867936335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4181762317799707823915113 3136321738349780867936335)
          ·
            refine ⟨4704482607524671301904503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3136321738349780867936335 4704482607524671301904503)
            ·
              refine ⟨7056723911287006952856755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4704482607524671301904503 7056723911287006952856755)
              ·
                refine ⟨10585085866930510429285133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7056723911287006952856755 10585085866930510429285133)
                ·
                  refine ⟨3969407200098941410981925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10585085866930510429285133 3969407200098941410981925)
                  ·
                    refine ⟨744263850018551514559111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3969407200098941410981925 744263850018551514559111)
                    ·
                      rfl

theorem cell22_2174173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_2174173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2174173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2174173 prefixEnd_2174173 := by exact prefixLift 2174173
  have htrace : WordTrace (prefixWord ++ tailWord_2174173) baseStart_2174173 baseEnd_2174173 := by
    simpa [prefixWord, tailWord_2174173, baseEnd_2174173] using wordTrace_append hprefix tailTrace_2174173
  have hstable : (prefixWord ++ tailWord_2174173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174173).length < 2 ^ (prefixWord ++ tailWord_2174173).sum := by decide
  have hdescent : baseEnd_2174173 < baseStart_2174173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174186 : List Nat := [3, 1, 3, 1, 1, 4, 1, 2, 1, 5]
def baseStart_2174186 : Nat := 118140960795 + 2174186 * 2 ^ 59
def prefixEnd_2174186 : Nat := 4983230072969 + 3 ^ 40 * 2174186 * 2
def baseEnd_2174186 : Nat := 744268300184223813984071

theorem tailTrace_2174186 : CollatzResearch.WordTrace tailWord_2174186 prefixEnd_2174186 744268300184223813984071 := by
  unfold tailWord_2174186
  simp only [CollatzResearch.WordTrace]
  refine ⟨19824769525325729562875603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52866052067535278834334941 19824769525325729562875603)
  ·
    refine ⟨29737154287988594344313405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19824769525325729562875603 29737154287988594344313405)
    ·
      refine ⟨11151432857995722879117527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29737154287988594344313405 11151432857995722879117527)
      ·
        refine ⟨16727149286993584318676291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11151432857995722879117527 16727149286993584318676291)
        ·
          refine ⟨25090723930490376478014437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16727149286993584318676291 25090723930490376478014437)
          ·
            refine ⟨4704510736966945589627707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25090723930490376478014437 4704510736966945589627707)
            ·
              refine ⟨7056766105450418384441561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4704510736966945589627707 7056766105450418384441561)
              ·
                refine ⟨5292574579087813788331171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7056766105450418384441561 5292574579087813788331171)
                ·
                  refine ⟨7938861868631720682496757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5292574579087813788331171 7938861868631720682496757)
                  ·
                    refine ⟨744268300184223813984071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7938861868631720682496757 744268300184223813984071)
                    ·
                      rfl

theorem cell22_2174186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_2174186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2174186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2174186 prefixEnd_2174186 := by exact prefixLift 2174186
  have htrace : WordTrace (prefixWord ++ tailWord_2174186) baseStart_2174186 baseEnd_2174186 := by
    simpa [prefixWord, tailWord_2174186, baseEnd_2174186] using wordTrace_append hprefix tailTrace_2174186
  have hstable : (prefixWord ++ tailWord_2174186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174186).length < 2 ^ (prefixWord ++ tailWord_2174186).sum := by decide
  have hdescent : baseEnd_2174186 < baseStart_2174186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174229 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 4, 6]
def baseStart_2174229 : Nat := 118140960795 + 2174229 * 2 ^ 59
def prefixEnd_2174229 : Nat := 4983230072969 + 3 ^ 40 * 2174229 * 2
def baseEnd_2174229 : Nat := 744283019962986035158939

theorem tailTrace_2174229 : CollatzResearch.WordTrace tailWord_2174229 prefixEnd_2174229 744283019962986035158939 := by
  unfold tailWord_2174229
  simp only [CollatzResearch.WordTrace]
  refine ⟨79300646440147136595317741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52867097626764757730211827 79300646440147136595317741)
  ·
    refine ⟨29737742415055176223244153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79300646440147136595317741 29737742415055176223244153)
    ·
      refine ⟨22303306811291382167433115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29737742415055176223244153 22303306811291382167433115)
      ·
        refine ⟨33454960216937073251149673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22303306811291382167433115 33454960216937073251149673)
        ·
          refine ⟨25091220162702804938362255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33454960216937073251149673 25091220162702804938362255)
          ·
            refine ⟨37636830244054207407543383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25091220162702804938362255 37636830244054207407543383)
            ·
              refine ⟨56455245366081311111315075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37636830244054207407543383 56455245366081311111315075)
              ·
                refine ⟨84682868049121966666972613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56455245366081311111315075 84682868049121966666972613)
                ·
                  refine ⟨15878037759210368750057365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84682868049121966666972613 15878037759210368750057365)
                  ·
                    refine ⟨744283019962986035158939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15878037759210368750057365 744283019962986035158939)
                    ·
                      rfl

theorem cell22_2174229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_2174229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2174229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2174229 prefixEnd_2174229 := by exact prefixLift 2174229
  have htrace : WordTrace (prefixWord ++ tailWord_2174229) baseStart_2174229 baseEnd_2174229 := by
    simpa [prefixWord, tailWord_2174229, baseEnd_2174229] using wordTrace_append hprefix tailTrace_2174229
  have hstable : (prefixWord ++ tailWord_2174229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174229).length < 2 ^ (prefixWord ++ tailWord_2174229).sum := by decide
  have hdescent : baseEnd_2174229 < baseStart_2174229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174261 : List Nat := [1, 3, 3, 1, 2, 3, 1, 1, 7]
def baseStart_2174261 : Nat := 118140960795 + 2174261 * 2 ^ 59
def prefixEnd_2174261 : Nat := 4983230072969 + 3 ^ 40 * 2174261 * 2
def baseEnd_2174261 : Nat := 248097991405649539452947

theorem tailTrace_2174261 : CollatzResearch.WordTrace tailWord_2174261 prefixEnd_2174261 248097991405649539452947 := by
  unfold tailWord_2174261
  simp only [CollatzResearch.WordTrace]
  refine ⟨79301813576031206060482637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52867875717354137373655091 79301813576031206060482637)
  ·
    refine ⟨29738180091011702272680989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79301813576031206060482637 29738180091011702272680989)
    ·
      refine ⟨11151817534129388352255371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29738180091011702272680989 11151817534129388352255371)
      ·
        refine ⟨16727726301194082528383057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11151817534129388352255371 16727726301194082528383057)
        ·
          refine ⟨12545794725895561896287293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16727726301194082528383057 12545794725895561896287293)
          ·
            refine ⟨4704673022210835711107735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12545794725895561896287293 4704673022210835711107735)
            ·
              refine ⟨7057009533316253566661603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4704673022210835711107735 7057009533316253566661603)
              ·
                refine ⟨10585514299974380349992405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7057009533316253566661603 10585514299974380349992405)
                ·
                  refine ⟨248097991405649539452947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10585514299974380349992405 248097991405649539452947)
                  ·
                    rfl

theorem cell22_2174261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 7].length) (baseStart_2174261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2174261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2174261 prefixEnd_2174261 := by exact prefixLift 2174261
  have htrace : WordTrace (prefixWord ++ tailWord_2174261) baseStart_2174261 baseEnd_2174261 := by
    simpa [prefixWord, tailWord_2174261, baseEnd_2174261] using wordTrace_append hprefix tailTrace_2174261
  have hstable : (prefixWord ++ tailWord_2174261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174261).length < 2 ^ (prefixWord ++ tailWord_2174261).sum := by decide
  have hdescent : baseEnd_2174261 < baseStart_2174261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174265 : List Nat := [1, 2, 1, 6, 2, 1, 2, 1, 3, 3]
def baseStart_2174265 : Nat := 118140960795 + 2174265 * 2 ^ 59
def prefixEnd_2174265 : Nat := 4983230072969 + 3 ^ 40 * 2174265 * 2
def baseEnd_2174265 : Nat := 744295343498693941258829

theorem tailTrace_2174265 : CollatzResearch.WordTrace tailWord_2174265 prefixEnd_2174265 744295343498693941258829 := by
  unfold tailWord_2174265
  simp only [CollatzResearch.WordTrace]
  refine ⟨79301959468016714743628249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52867972978677809829085499 79301959468016714743628249)
  ·
    refine ⟨59476469601012536057721187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79301959468016714743628249 59476469601012536057721187)
    ·
      refine ⟨89214704401518804086581781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59476469601012536057721187 89214704401518804086581781)
      ·
        refine ⟨4181939268821193941558521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 89214704401518804086581781 4181939268821193941558521)
        ·
          refine ⟨3136454451615895456168891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4181939268821193941558521 3136454451615895456168891)
          ·
            refine ⟨4704681677423843184253337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3136454451615895456168891 4704681677423843184253337)
            ·
              refine ⟨3528511258067882388190003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4704681677423843184253337 3528511258067882388190003)
              ·
                refine ⟨5292766887101823582285005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3528511258067882388190003 5292766887101823582285005)
                ·
                  refine ⟨1984787582663183843356877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5292766887101823582285005 1984787582663183843356877)
                  ·
                    refine ⟨744295343498693941258829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1984787582663183843356877 744295343498693941258829)
                    ·
                      rfl

theorem cell22_2174265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 3, 3].length) (baseStart_2174265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2174265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2174265 prefixEnd_2174265 := by exact prefixLift 2174265
  have htrace : WordTrace (prefixWord ++ tailWord_2174265) baseStart_2174265 baseEnd_2174265 := by
    simpa [prefixWord, tailWord_2174265, baseEnd_2174265] using wordTrace_append hprefix tailTrace_2174265
  have hstable : (prefixWord ++ tailWord_2174265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174265).length < 2 ^ (prefixWord ++ tailWord_2174265).sum := by decide
  have hdescent : baseEnd_2174265 < baseStart_2174265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174308 : List Nat := [2, 3, 1, 1, 3, 2, 2, 3, 1, 4]
def baseStart_2174308 : Nat := 118140960795 + 2174308 * 2 ^ 59
def prefixEnd_2174308 : Nat := 4983230072969 + 3 ^ 40 * 2174308 * 2
def baseEnd_2174308 : Nat := 744310063277456162433697

theorem tailTrace_2174308 : CollatzResearch.WordTrace tailWord_2174308 prefixEnd_2174308 744310063277456162433697 := by
  unfold tailWord_2174308
  simp only [CollatzResearch.WordTrace]
  refine ⟨39651763903430466543721789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52869018537907288724962385 39651763903430466543721789)
  ·
    refine ⟨14869411463786424953895671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39651763903430466543721789 14869411463786424953895671)
    ·
      refine ⟨22304117195679637430843507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14869411463786424953895671 22304117195679637430843507)
      ·
        refine ⟨33456175793519456146265261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22304117195679637430843507 33456175793519456146265261)
        ·
          refine ⟨12546065922569796054849473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33456175793519456146265261 12546065922569796054849473)
          ·
            refine ⟨9409549441927347041137105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12546065922569796054849473 9409549441927347041137105)
            ·
              refine ⟨7057162081445510280852829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9409549441927347041137105 7057162081445510280852829)
              ·
                refine ⟨2646435780542066355319811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7057162081445510280852829 2646435780542066355319811)
                ·
                  refine ⟨3969653670813099532979717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2646435780542066355319811 3969653670813099532979717)
                  ·
                    refine ⟨744310063277456162433697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3969653670813099532979717 744310063277456162433697)
                    ·
                      rfl

theorem cell22_2174308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_2174308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2174308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2174308 prefixEnd_2174308 := by exact prefixLift 2174308
  have htrace : WordTrace (prefixWord ++ tailWord_2174308) baseStart_2174308 baseEnd_2174308 := by
    simpa [prefixWord, tailWord_2174308, baseEnd_2174308] using wordTrace_append hprefix tailTrace_2174308
  have hstable : (prefixWord ++ tailWord_2174308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174308).length < 2 ^ (prefixWord ++ tailWord_2174308).sum := by decide
  have hdescent : baseEnd_2174308 < baseStart_2174308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174473 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 6, 3]
def baseStart_2174473 : Nat := 118140960795 + 2174473 * 2 ^ 59
def prefixEnd_2174473 : Nat := 4983230072969 + 3 ^ 40 * 2174473 * 2
def baseEnd_2174473 : Nat := 744366546149450732058191

theorem tailTrace_2174473 : CollatzResearch.WordTrace tailWord_2174473 prefixEnd_2174473 744366546149450732058191 := by
  unfold tailWord_2174473
  simp only [CollatzResearch.WordTrace]
  refine ⟨79309545851263166267200073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52873030567508777511466715 79309545851263166267200073)
  ·
    refine ⟨59482159388447374700400055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79309545851263166267200073 59482159388447374700400055)
    ·
      refine ⟨89223239082671062050600083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59482159388447374700400055 89223239082671062050600083)
      ·
        refine ⟨133834858624006593075900125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89223239082671062050600083 133834858624006593075900125)
        ·
          refine ⟨50188071984002472403462547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133834858624006593075900125 50188071984002472403462547)
          ·
            refine ⟨75282107976003708605193821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50188071984002472403462547 75282107976003708605193821)
            ·
              refine ⟨28230790491001390726947683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75282107976003708605193821 28230790491001390726947683)
              ·
                refine ⟨42346185736502086090421525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28230790491001390726947683 42346185736502086090421525)
                ·
                  refine ⟨1984977456398535285488509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42346185736502086090421525 1984977456398535285488509)
                  ·
                    refine ⟨744366546149450732058191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1984977456398535285488509 744366546149450732058191)
                    ·
                      rfl

theorem cell22_2174473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 6, 3].length) (baseStart_2174473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2174473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2174473 prefixEnd_2174473 := by exact prefixLift 2174473
  have htrace : WordTrace (prefixWord ++ tailWord_2174473) baseStart_2174473 baseEnd_2174473 := by
    simpa [prefixWord, tailWord_2174473, baseEnd_2174473] using wordTrace_append hprefix tailTrace_2174473
  have hstable : (prefixWord ++ tailWord_2174473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174473).length < 2 ^ (prefixWord ++ tailWord_2174473).sum := by decide
  have hdescent : baseEnd_2174473 < baseStart_2174473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174490 : List Nat := [3, 1, 1, 3, 1, 1, 1, 6, 2, 3]
def baseStart_2174490 : Nat := 118140960795 + 2174490 * 2 ^ 59
def prefixEnd_2174490 : Nat := 4983230072969 + 3 ^ 40 * 2174490 * 2
def baseEnd_2174490 : Nat := 744372365596868354383139

theorem tailTrace_2174490 : CollatzResearch.WordTrace tailWord_2174490 prefixEnd_2174490 744372365596868354383139 := by
  unfold tailWord_2174490
  simp only [CollatzResearch.WordTrace]
  refine ⟨19827541473050394542642231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52873443928134385447045949 19827541473050394542642231)
  ·
    refine ⟨29741312209575591813963347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19827541473050394542642231 29741312209575591813963347)
    ·
      refine ⟨44611968314363387720945021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29741312209575591813963347 44611968314363387720945021)
      ·
        refine ⟨16729488117886270395354383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44611968314363387720945021 16729488117886270395354383)
        ·
          refine ⟨25094232176829405593031575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16729488117886270395354383 25094232176829405593031575)
          ·
            refine ⟨37641348265244108389547363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25094232176829405593031575 37641348265244108389547363)
            ·
              refine ⟨56462022397866162584321045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37641348265244108389547363 56462022397866162584321045)
              ·
                refine ⟨2646657299899976371140049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56462022397866162584321045 2646657299899976371140049)
                ·
                  refine ⟨1984992974924982278355037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2646657299899976371140049 1984992974924982278355037)
                  ·
                    refine ⟨744372365596868354383139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1984992974924982278355037 744372365596868354383139)
                    ·
                      rfl

theorem cell22_2174490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 2, 3].length) (baseStart_2174490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2174490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2174490 prefixEnd_2174490 := by exact prefixLift 2174490
  have htrace : WordTrace (prefixWord ++ tailWord_2174490) baseStart_2174490 baseEnd_2174490 := by
    simpa [prefixWord, tailWord_2174490, baseEnd_2174490] using wordTrace_append hprefix tailTrace_2174490
  have hstable : (prefixWord ++ tailWord_2174490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174490).length < 2 ^ (prefixWord ++ tailWord_2174490).sum := by decide
  have hdescent : baseEnd_2174490 < baseStart_2174490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174492 : List Nat := [2, 2, 3, 1, 2, 1, 5, 2, 4]
def baseStart_2174492 : Nat := 118140960795 + 2174492 * 2 ^ 59
def prefixEnd_2174492 : Nat := 4983230072969 + 3 ^ 40 * 2174492 * 2
def baseEnd_2174492 : Nat := 248124350079247005277711

theorem tailTrace_2174492 : CollatzResearch.WordTrace tailWord_2174492 prefixEnd_2174492 248124350079247005277711 := by
  unfold tailWord_2174492
  simp only [CollatzResearch.WordTrace]
  refine ⟨39655119419097166256070865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52873492558796221674761153 39655119419097166256070865)
  ·
    refine ⟨29741339564322874692053149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39655119419097166256070865 29741339564322874692053149)
    ·
      refine ⟨11153002336621078009519931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29741339564322874692053149 11153002336621078009519931)
      ·
        refine ⟨16729503504931617014279897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11153002336621078009519931 16729503504931617014279897)
        ·
          refine ⟨12547127628698712760709923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16729503504931617014279897 12547127628698712760709923)
          ·
            refine ⟨18820691443048069141064885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12547127628698712760709923 18820691443048069141064885)
            ·
              refine ⟨1764439822785756481974833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18820691443048069141064885 1764439822785756481974833)
              ·
                refine ⟨1323329867089317361481125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1764439822785756481974833 1323329867089317361481125)
                ·
                  refine ⟨248124350079247005277711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1323329867089317361481125 248124350079247005277711)
                  ·
                    rfl

theorem cell22_2174492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2, 4].length) (baseStart_2174492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2174492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2174492 prefixEnd_2174492 := by exact prefixLift 2174492
  have htrace : WordTrace (prefixWord ++ tailWord_2174492) baseStart_2174492 baseEnd_2174492 := by
    simpa [prefixWord, tailWord_2174492, baseEnd_2174492] using wordTrace_append hprefix tailTrace_2174492
  have hstable : (prefixWord ++ tailWord_2174492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174492).length < 2 ^ (prefixWord ++ tailWord_2174492).sum := by decide
  have hdescent : baseEnd_2174492 < baseStart_2174492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174563 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 1, 7]
def baseStart_2174563 : Nat := 118140960795 + 2174563 * 2 ^ 59
def prefixEnd_2174563 : Nat := 4983230072969 + 3 ^ 40 * 2174563 * 2
def baseEnd_2174563 : Nat := 744397354988720497307915

theorem tailTrace_2174563 : CollatzResearch.WordTrace tailWord_2174563 prefixEnd_2174563 744397354988720497307915 := by
  unfold tailWord_2174563
  simp only [CollatzResearch.WordTrace]
  refine ⟨79312828420937111637976343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52875218947291407758650895 79312828420937111637976343)
  ·
    refine ⟨118969242631405667456964515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79312828420937111637976343 118969242631405667456964515)
    ·
      refine ⟨178453863947108501185446773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118969242631405667456964515 178453863947108501185446773)
      ·
        refine ⟨16730049745041421986135635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 178453863947108501185446773 16730049745041421986135635)
        ·
          refine ⟨25095074617562132979203453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16730049745041421986135635 25095074617562132979203453)
          ·
            refine ⟨9410652981585799867201295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25095074617562132979203453 9410652981585799867201295)
            ·
              refine ⟨14115979472378699800801943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9410652981585799867201295 14115979472378699800801943)
              ·
                refine ⟨21173969208568049701202915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14115979472378699800801943 21173969208568049701202915)
                ·
                  refine ⟨31760953812852074551804373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21173969208568049701202915 31760953812852074551804373)
                  ·
                    refine ⟨744397354988720497307915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31760953812852074551804373 744397354988720497307915)
                    ·
                      rfl

theorem cell22_2174563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 7].length) (baseStart_2174563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2174563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2174563 prefixEnd_2174563 := by exact prefixLift 2174563
  have htrace : WordTrace (prefixWord ++ tailWord_2174563) baseStart_2174563 baseEnd_2174563 := by
    simpa [prefixWord, tailWord_2174563, baseEnd_2174563] using wordTrace_append hprefix tailTrace_2174563
  have hstable : (prefixWord ++ tailWord_2174563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174563).length < 2 ^ (prefixWord ++ tailWord_2174563).sum := by decide
  have hdescent : baseEnd_2174563 < baseStart_2174563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174565 : List Nat := [1, 3, 1, 3, 3, 1, 2, 3, 5]
def baseStart_2174565 : Nat := 118140960795 + 2174565 * 2 ^ 59
def prefixEnd_2174565 : Nat := 4983230072969 + 3 ^ 40 * 2174565 * 2
def baseEnd_2174565 : Nat := 248132679876531052919303

theorem tailTrace_2174565 : CollatzResearch.WordTrace tailWord_2174565 prefixEnd_2174565 248132679876531052919303 := by
  unfold tailWord_2174565
  simp only [CollatzResearch.WordTrace]
  refine ⟨79312901366929865979549149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52875267577953243986366099 79312901366929865979549149)
  ·
    refine ⟨29742338012598699742330931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79312901366929865979549149 29742338012598699742330931)
    ·
      refine ⟨44613507018898049613496397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29742338012598699742330931 44613507018898049613496397)
      ·
        refine ⟨16730065132086768605061149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44613507018898049613496397 16730065132086768605061149)
        ·
          refine ⟨6273774424532538226897931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16730065132086768605061149 6273774424532538226897931)
          ·
            refine ⟨9410661636798807340346897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6273774424532538226897931 9410661636798807340346897)
            ·
              refine ⟨7057996227599105505260173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9410661636798807340346897 7057996227599105505260173)
              ·
                refine ⟨2646748585349664564472565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7057996227599105505260173 2646748585349664564472565)
                ·
                  refine ⟨248132679876531052919303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2646748585349664564472565 248132679876531052919303)
                  ·
                    rfl

theorem cell22_2174565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 5].length) (baseStart_2174565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2174565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2174565 prefixEnd_2174565 := by exact prefixLift 2174565
  have htrace : WordTrace (prefixWord ++ tailWord_2174565) baseStart_2174565 baseEnd_2174565 := by
    simpa [prefixWord, tailWord_2174565, baseEnd_2174565] using wordTrace_append hprefix tailTrace_2174565
  have hstable : (prefixWord ++ tailWord_2174565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174565).length < 2 ^ (prefixWord ++ tailWord_2174565).sum := by decide
  have hdescent : baseEnd_2174565 < baseStart_2174565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174608 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 3, 5]
def baseStart_2174608 : Nat := 118140960795 + 2174608 * 2 ^ 59
def prefixEnd_2174608 : Nat := 4983230072969 + 3 ^ 40 * 2174608 * 2
def baseEnd_2174608 : Nat := 744412759408355379932777

theorem tailTrace_2174608 : CollatzResearch.WordTrace tailWord_2174608 prefixEnd_2174608 744412759408355379932777 := by
  unfold tailWord_2174608
  simp only [CollatzResearch.WordTrace]
  refine ⟨39657234852887042161682239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52876313137182722882242985 39657234852887042161682239)
  ·
    refine ⟨59485852279330563242523359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39657234852887042161682239 59485852279330563242523359)
    ·
      refine ⟨89228778418995844863785039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59485852279330563242523359 89228778418995844863785039)
      ·
        refine ⟨133843167628493767295677559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89228778418995844863785039 133843167628493767295677559)
        ·
          refine ⟨200764751442740650943516339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133843167628493767295677559 200764751442740650943516339)
          ·
            refine ⟨301147127164110976415274509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200764751442740650943516339 301147127164110976415274509)
            ·
              refine ⟨112930172686541616155727941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 301147127164110976415274509 112930172686541616155727941)
              ·
                refine ⟨21174407378726553029198989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112930172686541616155727941 21174407378726553029198989)
                ·
                  refine ⟨7940402767022457385949621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21174407378726553029198989 7940402767022457385949621)
                  ·
                    refine ⟨744412759408355379932777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7940402767022457385949621 744412759408355379932777)
                    ·
                      rfl

theorem cell22_2174608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 3, 5].length) (baseStart_2174608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2174608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2174608 prefixEnd_2174608 := by exact prefixLift 2174608
  have htrace : WordTrace (prefixWord ++ tailWord_2174608) baseStart_2174608 baseEnd_2174608 := by
    simpa [prefixWord, tailWord_2174608, baseEnd_2174608] using wordTrace_append hprefix tailTrace_2174608
  have hstable : (prefixWord ++ tailWord_2174608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174608).length < 2 ^ (prefixWord ++ tailWord_2174608).sum := by decide
  have hdescent : baseEnd_2174608 < baseStart_2174608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174676 : List Nat := [2, 4, 1, 3, 1, 1, 4, 1, 2, 3]
def baseStart_2174676 : Nat := 118140960795 + 2174676 * 2 ^ 59
def prefixEnd_2174676 : Nat := 4983230072969 + 3 ^ 40 * 2174676 * 2
def baseEnd_2174676 : Nat := 744436037198025869232569

theorem tailTrace_2174676 : CollatzResearch.WordTrace tailWord_2174676 prefixEnd_2174676 744436037198025869232569 := by
  unfold tailWord_2174676
  simp only [CollatzResearch.WordTrace]
  refine ⟨39658474934763865968419941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52877966579685154624559921 39658474934763865968419941)
  ·
    refine ⟨7435964050268224869078739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39658474934763865968419941 7435964050268224869078739)
    ·
      refine ⟨11153946075402337303618109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7435964050268224869078739 11153946075402337303618109)
      ·
        refine ⟨4182729778275876488856791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11153946075402337303618109 4182729778275876488856791)
        ·
          refine ⟨6274094667413814733285187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4182729778275876488856791 6274094667413814733285187)
          ·
            refine ⟨9411142001120722099927781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6274094667413814733285187 9411142001120722099927781)
            ·
              refine ⟨1764589125210135393736459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9411142001120722099927781 1764589125210135393736459)
              ·
                refine ⟨2646883687815203090604689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1764589125210135393736459 2646883687815203090604689)
                ·
                  refine ⟨1985162765861402317953517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2646883687815203090604689 1985162765861402317953517)
                  ·
                    refine ⟨744436037198025869232569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1985162765861402317953517 744436037198025869232569)
                    ·
                      rfl

theorem cell22_2174676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_2174676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2174676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2174676 prefixEnd_2174676 := by exact prefixLift 2174676
  have htrace : WordTrace (prefixWord ++ tailWord_2174676) baseStart_2174676 baseEnd_2174676 := by
    simpa [prefixWord, tailWord_2174676, baseEnd_2174676] using wordTrace_append hprefix tailTrace_2174676
  have hstable : (prefixWord ++ tailWord_2174676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174676).length < 2 ^ (prefixWord ++ tailWord_2174676).sum := by decide
  have hdescent : baseEnd_2174676 < baseStart_2174676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174721 : List Nat := [1, 2, 4, 1, 1, 1, 6, 2, 1, 3]
def baseStart_2174721 : Nat := 118140960795 + 2174721 * 2 ^ 59
def prefixEnd_2174721 : Nat := 4983230072969 + 3 ^ 40 * 2174721 * 2
def baseEnd_2174721 : Nat := 744451441617660751857431

theorem tailTrace_2174721 : CollatzResearch.WordTrace tailWord_2174721 prefixEnd_2174721 744451441617660751857431 := by
  unfold tailWord_2174721
  simp only [CollatzResearch.WordTrace]
  refine ⟨79318591154364704622228017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52879060769576469748152011 79318591154364704622228017)
  ·
    refine ⟨59488943365773528466671013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79318591154364704622228017 59488943365773528466671013)
    ·
      refine ⟨11154176881082536587500815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59488943365773528466671013 11154176881082536587500815)
      ·
        refine ⟨16731265321623804881251223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11154176881082536587500815 16731265321623804881251223)
        ·
          refine ⟨25096897982435707321876835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16731265321623804881251223 25096897982435707321876835)
          ·
            refine ⟨37645346973653560982815253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25096897982435707321876835 37645346973653560982815253)
            ·
              refine ⟨1764625639390010671069465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 37645346973653560982815253 1764625639390010671069465)
              ·
                refine ⟨1323469229542508003302099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1764625639390010671069465 1323469229542508003302099)
                ·
                  refine ⟨1985203844313762004953149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1323469229542508003302099 1985203844313762004953149)
                  ·
                    refine ⟨744451441617660751857431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1985203844313762004953149 744451441617660751857431)
                    ·
                      rfl

theorem cell22_2174721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_2174721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2174721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2174721 prefixEnd_2174721 := by exact prefixLift 2174721
  have htrace : WordTrace (prefixWord ++ tailWord_2174721) baseStart_2174721 baseEnd_2174721 := by
    simpa [prefixWord, tailWord_2174721, baseEnd_2174721] using wordTrace_append hprefix tailTrace_2174721
  have hstable : (prefixWord ++ tailWord_2174721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174721).length < 2 ^ (prefixWord ++ tailWord_2174721).sum := by decide
  have hdescent : baseEnd_2174721 < baseStart_2174721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174764 : List Nat := [2, 2, 1, 1, 1, 5, 4, 1, 1, 4]
def baseStart_2174764 : Nat := 118140960795 + 2174764 * 2 ^ 59
def prefixEnd_2174764 : Nat := 4983230072969 + 3 ^ 40 * 2174764 * 2
def baseEnd_2174764 : Nat := 744466161396422973032299

theorem tailTrace_2174764 : CollatzResearch.WordTrace tailWord_2174764 prefixEnd_2174764 744466161396422973032299 := by
  unfold tailWord_2174764
  simp only [CollatzResearch.WordTrace]
  refine ⟨39660079746604461483021673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52880106328805948644028897 39660079746604461483021673)
  ·
    refine ⟨29745059809953346112266255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39660079746604461483021673 29745059809953346112266255)
    ·
      refine ⟨44617589714930019168399383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29745059809953346112266255 44617589714930019168399383)
      ·
        refine ⟨66926384572395028752599075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44617589714930019168399383 66926384572395028752599075)
        ·
          refine ⟨100389576858592543128898613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66926384572395028752599075 100389576858592543128898613)
          ·
            refine ⟨9411522830493050918334245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100389576858592543128898613 9411522830493050918334245)
            ·
              refine ⟨1764660530717447047187671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9411522830493050918334245 1764660530717447047187671)
              ·
                refine ⟨2646990796076170570781507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1764660530717447047187671 2646990796076170570781507)
                ·
                  refine ⟨3970486194114255856172261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2646990796076170570781507 3970486194114255856172261)
                  ·
                    refine ⟨744466161396422973032299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3970486194114255856172261 744466161396422973032299)
                    ·
                      rfl

theorem cell22_2174764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 4].length) (baseStart_2174764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2174764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2174764 prefixEnd_2174764 := by exact prefixLift 2174764
  have htrace : WordTrace (prefixWord ++ tailWord_2174764) baseStart_2174764 baseEnd_2174764 := by
    simpa [prefixWord, tailWord_2174764, baseEnd_2174764] using wordTrace_append hprefix tailTrace_2174764
  have hstable : (prefixWord ++ tailWord_2174764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174764).length < 2 ^ (prefixWord ++ tailWord_2174764).sum := by decide
  have hdescent : baseEnd_2174764 < baseStart_2174764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174807 : List Nat := [1, 1, 3, 2, 5, 1, 1, 8]
def baseStart_2174807 : Nat := 118140960795 + 2174807 * 2 ^ 59
def prefixEnd_2174807 : Nat := 4983230072969 + 3 ^ 40 * 2174807 * 2
def baseEnd_2174807 : Nat := 82720097908353910467463

theorem tailTrace_2174807 : CollatzResearch.WordTrace tailWord_2174807 prefixEnd_2174807 82720097908353910467463 := by
  unfold tailWord_2174807
  simp only [CollatzResearch.WordTrace]
  refine ⟨79321727832053141309858675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52881151888035427539905783 79321727832053141309858675)
  ·
    refine ⟨118982591748079711964788013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79321727832053141309858675 118982591748079711964788013)
    ·
      refine ⟨44618471905529891986795505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118982591748079711964788013 44618471905529891986795505)
      ·
        refine ⟨33463853929147418990096629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44618471905529891986795505 33463853929147418990096629)
        ·
          refine ⟨3137236305857570530321559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33463853929147418990096629 3137236305857570530321559)
          ·
            refine ⟨4705854458786355795482339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3137236305857570530321559 4705854458786355795482339)
            ·
              refine ⟨7058781688179533693223509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4705854458786355795482339 7058781688179533693223509)
              ·
                refine ⟨82720097908353910467463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7058781688179533693223509 82720097908353910467463)
                ·
                  rfl

theorem cell22_2174807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 8].length) (baseStart_2174807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2174807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2174807 prefixEnd_2174807 := by exact prefixLift 2174807
  have htrace : WordTrace (prefixWord ++ tailWord_2174807) baseStart_2174807 baseEnd_2174807 := by
    simpa [prefixWord, tailWord_2174807, baseEnd_2174807] using wordTrace_append hprefix tailTrace_2174807
  have hstable : (prefixWord ++ tailWord_2174807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174807).length < 2 ^ (prefixWord ++ tailWord_2174807).sum := by decide
  have hdescent : baseEnd_2174807 < baseStart_2174807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174826 : List Nat := [3, 1, 3, 4, 1, 1, 1, 2, 2, 4]
def baseStart_2174826 : Nat := 118140960795 + 2174826 * 2 ^ 59
def prefixEnd_2174826 : Nat := 4983230072969 + 3 ^ 40 * 2174826 * 2
def baseEnd_2174826 : Nat := 744487385263475477982109

theorem tailTrace_2174826 : CollatzResearch.WordTrace tailWord_2174826 prefixEnd_2174826 744487385263475477982109 := by
  unfold tailWord_2174826
  simp only [CollatzResearch.WordTrace]
  refine ⟨19830605204746076888700083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52881613879322871703200221 19830605204746076888700083)
  ·
    refine ⟨29745907807119115333050125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19830605204746076888700083 29745907807119115333050125)
    ·
      refine ⟨11154715427669668249893797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29745907807119115333050125 11154715427669668249893797)
      ·
        refine ⟨2091509142688062796855087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11154715427669668249893797 2091509142688062796855087)
        ·
          refine ⟨3137263714032094195282631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2091509142688062796855087 3137263714032094195282631)
          ·
            refine ⟨4705895571048141292923947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3137263714032094195282631 4705895571048141292923947)
            ·
              refine ⟨7058843356572211939385921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4705895571048141292923947 7058843356572211939385921)
              ·
                refine ⟨5294132517429158954539441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7058843356572211939385921 5294132517429158954539441)
                ·
                  refine ⟨3970599388071869215904581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5294132517429158954539441 3970599388071869215904581)
                  ·
                    refine ⟨744487385263475477982109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3970599388071869215904581 744487385263475477982109)
                    ·
                      rfl

theorem cell22_2174826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_2174826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2174826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2174826 prefixEnd_2174826 := by exact prefixLift 2174826
  have htrace : WordTrace (prefixWord ++ tailWord_2174826) baseStart_2174826 baseEnd_2174826 := by
    simpa [prefixWord, tailWord_2174826, baseEnd_2174826] using wordTrace_append hprefix tailTrace_2174826
  have hstable : (prefixWord ++ tailWord_2174826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174826).length < 2 ^ (prefixWord ++ tailWord_2174826).sum := by decide
  have hdescent : baseEnd_2174826 < baseStart_2174826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174837 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 2, 6]
def baseStart_2174837 : Nat := 118140960795 + 2174837 * 2 ^ 59
def prefixEnd_2174837 : Nat := 4983230072969 + 3 ^ 40 * 2174837 * 2
def baseEnd_2174837 : Nat := 744491150788275115957075

theorem tailTrace_2174837 : CollatzResearch.WordTrace tailWord_2174837 prefixEnd_2174837 744491150788275115957075 := by
  unfold tailWord_2174837
  simp only [CollatzResearch.WordTrace]
  refine ⟨79322822021944456433450765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52881881347962970955633843 79322822021944456433450765)
  ·
    refine ⟨29746058258229171162544037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79322822021944456433450765 29746058258229171162544037)
    ·
      refine ⟨5577385923417969592977007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29746058258229171162544037 5577385923417969592977007)
      ·
        refine ⟨8366078885126954389465511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5577385923417969592977007 8366078885126954389465511)
        ·
          refine ⟨12549118327690431584198267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8366078885126954389465511 12549118327690431584198267)
          ·
            refine ⟨18823677491535647376297401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12549118327690431584198267 18823677491535647376297401)
            ·
              refine ⟨14117758118651735532223051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18823677491535647376297401 14117758118651735532223051)
              ·
                refine ⟨21176637177977603298334577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14117758118651735532223051 21176637177977603298334577)
                ·
                  refine ⟨15882477883483202473750933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21176637177977603298334577 15882477883483202473750933)
                  ·
                    refine ⟨744491150788275115957075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15882477883483202473750933 744491150788275115957075)
                    ·
                      rfl

theorem cell22_2174837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_2174837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2174837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2174837 prefixEnd_2174837 := by exact prefixLift 2174837
  have htrace : WordTrace (prefixWord ++ tailWord_2174837) baseStart_2174837 baseEnd_2174837 := by
    simpa [prefixWord, tailWord_2174837, baseEnd_2174837] using wordTrace_append hprefix tailTrace_2174837
  have hstable : (prefixWord ++ tailWord_2174837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174837).length < 2 ^ (prefixWord ++ tailWord_2174837).sum := by decide
  have hdescent : baseEnd_2174837 < baseStart_2174837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174927 : List Nat := [1, 1, 2, 1, 1, 5, 3, 1, 1, 6]
def baseStart_2174927 : Nat := 118140960795 + 2174927 * 2 ^ 59
def prefixEnd_2174927 : Nat := 4983230072969 + 3 ^ 40 * 2174927 * 2
def baseEnd_2174927 : Nat := 744521959627544881206799

theorem tailTrace_2174927 : CollatzResearch.WordTrace tailWord_2174927 prefixEnd_2174927 744521959627544881206799 := by
  unfold tailWord_2174927
  simp only [CollatzResearch.WordTrace]
  refine ⟨79326104591618401804227035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52884069727745601202818023 79326104591618401804227035)
  ·
    refine ⟨118989156887427602706340553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79326104591618401804227035 118989156887427602706340553)
    ·
      refine ⟨89241867665570702029755415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118989156887427602706340553 89241867665570702029755415)
      ·
        refine ⟨133862801498356053044633123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89241867665570702029755415 133862801498356053044633123)
        ·
          refine ⟨200794202247534079566949685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133862801498356053044633123 200794202247534079566949685)
          ·
            refine ⟨18824456460706319959401533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 200794202247534079566949685 18824456460706319959401533)
            ·
              refine ⟨7059171172764869984775575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18824456460706319959401533 7059171172764869984775575)
              ·
                refine ⟨10588756759147304977163363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7059171172764869984775575 10588756759147304977163363)
                ·
                  refine ⟨15883135138720957465745045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10588756759147304977163363 15883135138720957465745045)
                  ·
                    refine ⟨744521959627544881206799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15883135138720957465745045 744521959627544881206799)
                    ·
                      rfl

theorem cell22_2174927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 6].length) (baseStart_2174927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2174927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2174927 prefixEnd_2174927 := by exact prefixLift 2174927
  have htrace : WordTrace (prefixWord ++ tailWord_2174927) baseStart_2174927 baseEnd_2174927 := by
    simpa [prefixWord, tailWord_2174927, baseEnd_2174927] using wordTrace_append hprefix tailTrace_2174927
  have hstable : (prefixWord ++ tailWord_2174927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174927).length < 2 ^ (prefixWord ++ tailWord_2174927).sum := by decide
  have hdescent : baseEnd_2174927 < baseStart_2174927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174933 : List Nat := [1, 3, 2, 3, 2, 3, 2, 1, 1, 4]
def baseStart_2174933 : Nat := 118140960795 + 2174933 * 2 ^ 59
def prefixEnd_2174933 : Nat := 4983230072969 + 3 ^ 40 * 2174933 * 2
def baseEnd_2174933 : Nat := 744524013550162865556781

theorem tailTrace_2174933 : CollatzResearch.WordTrace tailWord_2174933 prefixEnd_2174933 744524013550162865556781 := by
  unfold tailWord_2174933
  simp only [CollatzResearch.WordTrace]
  refine ⟨79326323429596664828945453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52884215619731109885963635 79326323429596664828945453)
  ·
    refine ⟨29747371286098749310854545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79326323429596664828945453 29747371286098749310854545)
    ·
      refine ⟨22310528464574061983140909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29747371286098749310854545 22310528464574061983140909)
      ·
        refine ⟨8366448174215273243677841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22310528464574061983140909 8366448174215273243677841)
        ·
          refine ⟨6274836130661454932758381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8366448174215273243677841 6274836130661454932758381)
          ·
            refine ⟨2353063548998045599784393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6274836130661454932758381 2353063548998045599784393)
            ·
              refine ⟨1764797661748534199838295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2353063548998045599784393 1764797661748534199838295)
              ·
                refine ⟨2647196492622801299757443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1764797661748534199838295 2647196492622801299757443)
                ·
                  refine ⟨3970794738934201949636165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2647196492622801299757443 3970794738934201949636165)
                  ·
                    refine ⟨744524013550162865556781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3970794738934201949636165 744524013550162865556781)
                    ·
                      rfl

theorem cell22_2174933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_2174933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2174933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2174933 prefixEnd_2174933 := by exact prefixLift 2174933
  have htrace : WordTrace (prefixWord ++ tailWord_2174933) baseStart_2174933 baseEnd_2174933 := by
    simpa [prefixWord, tailWord_2174933, baseEnd_2174933] using wordTrace_append hprefix tailTrace_2174933
  have hstable : (prefixWord ++ tailWord_2174933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174933).length < 2 ^ (prefixWord ++ tailWord_2174933).sum := by decide
  have hdescent : baseEnd_2174933 < baseStart_2174933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2174987 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 9]
def baseStart_2174987 : Nat := 118140960795 + 2174987 * 2 ^ 59
def prefixEnd_2174987 : Nat := 4983230072969 + 3 ^ 40 * 2174987 * 2
def baseEnd_2174987 : Nat := 248180832951241574902205

theorem tailTrace_2174987 : CollatzResearch.WordTrace tailWord_2174987 prefixEnd_2174987 248180832951241574902205 := by
  unfold tailWord_2174987
  simp only [CollatzResearch.WordTrace]
  refine ⟨79328292971401032051411215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52885528647600688034274143 79328292971401032051411215)
  ·
    refine ⟨118992439457101548077116823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79328292971401032051411215 118992439457101548077116823)
    ·
      refine ⟨178488659185652322115675235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118992439457101548077116823 178488659185652322115675235)
      ·
        refine ⟨267732988778478483173512853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178488659185652322115675235 267732988778478483173512853)
        ·
          refine ⟨12549983848991178898758415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 267732988778478483173512853 12549983848991178898758415)
          ·
            refine ⟨18824975773486768348137623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12549983848991178898758415 18824975773486768348137623)
            ·
              refine ⟨28237463660230152522206435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18824975773486768348137623 28237463660230152522206435)
              ·
                refine ⟨42356195490345228783309653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28237463660230152522206435 42356195490345228783309653)
                ·
                  refine ⟨248180832951241574902205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42356195490345228783309653 248180832951241574902205)
                  ·
                    rfl

theorem cell22_2174987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 9].length) (baseStart_2174987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2174987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2174987 prefixEnd_2174987 := by exact prefixLift 2174987
  have htrace : WordTrace (prefixWord ++ tailWord_2174987) baseStart_2174987 baseEnd_2174987 := by
    simpa [prefixWord, tailWord_2174987, baseEnd_2174987] using wordTrace_append hprefix tailTrace_2174987
  have hstable : (prefixWord ++ tailWord_2174987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2174987).length < 2 ^ (prefixWord ++ tailWord_2174987).sum := by decide
  have hdescent : baseEnd_2174987 < baseStart_2174987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2174987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175004 : List Nat := [2, 2, 3, 1, 3, 1, 2, 1, 7]
def baseStart_2175004 : Nat := 118140960795 + 2175004 * 2 ^ 59
def prefixEnd_2175004 : Nat := 4983230072969 + 3 ^ 40 * 2175004 * 2
def baseEnd_2175004 : Nat := 248182772767047449010521

theorem tailTrace_2175004 : CollatzResearch.WordTrace tailWord_2175004 prefixEnd_2175004 248182772767047449010521 := by
  unfold tailWord_2175004
  simp only [CollatzResearch.WordTrace]
  refine ⟨39664456506169721977390033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 52885942008226295969853377 39664456506169721977390033)
  ·
    refine ⟨29748342379627291483042525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39664456506169721977390033 29748342379627291483042525)
    ·
      refine ⟨11155628392360234306140947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29748342379627291483042525 11155628392360234306140947)
      ·
        refine ⟨16733442588540351459211421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11155628392360234306140947 16733442588540351459211421)
        ·
          refine ⟨6275040970702631797204283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16733442588540351459211421 6275040970702631797204283)
          ·
            refine ⟨9412561456053947695806425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6275040970702631797204283 9412561456053947695806425)
            ·
              refine ⟨7059421092040460771854819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9412561456053947695806425 7059421092040460771854819)
              ·
                refine ⟨10589131638060691157782229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7059421092040460771854819 10589131638060691157782229)
                ·
                  refine ⟨248182772767047449010521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10589131638060691157782229 248182772767047449010521)
                  ·
                    rfl

theorem cell22_2175004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 7].length) (baseStart_2175004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2175004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2175004 prefixEnd_2175004 := by exact prefixLift 2175004
  have htrace : WordTrace (prefixWord ++ tailWord_2175004) baseStart_2175004 baseEnd_2175004 := by
    simpa [prefixWord, tailWord_2175004, baseEnd_2175004] using wordTrace_append hprefix tailTrace_2175004
  have hstable : (prefixWord ++ tailWord_2175004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175004).length < 2 ^ (prefixWord ++ tailWord_2175004).sum := by decide
  have hdescent : baseEnd_2175004 < baseStart_2175004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175066 : List Nat := [3, 1, 1, 2, 1, 1, 5, 4, 4]
def baseStart_2175066 : Nat := 118140960795 + 2175066 * 2 ^ 59
def prefixEnd_2175066 : Nat := 4983230072969 + 3 ^ 40 * 2175066 * 2
def baseEnd_2175066 : Nat := 248189847389398283993791

theorem tailTrace_2175066 : CollatzResearch.WordTrace tailWord_2175066 prefixEnd_2175066 248189847389398283993791 := by
  unfold tailWord_2175066
  simp only [CollatzResearch.WordTrace]
  refine ⟨19832793584528707135884263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 52887449558743219029024701 19832793584528707135884263)
  ·
    refine ⟨29749190376793060703826395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19832793584528707135884263 29749190376793060703826395)
    ·
      refine ⟨44623785565189591055739593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29749190376793060703826395 44623785565189591055739593)
      ·
        refine ⟨33467839173892193291804695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44623785565189591055739593 33467839173892193291804695)
        ·
          refine ⟨50201758760838289937707043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33467839173892193291804695 50201758760838289937707043)
          ·
            refine ⟨75302638141257434906560565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50201758760838289937707043 75302638141257434906560565)
            ·
              refine ⟨7059622325742884522490053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75302638141257434906560565 7059622325742884522490053)
              ·
                refine ⟨1323679186076790847966885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7059622325742884522490053 1323679186076790847966885)
                ·
                  refine ⟨248189847389398283993791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1323679186076790847966885 248189847389398283993791)
                  ·
                    rfl

theorem cell22_2175066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4, 4].length) (baseStart_2175066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2175066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2175066 prefixEnd_2175066 := by exact prefixLift 2175066
  have htrace : WordTrace (prefixWord ++ tailWord_2175066) baseStart_2175066 baseEnd_2175066 := by
    simpa [prefixWord, tailWord_2175066, baseEnd_2175066] using wordTrace_append hprefix tailTrace_2175066
  have hstable : (prefixWord ++ tailWord_2175066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175066).length < 2 ^ (prefixWord ++ tailWord_2175066).sum := by decide
  have hdescent : baseEnd_2175066 < baseStart_2175066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175070 : List Nat := [4, 4, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_2175070 : Nat := 118140960795 + 2175070 * 2 ^ 59
def prefixEnd_2175070 : Nat := 4983230072969 + 3 ^ 40 * 2175070 * 2
def baseEnd_2175070 : Nat := 744570911449940174881361

theorem tailTrace_2175070 : CollatzResearch.WordTrace tailWord_2175070 prefixEnd_2175070 744570911449940174881361 := by
  unfold tailWord_2175070
  simp only [CollatzResearch.WordTrace]
  refine ⟨9916415028762542153335333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 52887546820066891484455109 9916415028762542153335333)
  ·
    refine ⟨1859327817892976653750375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9916415028762542153335333 1859327817892976653750375)
    ·
      refine ⟨2788991726839464980625563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1859327817892976653750375 2788991726839464980625563)
      ·
        refine ⟨4183487590259197470938345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2788991726839464980625563 4183487590259197470938345)
        ·
          refine ⟨3137615692694398103203759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4183487590259197470938345 3137615692694398103203759)
          ·
            refine ⟨4706423539041597154805639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3137615692694398103203759 4706423539041597154805639)
            ·
              refine ⟨7059635308562395732208459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4706423539041597154805639 7059635308562395732208459)
              ·
                refine ⟨10589452962843593598312689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7059635308562395732208459 10589452962843593598312689)
                ·
                  refine ⟨7942089722132695198734517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10589452962843593598312689 7942089722132695198734517)
                  ·
                    refine ⟨744570911449940174881361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7942089722132695198734517 744570911449940174881361)
                    ·
                      rfl

theorem cell22_2175070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_2175070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2175070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2175070 prefixEnd_2175070 := by exact prefixLift 2175070
  have htrace : WordTrace (prefixWord ++ tailWord_2175070) baseStart_2175070 baseEnd_2175070 := by
    simpa [prefixWord, tailWord_2175070, baseEnd_2175070] using wordTrace_append hprefix tailTrace_2175070
  have hstable : (prefixWord ++ tailWord_2175070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175070).length < 2 ^ (prefixWord ++ tailWord_2175070).sum := by decide
  have hdescent : baseEnd_2175070 < baseStart_2175070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2175079 : List Nat := [1, 1, 5, 1, 1, 2, 2, 2, 1, 6]
def baseStart_2175079 : Nat := 118140960795 + 2175079 * 2 ^ 59
def prefixEnd_2175079 : Nat := 4983230072969 + 3 ^ 40 * 2175079 * 2
def baseEnd_2175079 : Nat := 744573992333867151406333

theorem tailTrace_2175079 : CollatzResearch.WordTrace tailWord_2175079 prefixEnd_2175079 744573992333867151406333 := by
  unfold tailWord_2175079
  simp only [CollatzResearch.WordTrace]
  refine ⟨79331648487067731763760291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 52887765658045154509173527 79331648487067731763760291)
  ·
    refine ⟨118997472730601597645640437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79331648487067731763760291 118997472730601597645640437)
    ·
      refine ⟨11156013068493899779278791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118997472730601597645640437 11156013068493899779278791)
      ·
        refine ⟨16734019602740849668918187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11156013068493899779278791 16734019602740849668918187)
        ·
          refine ⟨25101029404111274503377281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16734019602740849668918187 25101029404111274503377281)
          ·
            refine ⟨18825772053083455877532961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25101029404111274503377281 18825772053083455877532961)
            ·
              refine ⟨14119329039812591908149721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18825772053083455877532961 14119329039812591908149721)
              ·
                refine ⟨10589496779859443931112291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14119329039812591908149721 10589496779859443931112291)
                ·
                  refine ⟨15884245169789165896668437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10589496779859443931112291 15884245169789165896668437)
                  ·
                    refine ⟨744573992333867151406333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15884245169789165896668437 744573992333867151406333)
                    ·
                      rfl

theorem cell22_2175079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_2175079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2175079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2175079 prefixEnd_2175079 := by exact prefixLift 2175079
  have htrace : WordTrace (prefixWord ++ tailWord_2175079) baseStart_2175079 baseEnd_2175079 := by
    simpa [prefixWord, tailWord_2175079, baseEnd_2175079] using wordTrace_append hprefix tailTrace_2175079
  have hstable : (prefixWord ++ tailWord_2175079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2175079).length < 2 ^ (prefixWord ++ tailWord_2175079).sum := by decide
  have hdescent : baseEnd_2175079 < baseStart_2175079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2175079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
