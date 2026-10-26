import V185TrunkScan23Chunk0960

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5689925 : List Nat := [1, 3, 1, 1, 1, 5, 2, 1, 1, 2, 5]
def baseStart_5689925 : Nat := 118140960795 + 5689925 * 2 ^ 59
def prefixEnd_5689925 : Nat := 4983230072969 + 3 ^ 40 * 5689925 * 2
def baseEnd_5689925 : Nat := 2921666413033755875970017

theorem tailTrace_5689925 : CollatzResearch.WordTrace tailWord_5689925 prefixEnd_5689925 2921666413033755875970017 := by
  unfold tailWord_5689925
  simp only [CollatzResearch.WordTrace]
  refine ⟨207528613911380961669199229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138352409274253974446132819 207528613911380961669199229)
  ·
    refine ⟨77823230216767860625949711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207528613911380961669199229 77823230216767860625949711)
    ·
      refine ⟨116734845325151790938924567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77823230216767860625949711 116734845325151790938924567)
      ·
        refine ⟨175102267987727686408386851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116734845325151790938924567 175102267987727686408386851)
        ·
          refine ⟨262653401981591529612580277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175102267987727686408386851 262653401981591529612580277)
          ·
            refine ⟨24623756435774205901179401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 262653401981591529612580277 24623756435774205901179401)
            ·
              refine ⟨18467817326830654425884551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24623756435774205901179401 18467817326830654425884551)
              ·
                refine ⟨27701725990245981638826827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18467817326830654425884551 27701725990245981638826827)
                ·
                  refine ⟨41552588985368972458240241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27701725990245981638826827 41552588985368972458240241)
                  ·
                    refine ⟨31164441739026729343680181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41552588985368972458240241 31164441739026729343680181)
                    ·
                      refine ⟨2921666413033755875970017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31164441739026729343680181 2921666413033755875970017)
                      ·
                        rfl

theorem cell23_5689925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_5689925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689925 prefixEnd_5689925 := by exact prefixLift 5689925
  have htrace : WordTrace (prefixWord ++ tailWord_5689925) baseStart_5689925 baseEnd_5689925 := by
    simpa [prefixWord, tailWord_5689925, baseEnd_5689925] using wordTrace_append hprefix tailTrace_5689925
  have hstable : (prefixWord ++ tailWord_5689925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689925).length < 2 ^ (prefixWord ++ tailWord_5689925).sum := by decide
  have hdescent : baseEnd_5689925 < baseStart_5689925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689935 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 4]
def baseStart_5689935 : Nat := 118140960795 + 5689935 * 2 ^ 59
def prefixEnd_5689935 : Nat := 4983230072969 + 3 ^ 40 * 5689935 * 2
def baseEnd_5689935 : Nat := 2921671547840300836844971

theorem tailTrace_5689935 : CollatzResearch.WordTrace tailWord_5689935 prefixEnd_5689935 2921671547840300836844971 := by
  unfold tailWord_5689935
  simp only [CollatzResearch.WordTrace]
  refine ⟨207528978641344733377063259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138352652427563155584708839 207528978641344733377063259)
  ·
    refine ⟨311293467962017100065594889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207528978641344733377063259 311293467962017100065594889)
    ·
      refine ⟨233470100971512825049196167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311293467962017100065594889 233470100971512825049196167)
      ·
        refine ⟨350205151457269237573794251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233470100971512825049196167 350205151457269237573794251)
        ·
          refine ⟨525307727185903856360691377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350205151457269237573794251 525307727185903856360691377)
          ·
            refine ⟨393980795389427892270518533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 525307727185903856360691377 393980795389427892270518533)
            ·
              refine ⟨73871399135517729800722225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 393980795389427892270518533 73871399135517729800722225)
              ·
                refine ⟨55403549351638297350541669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73871399135517729800722225 55403549351638297350541669)
                ·
                  refine ⟨10388165503432180753226563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55403549351638297350541669 10388165503432180753226563)
                  ·
                    refine ⟨15582248255148271129839845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10388165503432180753226563 15582248255148271129839845)
                    ·
                      refine ⟨2921671547840300836844971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15582248255148271129839845 2921671547840300836844971)
                      ·
                        rfl

theorem cell23_5689935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 4, 1, 4].length) (baseStart_5689935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689935 prefixEnd_5689935 := by exact prefixLift 5689935
  have htrace : WordTrace (prefixWord ++ tailWord_5689935) baseStart_5689935 baseEnd_5689935 := by
    simpa [prefixWord, tailWord_5689935, baseEnd_5689935] using wordTrace_append hprefix tailTrace_5689935
  have hstable : (prefixWord ++ tailWord_5689935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689935).length < 2 ^ (prefixWord ++ tailWord_5689935).sum := by decide
  have hdescent : baseEnd_5689935 < baseStart_5689935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689952 : List Nat := [2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 4]
def baseStart_5689952 : Nat := 118140960795 + 5689952 * 2 ^ 59
def prefixEnd_5689952 : Nat := 4983230072969 + 3 ^ 40 * 5689952 * 2
def baseEnd_5689952 : Nat := 2921680277011427270332393

theorem tailTrace_5689952 : CollatzResearch.WordTrace tailWord_5689952 prefixEnd_5689952 2921680277011427270332393 := by
  unfold tailWord_5689952
  simp only [CollatzResearch.WordTrace]
  refine ⟨103764799341141572640216055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138353065788188763520288073 103764799341141572640216055)
  ·
    refine ⟨155647199011712358960324083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103764799341141572640216055 155647199011712358960324083)
    ·
      refine ⟨233470798517568538440486125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155647199011712358960324083 233470798517568538440486125)
      ·
        refine ⟨87551549444088201915182297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233470798517568538440486125 87551549444088201915182297)
        ·
          refine ⟨65663662083066151436386723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87551549444088201915182297 65663662083066151436386723)
          ·
            refine ⟨98495493124599227154580085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65663662083066151436386723 98495493124599227154580085)
            ·
              refine ⟨9233952480431177545741883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98495493124599227154580085 9233952480431177545741883)
              ·
                refine ⟨13850928720646766318612825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9233952480431177545741883 13850928720646766318612825)
                ·
                  refine ⟨10388196540485074738959619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13850928720646766318612825 10388196540485074738959619)
                  ·
                    refine ⟨15582294810727612108439429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10388196540485074738959619 15582294810727612108439429)
                    ·
                      refine ⟨2921680277011427270332393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15582294810727612108439429 2921680277011427270332393)
                      ·
                        rfl

theorem cell23_5689952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_5689952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689952 prefixEnd_5689952 := by exact prefixLift 5689952
  have htrace : WordTrace (prefixWord ++ tailWord_5689952) baseStart_5689952 baseEnd_5689952 := by
    simpa [prefixWord, tailWord_5689952, baseEnd_5689952] using wordTrace_append hprefix tailTrace_5689952
  have hstable : (prefixWord ++ tailWord_5689952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689952).length < 2 ^ (prefixWord ++ tailWord_5689952).sum := by decide
  have hdescent : baseEnd_5689952 < baseStart_5689952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689962 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 5, 4]
def baseStart_5689962 : Nat := 118140960795 + 5689962 * 2 ^ 59
def prefixEnd_5689962 : Nat := 4983230072969 + 3 ^ 40 * 5689962 * 2
def baseEnd_5689962 : Nat := 973895137272657410402449

theorem tailTrace_5689962 : CollatzResearch.WordTrace tailWord_5689962 prefixEnd_5689962 973895137272657410402449 := by
  unfold tailWord_5689962
  simp only [CollatzResearch.WordTrace]
  refine ⟨51882490853061729247074035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138353308941497944658864093 51882490853061729247074035)
  ·
    refine ⟨77823736279592593870611053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51882490853061729247074035 77823736279592593870611053)
    ·
      refine ⟨29183901104847222701479145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77823736279592593870611053 29183901104847222701479145)
      ·
        refine ⟨21887925828635417026109359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29183901104847222701479145 21887925828635417026109359)
        ·
          refine ⟨32831888742953125539164039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21887925828635417026109359 32831888742953125539164039)
          ·
            refine ⟨49247833114429688308746059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32831888742953125539164039 49247833114429688308746059)
            ·
              refine ⟨73871749671644532463119089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49247833114429688308746059 73871749671644532463119089)
              ·
                refine ⟨55403812253733399347339317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73871749671644532463119089 55403812253733399347339317)
                ·
                  refine ⟨5194107398787506188813061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55403812253733399347339317 5194107398787506188813061)
                  ·
                    refine ⟨973895137272657410402449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5194107398787506188813061 973895137272657410402449)
                    ·
                      rfl

theorem cell23_5689962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_5689962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689962 prefixEnd_5689962 := by exact prefixLift 5689962
  have htrace : WordTrace (prefixWord ++ tailWord_5689962) baseStart_5689962 baseEnd_5689962 := by
    simpa [prefixWord, tailWord_5689962, baseEnd_5689962] using wordTrace_append hprefix tailTrace_5689962
  have hstable : (prefixWord ++ tailWord_5689962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689962).length < 2 ^ (prefixWord ++ tailWord_5689962).sum := by decide
  have hdescent : baseEnd_5689962 < baseStart_5689962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690030 : List Nat := [4, 1, 4, 1, 1, 2, 3, 2, 1, 4]
def baseStart_5690030 : Nat := 118140960795 + 5690030 * 2 ^ 59
def prefixEnd_5690030 : Nat := 4983230072969 + 3 ^ 40 * 5690030 * 2
def baseEnd_5690030 : Nat := 973906776167492655052345

theorem tailTrace_5690030 : CollatzResearch.WordTrace tailWord_5690030 prefixEnd_5690030 973906776167492655052345 := by
  unfold tailWord_5690030
  simp only [CollatzResearch.WordTrace]
  refine ⟨25941555447000070575221443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138354962384000376401181029 25941555447000070575221443)
  ·
    refine ⟨38912333170500105862832165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25941555447000070575221443 38912333170500105862832165)
    ·
      refine ⟨7296062469468769849281031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38912333170500105862832165 7296062469468769849281031)
      ·
        refine ⟨10944093704203154773921547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7296062469468769849281031 10944093704203154773921547)
        ·
          refine ⟨16416140556304732160882321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10944093704203154773921547 16416140556304732160882321)
          ·
            refine ⟨12312105417228549120661741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16416140556304732160882321 12312105417228549120661741)
            ·
              refine ⟨4617039531460705920248153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12312105417228549120661741 4617039531460705920248153)
              ·
                refine ⟨3462779648595529440186115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4617039531460705920248153 3462779648595529440186115)
                ·
                  refine ⟨5194169472893294160279173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3462779648595529440186115 5194169472893294160279173)
                  ·
                    refine ⟨973906776167492655052345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5194169472893294160279173 973906776167492655052345)
                    ·
                      rfl

theorem cell23_5690030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_5690030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690030 prefixEnd_5690030 := by exact prefixLift 5690030
  have htrace : WordTrace (prefixWord ++ tailWord_5690030) baseStart_5690030 baseEnd_5690030 := by
    simpa [prefixWord, tailWord_5690030, baseEnd_5690030] using wordTrace_append hprefix tailTrace_5690030
  have hstable : (prefixWord ++ tailWord_5690030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690030).length < 2 ^ (prefixWord ++ tailWord_5690030).sum := by decide
  have hdescent : baseEnd_5690030 < baseStart_5690030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690042 : List Nat := [3, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4]
def baseStart_5690042 : Nat := 118140960795 + 5690042 * 2 ^ 59
def prefixEnd_5690042 : Nat := 4983230072969 + 3 ^ 40 * 5690042 * 2
def baseEnd_5690042 : Nat := 2921726490270331918206979

theorem tailTrace_5690042 : CollatzResearch.WordTrace tailWord_5690042 prefixEnd_5690042 2921726490270331918206979 := by
  unfold tailWord_5690042
  simp only [CollatzResearch.WordTrace]
  refine ⟨51883220312989272662802095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138355254167971393767472253 51883220312989272662802095)
  ·
    refine ⟨77824830469483908994203143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51883220312989272662802095 77824830469483908994203143)
    ·
      refine ⟨116737245704225863491304715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77824830469483908994203143 116737245704225863491304715)
      ·
        refine ⟨175105868556338795236957073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116737245704225863491304715 175105868556338795236957073)
        ·
          refine ⟨131329401417254096427717805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175105868556338795236957073 131329401417254096427717805)
          ·
            refine ⟨49248525531470286160394177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131329401417254096427717805 49248525531470286160394177)
            ·
              refine ⟨36936394148602714620295633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49248525531470286160394177 36936394148602714620295633)
              ·
                refine ⟨27702295611452035965221725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36936394148602714620295633 27702295611452035965221725)
                ·
                  refine ⟨10388360854294513486958147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27702295611452035965221725 10388360854294513486958147)
                  ·
                    refine ⟨15582541281441770230437221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10388360854294513486958147 15582541281441770230437221)
                    ·
                      refine ⟨2921726490270331918206979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15582541281441770230437221 2921726490270331918206979)
                      ·
                        rfl

theorem cell23_5690042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_5690042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690042 prefixEnd_5690042 := by exact prefixLift 5690042
  have htrace : WordTrace (prefixWord ++ tailWord_5690042) baseStart_5690042 baseEnd_5690042 := by
    simpa [prefixWord, tailWord_5690042, baseEnd_5690042] using wordTrace_append hprefix tailTrace_5690042
  have hstable : (prefixWord ++ tailWord_5690042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690042).length < 2 ^ (prefixWord ++ tailWord_5690042).sum := by decide
  have hdescent : baseEnd_5690042 < baseStart_5690042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690065 : List Nat := [1, 2, 2, 1, 2, 3, 1, 11]
def baseStart_5690065 : Nat := 118140960795 + 5690065 * 2 ^ 59
def prefixEnd_5690065 : Nat := 4983230072969 + 3 ^ 40 * 5690065 * 2
def baseEnd_5690065 : Nat := 108212529641680938082199

theorem tailTrace_5690065 : CollatzResearch.WordTrace tailWord_5690065 prefixEnd_5690065 108212529641680938082199 := by
  unfold tailWord_5690065
  simp only [CollatzResearch.WordTrace]
  refine ⟨207533720130873765579295649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138355813420582510386197099 207533720130873765579295649)
  ·
    refine ⟨155650290098155324184471737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207533720130873765579295649 155650290098155324184471737)
    ·
      refine ⟨116737717573616493138353803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155650290098155324184471737 116737717573616493138353803)
      ·
        refine ⟨175106576360424739707530705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116737717573616493138353803 175106576360424739707530705)
        ·
          refine ⟨131329932270318554780648029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175106576360424739707530705 131329932270318554780648029)
          ·
            refine ⟨49248724601369458042743011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131329932270318554780648029 49248724601369458042743011)
            ·
              refine ⟨73873086902054187064114517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49248724601369458042743011 73873086902054187064114517)
              ·
                refine ⟨108212529641680938082199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 73873086902054187064114517 108212529641680938082199)
                ·
                  rfl

theorem cell23_5690065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 11].length) (baseStart_5690065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690065 prefixEnd_5690065 := by exact prefixLift 5690065
  have htrace : WordTrace (prefixWord ++ tailWord_5690065) baseStart_5690065 baseEnd_5690065 := by
    simpa [prefixWord, tailWord_5690065, baseEnd_5690065] using wordTrace_append hprefix tailTrace_5690065
  have hstable : (prefixWord ++ tailWord_5690065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690065).length < 2 ^ (prefixWord ++ tailWord_5690065).sum := by decide
  have hdescent : baseEnd_5690065 < baseStart_5690065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690072 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 3, 2, 4]
def baseStart_5690072 : Nat := 118140960795 + 5690072 * 2 ^ 59
def prefixEnd_5690072 : Nat := 4983230072969 + 3 ^ 40 * 5690072 * 2
def baseEnd_5690072 : Nat := 2921741894689966800831841

theorem tailTrace_5690072 : CollatzResearch.WordTrace tailWord_5690072 prefixEnd_5690072 2921741894689966800831841 := by
  unfold tailWord_5690072
  simp only [CollatzResearch.WordTrace]
  refine ⟨103766987720924202887400235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138355983627898937183200313 103766987720924202887400235)
  ·
    refine ⟨155650481581386304331100353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103766987720924202887400235 155650481581386304331100353)
    ·
      refine ⟨116737861186039728248325265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155650481581386304331100353 116737861186039728248325265)
      ·
        refine ⟨87553395889529796186243949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116737861186039728248325265 87553395889529796186243949)
        ·
          refine ⟨32832523458573673569841481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87553395889529796186243949 32832523458573673569841481)
          ·
            refine ⟨24624392593930255177381111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32832523458573673569841481 24624392593930255177381111)
            ·
              refine ⟨36936588890895382766071667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24624392593930255177381111 36936588890895382766071667)
              ·
                refine ⟨55404883336343074149107501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36936588890895382766071667 55404883336343074149107501)
                ·
                  refine ⟨20776831251128652805915313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55404883336343074149107501 20776831251128652805915313)
                  ·
                    refine ⟨15582623438346489604436485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20776831251128652805915313 15582623438346489604436485)
                    ·
                      refine ⟨2921741894689966800831841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15582623438346489604436485 2921741894689966800831841)
                      ·
                        rfl

theorem cell23_5690072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_5690072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690072 prefixEnd_5690072 := by exact prefixLift 5690072
  have htrace : WordTrace (prefixWord ++ tailWord_5690072) baseStart_5690072 baseEnd_5690072 := by
    simpa [prefixWord, tailWord_5690072, baseEnd_5690072] using wordTrace_append hprefix tailTrace_5690072
  have hstable : (prefixWord ++ tailWord_5690072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690072).length < 2 ^ (prefixWord ++ tailWord_5690072).sum := by decide
  have hdescent : baseEnd_5690072 < baseStart_5690072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690079 : List Nat := [1, 1, 2, 3, 2, 5, 1, 1, 1, 1, 5]
def baseStart_5690079 : Nat := 118140960795 + 5690079 * 2 ^ 59
def prefixEnd_5690079 : Nat := 4983230072969 + 3 ^ 40 * 5690079 * 2
def baseEnd_5690079 : Nat := 2921745489054548273444309

theorem tailTrace_5690079 : CollatzResearch.WordTrace tailWord_5690079 prefixEnd_5690079 2921745489054548273444309 := by
  unfold tailWord_5690079
  simp only [CollatzResearch.WordTrace]
  refine ⟨207534230752823045970305291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138356153835215363980203527 207534230752823045970305291)
  ·
    refine ⟨311301346129234568955457937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207534230752823045970305291 311301346129234568955457937)
    ·
      refine ⟨233476009596925926716593453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311301346129234568955457937 233476009596925926716593453)
      ·
        refine ⟨87553503598847222518722545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233476009596925926716593453 87553503598847222518722545)
        ·
          refine ⟨65665127699135416889041909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87553503598847222518722545 65665127699135416889041909)
          ·
            refine ⟨6156105721793945333347679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65665127699135416889041909 6156105721793945333347679)
            ·
              refine ⟨9234158582690918000021519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6156105721793945333347679 9234158582690918000021519)
              ·
                refine ⟨13851237874036377000032279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9234158582690918000021519 13851237874036377000032279)
                ·
                  refine ⟨20776856811054565500048419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13851237874036377000032279 20776856811054565500048419)
                  ·
                    refine ⟨31165285216581848250072629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20776856811054565500048419 31165285216581848250072629)
                    ·
                      refine ⟨2921745489054548273444309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31165285216581848250072629 2921745489054548273444309)
                      ·
                        rfl

theorem cell23_5690079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_5690079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690079 prefixEnd_5690079 := by exact prefixLift 5690079
  have htrace : WordTrace (prefixWord ++ tailWord_5690079) baseStart_5690079 baseEnd_5690079 := by
    simpa [prefixWord, tailWord_5690079, baseEnd_5690079] using wordTrace_append hprefix tailTrace_5690079
  have hstable : (prefixWord ++ tailWord_5690079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690079).length < 2 ^ (prefixWord ++ tailWord_5690079).sum := by decide
  have hdescent : baseEnd_5690079 < baseStart_5690079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690092 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 3]
def baseStart_5690092 : Nat := 118140960795 + 5690092 * 2 ^ 59
def prefixEnd_5690092 : Nat := 4983230072969 + 3 ^ 40 * 5690092 * 2
def baseEnd_5690092 : Nat := 2921752164303056722581749

theorem tailTrace_5690092 : CollatzResearch.WordTrace tailWord_5690092 prefixEnd_5690092 2921752164303056722581749 := by
  unfold tailWord_5690092
  simp only [CollatzResearch.WordTrace]
  refine ⟨103767352450887974595264265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138356469934517299460352353 103767352450887974595264265)
  ·
    refine ⟨77825514338165980946448199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103767352450887974595264265 77825514338165980946448199)
    ·
      refine ⟨116738271507248971419672299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77825514338165980946448199 116738271507248971419672299)
      ·
        refine ⟨175107407260873457129508449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116738271507248971419672299 175107407260873457129508449)
        ·
          refine ⟨131330555445655092847131337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175107407260873457129508449 131330555445655092847131337)
          ·
            refine ⟨98497916584241319635348503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131330555445655092847131337 98497916584241319635348503)
            ·
              refine ⟨147746874876361979453022755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98497916584241319635348503 147746874876361979453022755)
              ·
                refine ⟨221620312314542969179534133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147746874876361979453022755 221620312314542969179534133)
                ·
                  refine ⟨20776904279488403360581325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 221620312314542969179534133 20776904279488403360581325)
                  ·
                    refine ⟨7791339104808151260217997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20776904279488403360581325 7791339104808151260217997)
                    ·
                      refine ⟨2921752164303056722581749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7791339104808151260217997 2921752164303056722581749)
                      ·
                        rfl

theorem cell23_5690092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 3].length) (baseStart_5690092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690092 prefixEnd_5690092 := by exact prefixLift 5690092
  have htrace : WordTrace (prefixWord ++ tailWord_5690092) baseStart_5690092 baseEnd_5690092 := by
    simpa [prefixWord, tailWord_5690092, baseEnd_5690092] using wordTrace_append hprefix tailTrace_5690092
  have hstable : (prefixWord ++ tailWord_5690092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690092).length < 2 ^ (prefixWord ++ tailWord_5690092).sum := by decide
  have hdescent : baseEnd_5690092 < baseStart_5690092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690109 : List Nat := [1, 4, 1, 1, 1, 1, 6, 1, 1, 3, 3]
def baseStart_5690109 : Nat := 118140960795 + 5690109 * 2 ^ 59
def prefixEnd_5690109 : Nat := 4983230072969 + 3 ^ 40 * 5690109 * 2
def baseEnd_5690109 : Nat := 2921760893474183156069171

theorem tailTrace_5690109 : CollatzResearch.WordTrace tailWord_5690109 prefixEnd_5690109 2921760893474183156069171 := by
  unfold tailWord_5690109
  simp only [CollatzResearch.WordTrace]
  refine ⟨207535324942714361093897381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138356883295142907395931587 207535324942714361093897381)
  ·
    refine ⟨38912873426758942705105759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207535324942714361093897381 38912873426758942705105759)
    ·
      refine ⟨58369310140138414057658639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38912873426758942705105759 58369310140138414057658639)
      ·
        refine ⟨87553965210207621086487959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58369310140138414057658639 87553965210207621086487959)
        ·
          refine ⟨131330947815311431629731939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87553965210207621086487959 131330947815311431629731939)
          ·
            refine ⟨196996421722967147444597909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131330947815311431629731939 196996421722967147444597909)
            ·
              refine ⟨9234207268264085036465527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 196996421722967147444597909 9234207268264085036465527)
              ·
                refine ⟨13851310902396127554698291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9234207268264085036465527 13851310902396127554698291)
                ·
                  refine ⟨20776966353594191332047437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13851310902396127554698291 20776966353594191332047437)
                  ·
                    refine ⟨7791362382597821749517789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20776966353594191332047437 7791362382597821749517789)
                    ·
                      refine ⟨2921760893474183156069171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7791362382597821749517789 2921760893474183156069171)
                      ·
                        rfl

theorem cell23_5690109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_5690109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690109 prefixEnd_5690109 := by exact prefixLift 5690109
  have htrace : WordTrace (prefixWord ++ tailWord_5690109) baseStart_5690109 baseEnd_5690109 := by
    simpa [prefixWord, tailWord_5690109, baseEnd_5690109] using wordTrace_append hprefix tailTrace_5690109
  have hstable : (prefixWord ++ tailWord_5690109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690109).length < 2 ^ (prefixWord ++ tailWord_5690109).sum := by decide
  have hdescent : baseEnd_5690109 < baseStart_5690109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690122 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 2, 2, 5]
def baseStart_5690122 : Nat := 118140960795 + 5690122 * 2 ^ 59
def prefixEnd_5690122 : Nat := 4983230072969 + 3 ^ 40 * 5690122 * 2
def baseEnd_5690122 : Nat := 2921767568722691605206611

theorem tailTrace_5690122 : CollatzResearch.WordTrace tailWord_5690122 prefixEnd_5690122 2921767568722691605206611 := by
  unfold tailWord_5690122
  simp only [CollatzResearch.WordTrace]
  refine ⟨51883949772916816078530155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138357199394444842876080413 51883949772916816078530155)
  ·
    refine ⟨77825924659375224117795233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51883949772916816078530155 77825924659375224117795233)
    ·
      refine ⟨58369443494531418088346425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77825924659375224117795233 58369443494531418088346425)
      ·
        refine ⟨43777082620898563566259819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58369443494531418088346425 43777082620898563566259819)
        ·
          refine ⟨65665623931347845349389729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43777082620898563566259819 65665623931347845349389729)
          ·
            refine ⟨49249217948510884012042297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65665623931347845349389729 49249217948510884012042297)
            ·
              refine ⟨36936913461383163009031723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49249217948510884012042297 36936913461383163009031723)
              ·
                refine ⟨55405370192074744513547585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36936913461383163009031723 55405370192074744513547585)
                ·
                  refine ⟨41554027644056058385160689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55405370192074744513547585 41554027644056058385160689)
                  ·
                    refine ⟨31165520733042043788870517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41554027644056058385160689 31165520733042043788870517)
                    ·
                      refine ⟨2921767568722691605206611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31165520733042043788870517 2921767568722691605206611)
                      ·
                        rfl

theorem cell23_5690122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_5690122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690122 prefixEnd_5690122 := by exact prefixLift 5690122
  have htrace : WordTrace (prefixWord ++ tailWord_5690122) baseStart_5690122 baseEnd_5690122 := by
    simpa [prefixWord, tailWord_5690122, baseEnd_5690122] using wordTrace_append hprefix tailTrace_5690122
  have hstable : (prefixWord ++ tailWord_5690122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690122).length < 2 ^ (prefixWord ++ tailWord_5690122).sum := by decide
  have hdescent : baseEnd_5690122 < baseStart_5690122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690143 : List Nat := [1, 1, 2, 4, 2, 4, 1, 2, 2, 1, 3]
def baseStart_5690143 : Nat := 118140960795 + 5690143 * 2 ^ 59
def prefixEnd_5690143 : Nat := 4983230072969 + 3 ^ 40 * 5690143 * 2
def baseEnd_5690143 : Nat := 2921778351816436023044015

theorem tailTrace_5690143 : CollatzResearch.WordTrace tailWord_5690143 prefixEnd_5690143 2921778351816436023044015 := by
  unfold tailWord_5690143
  simp only [CollatzResearch.WordTrace]
  refine ⟨207536565024591184900635083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138357710016394123267090055 207536565024591184900635083)
  ·
    refine ⟨311304847536886777350952625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207536565024591184900635083 311304847536886777350952625)
    ·
      refine ⟨233478635652665083013214469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311304847536886777350952625 233478635652665083013214469)
      ·
        refine ⟨43777244184874703064977713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233478635652665083013214469 43777244184874703064977713)
        ·
          refine ⟨32832933138656027298733285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43777244184874703064977713 32832933138656027298733285)
          ·
            refine ⟨6156174963498005118512491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32832933138656027298733285 6156174963498005118512491)
            ·
              refine ⟨9234262445247007677768737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6156174963498005118512491 9234262445247007677768737)
              ·
                refine ⟨6925696833935255758326553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9234262445247007677768737 6925696833935255758326553)
                ·
                  refine ⟨5194272625451441818744915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6925696833935255758326553 5194272625451441818744915)
                  ·
                    refine ⟨7791408938177162728117373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5194272625451441818744915 7791408938177162728117373)
                    ·
                      refine ⟨2921778351816436023044015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7791408938177162728117373 2921778351816436023044015)
                      ·
                        rfl

theorem cell23_5690143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_5690143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690143 prefixEnd_5690143 := by exact prefixLift 5690143
  have htrace : WordTrace (prefixWord ++ tailWord_5690143) baseStart_5690143 baseEnd_5690143 := by
    simpa [prefixWord, tailWord_5690143, baseEnd_5690143] using wordTrace_append hprefix tailTrace_5690143
  have hstable : (prefixWord ++ tailWord_5690143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690143).length < 2 ^ (prefixWord ++ tailWord_5690143).sum := by decide
  have hdescent : baseEnd_5690143 < baseStart_5690143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690239 : List Nat := [1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 4]
def baseStart_5690239 : Nat := 118140960795 + 5690239 * 2 ^ 59
def prefixEnd_5690239 : Nat := 4983230072969 + 3 ^ 40 * 5690239 * 2
def baseEnd_5690239 : Nat := 2921827645959267647443573

theorem tailTrace_5690239 : CollatzResearch.WordTrace tailWord_5690239 prefixEnd_5690239 2921827645959267647443573 := by
  unfold tailWord_5690239
  simp only [CollatzResearch.WordTrace]
  refine ⟨207540066432243393296129771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138360044288162262197419847 207540066432243393296129771)
  ·
    refine ⟨311310099648365089944194657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207540066432243393296129771 311310099648365089944194657)
    ·
      refine ⟨233482574736273817458145993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311310099648365089944194657 233482574736273817458145993)
      ·
        refine ⟨175111931052205363093609495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233482574736273817458145993 175111931052205363093609495)
        ·
          refine ⟨262667896578308044640414243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175111931052205363093609495 262667896578308044640414243)
          ·
            refine ⟨394001844867462066960621365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262667896578308044640414243 394001844867462066960621365)
            ·
              refine ⟨36937672956324568777558253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 394001844867462066960621365 36937672956324568777558253)
              ·
                refine ⟨13851627358621713291584345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36937672956324568777558253 13851627358621713291584345)
                ·
                  refine ⟨10388720518966284968688259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13851627358621713291584345 10388720518966284968688259)
                  ·
                    refine ⟨15583080778449427453032389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10388720518966284968688259 15583080778449427453032389)
                    ·
                      refine ⟨2921827645959267647443573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15583080778449427453032389 2921827645959267647443573)
                      ·
                        rfl

theorem cell23_5690239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_5690239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690239 prefixEnd_5690239 := by exact prefixLift 5690239
  have htrace : WordTrace (prefixWord ++ tailWord_5690239) baseStart_5690239 baseEnd_5690239 := by
    simpa [prefixWord, tailWord_5690239, baseEnd_5690239] using wordTrace_append hprefix tailTrace_5690239
  have hstable : (prefixWord ++ tailWord_5690239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690239).length < 2 ^ (prefixWord ++ tailWord_5690239).sum := by decide
  have hdescent : baseEnd_5690239 < baseStart_5690239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690259 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 4, 2, 3]
def baseStart_5690259 : Nat := 118140960795 + 5690259 * 2 ^ 59
def prefixEnd_5690259 : Nat := 4983230072969 + 3 ^ 40 * 5690259 * 2
def baseEnd_5690259 : Nat := 2921837915572357569193481

theorem tailTrace_5690259 : CollatzResearch.WordTrace tailWord_5690259 prefixEnd_5690259 2921837915572357569193481 := by
  unfold tailWord_5690259
  simp only [CollatzResearch.WordTrace]
  refine ⟨207540795892170936711857831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138360530594780624474571887 207540795892170936711857831)
  ·
    refine ⟨311311193838256405067786747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207540795892170936711857831 311311193838256405067786747)
    ·
      refine ⟨466966790757384607601680121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311311193838256405067786747 466966790757384607601680121)
      ·
        refine ⟨350225093068038455701260091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466966790757384607601680121 350225093068038455701260091)
        ·
          refine ⟨525337639602057683551890137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350225093068038455701260091 525337639602057683551890137)
          ·
            refine ⟨394003229701543262663917603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 525337639602057683551890137 394003229701543262663917603)
            ·
              refine ⟨591004844552314893995876405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394003229701543262663917603 591004844552314893995876405)
              ·
                refine ⟨55406704176779521312113413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 591004844552314893995876405 55406704176779521312113413)
                ·
                  refine ⟨10388757033146160246021265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55406704176779521312113413 10388757033146160246021265)
                  ·
                    refine ⟨7791567774859620184515949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10388757033146160246021265 7791567774859620184515949)
                    ·
                      refine ⟨2921837915572357569193481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7791567774859620184515949 2921837915572357569193481)
                      ·
                        rfl

theorem cell23_5690259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2, 3].length) (baseStart_5690259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690259 prefixEnd_5690259 := by exact prefixLift 5690259
  have htrace : WordTrace (prefixWord ++ tailWord_5690259) baseStart_5690259 baseEnd_5690259 := by
    simpa [prefixWord, tailWord_5690259, baseEnd_5690259] using wordTrace_append hprefix tailTrace_5690259
  have hstable : (prefixWord ++ tailWord_5690259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690259).length < 2 ^ (prefixWord ++ tailWord_5690259).sum := by decide
  have hdescent : baseEnd_5690259 < baseStart_5690259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690273 : List Nat := [1, 2, 3, 4, 1, 2, 1, 1, 2, 4, 2]
def baseStart_5690273 : Nat := 118140960795 + 5690273 * 2 ^ 59
def prefixEnd_5690273 : Nat := 4983230072969 + 3 ^ 40 * 5690273 * 2
def baseEnd_5690273 : Nat := 2921845104301520514418417

theorem tailTrace_5690273 : CollatzResearch.WordTrace tailWord_5690273 prefixEnd_5690273 2921845104301520514418417 := by
  unfold tailWord_5690273
  simp only [CollatzResearch.WordTrace]
  refine ⟨207541306514120217102867473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138360871009413478068578315 207541306514120217102867473)
  ·
    refine ⟨155655979885590162827150605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207541306514120217102867473 155655979885590162827150605)
    ·
      refine ⟨58370992457096311060181477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155655979885590162827150605 58370992457096311060181477)
      ·
        refine ⟨10944561085705558323784027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58370992457096311060181477 10944561085705558323784027)
        ·
          refine ⟨16416841628558337485676041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10944561085705558323784027 16416841628558337485676041)
          ·
            refine ⟨12312631221418753114257031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16416841628558337485676041 12312631221418753114257031)
            ·
              refine ⟨18468946832128129671385547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12312631221418753114257031 18468946832128129671385547)
              ·
                refine ⟨27703420248192194507078321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18468946832128129671385547 27703420248192194507078321)
                ·
                  refine ⟨20777565186144145880308741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27703420248192194507078321 20777565186144145880308741)
                  ·
                    refine ⟨3895793472402027352557889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20777565186144145880308741 3895793472402027352557889)
                    ·
                      refine ⟨2921845104301520514418417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3895793472402027352557889 2921845104301520514418417)
                      ·
                        rfl

theorem cell23_5690273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_5690273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690273 prefixEnd_5690273 := by exact prefixLift 5690273
  have htrace : WordTrace (prefixWord ++ tailWord_5690273) baseStart_5690273 baseEnd_5690273 := by
    simpa [prefixWord, tailWord_5690273, baseEnd_5690273] using wordTrace_append hprefix tailTrace_5690273
  have hstable : (prefixWord ++ tailWord_5690273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690273).length < 2 ^ (prefixWord ++ tailWord_5690273).sum := by decide
  have hdescent : baseEnd_5690273 < baseStart_5690273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690333 : List Nat := [1, 4, 3, 1, 2, 1, 1, 2, 1, 5, 2]
def baseStart_5690333 : Nat := 118140960795 + 5690333 * 2 ^ 59
def prefixEnd_5690333 : Nat := 4983230072969 + 3 ^ 40 * 5690333 * 2
def baseEnd_5690333 : Nat := 2921875913140790279668141

theorem tailTrace_5690333 : CollatzResearch.WordTrace tailWord_5690333 prefixEnd_5690333 2921875913140790279668141 := by
  unfold tailWord_5690333
  simp only [CollatzResearch.WordTrace]
  refine ⟨207543494893902847350051653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138362329929268564900034435 207543494893902847350051653)
  ·
    refine ⟨38914405292606783878134685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207543494893902847350051653 38914405292606783878134685)
    ·
      refine ⟨14592901984727543954300507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38914405292606783878134685 14592901984727543954300507)
      ·
        refine ⟨21889352977091315931450761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14592901984727543954300507 21889352977091315931450761)
        ·
          refine ⟨16417014732818486948588071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21889352977091315931450761 16417014732818486948588071)
          ·
            refine ⟨24625522099227730422882107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16417014732818486948588071 24625522099227730422882107)
            ·
              refine ⟨36938283148841595634323161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24625522099227730422882107 36938283148841595634323161)
              ·
                refine ⟨27703712361631196725742371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36938283148841595634323161 27703712361631196725742371)
                ·
                  refine ⟨41555568542446795088613557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27703712361631196725742371 41555568542446795088613557)
                  ·
                    refine ⟨3895834550854387039557521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41555568542446795088613557 3895834550854387039557521)
                    ·
                      refine ⟨2921875913140790279668141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3895834550854387039557521 2921875913140790279668141)
                      ·
                        rfl

theorem cell23_5690333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_5690333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690333 prefixEnd_5690333 := by exact prefixLift 5690333
  have htrace : WordTrace (prefixWord ++ tailWord_5690333) baseStart_5690333 baseEnd_5690333 := by
    simpa [prefixWord, tailWord_5690333, baseEnd_5690333] using wordTrace_append hprefix tailTrace_5690333
  have hstable : (prefixWord ++ tailWord_5690333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690333).length < 2 ^ (prefixWord ++ tailWord_5690333).sum := by decide
  have hdescent : baseEnd_5690333 < baseStart_5690333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690343 : List Nat := [1, 1, 5, 2, 2, 2, 2, 2, 1, 5]
def baseStart_5690343 : Nat := 118140960795 + 5690343 * 2 ^ 59
def prefixEnd_5690343 : Nat := 4983230072969 + 3 ^ 40 * 5690343 * 2
def baseEnd_5690343 : Nat := 973960349315778413514365

theorem tailTrace_5690343 : CollatzResearch.WordTrace tailWord_5690343 prefixEnd_5690343 973960349315778413514365 := by
  unfold tailWord_5690343
  simp only [CollatzResearch.WordTrace]
  refine ⟨207543859623866619057915683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138362573082577746038610455 207543859623866619057915683)
  ·
    refine ⟨311315789435799928586873525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207543859623866619057915683 311315789435799928586873525)
    ·
      refine ⟨29185855259606243305019393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 311315789435799928586873525 29185855259606243305019393)
      ·
        refine ⟨21889391444704682478764545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29185855259606243305019393 21889391444704682478764545)
        ·
          refine ⟨16417043583528511859073409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21889391444704682478764545 16417043583528511859073409)
          ·
            refine ⟨12312782687646383894305057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16417043583528511859073409 12312782687646383894305057)
            ·
              refine ⟨9234587015734787920728793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12312782687646383894305057 9234587015734787920728793)
              ·
                refine ⟨6925940261801090940546595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9234587015734787920728793 6925940261801090940546595)
                ·
                  refine ⟨10388910392701636410819893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6925940261801090940546595 10388910392701636410819893)
                  ·
                    refine ⟨973960349315778413514365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10388910392701636410819893 973960349315778413514365)
                    ·
                      rfl

theorem cell23_5690343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_5690343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690343 prefixEnd_5690343 := by exact prefixLift 5690343
  have htrace : WordTrace (prefixWord ++ tailWord_5690343) baseStart_5690343 baseEnd_5690343 := by
    simpa [prefixWord, tailWord_5690343, baseEnd_5690343] using wordTrace_append hprefix tailTrace_5690343
  have hstable : (prefixWord ++ tailWord_5690343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690343).length < 2 ^ (prefixWord ++ tailWord_5690343).sum := by decide
  have hdescent : baseEnd_5690343 < baseStart_5690343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690369 : List Nat := [1, 2, 4, 1, 2, 2, 11]
def baseStart_5690369 : Nat := 118140960795 + 5690369 * 2 ^ 59
def prefixEnd_5690369 : Nat := 4983230072969 + 3 ^ 40 * 5690369 * 2
def baseEnd_5690369 : Nat := 36072770351164841219975

theorem tailTrace_5690369 : CollatzResearch.WordTrace tailWord_5690369 prefixEnd_5690369 36072770351164841219975 := by
  unfold tailWord_5690369
  simp only [CollatzResearch.WordTrace]
  refine ⟨207544807921772425498362161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138363205281181616998908107 207544807921772425498362161)
  ·
    refine ⟨155658605941329319123771621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207544807921772425498362161 155658605941329319123771621)
    ·
      refine ⟨29185988613999247335707179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155658605941329319123771621 29185988613999247335707179)
      ·
        refine ⟨43778982920998871003560769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29185988613999247335707179 43778982920998871003560769)
        ·
          refine ⟨32834237190749153252670577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43778982920998871003560769 32834237190749153252670577)
          ·
            refine ⟨24625677893061864939502933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32834237190749153252670577 24625677893061864939502933)
            ·
              refine ⟨36072770351164841219975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24625677893061864939502933 36072770351164841219975)
              ·
                rfl

theorem cell23_5690369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 11].length) (baseStart_5690369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690369 prefixEnd_5690369 := by exact prefixLift 5690369
  have htrace : WordTrace (prefixWord ++ tailWord_5690369) baseStart_5690369 baseEnd_5690369 := by
    simpa [prefixWord, tailWord_5690369, baseEnd_5690369] using wordTrace_append hprefix tailTrace_5690369
  have hstable : (prefixWord ++ tailWord_5690369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690369).length < 2 ^ (prefixWord ++ tailWord_5690369).sum := by decide
  have hdescent : baseEnd_5690369 < baseStart_5690369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690380 : List Nat := [2, 2, 1, 2, 3, 2, 3, 1, 3, 2, 2]
def baseStart_5690380 : Nat := 118140960795 + 5690380 * 2 ^ 59
def prefixEnd_5690380 : Nat := 4983230072969 + 3 ^ 40 * 5690380 * 2
def baseEnd_5690380 : Nat := 2921900046731551595780425

theorem tailTrace_5690380 : CollatzResearch.WordTrace tailWord_5690380 prefixEnd_5690380 2921900046731551595780425 := by
  unfold tailWord_5690380
  simp only [CollatzResearch.WordTrace]
  refine ⟨103772604562366287188506297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138363472749821716251341729 103772604562366287188506297)
  ·
    refine ⟨77829453421774715391379723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103772604562366287188506297 77829453421774715391379723)
    ·
      refine ⟨116744180132662073087069585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77829453421774715391379723 116744180132662073087069585)
      ·
        refine ⟨87558135099496554815302189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116744180132662073087069585 87558135099496554815302189)
        ·
          refine ⟨32834300662311208055738321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87558135099496554815302189 32834300662311208055738321)
          ·
            refine ⟨24625725496733406041803741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32834300662311208055738321 24625725496733406041803741)
            ·
              refine ⟨9234647061275027265676403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24625725496733406041803741 9234647061275027265676403)
              ·
                refine ⟨13851970591912540898514605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9234647061275027265676403 13851970591912540898514605)
                ·
                  refine ⟨5194488971967202836942977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13851970591912540898514605 5194488971967202836942977)
                  ·
                    refine ⟨3895866728975402127707233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5194488971967202836942977 3895866728975402127707233)
                    ·
                      refine ⟨2921900046731551595780425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3895866728975402127707233 2921900046731551595780425)
                      ·
                        rfl

theorem cell23_5690380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 3, 2, 2].length) (baseStart_5690380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690380 prefixEnd_5690380 := by exact prefixLift 5690380
  have htrace : WordTrace (prefixWord ++ tailWord_5690380) baseStart_5690380 baseEnd_5690380 := by
    simpa [prefixWord, tailWord_5690380, baseEnd_5690380] using wordTrace_append hprefix tailTrace_5690380
  have hstable : (prefixWord ++ tailWord_5690380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690380).length < 2 ^ (prefixWord ++ tailWord_5690380).sum := by decide
  have hdescent : baseEnd_5690380 < baseStart_5690380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690397 : List Nat := [1, 4, 2, 2, 4, 1, 1, 2, 1, 1, 4]
def baseStart_5690397 : Nat := 118140960795 + 5690397 * 2 ^ 59
def prefixEnd_5690397 : Nat := 4983230072969 + 3 ^ 40 * 5690397 * 2
def baseEnd_5690397 : Nat := 2921908775902678029267847

theorem tailTrace_5690397 : CollatzResearch.WordTrace tailWord_5690397 prefixEnd_5690397 2921908775902678029267847 := by
  unfold tailWord_5690397
  simp only [CollatzResearch.WordTrace]
  refine ⟨207545829165670986280381445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138363886110447324186920963 207545829165670986280381445)
  ·
    refine ⟨38914842968563309927571521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207545829165670986280381445 38914842968563309927571521)
    ·
      refine ⟨29186132226422482445678641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38914842968563309927571521 29186132226422482445678641)
      ·
        refine ⟨21889599169816861834258981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29186132226422482445678641 21889599169816861834258981)
        ·
          refine ⟨4104299844340661593923559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21889599169816861834258981 4104299844340661593923559)
          ·
            refine ⟨6156449766510992390885339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4104299844340661593923559 6156449766510992390885339)
            ·
              refine ⟨9234674649766488586328009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6156449766510992390885339 9234674649766488586328009)
              ·
                refine ⟨6926005987324866439746007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9234674649766488586328009 6926005987324866439746007)
                ·
                  refine ⟨10389008980987299659619011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6926005987324866439746007 10389008980987299659619011)
                  ·
                    refine ⟨15583513471480949489428517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10389008980987299659619011 15583513471480949489428517)
                    ·
                      refine ⟨2921908775902678029267847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15583513471480949489428517 2921908775902678029267847)
                      ·
                        rfl

theorem cell23_5690397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_5690397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690397 prefixEnd_5690397 := by exact prefixLift 5690397
  have htrace : WordTrace (prefixWord ++ tailWord_5690397) baseStart_5690397 baseEnd_5690397 := by
    simpa [prefixWord, tailWord_5690397, baseEnd_5690397] using wordTrace_append hprefix tailTrace_5690397
  have hstable : (prefixWord ++ tailWord_5690397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690397).length < 2 ^ (prefixWord ++ tailWord_5690397).sum := by decide
  have hdescent : baseEnd_5690397 < baseStart_5690397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690400 : List Nat := [2, 1, 1, 7, 1, 1, 1, 1, 3, 2, 3]
def baseStart_5690400 : Nat := 118140960795 + 5690400 * 2 ^ 59
def prefixEnd_5690400 : Nat := 4983230072969 + 3 ^ 40 * 5690400 * 2
def baseEnd_5690400 : Nat := 2921910316344641517530333

theorem tailTrace_5690400 : CollatzResearch.WordTrace tailWord_5690400 prefixEnd_5690400 2921910316344641517530333 := by
  unfold tailWord_5690400
  simp only [CollatzResearch.WordTrace]
  refine ⟨103772969292330058896370327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138363959056440078528493769 103772969292330058896370327)
  ·
    refine ⟨155659453938495088344555491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103772969292330058896370327 155659453938495088344555491)
    ·
      refine ⟨233489180907742632516833237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155659453938495088344555491 233489180907742632516833237)
      ·
        refine ⟨5472402677525217949613279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 233489180907742632516833237 5472402677525217949613279)
        ·
          refine ⟨8208604016287826924419919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5472402677525217949613279 8208604016287826924419919)
          ·
            refine ⟨12312906024431740386629879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8208604016287826924419919 12312906024431740386629879)
            ·
              refine ⟨18469359036647610579944819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12312906024431740386629879 18469359036647610579944819)
              ·
                refine ⟨27704038554971415869917229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18469359036647610579944819 27704038554971415869917229)
                ·
                  refine ⟨10389014458114280951218961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27704038554971415869917229 10389014458114280951218961)
                  ·
                    refine ⟨7791760843585710713414221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10389014458114280951218961 7791760843585710713414221)
                    ·
                      refine ⟨2921910316344641517530333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7791760843585710713414221 2921910316344641517530333)
                      ·
                        rfl

theorem cell23_5690400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_5690400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690400 prefixEnd_5690400 := by exact prefixLift 5690400
  have htrace : WordTrace (prefixWord ++ tailWord_5690400) baseStart_5690400 baseEnd_5690400 := by
    simpa [prefixWord, tailWord_5690400, baseEnd_5690400] using wordTrace_append hprefix tailTrace_5690400
  have hstable : (prefixWord ++ tailWord_5690400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690400).length < 2 ^ (prefixWord ++ tailWord_5690400).sum := by decide
  have hdescent : baseEnd_5690400 < baseStart_5690400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690446 : List Nat := [4, 1, 1, 1, 1, 3, 3, 1, 2, 6]
def baseStart_5690446 : Nat := 118140960795 + 5690446 * 2 ^ 59
def prefixEnd_5690446 : Nat := 4983230072969 + 3 ^ 40 * 5690446 * 2
def baseEnd_5690446 : Nat := 973977978818249445851707

theorem tailTrace_5690446 : CollatzResearch.WordTrace tailWord_5690446 prefixEnd_5690446 973977978818249445851707 := by
  unfold tailWord_5690446
  simp only [CollatzResearch.WordTrace]
  refine ⟨25943452042811683456114399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138365077561662311765943461 25943452042811683456114399)
  ·
    refine ⟨38915178064217525184171599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25943452042811683456114399 38915178064217525184171599)
    ·
      refine ⟨58372767096326287776257399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38915178064217525184171599 58372767096326287776257399)
      ·
        refine ⟨87559150644489431664386099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58372767096326287776257399 87559150644489431664386099)
        ·
          refine ⟨131338725966734147496579149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87559150644489431664386099 131338725966734147496579149)
          ·
            refine ⟨49252022237525305311217181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131338725966734147496579149 49252022237525305311217181)
            ·
              refine ⟨18469508339071989491706443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49252022237525305311217181 18469508339071989491706443)
              ·
                refine ⟨27704262508607984237559665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18469508339071989491706443 27704262508607984237559665)
                ·
                  refine ⟨20778196881455988178169749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27704262508607984237559665 20778196881455988178169749)
                  ·
                    refine ⟨973977978818249445851707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20778196881455988178169749 973977978818249445851707)
                    ·
                      rfl

theorem cell23_5690446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_5690446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690446 prefixEnd_5690446 := by exact prefixLift 5690446
  have htrace : WordTrace (prefixWord ++ tailWord_5690446) baseStart_5690446 baseEnd_5690446 := by
    simpa [prefixWord, tailWord_5690446, baseEnd_5690446] using wordTrace_append hprefix tailTrace_5690446
  have hstable : (prefixWord ++ tailWord_5690446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690446).length < 2 ^ (prefixWord ++ tailWord_5690446).sum := by decide
  have hdescent : baseEnd_5690446 < baseStart_5690446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690456 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 2, 4, 3]
def baseStart_5690456 : Nat := 118140960795 + 5690456 * 2 ^ 59
def prefixEnd_5690456 : Nat := 4983230072969 + 3 ^ 40 * 5690456 * 2
def baseEnd_5690456 : Nat := 2921939071261293298430075

theorem tailTrace_5690456 : CollatzResearch.WordTrace tailWord_5690456 prefixEnd_5690456 2921939071261293298430075 := by
  unfold tailWord_5690456
  simp only [CollatzResearch.WordTrace]
  refine ⟨103773990536228619678389611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138365320714971492904519481 103773990536228619678389611)
  ·
    refine ⟨155660985804342929517584417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103773990536228619678389611 155660985804342929517584417)
    ·
      refine ⟨116745739353257197138188313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155660985804342929517584417 116745739353257197138188313)
      ·
        refine ⟨87559304514942897853641235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116745739353257197138188313 87559304514942897853641235)
        ·
          refine ⟨131338956772414346780461853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87559304514942897853641235 131338956772414346780461853)
          ·
            refine ⟨49252108789655380042673195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131338956772414346780461853 49252108789655380042673195)
            ·
              refine ⟨73878163184483070064009793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49252108789655380042673195 73878163184483070064009793)
              ·
                refine ⟨55408622388362302548007345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73878163184483070064009793 55408622388362302548007345)
                ·
                  refine ⟨41556466791271726911005509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55408622388362302548007345 41556466791271726911005509)
                  ·
                    refine ⟨7791837523363448795813533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41556466791271726911005509 7791837523363448795813533)
                    ·
                      refine ⟨2921939071261293298430075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7791837523363448795813533 2921939071261293298430075)
                      ·
                        rfl

theorem cell23_5690456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_5690456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690456 prefixEnd_5690456 := by exact prefixLift 5690456
  have htrace : WordTrace (prefixWord ++ tailWord_5690456) baseStart_5690456 baseEnd_5690456 := by
    simpa [prefixWord, tailWord_5690456, baseEnd_5690456] using wordTrace_append hprefix tailTrace_5690456
  have hstable : (prefixWord ++ tailWord_5690456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690456).length < 2 ^ (prefixWord ++ tailWord_5690456).sum := by decide
  have hdescent : baseEnd_5690456 < baseStart_5690456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690474 : List Nat := [3, 1, 3, 2, 2, 3, 2, 1, 1, 3, 2]
def baseStart_5690474 : Nat := 118140960795 + 5690474 * 2 ^ 59
def prefixEnd_5690474 : Nat := 4983230072969 + 3 ^ 40 * 5690474 * 2
def baseEnd_5690474 : Nat := 2921948313913074228004993

theorem tailTrace_5690474 : CollatzResearch.WordTrace tailWord_5690474 prefixEnd_5690474 2921948313913074228004993 := by
  unfold tailWord_5690474
  simp only [CollatzResearch.WordTrace]
  refine ⟨51887159396598007107733619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138365758390928018953956317 51887159396598007107733619)
  ·
    refine ⟨77830739094897010661600429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51887159396598007107733619 77830739094897010661600429)
    ·
      refine ⟨29186527160586378998100161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77830739094897010661600429 29186527160586378998100161)
      ·
        refine ⟨21889895370439784248575121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29186527160586378998100161 21889895370439784248575121)
        ·
          refine ⟨16417421527829838186431341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21889895370439784248575121 16417421527829838186431341)
          ·
            refine ⟨6156533072936189319911753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16417421527829838186431341 6156533072936189319911753)
            ·
              refine ⟨4617399804702141989933815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6156533072936189319911753 4617399804702141989933815)
              ·
                refine ⟨6926099707053212984900723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4617399804702141989933815 6926099707053212984900723)
                ·
                  refine ⟨10389149560579819477351085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6926099707053212984900723 10389149560579819477351085)
                  ·
                    refine ⟨3895931085217432304006657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10389149560579819477351085 3895931085217432304006657)
                    ·
                      refine ⟨2921948313913074228004993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3895931085217432304006657 2921948313913074228004993)
                      ·
                        rfl

theorem cell23_5690474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_5690474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690474 prefixEnd_5690474 := by exact prefixLift 5690474
  have htrace : WordTrace (prefixWord ++ tailWord_5690474) baseStart_5690474 baseEnd_5690474 := by
    simpa [prefixWord, tailWord_5690474, baseEnd_5690474] using wordTrace_append hprefix tailTrace_5690474
  have hstable : (prefixWord ++ tailWord_5690474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690474).length < 2 ^ (prefixWord ++ tailWord_5690474).sum := by decide
  have hdescent : baseEnd_5690474 < baseStart_5690474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690493 : List Nat := [1, 4, 1, 1, 3, 1, 1, 6, 5]
def baseStart_5690493 : Nat := 118140960795 + 5690493 * 2 ^ 59
def prefixEnd_5690493 : Nat := 4983230072969 + 3 ^ 40 * 5690493 * 2
def baseEnd_5690493 : Nat := 324662007782834405963045

theorem tailTrace_5690493 : CollatzResearch.WordTrace tailWord_5690493 prefixEnd_5690493 324662007782834405963045 := by
  unfold tailWord_5690493
  simp only [CollatzResearch.WordTrace]
  refine ⟨207549330573323194675876133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138366220382215463117250755 207549330573323194675876133)
  ·
    refine ⟨38915499482498099001726775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207549330573323194675876133 38915499482498099001726775)
    ·
      refine ⟨58373249223747148502590163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38915499482498099001726775 58373249223747148502590163)
      ·
        refine ⟨87559873835620722753885245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58373249223747148502590163 87559873835620722753885245)
        ·
          refine ⟨32834952688357771032706967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87559873835620722753885245 32834952688357771032706967)
          ·
            refine ⟨49252429032536656549060451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32834952688357771032706967 49252429032536656549060451)
            ·
              refine ⟨73878643548804984823590677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49252429032536656549060451 73878643548804984823590677)
              ·
                refine ⟨3463061416350233663605813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73878643548804984823590677 3463061416350233663605813)
                ·
                  refine ⟨324662007782834405963045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3463061416350233663605813 324662007782834405963045)
                  ·
                    rfl

theorem cell23_5690493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6, 5].length) (baseStart_5690493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690493 prefixEnd_5690493 := by exact prefixLift 5690493
  have htrace : WordTrace (prefixWord ++ tailWord_5690493) baseStart_5690493 baseEnd_5690493 := by
    simpa [prefixWord, tailWord_5690493, baseEnd_5690493] using wordTrace_append hprefix tailTrace_5690493
  have hstable : (prefixWord ++ tailWord_5690493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690493).length < 2 ^ (prefixWord ++ tailWord_5690493).sum := by decide
  have hdescent : baseEnd_5690493 < baseStart_5690493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690504 : List Nat := [2, 1, 3, 4, 3, 1, 1, 1, 1, 4, 2]
def baseStart_5690504 : Nat := 118140960795 + 5690504 * 2 ^ 59
def prefixEnd_5690504 : Nat := 4983230072969 + 3 ^ 40 * 5690504 * 2
def baseEnd_5690504 : Nat := 2921963718332709110629855

theorem tailTrace_5690504 : CollatzResearch.WordTrace tailWord_5690504 prefixEnd_5690504 2921963718332709110629855 := by
  unfold tailWord_5690504
  simp only [CollatzResearch.WordTrace]
  refine ⟨103774865888141671777263283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138366487850855562369684377 103774865888141671777263283)
  ·
    refine ⟨155662298832212507665894925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103774865888141671777263283 155662298832212507665894925)
    ·
      refine ⟨58373362062079690374710597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155662298832212507665894925 58373362062079690374710597)
      ·
        refine ⟨10945005386639941945258237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58373362062079690374710597 10945005386639941945258237)
        ·
          refine ⟨4104377019989978229471839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10945005386639941945258237 4104377019989978229471839)
          ·
            refine ⟨6156565529984967344207759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4104377019989978229471839 6156565529984967344207759)
            ·
              refine ⟨9234848294977451016311639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6156565529984967344207759 9234848294977451016311639)
              ·
                refine ⟨13852272442466176524467459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9234848294977451016311639 13852272442466176524467459)
                ·
                  refine ⟨20778408663699264786701189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13852272442466176524467459 20778408663699264786701189)
                  ·
                    refine ⟨3895951624443612147506473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20778408663699264786701189 3895951624443612147506473)
                    ·
                      refine ⟨2921963718332709110629855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3895951624443612147506473 2921963718332709110629855)
                      ·
                        rfl

theorem cell23_5690504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_5690504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690504 prefixEnd_5690504 := by exact prefixLift 5690504
  have htrace : WordTrace (prefixWord ++ tailWord_5690504) baseStart_5690504 baseEnd_5690504 := by
    simpa [prefixWord, tailWord_5690504, baseEnd_5690504] using wordTrace_append hprefix tailTrace_5690504
  have hstable : (prefixWord ++ tailWord_5690504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690504).length < 2 ^ (prefixWord ++ tailWord_5690504).sum := by decide
  have hdescent : baseEnd_5690504 < baseStart_5690504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690506 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 3, 7]
def baseStart_5690506 : Nat := 118140960795 + 5690506 * 2 ^ 59
def prefixEnd_5690506 : Nat := 4983230072969 + 3 ^ 40 * 5690506 * 2
def baseEnd_5690506 : Nat := 973988248431339367601615

theorem tailTrace_5690506 : CollatzResearch.WordTrace tailWord_5690506 prefixEnd_5690506 973988248431339367601615 := by
  unfold tailWord_5690506
  simp only [CollatzResearch.WordTrace]
  refine ⟨51887451180569024474024843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138366536481517398597399581 51887451180569024474024843)
  ·
    refine ⟨77831176770853536711037265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51887451180569024474024843 77831176770853536711037265)
    ·
      refine ⟨58373382578140152533277949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77831176770853536711037265 58373382578140152533277949)
      ·
        refine ⟨21890018466802557199979231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58373382578140152533277949 21890018466802557199979231)
        ·
          refine ⟨32835027700203835799968847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21890018466802557199979231 32835027700203835799968847)
          ·
            refine ⟨49252541550305753699953271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32835027700203835799968847 49252541550305753699953271)
            ·
              refine ⟨73878812325458630549929907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49252541550305753699953271 73878812325458630549929907)
              ·
                refine ⟨110818218488187945824894861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73878812325458630549929907 110818218488187945824894861)
                ·
                  refine ⟨41556831933070479684335573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110818218488187945824894861 41556831933070479684335573)
                  ·
                    refine ⟨973988248431339367601615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41556831933070479684335573 973988248431339367601615)
                    ·
                      rfl

theorem cell23_5690506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_5690506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690506 prefixEnd_5690506 := by exact prefixLift 5690506
  have htrace : WordTrace (prefixWord ++ tailWord_5690506) baseStart_5690506 baseEnd_5690506 := by
    simpa [prefixWord, tailWord_5690506, baseEnd_5690506] using wordTrace_append hprefix tailTrace_5690506
  have hstable : (prefixWord ++ tailWord_5690506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690506).length < 2 ^ (prefixWord ++ tailWord_5690506).sum := by decide
  have hdescent : baseEnd_5690506 < baseStart_5690506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690527 : List Nat := [1, 1, 2, 6, 2, 2, 1, 3, 5]
def baseStart_5690527 : Nat := 118140960795 + 5690527 * 2 ^ 59
def prefixEnd_5690527 : Nat := 4983230072969 + 3 ^ 40 * 5690527 * 2
def baseEnd_5690527 : Nat := 324663947598640280071361

theorem tailTrace_5690527 : CollatzResearch.WordTrace tailWord_5690527 prefixEnd_5690527 324663947598640280071361 := by
  unfold tailWord_5690527
  simp only [CollatzResearch.WordTrace]
  refine ⟨207550570655200018482613835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138367047103466678988409223 207550570655200018482613835)
  ·
    refine ⟨311325855982800027723920753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207550570655200018482613835 311325855982800027723920753)
    ·
      refine ⟨233494391987100020792940565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311325855982800027723920753 233494391987100020792940565)
      ·
        refine ⟨10945049624395313474669089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 233494391987100020792940565 10945049624395313474669089)
        ·
          refine ⟨8208787218296485106001817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10945049624395313474669089 8208787218296485106001817)
          ·
            refine ⟨6156590413722363829501363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8208787218296485106001817 6156590413722363829501363)
            ·
              refine ⟨9234885620583545744252045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6156590413722363829501363 9234885620583545744252045)
              ·
                refine ⟨3463082107718829654094517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9234885620583545744252045 3463082107718829654094517)
                ·
                  refine ⟨324663947598640280071361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3463082107718829654094517 324663947598640280071361)
                  ·
                    rfl

theorem cell23_5690527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3, 5].length) (baseStart_5690527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690527 prefixEnd_5690527 := by exact prefixLift 5690527
  have htrace : WordTrace (prefixWord ++ tailWord_5690527) baseStart_5690527 baseEnd_5690527 := by
    simpa [prefixWord, tailWord_5690527, baseEnd_5690527] using wordTrace_append hprefix tailTrace_5690527
  have hstable : (prefixWord ++ tailWord_5690527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690527).length < 2 ^ (prefixWord ++ tailWord_5690527).sum := by decide
  have hdescent : baseEnd_5690527 < baseStart_5690527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690543 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 4, 4, 2]
def baseStart_5690543 : Nat := 118140960795 + 5690543 * 2 ^ 59
def prefixEnd_5690543 : Nat := 4983230072969 + 3 ^ 40 * 5690543 * 2
def baseEnd_5690543 : Nat := 2921983744078234458042175

theorem tailTrace_5690543 : CollatzResearch.WordTrace tailWord_5690543 prefixEnd_5690543 2921983744078234458042175 := by
  unfold tailWord_5690543
  simp only [CollatzResearch.WordTrace]
  refine ⟨207551154223142053215196283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138367436148761368810130855 207551154223142053215196283)
  ·
    refine ⟨311326731334713079822794425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207551154223142053215196283 311326731334713079822794425)
    ·
      refine ⟨233495048501034809867095819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311326731334713079822794425 233495048501034809867095819)
      ·
        refine ⟨350242572751552214800643729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233495048501034809867095819 350242572751552214800643729)
        ·
          refine ⟨262681929563664161100482797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350242572751552214800643729 262681929563664161100482797)
          ·
            refine ⟨98505723586374060412681049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 262681929563664161100482797 98505723586374060412681049)
            ·
              refine ⟨73879292689780545309510787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98505723586374060412681049 73879292689780545309510787)
              ·
                refine ⟨110818939034670817964266181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73879292689780545309510787 110818939034670817964266181)
                ·
                  refine ⟨20778551069000778368299909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110818939034670817964266181 20778551069000778368299909)
                  ·
                    refine ⟨3895978325437645944056233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20778551069000778368299909 3895978325437645944056233)
                    ·
                      refine ⟨2921983744078234458042175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3895978325437645944056233 2921983744078234458042175)
                      ·
                        rfl

theorem cell23_5690543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 4, 2].length) (baseStart_5690543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690543 prefixEnd_5690543 := by exact prefixLift 5690543
  have htrace : WordTrace (prefixWord ++ tailWord_5690543) baseStart_5690543 baseEnd_5690543 := by
    simpa [prefixWord, tailWord_5690543, baseEnd_5690543] using wordTrace_append hprefix tailTrace_5690543
  have hstable : (prefixWord ++ tailWord_5690543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690543).length < 2 ^ (prefixWord ++ tailWord_5690543).sum := by decide
  have hdescent : baseEnd_5690543 < baseStart_5690543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690586 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8]
def baseStart_5690586 : Nat := 118140960795 + 5690586 * 2 ^ 59
def prefixEnd_5690586 : Nat := 4983230072969 + 3 ^ 40 * 5690586 * 2
def baseEnd_5690586 : Nat := 2922005823746377789804477

theorem tailTrace_5690586 : CollatzResearch.WordTrace tailWord_5690586 prefixEnd_5690586 2922005823746377789804477 := by
  unfold tailWord_5690586
  simp only [CollatzResearch.WordTrace]
  refine ⟨51888180640496567889752903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138368481707990847706007741 51888180640496567889752903)
  ·
    refine ⟨77832270960744851834629355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51888180640496567889752903 77832270960744851834629355)
    ·
      refine ⟨116748406441117277751944033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77832270960744851834629355 116748406441117277751944033)
      ·
        refine ⟨87561304830837958313958025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116748406441117277751944033 87561304830837958313958025)
        ·
          refine ⟨65670978623128468735468519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87561304830837958313958025 65670978623128468735468519)
          ·
            refine ⟨98506467934692703103202779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65670978623128468735468519 98506467934692703103202779)
            ·
              refine ⟨147759701902039054654804169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98506467934692703103202779 147759701902039054654804169)
              ·
                refine ⟨110819776426529290991103127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147759701902039054654804169 110819776426529290991103127)
                ·
                  refine ⟨166229664639793936486654691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110819776426529290991103127 166229664639793936486654691)
                  ·
                    refine ⟨249344496959690904729982037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 166229664639793936486654691 249344496959690904729982037)
                    ·
                      refine ⟨2922005823746377789804477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 249344496959690904729982037 2922005823746377789804477)
                      ·
                        rfl

theorem cell23_5690586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_5690586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690586 prefixEnd_5690586 := by exact prefixLift 5690586
  have htrace : WordTrace (prefixWord ++ tailWord_5690586) baseStart_5690586 baseEnd_5690586 := by
    simpa [prefixWord, tailWord_5690586, baseEnd_5690586] using wordTrace_append hprefix tailTrace_5690586
  have hstable : (prefixWord ++ tailWord_5690586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690586).length < 2 ^ (prefixWord ++ tailWord_5690586).sum := by decide
  have hdescent : baseEnd_5690586 < baseStart_5690586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690604 : List Nat := [2, 2, 1, 1, 2, 6, 2, 2, 1, 4]
def baseStart_5690604 : Nat := 118140960795 + 5690604 * 2 ^ 59
def prefixEnd_5690604 : Nat := 4983230072969 + 3 ^ 40 * 5690604 * 2
def baseEnd_5690604 : Nat := 974005022132719573126465

theorem tailTrace_5690604 : CollatzResearch.WordTrace tailWord_5690604 prefixEnd_5690604 974005022132719573126465 := by
  unfold tailWord_5690604
  simp only [CollatzResearch.WordTrace]
  refine ⟨103776689537960530316583433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138368919383947373755444577 103776689537960530316583433)
  ·
    refine ⟨77832517153470397737437575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103776689537960530316583433 77832517153470397737437575)
    ·
      refine ⟨116748775730205596606156363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77832517153470397737437575 116748775730205596606156363)
      ·
        refine ⟨175123163595308394909234545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116748775730205596606156363 175123163595308394909234545)
        ·
          refine ⟨131342372696481296181925909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175123163595308394909234545 131342372696481296181925909)
          ·
            refine ⟨6156673720147560758527777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 131342372696481296181925909 6156673720147560758527777)
            ·
              refine ⟨4617505290110670568895833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6156673720147560758527777 4617505290110670568895833)
              ·
                refine ⟨3463128967583002926671875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4617505290110670568895833 3463128967583002926671875)
                ·
                  refine ⟨5194693451374504390007813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3463128967583002926671875 5194693451374504390007813)
                  ·
                    refine ⟨974005022132719573126465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5194693451374504390007813 974005022132719573126465)
                    ·
                      rfl

theorem cell23_5690604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2, 1, 4].length) (baseStart_5690604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690604 prefixEnd_5690604 := by exact prefixLift 5690604
  have htrace : WordTrace (prefixWord ++ tailWord_5690604) baseStart_5690604 baseEnd_5690604 := by
    simpa [prefixWord, tailWord_5690604, baseEnd_5690604] using wordTrace_append hprefix tailTrace_5690604
  have hstable : (prefixWord ++ tailWord_5690604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690604).length < 2 ^ (prefixWord ++ tailWord_5690604).sum := by decide
  have hdescent : baseEnd_5690604 < baseStart_5690604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690633 : List Nat := [1, 2, 1, 1, 3, 3, 1, 3, 3, 1, 4]
def baseStart_5690633 : Nat := 118140960795 + 5690633 * 2 ^ 59
def prefixEnd_5690633 : Nat := 4983230072969 + 3 ^ 40 * 5690633 * 2
def baseEnd_5690633 : Nat := 2922029957337139105916761

theorem tailTrace_5690633 : CollatzResearch.WordTrace tailWord_5690633 prefixEnd_5690633 2922029957337139105916761 := by
  unfold tailWord_5690633
  simp only [CollatzResearch.WordTrace]
  refine ⟨207554436792815998585972553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138369624528543999057315035 207554436792815998585972553)
  ·
    refine ⟨155665827594611998939479415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207554436792815998585972553 155665827594611998939479415)
    ·
      refine ⟨233498741391917998409219123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155665827594611998939479415 233498741391917998409219123)
      ·
        refine ⟨350248112087876997613828685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233498741391917998409219123 350248112087876997613828685)
        ·
          refine ⟨131343042032953874105185757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 350248112087876997613828685 131343042032953874105185757)
          ·
            refine ⟨49253640762357702789444659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131343042032953874105185757 49253640762357702789444659)
            ·
              refine ⟨73880461143536554184166989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49253640762357702789444659 73880461143536554184166989)
              ·
                refine ⟨27705172928826207819062621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73880461143536554184166989 27705172928826207819062621)
                ·
                  refine ⟨10389439848309827932148483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27705172928826207819062621 10389439848309827932148483)
                  ·
                    refine ⟨15584159772464741898222725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10389439848309827932148483 15584159772464741898222725)
                    ·
                      refine ⟨2922029957337139105916761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15584159772464741898222725 2922029957337139105916761)
                      ·
                        rfl

theorem cell23_5690633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 1, 4].length) (baseStart_5690633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690633 prefixEnd_5690633 := by exact prefixLift 5690633
  have htrace : WordTrace (prefixWord ++ tailWord_5690633) baseStart_5690633 baseEnd_5690633 := by
    simpa [prefixWord, tailWord_5690633, baseEnd_5690633] using wordTrace_append hprefix tailTrace_5690633
  have hstable : (prefixWord ++ tailWord_5690633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690633).length < 2 ^ (prefixWord ++ tailWord_5690633).sum := by decide
  have hdescent : baseEnd_5690633 < baseStart_5690633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690660 : List Nat := [2, 3, 1, 3, 1, 1, 3, 1, 4, 4]
def baseStart_5690660 : Nat := 118140960795 + 5690660 * 2 ^ 59
def prefixEnd_5690660 : Nat := 4983230072969 + 3 ^ 40 * 5690660 * 2
def baseEnd_5690660 : Nat := 974014607104936833426379

theorem tailTrace_5690660 : CollatzResearch.WordTrace tailWord_5690660 prefixEnd_5690660 974014607104936833426379 := by
  unfold tailWord_5690660
  simp only [CollatzResearch.WordTrace]
  refine ⟨103777710781859091098602717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138370281042478788131470289 103777710781859091098602717)
  ·
    refine ⟨38916641543197159161976019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103777710781859091098602717 38916641543197159161976019)
    ·
      refine ⟨58374962314795738742964029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38916641543197159161976019 58374962314795738742964029)
      ·
        refine ⟨21890610868048402028611511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58374962314795738742964029 21890610868048402028611511)
        ·
          refine ⟨32835916302072603042917267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21890610868048402028611511 32835916302072603042917267)
          ·
            refine ⟨49253874453108904564375901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32835916302072603042917267 49253874453108904564375901)
            ·
              refine ⟨18470202919915839211640963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49253874453108904564375901 18470202919915839211640963)
              ·
                refine ⟨27705304379873758817461445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18470202919915839211640963 27705304379873758817461445)
                ·
                  refine ⟨5194744571226329778274021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27705304379873758817461445 5194744571226329778274021)
                  ·
                    refine ⟨974014607104936833426379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5194744571226329778274021 974014607104936833426379)
                    ·
                      rfl

theorem cell23_5690660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_5690660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690660 prefixEnd_5690660 := by exact prefixLift 5690660
  have htrace : WordTrace (prefixWord ++ tailWord_5690660) baseStart_5690660 baseEnd_5690660 := by
    simpa [prefixWord, tailWord_5690660, baseEnd_5690660] using wordTrace_append hprefix tailTrace_5690660
  have hstable : (prefixWord ++ tailWord_5690660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690660).length < 2 ^ (prefixWord ++ tailWord_5690660).sum := by decide
  have hdescent : baseEnd_5690660 < baseStart_5690660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690687 : List Nat := [1, 1, 2, 2, 4, 3, 2, 2, 1, 2, 3]
def baseStart_5690687 : Nat := 118140960795 + 5690687 * 2 ^ 59
def prefixEnd_5690687 : Nat := 4983230072969 + 3 ^ 40 * 5690687 * 2
def baseEnd_5690687 : Nat := 2922057685292481894641513

theorem tailTrace_5690687 : CollatzResearch.WordTrace tailWord_5690687 prefixEnd_5690687 2922057685292481894641513 := by
  unfold tailWord_5690687
  simp only [CollatzResearch.WordTrace]
  refine ⟨207556406334620365808438315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138370937556413577205625543 207556406334620365808438315)
  ·
    refine ⟨311334609501930548712657473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207556406334620365808438315 311334609501930548712657473)
    ·
      refine ⟨233500957126447911534493105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311334609501930548712657473 233500957126447911534493105)
      ·
        refine ⟨175125717844835933650869829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233500957126447911534493105 175125717844835933650869829)
        ·
          refine ⟨32836072095906737559538093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175125717844835933650869829 32836072095906737559538093)
          ·
            refine ⟨12313527035965026584826785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32836072095906737559538093 12313527035965026584826785)
            ·
              refine ⟨9235145276973769938620089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12313527035965026584826785 9235145276973769938620089)
              ·
                refine ⟨6926358957730327453965067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9235145276973769938620089 6926358957730327453965067)
                ·
                  refine ⟨10389538436595491180947601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6926358957730327453965067 10389538436595491180947601)
                  ·
                    refine ⟨7792153827446618385710701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10389538436595491180947601 7792153827446618385710701)
                    ·
                      refine ⟨2922057685292481894641513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7792153827446618385710701 2922057685292481894641513)
                      ·
                        rfl

theorem cell23_5690687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 2, 3].length) (baseStart_5690687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690687 prefixEnd_5690687 := by exact prefixLift 5690687
  have htrace : WordTrace (prefixWord ++ tailWord_5690687) baseStart_5690687 baseEnd_5690687 := by
    simpa [prefixWord, tailWord_5690687, baseEnd_5690687] using wordTrace_append hprefix tailTrace_5690687
  have hstable : (prefixWord ++ tailWord_5690687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690687).length < 2 ^ (prefixWord ++ tailWord_5690687).sum := by decide
  have hdescent : baseEnd_5690687 < baseStart_5690687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690743 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 5]
def baseStart_5690743 : Nat := 118140960795 + 5690743 * 2 ^ 59
def prefixEnd_5690743 : Nat := 4983230072969 + 3 ^ 40 * 5690743 * 2
def baseEnd_5690743 : Nat := 2922086440209133675541255

theorem tailTrace_5690743 : CollatzResearch.WordTrace tailWord_5690743 prefixEnd_5690743 2922086440209133675541255 := by
  unfold tailWord_5690743
  simp only [CollatzResearch.WordTrace]
  refine ⟨207558448822417487372476883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138372299214944991581651255 207558448822417487372476883)
  ·
    refine ⟨311337673233626231058715325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207558448822417487372476883 311337673233626231058715325)
    ·
      refine ⟨116751627462609836647018247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 311337673233626231058715325 116751627462609836647018247)
      ·
        refine ⟨175127441193914754970527371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116751627462609836647018247 175127441193914754970527371)
        ·
          refine ⟨262691161790872132455791057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175127441193914754970527371 262691161790872132455791057)
          ·
            refine ⟨197018371343154099341843293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262691161790872132455791057 197018371343154099341843293)
            ·
              refine ⟨73881889253682787253191235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197018371343154099341843293 73881889253682787253191235)
              ·
                refine ⟨110822833880524180879786853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73881889253682787253191235 110822833880524180879786853)
                ·
                  refine ⟨20779281352598283914960035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110822833880524180879786853 20779281352598283914960035)
                  ·
                    refine ⟨31168922028897425872440053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20779281352598283914960035 31168922028897425872440053)
                    ·
                      refine ⟨2922086440209133675541255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31168922028897425872440053 2922086440209133675541255)
                      ·
                        rfl

theorem cell23_5690743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_5690743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690743 prefixEnd_5690743 := by exact prefixLift 5690743
  have htrace : WordTrace (prefixWord ++ tailWord_5690743) baseStart_5690743 baseEnd_5690743 := by
    simpa [prefixWord, tailWord_5690743, baseEnd_5690743] using wordTrace_append hprefix tailTrace_5690743
  have hstable : (prefixWord ++ tailWord_5690743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690743).length < 2 ^ (prefixWord ++ tailWord_5690743).sum := by decide
  have hdescent : baseEnd_5690743 < baseStart_5690743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690757 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 6, 2, 2]
def baseStart_5690757 : Nat := 118140960795 + 5690757 * 2 ^ 59
def prefixEnd_5690757 : Nat := 4983230072969 + 3 ^ 40 * 5690757 * 2
def baseEnd_5690757 : Nat := 2922093628938296620766191

theorem tailTrace_5690757 : CollatzResearch.WordTrace tailWord_5690757 prefixEnd_5690757 2922093628938296620766191 := by
  unfold tailWord_5690757
  simp only [CollatzResearch.WordTrace]
  refine ⟨207558959444366767763486525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138372639629577845175657683 207558959444366767763486525)
  ·
    refine ⟨77834609791637537911307447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207558959444366767763486525 77834609791637537911307447)
    ·
      refine ⟨116751914687456306866961171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77834609791637537911307447 116751914687456306866961171)
      ·
        refine ⟨175127872031184460300441757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116751914687456306866961171 175127872031184460300441757)
        ·
          refine ⟨65672952011694172612665659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175127872031184460300441757 65672952011694172612665659)
          ·
            refine ⟨98509428017541258918998489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65672952011694172612665659 98509428017541258918998489)
            ·
              refine ⟨73882071013155944189248867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98509428017541258918998489 73882071013155944189248867)
              ·
                refine ⟨110823106519733916283873301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73882071013155944189248867 110823106519733916283873301)
                ·
                  refine ⟨5194833118112527325806561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110823106519733916283873301 5194833118112527325806561)
                  ·
                    refine ⟨3896124838584395494354921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5194833118112527325806561 3896124838584395494354921)
                    ·
                      refine ⟨2922093628938296620766191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3896124838584395494354921 2922093628938296620766191)
                      ·
                        rfl

theorem cell23_5690757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6, 2, 2].length) (baseStart_5690757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690757 prefixEnd_5690757 := by exact prefixLift 5690757
  have htrace : WordTrace (prefixWord ++ tailWord_5690757) baseStart_5690757 baseEnd_5690757 := by
    simpa [prefixWord, tailWord_5690757, baseEnd_5690757] using wordTrace_append hprefix tailTrace_5690757
  have hstable : (prefixWord ++ tailWord_5690757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690757).length < 2 ^ (prefixWord ++ tailWord_5690757).sum := by decide
  have hdescent : baseEnd_5690757 < baseStart_5690757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690760 : List Nat := [2, 1, 3, 3, 1, 2, 2, 1, 2, 1, 5]
def baseStart_5690760 : Nat := 118140960795 + 5690760 * 2 ^ 59
def prefixEnd_5690760 : Nat := 4983230072969 + 3 ^ 40 * 5690760 * 2
def baseEnd_5690760 : Nat := 2922095169380260109028677

theorem tailTrace_5690760 : CollatzResearch.WordTrace tailWord_5690760 prefixEnd_5690760 2922095169380260109028677 := by
  unfold tailWord_5690760
  simp only [CollatzResearch.WordTrace]
  refine ⟨103779534431677949637922867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138372712575570599517230489 103779534431677949637922867)
  ·
    refine ⟨155669301647516924456884301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103779534431677949637922867 155669301647516924456884301)
    ·
      refine ⟨58375988117818846671331613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155669301647516924456884301 58375988117818846671331613)
      ·
        refine ⟨21890995544182067501749355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58375988117818846671331613 21890995544182067501749355)
        ·
          refine ⟨32836493316273101252624033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21890995544182067501749355 32836493316273101252624033)
          ·
            refine ⟨24627369987204825939468025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32836493316273101252624033 24627369987204825939468025)
            ·
              refine ⟨18470527490403619454601019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24627369987204825939468025 18470527490403619454601019)
              ·
                refine ⟨27705791235605429181901529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18470527490403619454601019 27705791235605429181901529)
                ·
                  refine ⟨20779343426704071886426147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27705791235605429181901529 20779343426704071886426147)
                  ·
                    refine ⟨31169015140056107829639221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20779343426704071886426147 31169015140056107829639221)
                    ·
                      refine ⟨2922095169380260109028677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31169015140056107829639221 2922095169380260109028677)
                      ·
                        rfl

theorem cell23_5690760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_5690760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690760 prefixEnd_5690760 := by exact prefixLift 5690760
  have htrace : WordTrace (prefixWord ++ tailWord_5690760) baseStart_5690760 baseEnd_5690760 := by
    simpa [prefixWord, tailWord_5690760, baseEnd_5690760] using wordTrace_append hprefix tailTrace_5690760
  have hstable : (prefixWord ++ tailWord_5690760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690760).length < 2 ^ (prefixWord ++ tailWord_5690760).sum := by decide
  have hdescent : baseEnd_5690760 < baseStart_5690760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690761 : List Nat := [1, 2, 1, 1, 7, 1, 3, 1, 1, 3, 2]
def baseStart_5690761 : Nat := 118140960795 + 5690761 * 2 ^ 59
def prefixEnd_5690761 : Nat := 4983230072969 + 3 ^ 40 * 5690761 * 2
def baseEnd_5690761 : Nat := 2922095682860914605116173

theorem tailTrace_5690761 : CollatzResearch.WordTrace tailWord_5690761 prefixEnd_5690761 2922095682860914605116173 := by
  unfold tailWord_5690761
  simp only [CollatzResearch.WordTrace]
  refine ⟨207559105336352276446632137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138372736890901517631088091 207559105336352276446632137)
  ·
    refine ⟨155669329002264207334974103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207559105336352276446632137 155669329002264207334974103)
    ·
      refine ⟨233503993503396311002461155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155669329002264207334974103 233503993503396311002461155)
      ·
        refine ⟨350255990255094466503691733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233503993503396311002461155 350255990255094466503691733)
        ·
          refine ⟨8209124771603776558680275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 350255990255094466503691733 8209124771603776558680275)
          ·
            refine ⟨12313687157405664838020413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8209124771603776558680275 12313687157405664838020413)
            ·
              refine ⟨4617632684027124314257655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12313687157405664838020413 4617632684027124314257655)
              ·
                refine ⟨6926449026040686471386483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4617632684027124314257655 6926449026040686471386483)
                ·
                  refine ⟨10389673539061029707079725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6926449026040686471386483 10389673539061029707079725)
                  ·
                    refine ⟨3896127577147886140154897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10389673539061029707079725 3896127577147886140154897)
                    ·
                      refine ⟨2922095682860914605116173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3896127577147886140154897 2922095682860914605116173)
                      ·
                        rfl

theorem cell23_5690761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 1, 3, 2].length) (baseStart_5690761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690761 prefixEnd_5690761 := by exact prefixLift 5690761
  have htrace : WordTrace (prefixWord ++ tailWord_5690761) baseStart_5690761 baseEnd_5690761 := by
    simpa [prefixWord, tailWord_5690761, baseEnd_5690761] using wordTrace_append hprefix tailTrace_5690761
  have hstable : (prefixWord ++ tailWord_5690761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690761).length < 2 ^ (prefixWord ++ tailWord_5690761).sum := by decide
  have hdescent : baseEnd_5690761 < baseStart_5690761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690773 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 1, 2, 7]
def baseStart_5690773 : Nat := 118140960795 + 5690773 * 2 ^ 59
def prefixEnd_5690773 : Nat := 4983230072969 + 3 ^ 40 * 5690773 * 2
def baseEnd_5690773 : Nat := 2922101844628768558166117

theorem tailTrace_5690773 : CollatzResearch.WordTrace tailWord_5690773 prefixEnd_5690773 2922101844628768558166117 := by
  unfold tailWord_5690773
  simp only [CollatzResearch.WordTrace]
  refine ⟨207559543012308802496068973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138373028674872534997379315 207559543012308802496068973)
  ·
    refine ⟨77834828629615800936025865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207559543012308802496068973 77834828629615800936025865)
    ·
      refine ⟨58376121472211850702019399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77834828629615800936025865 58376121472211850702019399)
      ·
        refine ⟨87564182208317776053029099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58376121472211850702019399 87564182208317776053029099)
        ·
          refine ⟨131346273312476664079543649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87564182208317776053029099 131346273312476664079543649)
          ·
            refine ⟨98509704984357498059657737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131346273312476664079543649 98509704984357498059657737)
            ·
              refine ⟨73882278738268123544743303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98509704984357498059657737 73882278738268123544743303)
              ·
                refine ⟨110823418107402185317114955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73882278738268123544743303 110823418107402185317114955)
                ·
                  refine ⟨166235127161103277975672433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110823418107402185317114955 166235127161103277975672433)
                  ·
                    refine ⟨124676345370827458481754325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 166235127161103277975672433 124676345370827458481754325)
                    ·
                      refine ⟨2922101844628768558166117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124676345370827458481754325 2922101844628768558166117)
                      ·
                        rfl

theorem cell23_5690773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_5690773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690773 prefixEnd_5690773 := by exact prefixLift 5690773
  have htrace : WordTrace (prefixWord ++ tailWord_5690773) baseStart_5690773 baseEnd_5690773 := by
    simpa [prefixWord, tailWord_5690773, baseEnd_5690773] using wordTrace_append hprefix tailTrace_5690773
  have hstable : (prefixWord ++ tailWord_5690773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690773).length < 2 ^ (prefixWord ++ tailWord_5690773).sum := by decide
  have hdescent : baseEnd_5690773 < baseStart_5690773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690797 : List Nat := [1, 5, 2, 2, 1, 2, 1, 2, 7]
def baseStart_5690797 : Nat := 118140960795 + 5690797 * 2 ^ 59
def prefixEnd_5690797 : Nat := 4983230072969 + 3 ^ 40 * 5690797 * 2
def baseEnd_5690797 : Nat := 324679352018275162696223

theorem tailTrace_5690797 : CollatzResearch.WordTrace tailWord_5690797 prefixEnd_5690797 324679352018275162696223 := by
  unfold tailWord_5690797
  simp only [CollatzResearch.WordTrace]
  refine ⟨207560418364221854594942645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138373612242814569729961763 207560418364221854594942645)
  ·
    refine ⟨19458789221645798868275873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 207560418364221854594942645 19458789221645798868275873)
    ·
      refine ⟨14594091916234349151206905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19458789221645798868275873 14594091916234349151206905)
      ·
        refine ⟨10945568937175761863405179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14594091916234349151206905 10945568937175761863405179)
        ·
          refine ⟨16418353405763642795107769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10945568937175761863405179 16418353405763642795107769)
          ·
            refine ⟨12313765054322732096330827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16418353405763642795107769 12313765054322732096330827)
            ·
              refine ⟨18470647581484098144496241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12313765054322732096330827 18470647581484098144496241)
              ·
                refine ⟨13852985686113073608372181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18470647581484098144496241 13852985686113073608372181)
                ·
                  refine ⟨324679352018275162696223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13852985686113073608372181 324679352018275162696223)
                  ·
                    rfl

theorem cell23_5690797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_5690797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690797 prefixEnd_5690797 := by exact prefixLift 5690797
  have htrace : WordTrace (prefixWord ++ tailWord_5690797) baseStart_5690797 baseEnd_5690797 := by
    simpa [prefixWord, tailWord_5690797, baseEnd_5690797] using wordTrace_append hprefix tailTrace_5690797
  have hstable : (prefixWord ++ tailWord_5690797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690797).length < 2 ^ (prefixWord ++ tailWord_5690797).sum := by decide
  have hdescent : baseEnd_5690797 < baseStart_5690797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690803 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 7]
def baseStart_5690803 : Nat := 118140960795 + 5690803 * 2 ^ 59
def prefixEnd_5690803 : Nat := 4983230072969 + 3 ^ 40 * 5690803 * 2
def baseEnd_5690803 : Nat := 2922117249048403440790979

theorem tailTrace_5690803 : CollatzResearch.WordTrace tailWord_5690803 prefixEnd_5690803 2922117249048403440790979 := by
  unfold tailWord_5690803
  simp only [CollatzResearch.WordTrace]
  refine ⟨207560637202200117619661063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138373758134800078413107375 207560637202200117619661063)
  ·
    refine ⟨311340955803300176429491595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207560637202200117619661063 311340955803300176429491595)
    ·
      refine ⟨467011433704950264644237393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311340955803300176429491595 467011433704950264644237393)
      ·
        refine ⟨350258575278712698483178045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 467011433704950264644237393 350258575278712698483178045)
        ·
          refine ⟨131346965729517261931191767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 350258575278712698483178045 131346965729517261931191767)
          ·
            refine ⟨197020448594275892896787651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131346965729517261931191767 197020448594275892896787651)
            ·
              refine ⟨295530672891413839345181477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197020448594275892896787651 295530672891413839345181477)
              ·
                refine ⟨55412001167140094877221527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 295530672891413839345181477 55412001167140094877221527)
                ·
                  refine ⟨83118001750710142315832291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55412001167140094877221527 83118001750710142315832291)
                  ·
                    refine ⟨124677002626065213473748437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 83118001750710142315832291 124677002626065213473748437)
                    ·
                      refine ⟨2922117249048403440790979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124677002626065213473748437 2922117249048403440790979)
                      ·
                        rfl

theorem cell23_5690803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 7].length) (baseStart_5690803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690803 prefixEnd_5690803 := by exact prefixLift 5690803
  have htrace : WordTrace (prefixWord ++ tailWord_5690803) baseStart_5690803 baseEnd_5690803 := by
    simpa [prefixWord, tailWord_5690803, baseEnd_5690803] using wordTrace_append hprefix tailTrace_5690803
  have hstable : (prefixWord ++ tailWord_5690803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690803).length < 2 ^ (prefixWord ++ tailWord_5690803).sum := by decide
  have hdescent : baseEnd_5690803 < baseStart_5690803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690847 : List Nat := [1, 1, 2, 3, 3, 1, 1, 3, 2, 4, 2]
def baseStart_5690847 : Nat := 118140960795 + 5690847 * 2 ^ 59
def prefixEnd_5690847 : Nat := 4983230072969 + 3 ^ 40 * 5690847 * 2
def baseEnd_5690847 : Nat := 2922139842197201268640777

theorem tailTrace_5690847 : CollatzResearch.WordTrace tailWord_5690847 prefixEnd_5690847 2922139842197201268640777 := by
  unfold tailWord_5690847
  simp only [CollatzResearch.WordTrace]
  refine ⟨207562242014040713134262795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138374828009360475422841863 207562242014040713134262795)
  ·
    refine ⟨311343363021061069701394193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207562242014040713134262795 311343363021061069701394193)
    ·
      refine ⟨233507522265795802276045645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311343363021061069701394193 233507522265795802276045645)
      ·
        refine ⟨87565320849673425853517117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233507522265795802276045645 87565320849673425853517117)
        ·
          refine ⟨32836995318627534695068919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87565320849673425853517117 32836995318627534695068919)
          ·
            refine ⟨49255492977941302042603379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32836995318627534695068919 49255492977941302042603379)
            ·
              refine ⟨73883239466911953063905069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49255492977941302042603379 73883239466911953063905069)
              ·
                refine ⟨27706214800091982398964401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73883239466911953063905069 27706214800091982398964401)
                ·
                  refine ⟨20779661100068986799223301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27706214800091982398964401 20779661100068986799223301)
                  ·
                    refine ⟨3896186456262935024854369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20779661100068986799223301 3896186456262935024854369)
                    ·
                      refine ⟨2922139842197201268640777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3896186456262935024854369 2922139842197201268640777)
                      ·
                        rfl

theorem cell23_5690847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 4, 2].length) (baseStart_5690847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690847 prefixEnd_5690847 := by exact prefixLift 5690847
  have htrace : WordTrace (prefixWord ++ tailWord_5690847) baseStart_5690847 baseEnd_5690847 := by
    simpa [prefixWord, tailWord_5690847, baseEnd_5690847] using wordTrace_append hprefix tailTrace_5690847
  have hstable : (prefixWord ++ tailWord_5690847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690847).length < 2 ^ (prefixWord ++ tailWord_5690847).sum := by decide
  have hdescent : baseEnd_5690847 < baseStart_5690847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690891 : List Nat := [1, 1, 1, 1, 9, 1, 1, 1, 3, 4]
def baseStart_5690891 : Nat := 118140960795 + 5690891 * 2 ^ 59
def prefixEnd_5690891 : Nat := 4983230072969 + 3 ^ 40 * 5690891 * 2
def baseEnd_5690891 : Nat := 974054145115333032163525

theorem tailTrace_5690891 : CollatzResearch.WordTrace tailWord_5690891 prefixEnd_5690891 974054145115333032163525 := by
  unfold tailWord_5690891
  simp only [CollatzResearch.WordTrace]
  refine ⟨207563846825881308648864527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138375897883920872432576351 207563846825881308648864527)
  ·
    refine ⟨311345770238821962973296791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207563846825881308648864527 311345770238821962973296791)
    ·
      refine ⟨467018655358232944459945187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311345770238821962973296791 467018655358232944459945187)
      ·
        refine ⟨700527983037349416689917781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467018655358232944459945187 700527983037349416689917781)
        ·
          refine ⟨4104656150609469238417487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 700527983037349416689917781 4104656150609469238417487)
          ·
            refine ⟨6156984225914203857626231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4104656150609469238417487 6156984225914203857626231)
            ·
              refine ⟨9235476338871305786439347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6156984225914203857626231 9235476338871305786439347)
              ·
                refine ⟨13853214508306958679659021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9235476338871305786439347 13853214508306958679659021)
                ·
                  refine ⟨5194955440615109504872133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13853214508306958679659021 5194955440615109504872133)
                  ·
                    refine ⟨974054145115333032163525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5194955440615109504872133 974054145115333032163525)
                    ·
                      rfl

theorem cell23_5690891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 3, 4].length) (baseStart_5690891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690891 prefixEnd_5690891 := by exact prefixLift 5690891
  have htrace : WordTrace (prefixWord ++ tailWord_5690891) baseStart_5690891 baseEnd_5690891 := by
    simpa [prefixWord, tailWord_5690891, baseEnd_5690891] using wordTrace_append hprefix tailTrace_5690891
  have hstable : (prefixWord ++ tailWord_5690891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690891).length < 2 ^ (prefixWord ++ tailWord_5690891).sum := by decide
  have hdescent : baseEnd_5690891 < baseStart_5690891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690914 : List Nat := [3, 3, 1, 1, 1, 1, 2, 4, 3, 1, 3]
def baseStart_5690914 : Nat := 118140960795 + 5690914 * 2 ^ 59
def prefixEnd_5690914 : Nat := 4983230072969 + 3 ^ 40 * 5690914 * 2
def baseEnd_5690914 : Nat := 2922174245401052506502969

theorem tailTrace_5690914 : CollatzResearch.WordTrace tailWord_5690914 prefixEnd_5690914 2922174245401052506502969 := by
  unfold tailWord_5690914
  simp only [CollatzResearch.WordTrace]
  refine ⟨51891171426199495894237949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138376457136531989051301197 51891171426199495894237949)
  ·
    refine ⟨19459189284824810960339231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51891171426199495894237949 19459189284824810960339231)
    ·
      refine ⟨29188783927237216440508847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19459189284824810960339231 29188783927237216440508847)
      ·
        refine ⟨43783175890855824660763271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29188783927237216440508847 43783175890855824660763271)
        ·
          refine ⟨65674763836283736991144907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43783175890855824660763271 65674763836283736991144907)
          ·
            refine ⟨98512145754425605486717361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65674763836283736991144907 98512145754425605486717361)
            ·
              refine ⟨73884109315819204115038021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98512145754425605486717361 73884109315819204115038021)
              ·
                refine ⟨13853270496716100771569629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73884109315819204115038021 13853270496716100771569629)
                ·
                  refine ⟨5194976436268537789338611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13853270496716100771569629 5194976436268537789338611)
                  ·
                    refine ⟨7792464654402806684007917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5194976436268537789338611 7792464654402806684007917)
                    ·
                      refine ⟨2922174245401052506502969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7792464654402806684007917 2922174245401052506502969)
                      ·
                        rfl

theorem cell23_5690914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_5690914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690914 prefixEnd_5690914 := by exact prefixLift 5690914
  have htrace : WordTrace (prefixWord ++ tailWord_5690914) baseStart_5690914 baseEnd_5690914 := by
    simpa [prefixWord, tailWord_5690914, baseEnd_5690914] using wordTrace_append hprefix tailTrace_5690914
  have hstable : (prefixWord ++ tailWord_5690914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690914).length < 2 ^ (prefixWord ++ tailWord_5690914).sum := by decide
  have hdescent : baseEnd_5690914 < baseStart_5690914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690964 : List Nat := [2, 4, 1, 1, 1, 2, 1, 5, 2, 4]
def baseStart_5690964 : Nat := 118140960795 + 5690964 * 2 ^ 59
def prefixEnd_5690964 : Nat := 4983230072969 + 3 ^ 40 * 5690964 * 2
def baseEnd_5690964 : Nat := 974066639811259103625913

theorem tailTrace_5690964 : CollatzResearch.WordTrace tailWord_5690964 prefixEnd_5690964 974066639811259103625913 := by
  unfold tailWord_5690964
  simp only [CollatzResearch.WordTrace]
  refine ⟨103783254677308421058135973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138377672903077894744181297 103783254677308421058135973)
  ·
    refine ⟨19459360251995328948400495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103783254677308421058135973 19459360251995328948400495)
    ·
      refine ⟨29189040377992993422600743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19459360251995328948400495 29189040377992993422600743)
      ·
        refine ⟨43783560566989490133901115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29189040377992993422600743 43783560566989490133901115)
        ·
          refine ⟨65675340850484235200851673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43783560566989490133901115 65675340850484235200851673)
          ·
            refine ⟨49256505637863176400638755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65675340850484235200851673 49256505637863176400638755)
            ·
              refine ⟨73884758456794764600958133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49256505637863176400638755 73884758456794764600958133)
              ·
                refine ⟨6926696105324509181339825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73884758456794764600958133 6926696105324509181339825)
                ·
                  refine ⟨5195022078993381886004869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6926696105324509181339825 5195022078993381886004869)
                  ·
                    refine ⟨974066639811259103625913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5195022078993381886004869 974066639811259103625913)
                    ·
                      rfl

theorem cell23_5690964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_5690964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690964 prefixEnd_5690964 := by exact prefixLift 5690964
  have htrace : WordTrace (prefixWord ++ tailWord_5690964) baseStart_5690964 baseEnd_5690964 := by
    simpa [prefixWord, tailWord_5690964, baseEnd_5690964] using wordTrace_append hprefix tailTrace_5690964
  have hstable : (prefixWord ++ tailWord_5690964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690964).length < 2 ^ (prefixWord ++ tailWord_5690964).sum := by decide
  have hdescent : baseEnd_5690964 < baseStart_5690964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690967 : List Nat := [1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 4]
def baseStart_5690967 : Nat := 118140960795 + 5690967 * 2 ^ 59
def prefixEnd_5690967 : Nat := 4983230072969 + 3 ^ 40 * 5690967 * 2
def baseEnd_5690967 : Nat := 2922201459875740799140225

theorem tailTrace_5690967 : CollatzResearch.WordTrace tailWord_5690967 prefixEnd_5690967 2922201459875740799140225 := by
  unfold tailWord_5690967
  simp only [CollatzResearch.WordTrace]
  refine ⟨207566618773605973628631155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138377745849070649085754103 207566618773605973628631155)
  ·
    refine ⟨311349928160408960442946733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207566618773605973628631155 311349928160408960442946733)
    ·
      refine ⟨116756223060153360166105025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 311349928160408960442946733 116756223060153360166105025)
      ·
        refine ⟨87567167295115020124578769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116756223060153360166105025 87567167295115020124578769)
        ·
          refine ⟨65675375471336265093434077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87567167295115020124578769 65675375471336265093434077)
          ·
            refine ⟨24628265801751099410037779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65675375471336265093434077 24628265801751099410037779)
            ·
              refine ⟨36942398702626649115056669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24628265801751099410037779 36942398702626649115056669)
              ·
                refine ⟨13853399513484993418146251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36942398702626649115056669 13853399513484993418146251)
                ·
                  refine ⟨20780099270227490127219377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13853399513484993418146251 20780099270227490127219377)
                  ·
                    refine ⟨15585074452670617595414533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20780099270227490127219377 15585074452670617595414533)
                    ·
                      refine ⟨2922201459875740799140225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15585074452670617595414533 2922201459875740799140225)
                      ·
                        rfl

theorem cell23_5690967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_5690967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690967 prefixEnd_5690967 := by exact prefixLift 5690967
  have htrace : WordTrace (prefixWord ++ tailWord_5690967) baseStart_5690967 baseEnd_5690967 := by
    simpa [prefixWord, tailWord_5690967, baseEnd_5690967] using wordTrace_append hprefix tailTrace_5690967
  have hstable : (prefixWord ++ tailWord_5690967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690967).length < 2 ^ (prefixWord ++ tailWord_5690967).sum := by decide
  have hdescent : baseEnd_5690967 < baseStart_5690967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690970 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7]
def baseStart_5690970 : Nat := 118140960795 + 5690970 * 2 ^ 59
def prefixEnd_5690970 : Nat := 4983230072969 + 3 ^ 40 * 5690970 * 2
def baseEnd_5690970 : Nat := 2922203000317704287402711

theorem tailTrace_5690970 : CollatzResearch.WordTrace tailWord_5690970 prefixEnd_5690970 2922203000317704287402711 := by
  unfold tailWord_5690970
  simp only [CollatzResearch.WordTrace]
  refine ⟨51891682048148776285247591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138377818795063403427326909 51891682048148776285247591)
  ·
    refine ⟨77837523072223164427871387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51891682048148776285247591 77837523072223164427871387)
    ·
      refine ⟨116756284608334746641807081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77837523072223164427871387 116756284608334746641807081)
      ·
        refine ⟨87567213456251059981355311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116756284608334746641807081 87567213456251059981355311)
        ·
          refine ⟨131350820184376589972032967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87567213456251059981355311 131350820184376589972032967)
          ·
            refine ⟨197026230276564884958049451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131350820184376589972032967 197026230276564884958049451)
            ·
              refine ⟨295539345414847327437074177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197026230276564884958049451 295539345414847327437074177)
              ·
                refine ⟨221654509061135495577805633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295539345414847327437074177 221654509061135495577805633)
                ·
                  refine ⟨166240881795851621683354225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221654509061135495577805633 166240881795851621683354225)
                  ·
                    refine ⟨124680661346888716262515669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 166240881795851621683354225 124680661346888716262515669)
                    ·
                      refine ⟨2922203000317704287402711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124680661346888716262515669 2922203000317704287402711)
                      ·
                        rfl

theorem cell23_5690970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_5690970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690970 prefixEnd_5690970 := by exact prefixLift 5690970
  have htrace : WordTrace (prefixWord ++ tailWord_5690970) baseStart_5690970 baseEnd_5690970 := by
    simpa [prefixWord, tailWord_5690970, baseEnd_5690970] using wordTrace_append hprefix tailTrace_5690970
  have hstable : (prefixWord ++ tailWord_5690970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690970).length < 2 ^ (prefixWord ++ tailWord_5690970).sum := by decide
  have hdescent : baseEnd_5690970 < baseStart_5690970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690977 : List Nat := [1, 2, 3, 1, 1, 3, 5, 7]
def baseStart_5690977 : Nat := 118140960795 + 5690977 * 2 ^ 59
def prefixEnd_5690977 : Nat := 4983230072969 + 3 ^ 40 * 5690977 * 2
def baseEnd_5690977 : Nat := 108229873877121694815377

theorem tailTrace_5690977 : CollatzResearch.WordTrace tailWord_5690977 prefixEnd_5690977 108229873877121694815377 := by
  unfold tailWord_5690977
  simp only [CollatzResearch.WordTrace]
  refine ⟨207566983503569745336495185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138377989002379830224330123 207566983503569745336495185)
  ·
    refine ⟨155675237627677309002371389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207566983503569745336495185 155675237627677309002371389)
    ·
      refine ⟨58378214110378990875889271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155675237627677309002371389 58378214110378990875889271)
      ·
        refine ⟨87567321165568486313833907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58378214110378990875889271 87567321165568486313833907)
        ·
          refine ⟨131350981748352729470750861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87567321165568486313833907 131350981748352729470750861)
          ·
            refine ⟨49256618155632273551531573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131350981748352729470750861 49256618155632273551531573)
            ·
              refine ⟨4617807952090525645456085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49256618155632273551531573 4617807952090525645456085)
              ·
                refine ⟨108229873877121694815377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4617807952090525645456085 108229873877121694815377)
                ·
                  rfl

theorem cell23_5690977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 7].length) (baseStart_5690977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690977 prefixEnd_5690977 := by exact prefixLift 5690977
  have htrace : WordTrace (prefixWord ++ tailWord_5690977) baseStart_5690977 baseEnd_5690977 := by
    simpa [prefixWord, tailWord_5690977, baseEnd_5690977] using wordTrace_append hprefix tailTrace_5690977
  have hstable : (prefixWord ++ tailWord_5690977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690977).length < 2 ^ (prefixWord ++ tailWord_5690977).sum := by decide
  have hdescent : baseEnd_5690977 < baseStart_5690977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690984 : List Nat := [2, 1, 4, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_5690984 : Nat := 118140960795 + 5690984 * 2 ^ 59
def prefixEnd_5690984 : Nat := 4983230072969 + 3 ^ 40 * 5690984 * 2
def baseEnd_5690984 : Nat := 2922210189046867232627647

theorem tailTrace_5690984 : CollatzResearch.WordTrace tailWord_5690984 prefixEnd_5690984 2922210189046867232627647 := by
  unfold tailWord_5690984
  simp only [CollatzResearch.WordTrace]
  refine ⟨103783619407272192766000003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138378159209696257021333337 103783619407272192766000003)
  ·
    refine ⟨155675429110908289149000005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103783619407272192766000003 155675429110908289149000005)
    ·
      refine ⟨29189142958295304215437501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155675429110908289149000005 29189142958295304215437501)
      ·
        refine ⟨10945928609360739080789063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29189142958295304215437501 10945928609360739080789063)
        ·
          refine ⟨16418892914041108621183595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10945928609360739080789063 16418892914041108621183595)
          ·
            refine ⟨24628339371061662931775393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16418892914041108621183595 24628339371061662931775393)
            ·
              refine ⟨18471254528296247198831545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24628339371061662931775393 18471254528296247198831545)
              ·
                refine ⟨13853440896222185399123659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18471254528296247198831545 13853440896222185399123659)
                ·
                  refine ⟨20780161344333278098685489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13853440896222185399123659 20780161344333278098685489)
                  ·
                    refine ⟨15585121008249958574014117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20780161344333278098685489 15585121008249958574014117)
                    ·
                      refine ⟨2922210189046867232627647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15585121008249958574014117 2922210189046867232627647)
                      ·
                        rfl

theorem cell23_5690984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_5690984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690984 prefixEnd_5690984 := by exact prefixLift 5690984
  have htrace : WordTrace (prefixWord ++ tailWord_5690984) baseStart_5690984 baseEnd_5690984 := by
    simpa [prefixWord, tailWord_5690984, baseEnd_5690984] using wordTrace_append hprefix tailTrace_5690984
  have hstable : (prefixWord ++ tailWord_5690984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690984).length < 2 ^ (prefixWord ++ tailWord_5690984).sum := by decide
  have hdescent : baseEnd_5690984 < baseStart_5690984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5690998 : List Nat := [5, 1, 1, 2, 2, 3, 1, 2, 2, 4]
def baseStart_5690998 : Nat := 118140960795 + 5690998 * 2 ^ 59
def prefixEnd_5690998 : Nat := 4983230072969 + 3 ^ 40 * 5690998 * 2
def baseEnd_5690998 : Nat := 974072459258676725950861

theorem tailTrace_5690998 : CollatzResearch.WordTrace tailWord_5690998 prefixEnd_5690998 974072459258676725950861 := by
  unfold tailWord_5690998
  simp only [CollatzResearch.WordTrace]
  refine ⟨12972984339780854120188103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138378499624329110615339765 12972984339780854120188103)
  ·
    refine ⟨19459476509671281180282155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12972984339780854120188103 19459476509671281180282155)
    ·
      refine ⟨29189214764506921770423233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19459476509671281180282155 29189214764506921770423233)
      ·
        refine ⟨21891911073380191327817425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29189214764506921770423233 21891911073380191327817425)
        ·
          refine ⟨16418933305035143495863069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21891911073380191327817425 16418933305035143495863069)
          ·
            refine ⟨6157099989388178810948651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16418933305035143495863069 6157099989388178810948651)
            ·
              refine ⟨9235649984082268216422977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6157099989388178810948651 9235649984082268216422977)
              ·
                refine ⟨6926737488061701162317233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9235649984082268216422977 6926737488061701162317233)
                ·
                  refine ⟨5195053116046275871737925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6926737488061701162317233 5195053116046275871737925)
                  ·
                    refine ⟨974072459258676725950861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5195053116046275871737925 974072459258676725950861)
                    ·
                      rfl

theorem cell23_5690998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_5690998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5690998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5690998 prefixEnd_5690998 := by exact prefixLift 5690998
  have htrace : WordTrace (prefixWord ++ tailWord_5690998) baseStart_5690998 baseEnd_5690998 := by
    simpa [prefixWord, tailWord_5690998, baseEnd_5690998] using wordTrace_append hprefix tailTrace_5690998
  have hstable : (prefixWord ++ tailWord_5690998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5690998).length < 2 ^ (prefixWord ++ tailWord_5690998).sum := by decide
  have hdescent : baseEnd_5690998 < baseStart_5690998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5690998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691000 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 2, 3, 7]
def baseStart_5691000 : Nat := 118140960795 + 5691000 * 2 ^ 59
def prefixEnd_5691000 : Nat := 4983230072969 + 3 ^ 40 * 5691000 * 2
def baseEnd_5691000 : Nat := 2922218404737339170027573

theorem tailTrace_5691000 : CollatzResearch.WordTrace tailWord_5691000 prefixEnd_5691000 2922218404737339170027573 := by
  unfold tailWord_5691000
  simp only [CollatzResearch.WordTrace]
  refine ⟨103783911191243210132291227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138378548254990946843054969 103783911191243210132291227)
  ·
    refine ⟨155675866786864815198436841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103783911191243210132291227 155675866786864815198436841)
    ·
      refine ⟨116756900090148611398827631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155675866786864815198436841 116756900090148611398827631)
      ·
        refine ⟨175135350135222917098241447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116756900090148611398827631 175135350135222917098241447)
        ·
          refine ⟨262703025202834375647362171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175135350135222917098241447 262703025202834375647362171)
          ·
            refine ⟨394054537804251563471043257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262703025202834375647362171 394054537804251563471043257)
            ·
              refine ⟨295540903353188672603282443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394054537804251563471043257 295540903353188672603282443)
              ·
                refine ⟨443311355029783008904923665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295540903353188672603282443 443311355029783008904923665)
                ·
                  refine ⟨332483516272337256678692749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443311355029783008904923665 332483516272337256678692749)
                  ·
                    refine ⟨124681318602126471254509781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 332483516272337256678692749 124681318602126471254509781)
                    ·
                      refine ⟨2922218404737339170027573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124681318602126471254509781 2922218404737339170027573)
                      ·
                        rfl

theorem cell23_5691000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_5691000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691000 prefixEnd_5691000 := by exact prefixLift 5691000
  have htrace : WordTrace (prefixWord ++ tailWord_5691000) baseStart_5691000 baseEnd_5691000 := by
    simpa [prefixWord, tailWord_5691000, baseEnd_5691000] using wordTrace_append hprefix tailTrace_5691000
  have hstable : (prefixWord ++ tailWord_5691000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691000).length < 2 ^ (prefixWord ++ tailWord_5691000).sum := by decide
  have hdescent : baseEnd_5691000 < baseStart_5691000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691028 : List Nat := [2, 4, 2, 2, 3, 1, 2, 7]
def baseStart_5691028 : Nat := 118140960795 + 5691028 * 2 ^ 59
def prefixEnd_5691028 : Nat := 4983230072969 + 3 ^ 40 * 5691028 * 2
def baseEnd_5691028 : Nat := 108230843785024631869535

theorem tailTrace_5691028 : CollatzResearch.WordTrace tailWord_5691028 prefixEnd_5691028 108230843785024631869535 := by
  unfold tailWord_5691028
  simp only [CollatzResearch.WordTrace]
  refine ⟨103784421813192490523300869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138379229084256654031067825 103784421813192490523300869)
  ·
    refine ⟨19459579089973591973118913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103784421813192490523300869 19459579089973591973118913)
    ·
      refine ⟨14594684317480193979839185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19459579089973591973118913 14594684317480193979839185)
      ·
        refine ⟨10946013238110145484879389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14594684317480193979839185 10946013238110145484879389)
        ·
          refine ⟨4104754964291304556829771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10946013238110145484879389 4104754964291304556829771)
          ·
            refine ⟨6157132446436956835244657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4104754964291304556829771 6157132446436956835244657)
            ·
              refine ⟨4617849334827717626433493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6157132446436956835244657 4617849334827717626433493)
              ·
                refine ⟨108230843785024631869535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4617849334827717626433493 108230843785024631869535)
                ·
                  rfl

theorem cell23_5691028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 7].length) (baseStart_5691028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691028 prefixEnd_5691028 := by exact prefixLift 5691028
  have htrace : WordTrace (prefixWord ++ tailWord_5691028) baseStart_5691028 baseEnd_5691028 := by
    simpa [prefixWord, tailWord_5691028, baseEnd_5691028] using wordTrace_append hprefix tailTrace_5691028
  have hstable : (prefixWord ++ tailWord_5691028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691028).length < 2 ^ (prefixWord ++ tailWord_5691028).sum := by decide
  have hdescent : baseEnd_5691028 < baseStart_5691028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691031 : List Nat := [1, 1, 3, 3, 2, 2, 1, 4, 1, 3, 2]
def baseStart_5691031 : Nat := 118140960795 + 5691031 * 2 ^ 59
def prefixEnd_5691031 : Nat := 4983230072969 + 3 ^ 40 * 5691031 * 2
def baseEnd_5691031 : Nat := 2922234322637628548739931

theorem tailTrace_5691031 : CollatzResearch.WordTrace tailWord_5691031 prefixEnd_5691031 2922234322637628548739931 := by
  unfold tailWord_5691031
  simp only [CollatzResearch.WordTrace]
  refine ⟨207568953045374112558960947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138379302030249408372640631 207568953045374112558960947)
  ·
    refine ⟨311353429568061168838441421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207568953045374112558960947 311353429568061168838441421)
    ·
      refine ⟨116757536088022938314415533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 311353429568061168838441421 116757536088022938314415533)
      ·
        refine ⟨43784076033008601867905825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116757536088022938314415533 43784076033008601867905825)
        ·
          refine ⟨32838057024756451400929369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43784076033008601867905825 32838057024756451400929369)
          ·
            refine ⟨24628542768567338550697027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32838057024756451400929369 24628542768567338550697027)
            ·
              refine ⟨36942814152851007826045541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24628542768567338550697027 36942814152851007826045541)
              ·
                refine ⟨6926777653659563967383539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36942814152851007826045541 6926777653659563967383539)
                ·
                  refine ⟨10390166480489345951075309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6926777653659563967383539 10390166480489345951075309)
                  ·
                    refine ⟨3896312430183504731653241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10390166480489345951075309 3896312430183504731653241)
                    ·
                      refine ⟨2922234322637628548739931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3896312430183504731653241 2922234322637628548739931)
                      ·
                        rfl

theorem cell23_5691031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_5691031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691031 prefixEnd_5691031 := by exact prefixLift 5691031
  have htrace : WordTrace (prefixWord ++ tailWord_5691031) baseStart_5691031 baseEnd_5691031 := by
    simpa [prefixWord, tailWord_5691031, baseEnd_5691031] using wordTrace_append hprefix tailTrace_5691031
  have hstable : (prefixWord ++ tailWord_5691031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691031).length < 2 ^ (prefixWord ++ tailWord_5691031).sum := by decide
  have hdescent : baseEnd_5691031 < baseStart_5691031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691039 : List Nat := [1, 1, 2, 7, 2, 1, 1, 3, 1, 2, 2]
def baseStart_5691039 : Nat := 118140960795 + 5691039 * 2 ^ 59
def prefixEnd_5691039 : Nat := 4983230072969 + 3 ^ 40 * 5691039 * 2
def baseEnd_5691039 : Nat := 2922238430482864517439895

theorem tailTrace_5691039 : CollatzResearch.WordTrace tailWord_5691039 prefixEnd_5691039 2922238430482864517439895 := by
  unfold tailWord_5691039
  simp only [CollatzResearch.WordTrace]
  refine ⟨207569244829345129925252171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138379496552896753283501447 207569244829345129925252171)
  ·
    refine ⟨311353867244017694887878257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207569244829345129925252171 311353867244017694887878257)
    ·
      refine ⟨233515400433013271165908693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311353867244017694887878257 233515400433013271165908693)
      ·
        refine ⟨5473017197648748542950985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 233515400433013271165908693 5473017197648748542950985)
        ·
          refine ⟨4104762898236561407213239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5473017197648748542950985 4104762898236561407213239)
          ·
            refine ⟨6157144347354842110819859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4104762898236561407213239 6157144347354842110819859)
            ·
              refine ⟨9235716521032263166229789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6157144347354842110819859 9235716521032263166229789)
              ·
                refine ⟨3463393695387098687336171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9235716521032263166229789 3463393695387098687336171)
                ·
                  refine ⟨5195090543080648031004257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3463393695387098687336171 5195090543080648031004257)
                  ·
                    refine ⟨3896317907310486023253193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5195090543080648031004257 3896317907310486023253193)
                    ·
                      refine ⟨2922238430482864517439895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3896317907310486023253193 2922238430482864517439895)
                      ·
                        rfl

theorem cell23_5691039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_5691039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691039 prefixEnd_5691039 := by exact prefixLift 5691039
  have htrace : WordTrace (prefixWord ++ tailWord_5691039) baseStart_5691039 baseEnd_5691039 := by
    simpa [prefixWord, tailWord_5691039, baseEnd_5691039] using wordTrace_append hprefix tailTrace_5691039
  have hstable : (prefixWord ++ tailWord_5691039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691039).length < 2 ^ (prefixWord ++ tailWord_5691039).sum := by decide
  have hdescent : baseEnd_5691039 < baseStart_5691039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691114 : List Nat := [3, 1, 3, 1, 1, 1, 4, 2, 2, 5]
def baseStart_5691114 : Nat := 118140960795 + 5691114 * 2 ^ 59
def prefixEnd_5691114 : Nat := 4983230072969 + 3 ^ 40 * 5691114 * 2
def baseEnd_5691114 : Nat := 974092313843983908000683

theorem tailTrace_5691114 : CollatzResearch.WordTrace tailWord_5691114 prefixEnd_5691114 974092313843983908000683 := by
  unfold tailWord_5691114
  simp only [CollatzResearch.WordTrace]
  refine ⟨51892995076018354433558099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138381320202715611822821597 51892995076018354433558099)
  ·
    refine ⟨77839492614027531650337149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51892995076018354433558099 77839492614027531650337149)
    ·
      refine ⟨29189809730260324368876431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77839492614027531650337149 29189809730260324368876431)
      ·
        refine ⟨43784714595390486553314647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29189809730260324368876431 43784714595390486553314647)
        ·
          refine ⟨65677071893085729829971971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43784714595390486553314647 65677071893085729829971971)
          ·
            refine ⟨98515607839628594744957957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65677071893085729829971971 98515607839628594744957957)
            ·
              refine ⟨18471676469930361514679617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98515607839628594744957957 18471676469930361514679617)
              ·
                refine ⟨13853757352447771136009713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18471676469930361514679617 13853757352447771136009713)
                ·
                  refine ⟨10390318014335828352007285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13853757352447771136009713 10390318014335828352007285)
                  ·
                    refine ⟨974092313843983908000683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10390318014335828352007285 974092313843983908000683)
                    ·
                      rfl

theorem cell23_5691114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_5691114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691114 prefixEnd_5691114 := by exact prefixLift 5691114
  have htrace : WordTrace (prefixWord ++ tailWord_5691114) baseStart_5691114 baseEnd_5691114 := by
    simpa [prefixWord, tailWord_5691114, baseEnd_5691114] using wordTrace_append hprefix tailTrace_5691114
  have hstable : (prefixWord ++ tailWord_5691114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691114).length < 2 ^ (prefixWord ++ tailWord_5691114).sum := by decide
  have hdescent : baseEnd_5691114 < baseStart_5691114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691212 : List Nat := [2, 2, 1, 3, 5, 1, 1, 3, 1, 4]
def baseStart_5691212 : Nat := 118140960795 + 5691212 * 2 ^ 59
def prefixEnd_5691212 : Nat := 4983230072969 + 3 ^ 40 * 5691212 * 2
def baseEnd_5691212 : Nat := 974109087545364113525533

theorem tailTrace_5691212 : CollatzResearch.WordTrace tailWord_5691212 prefixEnd_5691212 974109087545364113525533 := by
  unfold tailWord_5691212
  simp only [CollatzResearch.WordTrace]
  refine ⟨103787777328859190235649945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138383703105145586980866593 103787777328859190235649945)
  ·
    refine ⟨77840832996644392676737459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103787777328859190235649945 77840832996644392676737459)
    ·
      refine ⟨116761249494966589015106189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77840832996644392676737459 116761249494966589015106189)
      ·
        refine ⟨43785468560612470880664821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116761249494966589015106189 43785468560612470880664821)
        ·
          refine ⟨4104887677557419145062327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43785468560612470880664821 4104887677557419145062327)
          ·
            refine ⟨6157331516336128717593491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4104887677557419145062327 6157331516336128717593491)
            ·
              refine ⟨9235997274504193076390237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6157331516336128717593491 9235997274504193076390237)
              ·
                refine ⟨3463498977939072403646339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9235997274504193076390237 3463498977939072403646339)
                ·
                  refine ⟨5195248466908608605469509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3463498977939072403646339 5195248466908608605469509)
                  ·
                    refine ⟨974109087545364113525533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5195248466908608605469509 974109087545364113525533)
                    ·
                      rfl

theorem cell23_5691212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3, 1, 4].length) (baseStart_5691212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691212 prefixEnd_5691212 := by exact prefixLift 5691212
  have htrace : WordTrace (prefixWord ++ tailWord_5691212) baseStart_5691212 baseEnd_5691212 := by
    simpa [prefixWord, tailWord_5691212, baseEnd_5691212] using wordTrace_append hprefix tailTrace_5691212
  have hstable : (prefixWord ++ tailWord_5691212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691212).length < 2 ^ (prefixWord ++ tailWord_5691212).sum := by decide
  have hdescent : baseEnd_5691212 < baseStart_5691212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691221 : List Nat := [1, 3, 2, 2, 2, 2, 2, 3, 1, 5]
def baseStart_5691221 : Nat := 118140960795 + 5691221 * 2 ^ 59
def prefixEnd_5691221 : Nat := 4983230072969 + 3 ^ 40 * 5691221 * 2
def baseEnd_5691221 : Nat := 974110627987327601788019

theorem tailTrace_5691221 : CollatzResearch.WordTrace tailWord_5691221 prefixEnd_5691221 974110627987327601788019 := by
  unfold tailWord_5691221
  simp only [CollatzResearch.WordTrace]
  refine ⟨207575882914685775008377517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138383921943123850005585011 207575882914685775008377517)
  ·
    refine ⟨77840956093007165628141569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207575882914685775008377517 77840956093007165628141569)
    ·
      refine ⟨58380717069755374221106177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77840956093007165628141569 58380717069755374221106177)
      ·
        refine ⟨43785537802316530665829633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58380717069755374221106177 43785537802316530665829633)
        ·
          refine ⟨32839153351737397999372225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43785537802316530665829633 32839153351737397999372225)
          ·
            refine ⟨24629365013803048499529169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32839153351737397999372225 24629365013803048499529169)
            ·
              refine ⟨18472023760352286374646877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24629365013803048499529169 18472023760352286374646877)
              ·
                refine ⟨6927008910132107390492579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18472023760352286374646877 6927008910132107390492579)
                ·
                  refine ⟨10390513365198161085738869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6927008910132107390492579 10390513365198161085738869)
                  ·
                    refine ⟨974110627987327601788019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10390513365198161085738869 974110627987327601788019)
                    ·
                      rfl

theorem cell23_5691221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_5691221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691221 prefixEnd_5691221 := by exact prefixLift 5691221
  have htrace : WordTrace (prefixWord ++ tailWord_5691221) baseStart_5691221 baseEnd_5691221 := by
    simpa [prefixWord, tailWord_5691221, baseEnd_5691221] using wordTrace_append hprefix tailTrace_5691221
  have hstable : (prefixWord ++ tailWord_5691221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691221).length < 2 ^ (prefixWord ++ tailWord_5691221).sum := by decide
  have hdescent : baseEnd_5691221 < baseStart_5691221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691224 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 7, 1, 4]
def baseStart_5691224 : Nat := 118140960795 + 5691224 * 2 ^ 59
def prefixEnd_5691224 : Nat := 4983230072969 + 3 ^ 40 * 5691224 * 2
def baseEnd_5691224 : Nat := 2922333424403946293626543

theorem tailTrace_5691224 : CollatzResearch.WordTrace tailWord_5691224 prefixEnd_5691224 2922333424403946293626543 := by
  unfold tailWord_5691224
  simp only [CollatzResearch.WordTrace]
  refine ⟨103787996166837453260368363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138383994889116604347157817 103787996166837453260368363)
  ·
    refine ⟨155681994250256179890552545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103787996166837453260368363 155681994250256179890552545)
    ·
      refine ⟨116761495687692134917914409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155681994250256179890552545 116761495687692134917914409)
      ·
        refine ⟨87571121765769101188435807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116761495687692134917914409 87571121765769101188435807)
        ·
          refine ⟨131356682648653651782653711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87571121765769101188435807 131356682648653651782653711)
          ·
            refine ⟨197035023972980477673980567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131356682648653651782653711 197035023972980477673980567)
            ·
              refine ⟨295552535959470716510970851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197035023972980477673980567 295552535959470716510970851)
              ·
                refine ⟨443328803939206074766456277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295552535959470716510970851 443328803939206074766456277)
                ·
                  refine ⟨10390518842325142377338819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 443328803939206074766456277 10390518842325142377338819)
                  ·
                    refine ⟨15585778263487713566008229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10390518842325142377338819 15585778263487713566008229)
                    ·
                      refine ⟨2922333424403946293626543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15585778263487713566008229 2922333424403946293626543)
                      ·
                        rfl

theorem cell23_5691224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_5691224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691224 prefixEnd_5691224 := by exact prefixLift 5691224
  have htrace : WordTrace (prefixWord ++ tailWord_5691224) baseStart_5691224 baseEnd_5691224 := by
    simpa [prefixWord, tailWord_5691224, baseEnd_5691224] using wordTrace_append hprefix tailTrace_5691224
  have hstable : (prefixWord ++ tailWord_5691224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691224).length < 2 ^ (prefixWord ++ tailWord_5691224).sum := by decide
  have hdescent : baseEnd_5691224 < baseStart_5691224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691235 : List Nat := [1, 1, 1, 5, 4, 2, 1, 1, 3, 1, 3]
def baseStart_5691235 : Nat := 118140960795 + 5691235 * 2 ^ 59
def prefixEnd_5691235 : Nat := 4983230072969 + 3 ^ 40 * 5691235 * 2
def baseEnd_5691235 : Nat := 2922339072691145750588993

theorem tailTrace_5691235 : CollatzResearch.WordTrace tailWord_5691235 prefixEnd_5691235 2922339072691145750588993 := by
  unfold tailWord_5691235
  simp only [CollatzResearch.WordTrace]
  refine ⟨207576393536635055399387159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138384262357756703599591439 207576393536635055399387159)
  ·
    refine ⟨311364590304952583099080739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207576393536635055399387159 311364590304952583099080739)
    ·
      refine ⟨467046885457428874648621109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311364590304952583099080739 467046885457428874648621109)
      ·
        refine ⟨43785645511633956998308229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 467046885457428874648621109 43785645511633956998308229)
        ·
          refine ⟨8209808533431366937182793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43785645511633956998308229 8209808533431366937182793)
          ·
            refine ⟨6157356400073525202887095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8209808533431366937182793 6157356400073525202887095)
            ·
              refine ⟨9236034600110287804330643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6157356400073525202887095 9236034600110287804330643)
              ·
                refine ⟨13854051900165431706495965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9236034600110287804330643 13854051900165431706495965)
                ·
                  refine ⟨5195269462562036889935987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13854051900165431706495965 5195269462562036889935987)
                  ·
                    refine ⟨7792904193843055334903981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5195269462562036889935987 7792904193843055334903981)
                    ·
                      refine ⟨2922339072691145750588993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7792904193843055334903981 2922339072691145750588993)
                      ·
                        rfl

theorem cell23_5691235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_5691235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691235 prefixEnd_5691235 := by exact prefixLift 5691235
  have htrace : WordTrace (prefixWord ++ tailWord_5691235) baseStart_5691235 baseEnd_5691235 := by
    simpa [prefixWord, tailWord_5691235, baseEnd_5691235] using wordTrace_append hprefix tailTrace_5691235
  have hstable : (prefixWord ++ tailWord_5691235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691235).length < 2 ^ (prefixWord ++ tailWord_5691235).sum := by decide
  have hdescent : baseEnd_5691235 < baseStart_5691235 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691242 : List Nat := [3, 1, 3, 4, 2, 1, 2, 1, 6]
def baseStart_5691242 : Nat := 118140960795 + 5691242 * 2 ^ 59
def prefixEnd_5691242 : Nat := 4983230072969 + 3 ^ 40 * 5691242 * 2
def baseEnd_5691242 : Nat := 324704740783969691466829

theorem tailTrace_5691242 : CollatzResearch.WordTrace tailWord_5691242 prefixEnd_5691242 324704740783969691466829 := by
  unfold tailWord_5691242
  simp only [CollatzResearch.WordTrace]
  refine ⟨51894162211902423898722995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138384432565073130396594653 51894162211902423898722995)
  ·
    refine ⟨77841243317853635848084493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51894162211902423898722995 77841243317853635848084493)
    ·
      refine ⟨29190466244195113443031685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77841243317853635848084493 29190466244195113443031685)
      ·
        refine ⟨5473212420786583770568441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29190466244195113443031685 5473212420786583770568441)
        ·
          refine ⟨4104909315589937827926331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5473212420786583770568441 4104909315589937827926331)
          ·
            refine ⟨6157363973384906741889497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4104909315589937827926331 6157363973384906741889497)
            ·
              refine ⟨4618022980038680056417123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6157363973384906741889497 4618022980038680056417123)
              ·
                refine ⟨6927034470058020084625685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4618022980038680056417123 6927034470058020084625685)
                ·
                  refine ⟨324704740783969691466829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6927034470058020084625685 324704740783969691466829)
                  ·
                    rfl

theorem cell23_5691242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 6].length) (baseStart_5691242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691242 prefixEnd_5691242 := by exact prefixLift 5691242
  have htrace : WordTrace (prefixWord ++ tailWord_5691242) baseStart_5691242 baseEnd_5691242 := by
    simpa [prefixWord, tailWord_5691242, baseEnd_5691242] using wordTrace_append hprefix tailTrace_5691242
  have hstable : (prefixWord ++ tailWord_5691242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691242).length < 2 ^ (prefixWord ++ tailWord_5691242).sum := by decide
  have hdescent : baseEnd_5691242 < baseStart_5691242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691258 : List Nat := [3, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2]
def baseStart_5691258 : Nat := 118140960795 + 5691258 * 2 ^ 59
def prefixEnd_5691258 : Nat := 4983230072969 + 3 ^ 40 * 5691258 * 2
def baseEnd_5691258 : Nat := 2922350882746199160601387

theorem tailTrace_5691258 : CollatzResearch.WordTrace tailWord_5691258 prefixEnd_5691258 2922350882746199160601387 := by
  unfold tailWord_5691258
  simp only [CollatzResearch.WordTrace]
  refine ⟨51894308103887932581868607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138384821610367820218316285 51894308103887932581868607)
  ·
    refine ⟨77841462155831898872802911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51894308103887932581868607 77841462155831898872802911)
    ·
      refine ⟨116762193233747848309204367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77841462155831898872802911 116762193233747848309204367)
      ·
        refine ⟨175143289850621772463806551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116762193233747848309204367 175143289850621772463806551)
        ·
          refine ⟨262714934775932658695709827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175143289850621772463806551 262714934775932658695709827)
          ·
            refine ⟨394072402163898988043564741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262714934775932658695709827 394072402163898988043564741)
            ·
              refine ⟨73888575405731060258168389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 394072402163898988043564741 73888575405731060258168389)
              ·
                refine ⟨13854107888574573798406573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73888575405731060258168389 13854107888574573798406573)
                ·
                  refine ⟨5195290458215465174402465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13854107888574573798406573 5195290458215465174402465)
                  ·
                    refine ⟨3896467843661598880801849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5195290458215465174402465 3896467843661598880801849)
                    ·
                      refine ⟨2922350882746199160601387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3896467843661598880801849 2922350882746199160601387)
                      ·
                        rfl

theorem cell23_5691258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 3, 2, 2].length) (baseStart_5691258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691258 prefixEnd_5691258 := by exact prefixLift 5691258
  have htrace : WordTrace (prefixWord ++ tailWord_5691258) baseStart_5691258 baseEnd_5691258 := by
    simpa [prefixWord, tailWord_5691258, baseEnd_5691258] using wordTrace_append hprefix tailTrace_5691258
  have hstable : (prefixWord ++ tailWord_5691258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691258).length < 2 ^ (prefixWord ++ tailWord_5691258).sum := by decide
  have hdescent : baseEnd_5691258 < baseStart_5691258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691262 : List Nat := [4, 2, 3, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_5691262 : Nat := 118140960795 + 5691262 * 2 ^ 59
def prefixEnd_5691262 : Nat := 4983230072969 + 3 ^ 40 * 5691262 * 2
def baseEnd_5691262 : Nat := 2922352936668817144951369

theorem tailTrace_5691262 : CollatzResearch.WordTrace tailWord_5691262 prefixEnd_5691262 2922352936668817144951369 := by
  unfold tailWord_5691262
  simp only [CollatzResearch.WordTrace]
  refine ⟨25947172288442154876327505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138384918871691492673746693 25947172288442154876327505)
  ·
    refine ⟨19460379216331616157245629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25947172288442154876327505 19460379216331616157245629)
    ·
      refine ⟨7297642206124356058967111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19460379216331616157245629 7297642206124356058967111)
      ·
        refine ⟨10946463309186534088450667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7297642206124356058967111 10946463309186534088450667)
        ·
          refine ⟨16419694963779801132676001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10946463309186534088450667 16419694963779801132676001)
          ·
            refine ⟨12314771222834850849507001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16419694963779801132676001 12314771222834850849507001)
            ·
              refine ⟨9236078417126138137130251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12314771222834850849507001 9236078417126138137130251)
              ·
                refine ⟨13854117625689207205695377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9236078417126138137130251 13854117625689207205695377)
                ·
                  refine ⟨10390588219266905404271533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13854117625689207205695377 10390588219266905404271533)
                  ·
                    refine ⟨3896470582225089526601825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10390588219266905404271533 3896470582225089526601825)
                    ·
                      refine ⟨2922352936668817144951369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3896470582225089526601825 2922352936668817144951369)
                      ·
                        rfl

theorem cell23_5691262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_5691262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691262 prefixEnd_5691262 := by exact prefixLift 5691262
  have htrace : WordTrace (prefixWord ++ tailWord_5691262) baseStart_5691262 baseEnd_5691262 := by
    simpa [prefixWord, tailWord_5691262, baseEnd_5691262] using wordTrace_append hprefix tailTrace_5691262
  have hstable : (prefixWord ++ tailWord_5691262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691262).length < 2 ^ (prefixWord ++ tailWord_5691262).sum := by decide
  have hdescent : baseEnd_5691262 < baseStart_5691262 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691275 : List Nat := [1, 1, 1, 1, 4, 2, 1, 7, 1, 2, 2]
def baseStart_5691275 : Nat := 118140960795 + 5691275 * 2 ^ 59
def prefixEnd_5691275 : Nat := 4983230072969 + 3 ^ 40 * 5691275 * 2
def baseEnd_5691275 : Nat := 2922359611917325594088809

theorem tailTrace_5691275 : CollatzResearch.WordTrace tailWord_5691275 prefixEnd_5691275 2922359611917325594088809 := by
  unfold tailWord_5691275
  simp only [CollatzResearch.WordTrace]
  refine ⟨207577852456490142230843279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138385234970993428153895519 207577852456490142230843279)
  ·
    refine ⟨311366778684735213346264919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207577852456490142230843279 311366778684735213346264919)
    ·
      refine ⟨467050168027102820019397379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311366778684735213346264919 467050168027102820019397379)
      ·
        refine ⟨700575252040654230029096069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467050168027102820019397379 700575252040654230029096069)
        ·
          refine ⟨131357859757622668130455513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 700575252040654230029096069 131357859757622668130455513)
          ·
            refine ⟨98518394818217001097841635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131357859757622668130455513 98518394818217001097841635)
            ·
              refine ⟨147777592227325501646762453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98518394818217001097841635 147777592227325501646762453)
              ·
                refine ⟨3463537317827941444845995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 147777592227325501646762453 3463537317827941444845995)
                ·
                  refine ⟨5195305976741912167268993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3463537317827941444845995 5195305976741912167268993)
                  ·
                    refine ⟨3896479482556434125451745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5195305976741912167268993 3896479482556434125451745)
                    ·
                      refine ⟨2922359611917325594088809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3896479482556434125451745 2922359611917325594088809)
                      ·
                        rfl

theorem cell23_5691275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7, 1, 2, 2].length) (baseStart_5691275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691275 prefixEnd_5691275 := by exact prefixLift 5691275
  have htrace : WordTrace (prefixWord ++ tailWord_5691275) baseStart_5691275 baseEnd_5691275 := by
    simpa [prefixWord, tailWord_5691275, baseEnd_5691275] using wordTrace_append hprefix tailTrace_5691275
  have hstable : (prefixWord ++ tailWord_5691275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691275).length < 2 ^ (prefixWord ++ tailWord_5691275).sum := by decide
  have hdescent : baseEnd_5691275 < baseStart_5691275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691286 : List Nat := [5, 3, 1, 1, 2, 1, 1, 4, 1, 1, 3]
def baseStart_5691286 : Nat := 118140960795 + 5691286 * 2 ^ 59
def prefixEnd_5691286 : Nat := 4983230072969 + 3 ^ 40 * 5691286 * 2
def baseEnd_5691286 : Nat := 2922365260204525051051259

theorem tailTrace_5691286 : CollatzResearch.WordTrace tailWord_5691286 prefixEnd_5691286 2922365260204525051051259 := by
  unfold tailWord_5691286
  simp only [CollatzResearch.WordTrace]
  refine ⟨12973640853715643194343357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138385502439633527406329141 12973640853715643194343357)
  ·
    refine ⟨4865115320143366197878759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12973640853715643194343357 4865115320143366197878759)
    ·
      refine ⟨7297672980215049296818139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4865115320143366197878759 7297672980215049296818139)
      ·
        refine ⟨10946509470322573945227209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7297672980215049296818139 10946509470322573945227209)
        ·
          refine ⟨8209882102741930458920407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10946509470322573945227209 8209882102741930458920407)
          ·
            refine ⟨12314823154112895688380611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8209882102741930458920407 12314823154112895688380611)
            ·
              refine ⟨18472234731169343532570917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12314823154112895688380611 18472234731169343532570917)
              ·
                refine ⟨3463544012094251912357047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18472234731169343532570917 3463544012094251912357047)
                ·
                  refine ⟨5195316018141377868535571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3463544012094251912357047 5195316018141377868535571)
                  ·
                    refine ⟨7792974027212066802803357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5195316018141377868535571 7792974027212066802803357)
                    ·
                      refine ⟨2922365260204525051051259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7792974027212066802803357 2922365260204525051051259)
                      ·
                        rfl

theorem cell23_5691286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_5691286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691286 prefixEnd_5691286 := by exact prefixLift 5691286
  have htrace : WordTrace (prefixWord ++ tailWord_5691286) baseStart_5691286 baseEnd_5691286 := by
    simpa [prefixWord, tailWord_5691286, baseEnd_5691286] using wordTrace_append hprefix tailTrace_5691286
  have hstable : (prefixWord ++ tailWord_5691286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691286).length < 2 ^ (prefixWord ++ tailWord_5691286).sum := by decide
  have hdescent : baseEnd_5691286 < baseStart_5691286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691298 : List Nat := [3, 3, 1, 2, 3, 2, 1, 8]
def baseStart_5691298 : Nat := 118140960795 + 5691298 * 2 ^ 59
def prefixEnd_5691298 : Nat := 4983230072969 + 3 ^ 40 * 5691298 * 2
def baseEnd_5691298 : Nat := 108235978591569592744489

theorem tailTrace_5691298 : CollatzResearch.WordTrace tailWord_5691298 prefixEnd_5691298 108235978591569592744489 := by
  unfold tailWord_5691298
  simp only [CollatzResearch.WordTrace]
  refine ⟨51894672833851704289732637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138385794223604544772620365 51894672833851704289732637)
  ·
    refine ⟨19460502312694389108649739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51894672833851704289732637 19460502312694389108649739)
    ·
      refine ⟨29190753469041583662974609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19460502312694389108649739 29190753469041583662974609)
      ·
        refine ⟨21893065101781187747230957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29190753469041583662974609 21893065101781187747230957)
        ·
          refine ⟨8209899413167945405211609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21893065101781187747230957 8209899413167945405211609)
          ·
            refine ⟨6157424559875959053908707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8209899413167945405211609 6157424559875959053908707)
            ·
              refine ⟨9236136839813938580863061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6157424559875959053908707 9236136839813938580863061)
              ·
                refine ⟨108235978591569592744489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9236136839813938580863061 108235978591569592744489)
                ·
                  rfl

theorem cell23_5691298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 8].length) (baseStart_5691298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691298 prefixEnd_5691298 := by exact prefixLift 5691298
  have htrace : WordTrace (prefixWord ++ tailWord_5691298) baseStart_5691298 baseEnd_5691298 := by
    simpa [prefixWord, tailWord_5691298, baseEnd_5691298] using wordTrace_append hprefix tailTrace_5691298
  have hstable : (prefixWord ++ tailWord_5691298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691298).length < 2 ^ (prefixWord ++ tailWord_5691298).sum := by decide
  have hdescent : baseEnd_5691298 < baseStart_5691298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691361 : List Nat := [1, 2, 3, 1, 2, 1, 4, 1, 2, 2, 4]
def baseStart_5691361 : Nat := 118140960795 + 5691361 * 2 ^ 59
def prefixEnd_5691361 : Nat := 4983230072969 + 3 ^ 40 * 5691361 * 2
def baseEnd_5691361 : Nat := 2922403771253612257613413

theorem tailTrace_5691361 : CollatzResearch.WordTrace tailWord_5691361 prefixEnd_5691361 2922403771253612257613413 := by
  unfold tailWord_5691361
  simp only [CollatzResearch.WordTrace]
  refine ⟨207580989134178578918473937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138387326089452385945649291 207580989134178578918473937)
  ·
    refine ⟨155685741850633934188855453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207580989134178578918473937 155685741850633934188855453)
    ·
      refine ⟨58382153193987725320820795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155685741850633934188855453 58382153193987725320820795)
      ·
        refine ⟨87573229790981587981231193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58382153193987725320820795 87573229790981587981231193)
        ·
          refine ⟨65679922343236190985923395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87573229790981587981231193 65679922343236190985923395)
          ·
            refine ⟨98519883514854286478885093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65679922343236190985923395 98519883514854286478885093)
            ·
              refine ⟨18472478159035178714790955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98519883514854286478885093 18472478159035178714790955)
              ·
                refine ⟨27708717238552768072186433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18472478159035178714790955 27708717238552768072186433)
                ·
                  refine ⟨20781537928914576054139825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27708717238552768072186433 20781537928914576054139825)
                  ·
                    refine ⟨15586153446685932040604869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20781537928914576054139825 15586153446685932040604869)
                    ·
                      refine ⟨2922403771253612257613413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15586153446685932040604869 2922403771253612257613413)
                      ·
                        rfl

theorem cell23_5691361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_5691361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691361 prefixEnd_5691361 := by exact prefixLift 5691361
  have htrace : WordTrace (prefixWord ++ tailWord_5691361) baseStart_5691361 baseEnd_5691361 := by
    simpa [prefixWord, tailWord_5691361, baseEnd_5691361] using wordTrace_append hprefix tailTrace_5691361
  have hstable : (prefixWord ++ tailWord_5691361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691361).length < 2 ^ (prefixWord ++ tailWord_5691361).sum := by decide
  have hdescent : baseEnd_5691361 < baseStart_5691361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691465 : List Nat := [1, 2, 1, 1, 2, 2, 5, 4, 1, 4]
def baseStart_5691465 : Nat := 118140960795 + 5691465 * 2 ^ 59
def prefixEnd_5691465 : Nat := 4983230072969 + 3 ^ 40 * 5691465 * 2
def baseEnd_5691465 : Nat := 974152391080559950237645

theorem tailTrace_5691465 : CollatzResearch.WordTrace tailWord_5691465 prefixEnd_5691465 974152391080559950237645 := by
  unfold tailWord_5691465
  simp only [CollatzResearch.WordTrace]
  refine ⟨207584782325801804680259849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138389854883867869786839899 207584782325801804680259849)
  ·
    refine ⟨155688586744351353510194887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207584782325801804680259849 155688586744351353510194887)
    ·
      refine ⟨233532880116527030265292331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155688586744351353510194887 233532880116527030265292331)
      ·
        refine ⟨350299320174790545397938497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233532880116527030265292331 350299320174790545397938497)
        ·
          refine ⟨262724490131092909048453873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350299320174790545397938497 262724490131092909048453873)
          ·
            refine ⟨197043367598319681786340405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262724490131092909048453873 197043367598319681786340405)
            ·
              refine ⟨18472815712342470167469413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 197043367598319681786340405 18472815712342470167469413)
              ·
                refine ⟨3463652946064213156400515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18472815712342470167469413 3463652946064213156400515)
                ·
                  refine ⟨5195479419096319734600773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3463652946064213156400515 5195479419096319734600773)
                  ·
                    refine ⟨974152391080559950237645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5195479419096319734600773 974152391080559950237645)
                    ·
                      rfl

theorem cell23_5691465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4, 1, 4].length) (baseStart_5691465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691465 prefixEnd_5691465 := by exact prefixLift 5691465
  have htrace : WordTrace (prefixWord ++ tailWord_5691465) baseStart_5691465 baseEnd_5691465 := by
    simpa [prefixWord, tailWord_5691465, baseEnd_5691465] using wordTrace_append hprefix tailTrace_5691465
  have hstable : (prefixWord ++ tailWord_5691465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691465).length < 2 ^ (prefixWord ++ tailWord_5691465).sum := by decide
  have hdescent : baseEnd_5691465 < baseStart_5691465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691486 : List Nat := [4, 4, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_5691486 : Nat := 118140960795 + 5691486 * 2 ^ 59
def prefixEnd_5691486 : Nat := 4983230072969 + 3 ^ 40 * 5691486 * 2
def baseEnd_5691486 : Nat := 974155985445141422850113

theorem tailTrace_5691486 : CollatzResearch.WordTrace tailWord_5691486 prefixEnd_5691486 974155985445141422850113 := by
  unfold tailWord_5691486
  simp only [CollatzResearch.WordTrace]
  refine ⟨25948193532340715658346789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138390365505817150177849541 25948193532340715658346789)
  ·
    refine ⟨4865286287313884185940023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25948193532340715658346789 4865286287313884185940023)
    ·
      refine ⟨7297929430970826278910035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4865286287313884185940023 7297929430970826278910035)
      ·
        refine ⟨10946894146456239418365053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7297929430970826278910035 10946894146456239418365053)
        ·
          refine ⟨4105085304921089781886895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10946894146456239418365053 4105085304921089781886895)
          ·
            refine ⟨6157627957381634672830343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4105085304921089781886895 6157627957381634672830343)
            ·
              refine ⟨9236441936072452009245515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6157627957381634672830343 9236441936072452009245515)
              ·
                refine ⟨13854662904108678013868273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9236441936072452009245515 13854662904108678013868273)
                ·
                  refine ⟨10390997178081508510401205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13854662904108678013868273 10390997178081508510401205)
                  ·
                    refine ⟨974155985445141422850113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10390997178081508510401205 974155985445141422850113)
                    ·
                      rfl

theorem cell23_5691486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_5691486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691486 prefixEnd_5691486 := by exact prefixLift 5691486
  have htrace : WordTrace (prefixWord ++ tailWord_5691486) baseStart_5691486 baseEnd_5691486 := by
    simpa [prefixWord, tailWord_5691486, baseEnd_5691486] using wordTrace_append hprefix tailTrace_5691486
  have hstable : (prefixWord ++ tailWord_5691486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691486).length < 2 ^ (prefixWord ++ tailWord_5691486).sum := by decide
  have hdescent : baseEnd_5691486 < baseStart_5691486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691548 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_5691548 : Nat := 118140960795 + 5691548 * 2 ^ 59
def prefixEnd_5691548 : Nat := 4983230072969 + 3 ^ 40 * 5691548 * 2
def baseEnd_5691548 : Nat := 2922499792136003025975053

theorem tailTrace_5691548 : CollatzResearch.WordTrace tailWord_5691548 prefixEnd_5691548 2922499792136003025975053 := by
  unfold tailWord_5691548
  simp only [CollatzResearch.WordTrace]
  refine ⟨103793904792250554927765649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138391873056334073237020865 103793904792250554927765649)
  ·
    refine ⟨77845428594187916195824237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103793904792250554927765649 77845428594187916195824237)
    ·
      refine ⟨29192035722820468573434089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77845428594187916195824237 29192035722820468573434089)
      ·
        refine ⟨21894026792115351430075567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29192035722820468573434089 21894026792115351430075567)
        ·
          refine ⟨32841040188173027145113351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21894026792115351430075567 32841040188173027145113351)
          ·
            refine ⟨49261560282259540717670027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32841040188173027145113351 49261560282259540717670027)
            ·
              refine ⟨73892340423389311076505041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49261560282259540717670027 73892340423389311076505041)
              ·
                refine ⟨55419255317541983307378781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73892340423389311076505041 55419255317541983307378781)
                ·
                  refine ⟨20782220744078243740267043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55419255317541983307378781 20782220744078243740267043)
                  ·
                    refine ⟨31173331116117365610400565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20782220744078243740267043 31173331116117365610400565)
                    ·
                      refine ⟨2922499792136003025975053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31173331116117365610400565 2922499792136003025975053)
                      ·
                        rfl

theorem cell23_5691548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_5691548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691548 prefixEnd_5691548 := by exact prefixLift 5691548
  have htrace : WordTrace (prefixWord ++ tailWord_5691548) baseStart_5691548 baseEnd_5691548 := by
    simpa [prefixWord, tailWord_5691548, baseEnd_5691548] using wordTrace_append hprefix tailTrace_5691548
  have hstable : (prefixWord ++ tailWord_5691548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691548).length < 2 ^ (prefixWord ++ tailWord_5691548).sum := by decide
  have hdescent : baseEnd_5691548 < baseStart_5691548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691556 : List Nat := [2, 3, 1, 2, 4, 2, 1, 3, 1, 1, 3]
def baseStart_5691556 : Nat := 118140960795 + 5691556 * 2 ^ 59
def prefixEnd_5691556 : Nat := 4983230072969 + 3 ^ 40 * 5691556 * 2
def baseEnd_5691556 : Nat := 2922503899981238994675017

theorem tailTrace_5691556 : CollatzResearch.WordTrace tailWord_5691556 prefixEnd_5691556 2922503899981238994675017 := by
  unfold tailWord_5691556
  simp only [CollatzResearch.WordTrace]
  refine ⟨103794050684236063610911261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138392067578981418147881681 103794050684236063610911261)
  ·
    refine ⟨38922769006588523854091723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103794050684236063610911261 38922769006588523854091723)
    ·
      refine ⟨58384153509882785781137585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38922769006588523854091723 58384153509882785781137585)
      ·
        refine ⟨43788115132412089335853189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58384153509882785781137585 43788115132412089335853189)
        ·
          refine ⟨8210271587327266750472473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43788115132412089335853189 8210271587327266750472473)
          ·
            refine ⟨6157703690495450062854355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8210271587327266750472473 6157703690495450062854355)
            ·
              refine ⟨9236555535743175094281533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6157703690495450062854355 9236555535743175094281533)
              ·
                refine ⟨3463708325903690660355575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9236555535743175094281533 3463708325903690660355575)
                ·
                  refine ⟨5195562488855535990533363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3463708325903690660355575 5195562488855535990533363)
                  ·
                    refine ⟨7793343733283303985800045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5195562488855535990533363 7793343733283303985800045)
                    ·
                      refine ⟨2922503899981238994675017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7793343733283303985800045 2922503899981238994675017)
                      ·
                        rfl

theorem cell23_5691556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_5691556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691556 prefixEnd_5691556 := by exact prefixLift 5691556
  have htrace : WordTrace (prefixWord ++ tailWord_5691556) baseStart_5691556 baseEnd_5691556 := by
    simpa [prefixWord, tailWord_5691556, baseEnd_5691556] using wordTrace_append hprefix tailTrace_5691556
  have hstable : (prefixWord ++ tailWord_5691556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691556).length < 2 ^ (prefixWord ++ tailWord_5691556).sum := by decide
  have hdescent : baseEnd_5691556 < baseStart_5691556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691565 : List Nat := [1, 5, 2, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_5691565 : Nat := 118140960795 + 5691565 * 2 ^ 59
def prefixEnd_5691565 : Nat := 4983230072969 + 3 ^ 40 * 5691565 * 2
def baseEnd_5691565 : Nat := 2922508521307129459462475

theorem tailTrace_5691565 : CollatzResearch.WordTrace tailWord_5691565 prefixEnd_5691565 2922508521307129459462475 := by
  unfold tailWord_5691565
  simp only [CollatzResearch.WordTrace]
  refine ⟨207588429625439521758900149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138392286416959681172600099 207588429625439521758900149)
  ·
    refine ⟨19461415277384955164896889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 207588429625439521758900149 19461415277384955164896889)
    ·
      refine ⟨14596061458038716373672667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19461415277384955164896889 14596061458038716373672667)
      ·
        refine ⟨21894092187058074560509001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14596061458038716373672667 21894092187058074560509001)
        ·
          refine ⟨16420569140293555920381751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21894092187058074560509001 16420569140293555920381751)
          ·
            refine ⟨24630853710440333880572627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16420569140293555920381751 24630853710440333880572627)
            ·
              refine ⟨36946280565660500820858941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24630853710440333880572627 36946280565660500820858941)
              ·
                refine ⟨13854855212122687807822103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36946280565660500820858941 13854855212122687807822103)
                ·
                  refine ⟨20782282818184031711733155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13854855212122687807822103 20782282818184031711733155)
                  ·
                    refine ⟨31173424227276047567599733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20782282818184031711733155 31173424227276047567599733)
                    ·
                      refine ⟨2922508521307129459462475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31173424227276047567599733 2922508521307129459462475)
                      ·
                        rfl

theorem cell23_5691565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_5691565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691565 prefixEnd_5691565 := by exact prefixLift 5691565
  have htrace : WordTrace (prefixWord ++ tailWord_5691565) baseStart_5691565 baseEnd_5691565 := by
    simpa [prefixWord, tailWord_5691565, baseEnd_5691565] using wordTrace_append hprefix tailTrace_5691565
  have hstable : (prefixWord ++ tailWord_5691565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691565).length < 2 ^ (prefixWord ++ tailWord_5691565).sum := by decide
  have hdescent : baseEnd_5691565 < baseStart_5691565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691566 : List Nat := [4, 1, 4, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_5691566 : Nat := 118140960795 + 5691566 * 2 ^ 59
def prefixEnd_5691566 : Nat := 4983230072969 + 3 ^ 40 * 5691566 * 2
def baseEnd_5691566 : Nat := 2922509034787783955549971

theorem tailTrace_5691566 : CollatzResearch.WordTrace tailWord_5691566 prefixEnd_5691566 2922509034787783955549971 := by
  unfold tailWord_5691566
  simp only [CollatzResearch.WordTrace]
  refine ⟨25948558262304487366210819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138392310732290599286457701 25948558262304487366210819)
  ·
    refine ⟨38922837393456731049316229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25948558262304487366210819 38922837393456731049316229)
    ·
      refine ⟨7298032011273137071746793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38922837393456731049316229 7298032011273137071746793)
      ·
        refine ⟨5473524008454852803810095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7298032011273137071746793 5473524008454852803810095)
        ·
          refine ⟨8210286012682279205715143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5473524008454852803810095 8210286012682279205715143)
          ·
            refine ⟨12315429019023418808572715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8210286012682279205715143 12315429019023418808572715)
            ·
              refine ⟨18473143528535128212859073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12315429019023418808572715 18473143528535128212859073)
              ·
                refine ⟨13854857646401346159644305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18473143528535128212859073 13854857646401346159644305)
                ·
                  refine ⟨10391143234801009619733229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13854857646401346159644305 10391143234801009619733229)
                  ·
                    refine ⟨3896678713050378607399961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10391143234801009619733229 3896678713050378607399961)
                    ·
                      refine ⟨2922509034787783955549971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3896678713050378607399961 2922509034787783955549971)
                      ·
                        rfl

theorem cell23_5691566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_5691566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691566 prefixEnd_5691566 := by exact prefixLift 5691566
  have htrace : WordTrace (prefixWord ++ tailWord_5691566) baseStart_5691566 baseEnd_5691566 := by
    simpa [prefixWord, tailWord_5691566, baseEnd_5691566] using wordTrace_append hprefix tailTrace_5691566
  have hstable : (prefixWord ++ tailWord_5691566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691566).length < 2 ^ (prefixWord ++ tailWord_5691566).sum := by decide
  have hdescent : baseEnd_5691566 < baseStart_5691566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691573 : List Nat := [1, 3, 3, 4, 1, 1, 3, 2, 1, 1, 3]
def baseStart_5691573 : Nat := 118140960795 + 5691573 * 2 ^ 59
def prefixEnd_5691573 : Nat := 4983230072969 + 3 ^ 40 * 5691573 * 2
def baseEnd_5691573 : Nat := 2922512629152365428162439

theorem tailTrace_5691573 : CollatzResearch.WordTrace tailWord_5691573 prefixEnd_5691573 2922512629152365428162439 := by
  unfold tailWord_5691573
  simp only [CollatzResearch.WordTrace]
  refine ⟨207588721409410539125191373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138392480939607026083460915 207588721409410539125191373)
  ·
    refine ⟨77845770528528952171946765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207588721409410539125191373 77845770528528952171946765)
    ·
      refine ⟨29192163948198357064480037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77845770528528952171946765 29192163948198357064480037)
      ·
        refine ⟨5473530740287191949590007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29192163948198357064480037 5473530740287191949590007)
        ·
          refine ⟨8210296110430787924385011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5473530740287191949590007 8210296110430787924385011)
          ·
            refine ⟨12315444165646181886577517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8210296110430787924385011 12315444165646181886577517)
            ·
              refine ⟨4618291562117318207466569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12315444165646181886577517 4618291562117318207466569)
              ·
                refine ⟨3463718671587988655599927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4618291562117318207466569 3463718671587988655599927)
                ·
                  refine ⟨5195578007381982983399891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3463718671587988655599927 5195578007381982983399891)
                  ·
                    refine ⟨7793367011072974475099837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5195578007381982983399891 7793367011072974475099837)
                    ·
                      refine ⟨2922512629152365428162439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7793367011072974475099837 2922512629152365428162439)
                      ·
                        rfl

theorem cell23_5691573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_5691573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691573 prefixEnd_5691573 := by exact prefixLift 5691573
  have htrace : WordTrace (prefixWord ++ tailWord_5691573) baseStart_5691573 baseEnd_5691573 := by
    simpa [prefixWord, tailWord_5691573, baseEnd_5691573] using wordTrace_append hprefix tailTrace_5691573
  have hstable : (prefixWord ++ tailWord_5691573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691573).length < 2 ^ (prefixWord ++ tailWord_5691573).sum := by decide
  have hdescent : baseEnd_5691573 < baseStart_5691573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691596 : List Nat := [2, 2, 1, 6, 2, 1, 1, 2, 1, 1, 4]
def baseStart_5691596 : Nat := 118140960795 + 5691596 * 2 ^ 59
def prefixEnd_5691596 : Nat := 4983230072969 + 3 ^ 40 * 5691596 * 2
def baseEnd_5691596 : Nat := 2922524439207418838174833

theorem tailTrace_5691596 : CollatzResearch.WordTrace tailWord_5691596 prefixEnd_5691596 2922524439207418838174833 := by
  unfold tailWord_5691596
  simp only [CollatzResearch.WordTrace]
  refine ⟨103794780144163607026639321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138393040192218142702185761 103794780144163607026639321)
  ·
    refine ⟨77846085108122705269979491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103794780144163607026639321 77846085108122705269979491)
    ·
      refine ⟨116769127662184057904969237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77846085108122705269979491 116769127662184057904969237)
      ·
        refine ⟨5473552859164877714295433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 116769127662184057904969237 5473552859164877714295433)
        ·
          refine ⟨4105164644373658285721575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5473552859164877714295433 4105164644373658285721575)
          ·
            refine ⟨6157746966560487428582363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4105164644373658285721575 6157746966560487428582363)
            ·
              refine ⟨9236620449840731142873545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6157746966560487428582363 9236620449840731142873545)
              ·
                refine ⟨6927465337380548357155159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9236620449840731142873545 6927465337380548357155159)
                ·
                  refine ⟨10391198006070822535732739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6927465337380548357155159 10391198006070822535732739)
                  ·
                    refine ⟨15586797009106233803599109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10391198006070822535732739 15586797009106233803599109)
                    ·
                      refine ⟨2922524439207418838174833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15586797009106233803599109 2922524439207418838174833)
                      ·
                        rfl

theorem cell23_5691596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_5691596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691596 prefixEnd_5691596 := by exact prefixLift 5691596
  have htrace : WordTrace (prefixWord ++ tailWord_5691596) baseStart_5691596 baseEnd_5691596 := by
    simpa [prefixWord, tailWord_5691596, baseEnd_5691596] using wordTrace_append hprefix tailTrace_5691596
  have hstable : (prefixWord ++ tailWord_5691596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691596).length < 2 ^ (prefixWord ++ tailWord_5691596).sum := by decide
  have hdescent : baseEnd_5691596 < baseStart_5691596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691628 : List Nat := [2, 2, 1, 1, 2, 3, 2, 2, 2, 6]
def baseStart_5691628 : Nat := 118140960795 + 5691628 * 2 ^ 59
def prefixEnd_5691628 : Nat := 4983230072969 + 3 ^ 40 * 5691628 * 2
def baseEnd_5691628 : Nat := 974180290196120904324895

theorem tailTrace_5691628 : CollatzResearch.WordTrace tailWord_5691628 prefixEnd_5691628 974180290196120904324895 := by
  unfold tailWord_5691628
  simp only [CollatzResearch.WordTrace]
  refine ⟨103795363712105641759221769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138393818282807522345629025 103795363712105641759221769)
  ·
    refine ⟨77846522784079231319416327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103795363712105641759221769 77846522784079231319416327)
    ·
      refine ⟨116769784176118846979124491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77846522784079231319416327 116769784176118846979124491)
      ·
        refine ⟨175154676264178270468686737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116769784176118846979124491 175154676264178270468686737)
        ·
          refine ⟨131366007198133702851515053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175154676264178270468686737 131366007198133702851515053)
          ·
            refine ⟨49262252699300138569318145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131366007198133702851515053 49262252699300138569318145)
            ·
              refine ⟨36946689524475103926988609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49262252699300138569318145 36946689524475103926988609)
              ·
                refine ⟨27710017143356327945241457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36946689524475103926988609 27710017143356327945241457)
                ·
                  refine ⟨20782512857517245958931093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27710017143356327945241457 20782512857517245958931093)
                  ·
                    refine ⟨974180290196120904324895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20782512857517245958931093 974180290196120904324895)
                    ·
                      rfl

theorem cell23_5691628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 6].length) (baseStart_5691628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691628 prefixEnd_5691628 := by exact prefixLift 5691628
  have htrace : WordTrace (prefixWord ++ tailWord_5691628) baseStart_5691628 baseEnd_5691628 := by
    simpa [prefixWord, tailWord_5691628, baseEnd_5691628] using wordTrace_append hprefix tailTrace_5691628
  have hstable : (prefixWord ++ tailWord_5691628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691628).length < 2 ^ (prefixWord ++ tailWord_5691628).sum := by decide
  have hdescent : baseEnd_5691628 < baseStart_5691628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691635 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 3, 4, 2]
def baseStart_5691635 : Nat := 118140960795 + 5691635 * 2 ^ 59
def prefixEnd_5691635 : Nat := 4983230072969 + 3 ^ 40 * 5691635 * 2
def baseEnd_5691635 : Nat := 2922544464952944185587153

theorem tailTrace_5691635 : CollatzResearch.WordTrace tailWord_5691635 prefixEnd_5691635 2922544464952944185587153 := by
  unfold tailWord_5691635
  simp only [CollatzResearch.WordTrace]
  refine ⟨207590982735185923713948359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138393988490123949142632239 207590982735185923713948359)
  ·
    refine ⟨311386474102778885570922539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207590982735185923713948359 311386474102778885570922539)
    ·
      refine ⟨467079711154168328356383809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311386474102778885570922539 467079711154168328356383809)
      ·
        refine ⟨350309783365626246267287857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 467079711154168328356383809 350309783365626246267287857)
        ·
          refine ⟨262732337524219684700465893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350309783365626246267287857 262732337524219684700465893)
          ·
            refine ⟨49262313285791190881337355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 262732337524219684700465893 49262313285791190881337355)
            ·
              refine ⟨73893469928686786322006033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49262313285791190881337355 73893469928686786322006033)
              ·
                refine ⟨55420102446515089741504525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73893469928686786322006033 55420102446515089741504525)
                ·
                  refine ⟨20782538417443158653064197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55420102446515089741504525 20782538417443158653064197)
                  ·
                    refine ⟨3896725953270592247449537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20782538417443158653064197 3896725953270592247449537)
                    ·
                      refine ⟨2922544464952944185587153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3896725953270592247449537 2922544464952944185587153)
                      ·
                        rfl

theorem cell23_5691635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 4, 2].length) (baseStart_5691635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691635 prefixEnd_5691635 := by exact prefixLift 5691635
  have htrace : WordTrace (prefixWord ++ tailWord_5691635) baseStart_5691635 baseEnd_5691635 := by
    simpa [prefixWord, tailWord_5691635, baseEnd_5691635] using wordTrace_append hprefix tailTrace_5691635
  have hstable : (prefixWord ++ tailWord_5691635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691635).length < 2 ^ (prefixWord ++ tailWord_5691635).sum := by decide
  have hdescent : baseEnd_5691635 < baseStart_5691635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691648 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 4]
def baseStart_5691648 : Nat := 118140960795 + 5691648 * 2 ^ 59
def prefixEnd_5691648 : Nat := 4983230072969 + 3 ^ 40 * 5691648 * 2
def baseEnd_5691648 : Nat := 2922551140201452634724593

theorem tailTrace_5691648 : CollatzResearch.WordTrace tailWord_5691648 prefixEnd_5691648 2922551140201452634724593 := by
  unfold tailWord_5691648
  simp only [CollatzResearch.WordTrace]
  refine ⟨103795728442069413467085799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138394304589425884622781065 103795728442069413467085799)
  ·
    refine ⟨155693592663104120200628699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103795728442069413467085799 155693592663104120200628699)
    ·
      refine ⟨233540388994656180300943049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155693592663104120200628699 233540388994656180300943049)
      ·
        refine ⟨175155291745992135225707287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233540388994656180300943049 175155291745992135225707287)
        ·
          refine ⟨262732937618988202838560931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175155291745992135225707287 262732937618988202838560931)
          ·
            refine ⟨394099406428482304257841397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262732937618988202838560931 394099406428482304257841397)
            ·
              refine ⟨36946819352670216024172631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 394099406428482304257841397 36946819352670216024172631)
              ·
                refine ⟨55420229029005324036258947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36946819352670216024172631 55420229029005324036258947)
                ·
                  refine ⟨83130343543507986054388421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55420229029005324036258947 83130343543507986054388421)
                  ·
                    refine ⟨15586939414407747385197829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83130343543507986054388421 15586939414407747385197829)
                    ·
                      refine ⟨2922551140201452634724593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15586939414407747385197829 2922551140201452634724593)
                      ·
                        rfl

theorem cell23_5691648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_5691648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691648 prefixEnd_5691648 := by exact prefixLift 5691648
  have htrace : WordTrace (prefixWord ++ tailWord_5691648) baseStart_5691648 baseEnd_5691648 := by
    simpa [prefixWord, tailWord_5691648, baseEnd_5691648] using wordTrace_append hprefix tailTrace_5691648
  have hstable : (prefixWord ++ tailWord_5691648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691648).length < 2 ^ (prefixWord ++ tailWord_5691648).sum := by decide
  have hdescent : baseEnd_5691648 < baseStart_5691648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691658 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 9]
def baseStart_5691658 : Nat := 118140960795 + 5691658 * 2 ^ 59
def prefixEnd_5691658 : Nat := 4983230072969 + 3 ^ 40 * 5691658 * 2
def baseEnd_5691658 : Nat := 324728475000888621733283

theorem tailTrace_5691658 : CollatzResearch.WordTrace tailWord_5691658 prefixEnd_5691658 324728475000888621733283 := by
  unfold tailWord_5691658
  simp only [CollatzResearch.WordTrace]
  refine ⟨51897955403525649660508907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138394547742735065761357085 51897955403525649660508907)
  ·
    refine ⟨77846933105288474490763361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51897955403525649660508907 77846933105288474490763361)
    ·
      refine ⟨58385199828966355868072521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77846933105288474490763361 58385199828966355868072521)
      ·
        refine ⟨43788899871724766901054391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58385199828966355868072521 43788899871724766901054391)
        ·
          refine ⟨65683349807587150351581587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43788899871724766901054391 65683349807587150351581587)
          ·
            refine ⟨98525024711380725527372381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65683349807587150351581587 98525024711380725527372381)
            ·
              refine ⟨36946884266767772072764643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98525024711380725527372381 36946884266767772072764643)
              ·
                refine ⟨55420326400151658109146965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36946884266767772072764643 55420326400151658109146965)
                ·
                  refine ⟨324728475000888621733283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55420326400151658109146965 324728475000888621733283)
                  ·
                    rfl

theorem cell23_5691658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 9].length) (baseStart_5691658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691658 prefixEnd_5691658 := by exact prefixLift 5691658
  have htrace : WordTrace (prefixWord ++ tailWord_5691658) baseStart_5691658 baseEnd_5691658 := by
    simpa [prefixWord, tailWord_5691658, baseEnd_5691658] using wordTrace_append hprefix tailTrace_5691658
  have hstable : (prefixWord ++ tailWord_5691658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691658).length < 2 ^ (prefixWord ++ tailWord_5691658).sum := by decide
  have hdescent : baseEnd_5691658 < baseStart_5691658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691675 : List Nat := [1, 1, 1, 1, 1, 1, 7, 5, 5]
def baseStart_5691675 : Nat := 118140960795 + 5691675 * 2 ^ 59
def prefixEnd_5691675 : Nat := 4983230072969 + 3 ^ 40 * 5691675 * 2
def baseEnd_5691675 : Nat := 324729444908791558787441

theorem tailTrace_5691675 : CollatzResearch.WordTrace tailWord_5691675 prefixEnd_5691675 324729444908791558787441 := by
  unfold tailWord_5691675
  simp only [CollatzResearch.WordTrace]
  refine ⟨207592441655041010545404479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138394961103360673696936319 207592441655041010545404479)
  ·
    refine ⟨311388662482561515818106719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207592441655041010545404479 311388662482561515818106719)
    ·
      refine ⟨467082993723842273727160079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311388662482561515818106719 467082993723842273727160079)
      ·
        refine ⟨700624490585763410590740119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467082993723842273727160079 700624490585763410590740119)
        ·
          refine ⟨1050936735878645115886110179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 700624490585763410590740119 1050936735878645115886110179)
          ·
            refine ⟨1576405103817967673829165269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1050936735878645115886110179 1576405103817967673829165269)
            ·
              refine ⟨36946994620733617355371061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1576405103817967673829165269 36946994620733617355371061)
              ·
                refine ⟨3463780745693776627066037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36946994620733617355371061 3463780745693776627066037)
                ·
                  refine ⟨324729444908791558787441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3463780745693776627066037 324729444908791558787441)
                  ·
                    rfl

theorem cell23_5691675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5, 5].length) (baseStart_5691675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691675 prefixEnd_5691675 := by exact prefixLift 5691675
  have htrace : WordTrace (prefixWord ++ tailWord_5691675) baseStart_5691675 baseEnd_5691675 := by
    simpa [prefixWord, tailWord_5691675, baseEnd_5691675] using wordTrace_append hprefix tailTrace_5691675
  have hstable : (prefixWord ++ tailWord_5691675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691675).length < 2 ^ (prefixWord ++ tailWord_5691675).sum := by decide
  have hdescent : baseEnd_5691675 < baseStart_5691675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691695 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 1, 7, 2]
def baseStart_5691695 : Nat := 118140960795 + 5691695 * 2 ^ 59
def prefixEnd_5691695 : Nat := 4983230072969 + 3 ^ 40 * 5691695 * 2
def baseEnd_5691695 : Nat := 2922575273792213950836877

theorem tailTrace_5691695 : CollatzResearch.WordTrace tailWord_5691695 prefixEnd_5691695 2922575273792213950836877 := by
  unfold tailWord_5691695
  simp only [CollatzResearch.WordTrace]
  refine ⟨207593171114968553961132539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138395447409979035974088359 207593171114968553961132539)
  ·
    refine ⟨311389756672452830941698809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207593171114968553961132539 311389756672452830941698809)
    ·
      refine ⟨233542317504339623206274107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311389756672452830941698809 233542317504339623206274107)
      ·
        refine ⟨350313476256509434809411161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233542317504339623206274107 350313476256509434809411161)
        ·
          refine ⟨262735107192382076107058371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350313476256509434809411161 262735107192382076107058371)
          ·
            refine ⟨394102660788573114160587557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262735107192382076107058371 394102660788573114160587557)
            ·
              refine ⟨73894248897857458905110167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 394102660788573114160587557 73894248897857458905110167)
              ·
                refine ⟨110841373346786188357665251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73894248897857458905110167 110841373346786188357665251)
                ·
                  refine ⟨166262060020179282536497877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110841373346786188357665251 166262060020179282536497877)
                  ·
                    refine ⟨3896767031722951934449169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 166262060020179282536497877 3896767031722951934449169)
                    ·
                      refine ⟨2922575273792213950836877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3896767031722951934449169 2922575273792213950836877)
                      ·
                        rfl

theorem cell23_5691695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 7, 2].length) (baseStart_5691695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691695 prefixEnd_5691695 := by exact prefixLift 5691695
  have htrace : WordTrace (prefixWord ++ tailWord_5691695) baseStart_5691695 baseEnd_5691695 := by
    simpa [prefixWord, tailWord_5691695, baseEnd_5691695] using wordTrace_append hprefix tailTrace_5691695
  have hstable : (prefixWord ++ tailWord_5691695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691695).length < 2 ^ (prefixWord ++ tailWord_5691695).sum := by decide
  have hdescent : baseEnd_5691695 < baseStart_5691695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691705 : List Nat := [1, 2, 1, 6, 1, 1, 1, 2, 1, 7]
def baseStart_5691705 : Nat := 118140960795 + 5691705 * 2 ^ 59
def prefixEnd_5691705 : Nat := 4983230072969 + 3 ^ 40 * 5691705 * 2
def baseEnd_5691705 : Nat := 974193469532919637237277

theorem tailTrace_5691705 : CollatzResearch.WordTrace tailWord_5691705 prefixEnd_5691705 974193469532919637237277 := by
  unfold tailWord_5691705
  simp only [CollatzResearch.WordTrace]
  refine ⟨207593535844932325668996569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138395690563288217112664379 207593535844932325668996569)
  ·
    refine ⟨155695151883699244251747427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207593535844932325668996569 155695151883699244251747427)
    ·
      refine ⟨233542727825548866377621141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155695151883699244251747427 233542727825548866377621141)
      ·
        refine ⟨10947315366822603111450991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 233542727825548866377621141 10947315366822603111450991)
        ·
          refine ⟨16420973050233904667176487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10947315366822603111450991 16420973050233904667176487)
          ·
            refine ⟨24631459575350857000764731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16420973050233904667176487 24631459575350857000764731)
            ·
              refine ⟨36947189363026285501147097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24631459575350857000764731 36947189363026285501147097)
              ·
                refine ⟨27710392022269714125860323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36947189363026285501147097 27710392022269714125860323)
                ·
                  refine ⟨41565588033404571188790485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27710392022269714125860323 41565588033404571188790485)
                  ·
                    refine ⟨974193469532919637237277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41565588033404571188790485 974193469532919637237277)
                    ·
                      rfl

theorem cell23_5691705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 7].length) (baseStart_5691705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691705 prefixEnd_5691705 := by exact prefixLift 5691705
  have htrace : WordTrace (prefixWord ++ tailWord_5691705) baseStart_5691705 baseEnd_5691705 := by
    simpa [prefixWord, tailWord_5691705, baseEnd_5691705] using wordTrace_append hprefix tailTrace_5691705
  have hstable : (prefixWord ++ tailWord_5691705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691705).length < 2 ^ (prefixWord ++ tailWord_5691705).sum := by decide
  have hdescent : baseEnd_5691705 < baseStart_5691705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691779 : List Nat := [1, 1, 1, 3, 6, 1, 2, 1, 2, 2, 3]
def baseStart_5691779 : Nat := 118140960795 + 5691779 * 2 ^ 59
def prefixEnd_5691779 : Nat := 4983230072969 + 3 ^ 40 * 5691779 * 2
def baseEnd_5691779 : Nat := 2922618406167191622186491

theorem tailTrace_5691779 : CollatzResearch.WordTrace tailWord_5691779 prefixEnd_5691779 2922618406167191622186491 := by
  unfold tailWord_5691779
  simp only [CollatzResearch.WordTrace]
  refine ⟨207596234846664236307190391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138397489897776157538126927 207596234846664236307190391)
  ·
    refine ⟨311394352269996354460785587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207596234846664236307190391 311394352269996354460785587)
    ·
      refine ⟨467091528404994531691178381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311394352269996354460785587 467091528404994531691178381)
      ·
        refine ⟨175159323151872949384191893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 467091528404994531691178381 175159323151872949384191893)
        ·
          refine ⟨8210593272744044502383995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 175159323151872949384191893 8210593272744044502383995)
          ·
            refine ⟨12315889909116066753575993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8210593272744044502383995 12315889909116066753575993)
            ·
              refine ⟨9236917431837050065181995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12315889909116066753575993 9236917431837050065181995)
              ·
                refine ⟨13855376147755575097772993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9236917431837050065181995 13855376147755575097772993)
                ·
                  refine ⟨10391532110816681323329745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13855376147755575097772993 10391532110816681323329745)
                  ·
                    refine ⟨7793649083112510992497309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10391532110816681323329745 7793649083112510992497309)
                    ·
                      refine ⟨2922618406167191622186491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7793649083112510992497309 2922618406167191622186491)
                      ·
                        rfl

theorem cell23_5691779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 2, 3].length) (baseStart_5691779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691779 prefixEnd_5691779 := by exact prefixLift 5691779
  have htrace : WordTrace (prefixWord ++ tailWord_5691779) baseStart_5691779 baseEnd_5691779 := by
    simpa [prefixWord, tailWord_5691779, baseEnd_5691779] using wordTrace_append hprefix tailTrace_5691779
  have hstable : (prefixWord ++ tailWord_5691779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691779).length < 2 ^ (prefixWord ++ tailWord_5691779).sum := by decide
  have hdescent : baseEnd_5691779 < baseStart_5691779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691832 : List Nat := [2, 1, 2, 1, 2, 2, 1, 6, 1, 1, 4]
def baseStart_5691832 : Nat := 118140960795 + 5691832 * 2 ^ 59
def prefixEnd_5691832 : Nat := 4983230072969 + 3 ^ 40 * 5691832 * 2
def baseEnd_5691832 : Nat := 2922645620641879914823747

theorem tailTrace_5691832 : CollatzResearch.WordTrace tailWord_5691832 prefixEnd_5691832 2922645620641879914823747 := by
  unfold tailWord_5691832
  simp only [CollatzResearch.WordTrace]
  refine ⟨103799083957736113179434875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138398778610314817572579833 103799083957736113179434875)
  ·
    refine ⟨155698625936604169769152313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103799083957736113179434875 155698625936604169769152313)
    ·
      refine ⟨116773969452453127326864235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155698625936604169769152313 116773969452453127326864235)
      ·
        refine ⟨175160954178679690990296353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116773969452453127326864235 175160954178679690990296353)
        ·
          refine ⟨131370715634009768242722265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175160954178679690990296353 131370715634009768242722265)
          ·
            refine ⟨98528036725507326182041699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131370715634009768242722265 98528036725507326182041699)
            ·
              refine ⟨147792055088260989273062549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98528036725507326182041699 147792055088260989273062549)
              ·
                refine ⟨6927752582262233872174807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 147792055088260989273062549 6927752582262233872174807)
                ·
                  refine ⟨10391628873393350808262211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6927752582262233872174807 10391628873393350808262211)
                  ·
                    refine ⟨15587443310090026212393317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10391628873393350808262211 15587443310090026212393317)
                    ·
                      refine ⟨2922645620641879914823747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15587443310090026212393317 2922645620641879914823747)
                      ·
                        rfl

theorem cell23_5691832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 1, 1, 4].length) (baseStart_5691832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691832 prefixEnd_5691832 := by exact prefixLift 5691832
  have htrace : WordTrace (prefixWord ++ tailWord_5691832) baseStart_5691832 baseEnd_5691832 := by
    simpa [prefixWord, tailWord_5691832, baseEnd_5691832] using wordTrace_append hprefix tailTrace_5691832
  have hstable : (prefixWord ++ tailWord_5691832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691832).length < 2 ^ (prefixWord ++ tailWord_5691832).sum := by decide
  have hdescent : baseEnd_5691832 < baseStart_5691832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691835 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 4, 6, 3]
def baseStart_5691835 : Nat := 118140960795 + 5691835 * 2 ^ 59
def prefixEnd_5691835 : Nat := 4983230072969 + 3 ^ 40 * 5691835 * 2
def baseEnd_5691835 : Nat := 2922647161083843403086233

theorem tailTrace_5691835 : CollatzResearch.WordTrace tailWord_5691835 prefixEnd_5691835 2922647161083843403086233 := by
  unfold tailWord_5691835
  simp only [CollatzResearch.WordTrace]
  refine ⟨207598277334461357871228959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138398851556307571914152639 207598277334461357871228959)
  ·
    refine ⟨311397416001692036806843439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207598277334461357871228959 311397416001692036806843439)
    ·
      refine ⟨467096124002538055210265159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311397416001692036806843439 467096124002538055210265159)
      ·
        refine ⟨700644186003807082815397739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467096124002538055210265159 700644186003807082815397739)
        ·
          refine ⟨1050966279005710624223096609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 700644186003807082815397739 1050966279005710624223096609)
          ·
            refine ⟨788224709254282968167322457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1050966279005710624223096609 788224709254282968167322457)
            ·
              refine ⟨591168531940712226125491843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 788224709254282968167322457 591168531940712226125491843)
              ·
                refine ⟨886752797911068339188237765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 591168531940712226125491843 886752797911068339188237765)
                ·
                  refine ⟨166266149608325313597794581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 886752797911068339188237765 166266149608325313597794581)
                  ·
                    refine ⟨7793725762890249074896621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 166266149608325313597794581 7793725762890249074896621)
                    ·
                      refine ⟨2922647161083843403086233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7793725762890249074896621 2922647161083843403086233)
                      ·
                        rfl

theorem cell23_5691835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6, 3].length) (baseStart_5691835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691835 prefixEnd_5691835 := by exact prefixLift 5691835
  have htrace : WordTrace (prefixWord ++ tailWord_5691835) baseStart_5691835 baseEnd_5691835 := by
    simpa [prefixWord, tailWord_5691835, baseEnd_5691835] using wordTrace_append hprefix tailTrace_5691835
  have hstable : (prefixWord ++ tailWord_5691835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691835).length < 2 ^ (prefixWord ++ tailWord_5691835).sum := by decide
  have hdescent : baseEnd_5691835 < baseStart_5691835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691836 : List Nat := [2, 2, 2, 4, 1, 1, 3, 1, 2, 3, 2]
def baseStart_5691836 : Nat := 118140960795 + 5691836 * 2 ^ 59
def prefixEnd_5691836 : Nat := 4983230072969 + 3 ^ 40 * 5691836 * 2
def baseEnd_5691836 : Nat := 2922647674564497899173729

theorem tailTrace_5691836 : CollatzResearch.WordTrace tailWord_5691836 prefixEnd_5691836 2922647674564497899173729 := by
  unfold tailWord_5691836
  simp only [CollatzResearch.WordTrace]
  refine ⟨103799156903728867521007681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138398875871638490028010241 103799156903728867521007681)
  ·
    refine ⟨77849367677796650640755761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103799156903728867521007681 77849367677796650640755761)
    ·
      refine ⟨58387025758347487980566821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77849367677796650640755761 58387025758347487980566821)
      ·
        refine ⟨10947567329690153996356279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58387025758347487980566821 10947567329690153996356279)
        ·
          refine ⟨16421350994535230994534419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10947567329690153996356279 16421350994535230994534419)
          ·
            refine ⟨24632026491802846491801629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16421350994535230994534419 24632026491802846491801629)
            ·
              refine ⟨9237009934426067434425611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24632026491802846491801629 9237009934426067434425611)
              ·
                refine ⟨13855514901639101151638417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9237009934426067434425611 13855514901639101151638417)
                ·
                  refine ⟨10391636176229325863728813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13855514901639101151638417 10391636176229325863728813)
                  ·
                    refine ⟨3896863566085997198898305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10391636176229325863728813 3896863566085997198898305)
                    ·
                      refine ⟨2922647674564497899173729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3896863566085997198898305 2922647674564497899173729)
                      ·
                        rfl

theorem cell23_5691836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_5691836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691836 prefixEnd_5691836 := by exact prefixLift 5691836
  have htrace : WordTrace (prefixWord ++ tailWord_5691836) baseStart_5691836 baseEnd_5691836 := by
    simpa [prefixWord, tailWord_5691836, baseEnd_5691836] using wordTrace_append hprefix tailTrace_5691836
  have hstable : (prefixWord ++ tailWord_5691836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691836).length < 2 ^ (prefixWord ++ tailWord_5691836).sum := by decide
  have hdescent : baseEnd_5691836 < baseStart_5691836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691849 : List Nat := [1, 2, 1, 1, 2, 1, 8, 1, 1, 1, 4]
def baseStart_5691849 : Nat := 118140960795 + 5691849 * 2 ^ 59
def prefixEnd_5691849 : Nat := 4983230072969 + 3 ^ 40 * 5691849 * 2
def baseEnd_5691849 : Nat := 2922654349813006348311169

theorem tailTrace_5691849 : CollatzResearch.WordTrace tailWord_5691849 prefixEnd_5691849 2922654349813006348311169 := by
  unfold tailWord_5691849
  simp only [CollatzResearch.WordTrace]
  refine ⟨207598787956410638262238601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138399191970940425508159067 207598787956410638262238601)
  ·
    refine ⟨155699090967307978696678951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207598787956410638262238601 155699090967307978696678951)
    ·
      refine ⟨233548636450961968045018427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155699090967307978696678951 233548636450961968045018427)
      ·
        refine ⟨350322954676442952067527641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233548636450961968045018427 350322954676442952067527641)
        ·
          refine ⟨262742216007332214050645731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350322954676442952067527641 262742216007332214050645731)
          ·
            refine ⟨394113324010998321075968597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262742216007332214050645731 394113324010998321075968597)
            ·
              refine ⟨4618515515753886575109007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 394113324010998321075968597 4618515515753886575109007)
              ·
                refine ⟨6927773273630829862663511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4618515515753886575109007 6927773273630829862663511)
                ·
                  refine ⟨10391659910446244793995267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6927773273630829862663511 10391659910446244793995267)
                  ·
                    refine ⟨15587489865669367190992901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10391659910446244793995267 15587489865669367190992901)
                    ·
                      refine ⟨2922654349813006348311169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15587489865669367190992901 2922654349813006348311169)
                      ·
                        rfl

theorem cell23_5691849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 8, 1, 1, 1, 4].length) (baseStart_5691849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691849 prefixEnd_5691849 := by exact prefixLift 5691849
  have htrace : WordTrace (prefixWord ++ tailWord_5691849) baseStart_5691849 baseEnd_5691849 := by
    simpa [prefixWord, tailWord_5691849, baseEnd_5691849] using wordTrace_append hprefix tailTrace_5691849
  have hstable : (prefixWord ++ tailWord_5691849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691849).length < 2 ^ (prefixWord ++ tailWord_5691849).sum := by decide
  have hdescent : baseEnd_5691849 < baseStart_5691849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691866 : List Nat := [3, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2]
def baseStart_5691866 : Nat := 118140960795 + 5691866 * 2 ^ 59
def prefixEnd_5691866 : Nat := 4983230072969 + 3 ^ 40 * 5691866 * 2
def baseEnd_5691866 : Nat := 2922663078984132781798591

theorem tailTrace_5691866 : CollatzResearch.WordTrace tailWord_5691866 prefixEnd_5691866 2922663078984132781798591 := by
  unfold tailWord_5691866
  simp only [CollatzResearch.WordTrace]
  refine ⟨51899851999337262541401863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138399605331566033443738301 51899851999337262541401863)
  ·
    refine ⟨77849777999005893812102795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51899851999337262541401863 77849777999005893812102795)
    ·
      refine ⟨116774666998508840718154193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77849777999005893812102795 116774666998508840718154193)
      ·
        refine ⟨87581000248881630538615645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116774666998508840718154193 87581000248881630538615645)
        ·
          refine ⟨32842875093330611451980867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87581000248881630538615645 32842875093330611451980867)
          ·
            refine ⟨49264312639995917177971301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32842875093330611451980867 49264312639995917177971301)
            ·
              refine ⟨9237058619999234470869619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49264312639995917177971301 9237058619999234470869619)
              ·
                refine ⟨13855587929998851706304429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9237058619999234470869619 13855587929998851706304429)
                ·
                  refine ⟨5195845473749569389864161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13855587929998851706304429 5195845473749569389864161)
                  ·
                    refine ⟨3896884105312177042398121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5195845473749569389864161 3896884105312177042398121)
                    ·
                      refine ⟨2922663078984132781798591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3896884105312177042398121 2922663078984132781798591)
                      ·
                        rfl

theorem cell23_5691866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2].length) (baseStart_5691866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691866 prefixEnd_5691866 := by exact prefixLift 5691866
  have htrace : WordTrace (prefixWord ++ tailWord_5691866) baseStart_5691866 baseEnd_5691866 := by
    simpa [prefixWord, tailWord_5691866, baseEnd_5691866] using wordTrace_append hprefix tailTrace_5691866
  have hstable : (prefixWord ++ tailWord_5691866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691866).length < 2 ^ (prefixWord ++ tailWord_5691866).sum := by decide
  have hdescent : baseEnd_5691866 < baseStart_5691866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691886 : List Nat := [4, 1, 2, 1, 2, 3, 2, 2, 1, 2, 3]
def baseStart_5691886 : Nat := 118140960795 + 5691886 * 2 ^ 59
def prefixEnd_5691886 : Nat := 4983230072969 + 3 ^ 40 * 5691886 * 2
def baseEnd_5691886 : Nat := 2922673348597222703548499

theorem tailTrace_5691886 : CollatzResearch.WordTrace tailWord_5691886 prefixEnd_5691886 2922673348597222703548499 := by
  unfold tailWord_5691886
  simp only [CollatzResearch.WordTrace]
  refine ⟨25950017182159574197666939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138400091638184395720890341 25950017182159574197666939)
  ·
    refine ⟨38925025773239361296500409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25950017182159574197666939 38925025773239361296500409)
    ·
      refine ⟨29193769329929520972375307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38925025773239361296500409 29193769329929520972375307)
      ·
        refine ⟨43790653994894281458562961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29193769329929520972375307 43790653994894281458562961)
        ·
          refine ⟨32842990496170711093922221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43790653994894281458562961 32842990496170711093922221)
          ·
            refine ⟨12316121436064016660220833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32842990496170711093922221 12316121436064016660220833)
            ·
              refine ⟨9237091077048012495165625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12316121436064016660220833 9237091077048012495165625)
              ·
                refine ⟨6927818307786009371374219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9237091077048012495165625 6927818307786009371374219)
                ·
                  refine ⟨10391727461679014057061329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6927818307786009371374219 10391727461679014057061329)
                  ·
                    refine ⟨7793795596259260542795997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10391727461679014057061329 7793795596259260542795997)
                    ·
                      refine ⟨2922673348597222703548499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7793795596259260542795997 2922673348597222703548499)
                      ·
                        rfl

theorem cell23_5691886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_5691886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691886 prefixEnd_5691886 := by exact prefixLift 5691886
  have htrace : WordTrace (prefixWord ++ tailWord_5691886) baseStart_5691886 baseEnd_5691886 := by
    simpa [prefixWord, tailWord_5691886, baseEnd_5691886] using wordTrace_append hprefix tailTrace_5691886
  have hstable : (prefixWord ++ tailWord_5691886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691886).length < 2 ^ (prefixWord ++ tailWord_5691886).sum := by decide
  have hdescent : baseEnd_5691886 < baseStart_5691886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691906 : List Nat := [3, 4, 1, 2, 3, 1, 9]
def baseStart_5691906 : Nat := 118140960795 + 5691906 * 2 ^ 59
def prefixEnd_5691906 : Nat := 4983230072969 + 3 ^ 40 * 5691906 * 2
def baseEnd_5691906 : Nat := 36082513805065587966647

theorem tailTrace_5691906 : CollatzResearch.WordTrace tailWord_5691906 prefixEnd_5691906 36082513805065587966647 := by
  unfold tailWord_5691906
  simp only [CollatzResearch.WordTrace]
  refine ⟨51900216729301034249265893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138400577944802757998042381 51900216729301034249265893)
  ·
    refine ⟨9731290636743943921737355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51900216729301034249265893 9731290636743943921737355)
    ·
      refine ⟨14596935955115915882606033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9731290636743943921737355 14596935955115915882606033)
      ·
        refine ⟨10947701966336936911954525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14596935955115915882606033 10947701966336936911954525)
        ·
          refine ⟨4105388237376351341982947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10947701966336936911954525 4105388237376351341982947)
          ·
            refine ⟨6158082356064527012974421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4105388237376351341982947 6158082356064527012974421)
            ·
              refine ⟨36082513805065587966647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6158082356064527012974421 36082513805065587966647)
              ·
                rfl

theorem cell23_5691906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 9].length) (baseStart_5691906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691906 prefixEnd_5691906 := by exact prefixLift 5691906
  have htrace : WordTrace (prefixWord ++ tailWord_5691906) baseStart_5691906 baseEnd_5691906 := by
    simpa [prefixWord, tailWord_5691906, baseEnd_5691906] using wordTrace_append hprefix tailTrace_5691906
  have hstable : (prefixWord ++ tailWord_5691906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691906).length < 2 ^ (prefixWord ++ tailWord_5691906).sum := by decide
  have hdescent : baseEnd_5691906 < baseStart_5691906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691917 : List Nat := [1, 7, 1, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_5691917 : Nat := 118140960795 + 5691917 * 2 ^ 59
def prefixEnd_5691917 : Nat := 4983230072969 + 3 ^ 40 * 5691917 * 2
def baseEnd_5691917 : Nat := 2922689266497512082260857

theorem tailTrace_5691917 : CollatzResearch.WordTrace tailWord_5691917 prefixEnd_5691917 2922689266497512082260857 := by
  unfold tailWord_5691917
  simp only [CollatzResearch.WordTrace]
  refine ⟨207601268120164285875714005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138400845413442857250476003 207601268120164285875714005)
  ·
    refine ⟨4865654721566350450212047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 207601268120164285875714005 4865654721566350450212047)
    ·
      refine ⟨7298482082349525675318071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4865654721566350450212047 7298482082349525675318071)
      ·
        refine ⟨10947723123524288512977107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7298482082349525675318071 10947723123524288512977107)
        ·
          refine ⟨16421584685286432769465661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10947723123524288512977107 16421584685286432769465661)
          ·
            refine ⟨6158094256982412288549623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16421584685286432769465661 6158094256982412288549623)
            ·
              refine ⟨9237141385473618432824435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6158094256982412288549623 9237141385473618432824435)
              ·
                refine ⟨13855712078210427649236653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9237141385473618432824435 13855712078210427649236653)
                ·
                  refine ⟨5195892029328910368463745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13855712078210427649236653 5195892029328910368463745)
                  ·
                    refine ⟨3896919021996682776347809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5195892029328910368463745 3896919021996682776347809)
                    ·
                      refine ⟨2922689266497512082260857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3896919021996682776347809 2922689266497512082260857)
                      ·
                        rfl

theorem cell23_5691917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_5691917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691917 prefixEnd_5691917 := by exact prefixLift 5691917
  have htrace : WordTrace (prefixWord ++ tailWord_5691917) baseStart_5691917 baseEnd_5691917 := by
    simpa [prefixWord, tailWord_5691917, baseEnd_5691917] using wordTrace_append hprefix tailTrace_5691917
  have hstable : (prefixWord ++ tailWord_5691917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691917).length < 2 ^ (prefixWord ++ tailWord_5691917).sum := by decide
  have hdescent : baseEnd_5691917 < baseStart_5691917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691933 : List Nat := [1, 4, 2, 2, 1, 2, 4, 1, 2, 1, 3]
def baseStart_5691933 : Nat := 118140960795 + 5691933 * 2 ^ 59
def prefixEnd_5691933 : Nat := 4983230072969 + 3 ^ 40 * 5691933 * 2
def baseEnd_5691933 : Nat := 2922697482187984019660783

theorem tailTrace_5691933 : CollatzResearch.WordTrace tailWord_5691933 prefixEnd_5691933 2922697482187984019660783 := by
  unfold tailWord_5691933
  simp only [CollatzResearch.WordTrace]
  refine ⟨207601851688106320608296453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138401234458737547072197635 207601851688106320608296453)
  ·
    refine ⟨38925347191519935114055585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207601851688106320608296453 38925347191519935114055585)
    ·
      refine ⟨29194010393639951335541689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38925347191519935114055585 29194010393639951335541689)
      ·
        refine ⟨21895507795229963501656267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29194010393639951335541689 21895507795229963501656267)
        ·
          refine ⟨32843261692844945252484401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21895507795229963501656267 32843261692844945252484401)
          ·
            refine ⟨24632446269633708939363301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32843261692844945252484401 24632446269633708939363301)
            ·
              refine ⟨4618583675556320426130619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24632446269633708939363301 4618583675556320426130619)
              ·
                refine ⟨6927875513334480639195929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4618583675556320426130619 6927875513334480639195929)
                ·
                  refine ⟨5195906635000860479396947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6927875513334480639195929 5195906635000860479396947)
                  ·
                    refine ⟨7793859952501290719095421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5195906635000860479396947 7793859952501290719095421)
                    ·
                      refine ⟨2922697482187984019660783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7793859952501290719095421 2922697482187984019660783)
                      ·
                        rfl

theorem cell23_5691933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_5691933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691933 prefixEnd_5691933 := by exact prefixLift 5691933
  have htrace : WordTrace (prefixWord ++ tailWord_5691933) baseStart_5691933 baseEnd_5691933 := by
    simpa [prefixWord, tailWord_5691933, baseEnd_5691933] using wordTrace_append hprefix tailTrace_5691933
  have hstable : (prefixWord ++ tailWord_5691933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691933).length < 2 ^ (prefixWord ++ tailWord_5691933).sum := by decide
  have hdescent : baseEnd_5691933 < baseStart_5691933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691973 : List Nat := [1, 3, 1, 1, 1, 6, 2, 2, 2, 2, 2]
def baseStart_5691973 : Nat := 118140960795 + 5691973 * 2 ^ 59
def prefixEnd_5691973 : Nat := 4983230072969 + 3 ^ 40 * 5691973 * 2
def baseEnd_5691973 : Nat := 2922718021414163863160599

theorem tailTrace_5691973 : CollatzResearch.WordTrace tailWord_5691973 prefixEnd_5691973 2922718021414163863160599 := by
  unfold tailWord_5691973
  simp only [CollatzResearch.WordTrace]
  refine ⟨207603310607961407439752573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138402207071974271626501715 207603310607961407439752573)
  ·
    refine ⟨77851241477985527789907215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207603310607961407439752573 77851241477985527789907215)
    ·
      refine ⟨116776862216978291684860823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77851241477985527789907215 116776862216978291684860823)
      ·
        refine ⟨175165293325467437527291235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116776862216978291684860823 175165293325467437527291235)
        ·
          refine ⟨262747939988201156290936853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175165293325467437527291235 262747939988201156290936853)
          ·
            refine ⟨12316309686946929201137665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 262747939988201156290936853 12316309686946929201137665)
            ·
              refine ⟨9237232265210196900853249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12316309686946929201137665 9237232265210196900853249)
              ·
                refine ⟨6927924198907647675639937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9237232265210196900853249 6927924198907647675639937)
                ·
                  refine ⟨5195943149180735756729953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6927924198907647675639937 5195943149180735756729953)
                  ·
                    refine ⟨3896957361885551817547465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5195943149180735756729953 3896957361885551817547465)
                    ·
                      refine ⟨2922718021414163863160599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3896957361885551817547465 2922718021414163863160599)
                      ·
                        rfl

theorem cell23_5691973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2, 2, 2].length) (baseStart_5691973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691973 prefixEnd_5691973 := by exact prefixLift 5691973
  have htrace : WordTrace (prefixWord ++ tailWord_5691973) baseStart_5691973 baseEnd_5691973 := by
    simpa [prefixWord, tailWord_5691973, baseEnd_5691973] using wordTrace_append hprefix tailTrace_5691973
  have hstable : (prefixWord ++ tailWord_5691973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691973).length < 2 ^ (prefixWord ++ tailWord_5691973).sum := by decide
  have hdescent : baseEnd_5691973 < baseStart_5691973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5691992 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 4, 5]
def baseStart_5691992 : Nat := 118140960795 + 5691992 * 2 ^ 59
def prefixEnd_5691992 : Nat := 4983230072969 + 3 ^ 40 * 5691992 * 2
def baseEnd_5691992 : Nat := 974242592515533096274337

theorem tailTrace_5691992 : CollatzResearch.WordTrace tailWord_5691992 prefixEnd_5691992 974242592515533096274337 := by
  unfold tailWord_5691992
  simp only [CollatzResearch.WordTrace]
  refine ⟨103802001797446286842347115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138402669063261715789796153 103802001797446286842347115)
  ·
    refine ⟨155703002696169430263520673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103802001797446286842347115 155703002696169430263520673)
    ·
      refine ⟨116777252022127072697640505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155703002696169430263520673 116777252022127072697640505)
      ·
        refine ⟨87582939016595304523230379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116777252022127072697640505 87582939016595304523230379)
        ·
          refine ⟨131374408524892956784845569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87582939016595304523230379 131374408524892956784845569)
          ·
            refine ⟨98530806393669717588634177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131374408524892956784845569 98530806393669717588634177)
            ·
              refine ⟨73898104795252288191475633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98530806393669717588634177 73898104795252288191475633)
              ·
                refine ⟨55423578596439216143606725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73898104795252288191475633 55423578596439216143606725)
                ·
                  refine ⟨10391920986832353026926261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55423578596439216143606725 10391920986832353026926261)
                  ·
                    refine ⟨974242592515533096274337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10391920986832353026926261 974242592515533096274337)
                    ·
                      rfl

theorem cell23_5691992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 4, 5].length) (baseStart_5691992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5691992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5691992 prefixEnd_5691992 := by exact prefixLift 5691992
  have htrace : WordTrace (prefixWord ++ tailWord_5691992) baseStart_5691992 baseEnd_5691992 := by
    simpa [prefixWord, tailWord_5691992, baseEnd_5691992] using wordTrace_append hprefix tailTrace_5691992
  have hstable : (prefixWord ++ tailWord_5691992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5691992).length < 2 ^ (prefixWord ++ tailWord_5691992).sum := by decide
  have hdescent : baseEnd_5691992 < baseStart_5691992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5691992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692046 : List Nat := [4, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2]
def baseStart_5692046 : Nat := 118140960795 + 5692046 * 2 ^ 59
def prefixEnd_5692046 : Nat := 4983230072969 + 3 ^ 40 * 5692046 * 2
def baseEnd_5692046 : Nat := 2922755505501942077547763

theorem tailTrace_5692046 : CollatzResearch.WordTrace tailWord_5692046 prefixEnd_5692046 2922755505501942077547763 := by
  unfold tailWord_5692046
  simp only [CollatzResearch.WordTrace]
  refine ⟨25950746642087117613394999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138403982091131293938106661 25950746642087117613394999)
  ·
    refine ⟨38926119963130676420092499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25950746642087117613394999 38926119963130676420092499)
    ·
      refine ⟨58389179944696014630138749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38926119963130676420092499 58389179944696014630138749)
      ·
        refine ⟨21895942479261005486302031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58389179944696014630138749 21895942479261005486302031)
        ·
          refine ⟨32843913718891508229453047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21895942479261005486302031 32843913718891508229453047)
          ·
            refine ⟨49265870578337262344179571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32843913718891508229453047 49265870578337262344179571)
            ·
              refine ⟨73898805867505893516269357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49265870578337262344179571 73898805867505893516269357)
              ·
                refine ⟨27712052200314710068601009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73898805867505893516269357 27712052200314710068601009)
                ·
                  refine ⟨20784039150236032551450757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27712052200314710068601009 20784039150236032551450757)
                  ·
                    refine ⟨3897007340669256103397017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20784039150236032551450757 3897007340669256103397017)
                    ·
                      refine ⟨2922755505501942077547763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3897007340669256103397017 2922755505501942077547763)
                      ·
                        rfl

theorem cell23_5692046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_5692046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692046 prefixEnd_5692046 := by exact prefixLift 5692046
  have htrace : WordTrace (prefixWord ++ tailWord_5692046) baseStart_5692046 baseEnd_5692046 := by
    simpa [prefixWord, tailWord_5692046, baseEnd_5692046] using wordTrace_append hprefix tailTrace_5692046
  have hstable : (prefixWord ++ tailWord_5692046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692046).length < 2 ^ (prefixWord ++ tailWord_5692046).sum := by decide
  have hdescent : baseEnd_5692046 < baseStart_5692046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692129 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 3, 6]
def baseStart_5692129 : Nat := 118140960795 + 5692129 * 2 ^ 59
def prefixEnd_5692129 : Nat := 4983230072969 + 3 ^ 40 * 5692129 * 2
def baseEnd_5692129 : Nat := 974266041465421750936627

theorem tailTrace_5692129 : CollatzResearch.WordTrace tailWord_5692129 prefixEnd_5692129 974266041465421750936627 := by
  unfold tailWord_5692129
  simp only [CollatzResearch.WordTrace]
  refine ⟨207609000395396246082431441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138406000263597497388287627 207609000395396246082431441)
  ·
    refine ⟨155706750296547184561823581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207609000395396246082431441 155706750296547184561823581)
    ·
      refine ⟨58390031361205194210683843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155706750296547184561823581 58390031361205194210683843)
      ·
        refine ⟨87585047041807791316025765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58390031361205194210683843 87585047041807791316025765)
        ·
          refine ⟨16422196320338960871754831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87585047041807791316025765 16422196320338960871754831)
          ·
            refine ⟨24633294480508441307632247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16422196320338960871754831 24633294480508441307632247)
            ·
              refine ⟨36949941720762661961448371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24633294480508441307632247 36949941720762661961448371)
              ·
                refine ⟨55424912581143992942172557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36949941720762661961448371 55424912581143992942172557)
                ·
                  refine ⟨20784342217928997353314709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55424912581143992942172557 20784342217928997353314709)
                  ·
                    refine ⟨974266041465421750936627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20784342217928997353314709 974266041465421750936627)
                    ·
                      rfl

theorem cell23_5692129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_5692129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692129 prefixEnd_5692129 := by exact prefixLift 5692129
  have htrace : WordTrace (prefixWord ++ tailWord_5692129) baseStart_5692129 baseEnd_5692129 := by
    simpa [prefixWord, tailWord_5692129, baseEnd_5692129] using wordTrace_append hprefix tailTrace_5692129
  have hstable : (prefixWord ++ tailWord_5692129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692129).length < 2 ^ (prefixWord ++ tailWord_5692129).sum := by decide
  have hdescent : baseEnd_5692129 < baseStart_5692129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692133 : List Nat := [1, 3, 1, 4, 1, 3, 3, 1, 1, 5]
def baseStart_5692133 : Nat := 118140960795 + 5692133 * 2 ^ 59
def prefixEnd_5692133 : Nat := 4983230072969 + 3 ^ 40 * 5692133 * 2
def baseEnd_5692133 : Nat := 974266726106294412386621

theorem tailTrace_5692133 : CollatzResearch.WordTrace tailWord_5692133 prefixEnd_5692133 974266726106294412386621 := by
  unfold tailWord_5692133
  simp only [CollatzResearch.WordTrace]
  refine ⟨207609146287381754765577053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138406097524921169843718035 207609146287381754765577053)
  ·
    refine ⟨77853429857768158037091395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207609146287381754765577053 77853429857768158037091395)
    ·
      refine ⟨116780144786652237055637093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77853429857768158037091395 116780144786652237055637093)
      ·
        refine ⟨21896277147497294447931955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116780144786652237055637093 21896277147497294447931955)
        ·
          refine ⟨32844415721245941671897933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21896277147497294447931955 32844415721245941671897933)
          ·
            refine ⟨12316655895467228126961725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32844415721245941671897933 12316655895467228126961725)
            ·
              refine ⟨4618745960800210547610647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12316655895467228126961725 4618745960800210547610647)
              ·
                refine ⟨6928118941200315821415971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4618745960800210547610647 6928118941200315821415971)
                ·
                  refine ⟨10392178411800473732123957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6928118941200315821415971 10392178411800473732123957)
                  ·
                    refine ⟨974266726106294412386621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10392178411800473732123957 974266726106294412386621)
                    ·
                      rfl

theorem cell23_5692133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 1, 5].length) (baseStart_5692133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692133 prefixEnd_5692133 := by exact prefixLift 5692133
  have htrace : WordTrace (prefixWord ++ tailWord_5692133) baseStart_5692133 baseEnd_5692133 := by
    simpa [prefixWord, tailWord_5692133, baseEnd_5692133] using wordTrace_append hprefix tailTrace_5692133
  have hstable : (prefixWord ++ tailWord_5692133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692133).length < 2 ^ (prefixWord ++ tailWord_5692133).sum := by decide
  have hdescent : baseEnd_5692133 < baseStart_5692133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692156 : List Nat := [2, 2, 2, 1, 3, 2, 1, 2, 3, 2, 3]
def baseStart_5692156 : Nat := 118140960795 + 5692156 * 2 ^ 59
def prefixEnd_5692156 : Nat := 4983230072969 + 3 ^ 40 * 5692156 * 2
def baseEnd_5692156 : Nat := 2922811988373936647172257

theorem tailTrace_5692156 : CollatzResearch.WordTrace tailWord_5692156 prefixEnd_5692156 2922811988373936647172257 := by
  unfold tailWord_5692156
  simp only [CollatzResearch.WordTrace]
  refine ⟨103804992583149214846832161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138406656777532286462442881 103804992583149214846832161)
  ·
    refine ⟨77853744437361911135124121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103804992583149214846832161 77853744437361911135124121)
    ·
      refine ⟨58390308328021433351343091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77853744437361911135124121 58390308328021433351343091)
      ·
        refine ⟨87585462492032150027014637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58390308328021433351343091 87585462492032150027014637)
        ·
          refine ⟨32844548434512056260130489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87585462492032150027014637 32844548434512056260130489)
          ·
            refine ⟨24633411325884042195097867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32844548434512056260130489 24633411325884042195097867)
            ·
              refine ⟨36950116988826063292646801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24633411325884042195097867 36950116988826063292646801)
              ·
                refine ⟨27712587741619547469485101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36950116988826063292646801 27712587741619547469485101)
                ·
                  refine ⟨10392220403107330301056913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27712587741619547469485101 10392220403107330301056913)
                  ·
                    refine ⟨7794165302330497725792685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10392220403107330301056913 7794165302330497725792685)
                    ·
                      refine ⟨2922811988373936647172257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7794165302330497725792685 2922811988373936647172257)
                      ·
                        rfl

theorem cell23_5692156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_5692156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692156 prefixEnd_5692156 := by exact prefixLift 5692156
  have htrace : WordTrace (prefixWord ++ tailWord_5692156) baseStart_5692156 baseEnd_5692156 := by
    simpa [prefixWord, tailWord_5692156, baseEnd_5692156] using wordTrace_append hprefix tailTrace_5692156
  have hstable : (prefixWord ++ tailWord_5692156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692156).length < 2 ^ (prefixWord ++ tailWord_5692156).sum := by decide
  have hdescent : baseEnd_5692156 < baseStart_5692156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692186 : List Nat := [3, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3]
def baseStart_5692186 : Nat := 118140960795 + 5692186 * 2 ^ 59
def prefixEnd_5692186 : Nat := 4983230072969 + 3 ^ 40 * 5692186 * 2
def baseEnd_5692186 : Nat := 2922827392793571529797119

theorem tailTrace_5692186 : CollatzResearch.WordTrace tailWord_5692186 prefixEnd_5692186 2922827392793571529797119 := by
  unfold tailWord_5692186
  simp only [CollatzResearch.WordTrace]
  refine ⟨51902769839047436204314103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138407386237459829878170941 51902769839047436204314103)
  ·
    refine ⟨77854154758571154306471155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51902769839047436204314103 77854154758571154306471155)
    ·
      refine ⟨116781232137856731459706733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77854154758571154306471155 116781232137856731459706733)
      ·
        refine ⟨43792962051696274297390025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116781232137856731459706733 43792962051696274297390025)
        ·
          refine ⟨32844721538772205723042519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43792962051696274297390025 32844721538772205723042519)
          ·
            refine ⟨49267082308158308584563779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32844721538772205723042519 49267082308158308584563779)
            ·
              refine ⟨73900623462237462876845669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49267082308158308584563779 73900623462237462876845669)
              ·
                refine ⟨13856366899169524289408563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73900623462237462876845669 13856366899169524289408563)
                ·
                  refine ⟨20784550348754286434112845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13856366899169524289408563 20784550348754286434112845)
                  ·
                    refine ⟨7794206380782857412792317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20784550348754286434112845 7794206380782857412792317)
                    ·
                      refine ⟨2922827392793571529797119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7794206380782857412792317 2922827392793571529797119)
                      ·
                        rfl

theorem cell23_5692186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_5692186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692186 prefixEnd_5692186 := by exact prefixLift 5692186
  have htrace : WordTrace (prefixWord ++ tailWord_5692186) baseStart_5692186 baseEnd_5692186 := by
    simpa [prefixWord, tailWord_5692186, baseEnd_5692186] using wordTrace_append hprefix tailTrace_5692186
  have hstable : (prefixWord ++ tailWord_5692186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692186).length < 2 ^ (prefixWord ++ tailWord_5692186).sum := by decide
  have hdescent : baseEnd_5692186 < baseStart_5692186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692260 : List Nat := [2, 3, 1, 1, 4, 1, 2, 1, 4, 2, 2]
def baseStart_5692260 : Nat := 118140960795 + 5692260 * 2 ^ 59
def prefixEnd_5692260 : Nat := 4983230072969 + 3 ^ 40 * 5692260 * 2
def baseEnd_5692260 : Nat := 2922865390362004240271779

theorem tailTrace_5692260 : CollatzResearch.WordTrace tailWord_5692260 prefixEnd_5692260 2922865390362004240271779 := by
  unfold tailWord_5692260
  simp only [CollatzResearch.WordTrace]
  refine ⟨103806889178960827727725117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138409185571947770303633489 103806889178960827727725117)
  ·
    refine ⟨38927583442110310397896919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103806889178960827727725117 38927583442110310397896919)
    ·
      refine ⟨58391375163165465596845379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38927583442110310397896919 58391375163165465596845379)
      ·
        refine ⟨87587062744748198395268069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58391375163165465596845379 87587062744748198395268069)
        ·
          refine ⟨16422574264640287199112763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87587062744748198395268069 16422574264640287199112763)
          ·
            refine ⟨24633861396960430798669145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16422574264640287199112763 24633861396960430798669145)
            ·
              refine ⟨18475396047720323099001859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24633861396960430798669145 18475396047720323099001859)
              ·
                refine ⟨27713094071580484648502789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18475396047720323099001859 27713094071580484648502789)
                ·
                  refine ⟨5196205138421340871594273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27713094071580484648502789 5196205138421340871594273)
                  ·
                    refine ⟨3897153853816005653695705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5196205138421340871594273 3897153853816005653695705)
                    ·
                      refine ⟨2922865390362004240271779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3897153853816005653695705 2922865390362004240271779)
                      ·
                        rfl

theorem cell23_5692260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 4, 2, 2].length) (baseStart_5692260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692260 prefixEnd_5692260 := by exact prefixLift 5692260
  have htrace : WordTrace (prefixWord ++ tailWord_5692260) baseStart_5692260 baseEnd_5692260 := by
    simpa [prefixWord, tailWord_5692260, baseEnd_5692260] using wordTrace_append hprefix tailTrace_5692260
  have hstable : (prefixWord ++ tailWord_5692260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692260).length < 2 ^ (prefixWord ++ tailWord_5692260).sum := by decide
  have hdescent : baseEnd_5692260 < baseStart_5692260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692277 : List Nat := [1, 3, 4, 1, 1, 3, 1, 3, 2, 2, 2]
def baseStart_5692277 : Nat := 118140960795 + 5692277 * 2 ^ 59
def prefixEnd_5692277 : Nat := 4983230072969 + 3 ^ 40 * 5692277 * 2
def baseEnd_5692277 : Nat := 2922874119533130673759201

theorem tailTrace_5692277 : CollatzResearch.WordTrace tailWord_5692277 prefixEnd_5692277 2922874119533130673759201 := by
  unfold tailWord_5692277
  simp only [CollatzResearch.WordTrace]
  refine ⟨207614398398860067358819085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138409598932573378239212723 207614398398860067358819085)
  ·
    refine ⟨77855399399572525259557157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207614398398860067358819085 77855399399572525259557157)
    ·
      refine ⟨14597887387419848486166967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77855399399572525259557157 14597887387419848486166967)
      ·
        refine ⟨21896831081129772729250451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14597887387419848486166967 21896831081129772729250451)
        ·
          refine ⟨32845246621694659093875677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21896831081129772729250451 32845246621694659093875677)
          ·
            refine ⟨12316967483135497160203379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32845246621694659093875677 12316967483135497160203379)
            ·
              refine ⟨18475451224703245740305069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12316967483135497160203379 18475451224703245740305069)
              ·
                refine ⟨6928294209263717152614401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18475451224703245740305069 6928294209263717152614401)
                ·
                  refine ⟨5196220656947787864460801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6928294209263717152614401 5196220656947787864460801)
                  ·
                    refine ⟨3897165492710840898345601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5196220656947787864460801 3897165492710840898345601)
                    ·
                      refine ⟨2922874119533130673759201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3897165492710840898345601 2922874119533130673759201)
                      ·
                        rfl

theorem cell23_5692277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_5692277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692277 prefixEnd_5692277 := by exact prefixLift 5692277
  have htrace : WordTrace (prefixWord ++ tailWord_5692277) baseStart_5692277 baseEnd_5692277 := by
    simpa [prefixWord, tailWord_5692277, baseEnd_5692277] using wordTrace_append hprefix tailTrace_5692277
  have hstable : (prefixWord ++ tailWord_5692277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692277).length < 2 ^ (prefixWord ++ tailWord_5692277).sum := by decide
  have hdescent : baseEnd_5692277 < baseStart_5692277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692279 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 3, 7]
def baseStart_5692279 : Nat := 118140960795 + 5692279 * 2 ^ 59
def prefixEnd_5692279 : Nat := 4983230072969 + 3 ^ 40 * 5692279 * 2
def baseEnd_5692279 : Nat := 974291715498146555311397

theorem tailTrace_5692279 : CollatzResearch.WordTrace tailWord_5692279 prefixEnd_5692279 974291715498146555311397 := by
  unfold tailWord_5692279
  simp only [CollatzResearch.WordTrace]
  refine ⟨207614471344852821700391891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138409647563235214466927927 207614471344852821700391891)
  ·
    refine ⟨311421707017279232550587837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207614471344852821700391891 311421707017279232550587837)
    ·
      refine ⟨116783140131479712206470439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 311421707017279232550587837 116783140131479712206470439)
      ·
        refine ⟨175174710197219568309705659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116783140131479712206470439 175174710197219568309705659)
        ·
          refine ⟨262762065295829352464558489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175174710197219568309705659 262762065295829352464558489)
          ·
            refine ⟨197071548971872014348418867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262762065295829352464558489 197071548971872014348418867)
            ·
              refine ⟨295607323457808021522628301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197071548971872014348418867 295607323457808021522628301)
              ·
                refine ⟨110852746296678008070985613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 295607323457808021522628301 110852746296678008070985613)
                ·
                  refine ⟨41569779861254253026619605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110852746296678008070985613 41569779861254253026619605)
                  ·
                    refine ⟨974291715498146555311397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41569779861254253026619605 974291715498146555311397)
                    ·
                      rfl

theorem cell23_5692279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_5692279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692279 prefixEnd_5692279 := by exact prefixLift 5692279
  have htrace : WordTrace (prefixWord ++ tailWord_5692279) baseStart_5692279 baseEnd_5692279 := by
    simpa [prefixWord, tailWord_5692279, baseEnd_5692279] using wordTrace_append hprefix tailTrace_5692279
  have hstable : (prefixWord ++ tailWord_5692279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692279).length < 2 ^ (prefixWord ++ tailWord_5692279).sum := by decide
  have hdescent : baseEnd_5692279 < baseStart_5692279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692373 : List Nat := [1, 3, 2, 3, 3, 1, 1, 1, 8]
def baseStart_5692373 : Nat := 118140960795 + 5692373 * 2 ^ 59
def prefixEnd_5692373 : Nat := 4983230072969 + 3 ^ 40 * 5692373 * 2
def baseEnd_5692373 : Nat := 324769268186218033128751

theorem tailTrace_5692373 : CollatzResearch.WordTrace tailWord_5692373 prefixEnd_5692373 324769268186218033128751 := by
  unfold tailWord_5692373
  simp only [CollatzResearch.WordTrace]
  refine ⟨207617899806512275754313773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138411933204341517169542515 207617899806512275754313773)
  ·
    refine ⟨77856712427442103407867665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207617899806512275754313773 77856712427442103407867665)
    ·
      refine ⟨58392534320581577555900749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77856712427442103407867665 58392534320581577555900749)
      ·
        refine ⟨21897200370218091583462781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58392534320581577555900749 21897200370218091583462781)
        ·
          refine ⟨8211450138831784343798543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21897200370218091583462781 8211450138831784343798543)
          ·
            refine ⟨12317175208247676515697815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8211450138831784343798543 12317175208247676515697815)
            ·
              refine ⟨18475762812371514773546723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12317175208247676515697815 18475762812371514773546723)
              ·
                refine ⟨27713644218557272160320085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18475762812371514773546723 27713644218557272160320085)
                ·
                  refine ⟨324769268186218033128751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27713644218557272160320085 324769268186218033128751)
                  ·
                    rfl

theorem cell23_5692373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 8].length) (baseStart_5692373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692373 prefixEnd_5692373 := by exact prefixLift 5692373
  have htrace : WordTrace (prefixWord ++ tailWord_5692373) baseStart_5692373 baseEnd_5692373 := by
    simpa [prefixWord, tailWord_5692373, baseEnd_5692373] using wordTrace_append hprefix tailTrace_5692373
  have hstable : (prefixWord ++ tailWord_5692373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692373).length < 2 ^ (prefixWord ++ tailWord_5692373).sum := by decide
  have hdescent : baseEnd_5692373 < baseStart_5692373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692376 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 1, 2, 6]
def baseStart_5692376 : Nat := 118140960795 + 5692376 * 2 ^ 59
def prefixEnd_5692376 : Nat := 4983230072969 + 3 ^ 40 * 5692376 * 2
def baseEnd_5692376 : Nat := 2922924954117925786421245

theorem tailTrace_5692376 : CollatzResearch.WordTrace tailWord_5692376 prefixEnd_5692376 2922924954117925786421245 := by
  unfold tailWord_5692376
  simp only [CollatzResearch.WordTrace]
  refine ⟨103809004612750703633336491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138412006150334271511115321 103809004612750703633336491)
  ·
    refine ⟨155713506919126055450004737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103809004612750703633336491 155713506919126055450004737)
    ·
      refine ⟨116785130189344541587503553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155713506919126055450004737 116785130189344541587503553)
      ·
        refine ⟨87588847642008406190627665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116785130189344541587503553 87588847642008406190627665)
        ·
          refine ⟨65691635731506304642970749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87588847642008406190627665 65691635731506304642970749)
          ·
            refine ⟨24634363399314864241114031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65691635731506304642970749 24634363399314864241114031)
            ·
              refine ⟨36951545098972296361671047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24634363399314864241114031 36951545098972296361671047)
              ·
                refine ⟨55427317648458444542506571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36951545098972296361671047 55427317648458444542506571)
                ·
                  refine ⟨83140976472687666813759857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55427317648458444542506571 83140976472687666813759857)
                  ·
                    refine ⟨62355732354515750110319893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83140976472687666813759857 62355732354515750110319893)
                    ·
                      refine ⟨2922924954117925786421245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62355732354515750110319893 2922924954117925786421245)
                      ·
                        rfl

theorem cell23_5692376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_5692376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692376 prefixEnd_5692376 := by exact prefixLift 5692376
  have htrace : WordTrace (prefixWord ++ tailWord_5692376) baseStart_5692376 baseEnd_5692376 := by
    simpa [prefixWord, tailWord_5692376, baseEnd_5692376] using wordTrace_append hprefix tailTrace_5692376
  have hstable : (prefixWord ++ tailWord_5692376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692376).length < 2 ^ (prefixWord ++ tailWord_5692376).sum := by decide
  have hdescent : baseEnd_5692376 < baseStart_5692376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692453 : List Nat := [1, 3, 1, 2, 2, 2, 2, 3, 1, 2, 4]
def baseStart_5692453 : Nat := 118140960795 + 5692453 * 2 ^ 59
def prefixEnd_5692453 : Nat := 4983230072969 + 3 ^ 40 * 5692453 * 2
def baseEnd_5692453 : Nat := 2922964492128321985158391

theorem tailTrace_5692453 : CollatzResearch.WordTrace tailWord_5692453 prefixEnd_5692453 2922964492128321985158391 := by
  unfold tailWord_5692453
  simp only [CollatzResearch.WordTrace]
  refine ⟨207620817646222449417226013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138413878430814966278150675 207620817646222449417226013)
  ·
    refine ⟨77857806617333418531459755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207620817646222449417226013 77857806617333418531459755)
    ·
      refine ⟨116786709926000127797189633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77857806617333418531459755 116786709926000127797189633)
      ·
        refine ⟨87590032444500095847892225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116786709926000127797189633 87590032444500095847892225)
        ·
          refine ⟨65692524333375071885919169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87590032444500095847892225 65692524333375071885919169)
          ·
            refine ⟨49269393250031303914439377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65692524333375071885919169 49269393250031303914439377)
            ·
              refine ⟨36952044937523477935829533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49269393250031303914439377 36952044937523477935829533)
              ·
                refine ⟨13857016851571304225936075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36952044937523477935829533 13857016851571304225936075)
                ·
                  refine ⟨20785525277356956338904113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13857016851571304225936075 20785525277356956338904113)
                  ·
                    refine ⟨15589143958017717254178085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20785525277356956338904113 15589143958017717254178085)
                    ·
                      refine ⟨2922964492128321985158391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15589143958017717254178085 2922964492128321985158391)
                      ·
                        rfl

theorem cell23_5692453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_5692453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692453 prefixEnd_5692453 := by exact prefixLift 5692453
  have htrace : WordTrace (prefixWord ++ tailWord_5692453) baseStart_5692453 baseEnd_5692453 := by
    simpa [prefixWord, tailWord_5692453, baseEnd_5692453] using wordTrace_append hprefix tailTrace_5692453
  have hstable : (prefixWord ++ tailWord_5692453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692453).length < 2 ^ (prefixWord ++ tailWord_5692453).sum := by decide
  have hdescent : baseEnd_5692453 < baseStart_5692453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692470 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_5692470 : Nat := 118140960795 + 5692470 * 2 ^ 59
def prefixEnd_5692470 : Nat := 4983230072969 + 3 ^ 40 * 5692470 * 2
def baseEnd_5692470 : Nat := 2922973221299448418645813

theorem tailTrace_5692470 : CollatzResearch.WordTrace tailWord_5692470 prefixEnd_5692470 2922973221299448418645813 := by
  unfold tailWord_5692470
  simp only [CollatzResearch.WordTrace]
  refine ⟨12976339855447553832537179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138414291791440574213729909 12976339855447553832537179)
  ·
    refine ⟨19464509783171330748805769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12976339855447553832537179 19464509783171330748805769)
    ·
      refine ⟨14598382337378498061604327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19464509783171330748805769 14598382337378498061604327)
      ·
        refine ⟨21897573506067747092406491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14598382337378498061604327 21897573506067747092406491)
        ·
          refine ⟨32846360259101620638609737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21897573506067747092406491 32846360259101620638609737)
          ·
            refine ⟨24634770194326215478957303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32846360259101620638609737 24634770194326215478957303)
            ·
              refine ⟨36952155291489323218435955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24634770194326215478957303 36952155291489323218435955)
              ·
                refine ⟨55428232937233984827653933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36952155291489323218435955 55428232937233984827653933)
                ·
                  refine ⟨20785587351462744310370225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55428232937233984827653933 20785587351462744310370225)
                  ·
                    refine ⟨15589190513597058232777669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20785587351462744310370225 15589190513597058232777669)
                    ·
                      refine ⟨2922973221299448418645813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15589190513597058232777669 2922973221299448418645813)
                      ·
                        rfl

theorem cell23_5692470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_5692470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692470 prefixEnd_5692470 := by exact prefixLift 5692470
  have htrace : WordTrace (prefixWord ++ tailWord_5692470) baseStart_5692470 baseEnd_5692470 := by
    simpa [prefixWord, tailWord_5692470, baseEnd_5692470] using wordTrace_append hprefix tailTrace_5692470
  have hstable : (prefixWord ++ tailWord_5692470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692470).length < 2 ^ (prefixWord ++ tailWord_5692470).sum := by decide
  have hdescent : baseEnd_5692470 < baseStart_5692470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692490 : List Nat := [3, 1, 2, 1, 1, 2, 2, 3, 4, 1, 3]
def baseStart_5692490 : Nat := 118140960795 + 5692490 * 2 ^ 59
def prefixEnd_5692490 : Nat := 4983230072969 + 3 ^ 40 * 5692490 * 2
def baseEnd_5692490 : Nat := 2922983490912538340395721

theorem tailTrace_5692490 : CollatzResearch.WordTrace tailWord_5692490 prefixEnd_5692490 2922983490912538340395721 := by
  unfold tailWord_5692490
  simp only [CollatzResearch.WordTrace]
  refine ⟨51905541786772101184080731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138414778098058936490881949 51905541786772101184080731)
  ·
    refine ⟨77858312680158151776121097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51905541786772101184080731 77858312680158151776121097)
    ·
      refine ⟨58393734510118613832090823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77858312680158151776121097 58393734510118613832090823)
      ·
        refine ⟨87590601765177920748136235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58393734510118613832090823 87590601765177920748136235)
        ·
          refine ⟨131385902647766881122204353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87590601765177920748136235 131385902647766881122204353)
          ·
            refine ⟨98539426985825160841653265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131385902647766881122204353 98539426985825160841653265)
            ·
              refine ⟨73904570239368870631239949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98539426985825160841653265 73904570239368870631239949)
              ·
                refine ⟨27714213839763326486714981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73904570239368870631239949 27714213839763326486714981)
                ·
                  refine ⟨5196415094955623716259059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27714213839763326486714981 5196415094955623716259059)
                  ·
                    refine ⟨7794622642433435574388589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5196415094955623716259059 7794622642433435574388589)
                    ·
                      refine ⟨2922983490912538340395721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7794622642433435574388589 2922983490912538340395721)
                      ·
                        rfl

theorem cell23_5692490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_5692490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692490 prefixEnd_5692490 := by exact prefixLift 5692490
  have htrace : WordTrace (prefixWord ++ tailWord_5692490) baseStart_5692490 baseEnd_5692490 := by
    simpa [prefixWord, tailWord_5692490, baseEnd_5692490] using wordTrace_append hprefix tailTrace_5692490
  have hstable : (prefixWord ++ tailWord_5692490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692490).length < 2 ^ (prefixWord ++ tailWord_5692490).sum := by decide
  have hdescent : baseEnd_5692490 < baseStart_5692490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692517 : List Nat := [1, 3, 1, 3, 2, 1, 2, 4, 1, 3, 2]
def baseStart_5692517 : Nat := 118140960795 + 5692517 * 2 ^ 59
def prefixEnd_5692517 : Nat := 4983230072969 + 3 ^ 40 * 5692517 * 2
def baseEnd_5692517 : Nat := 2922997354890209734758097

theorem tailTrace_5692517 : CollatzResearch.WordTrace tailWord_5692517 prefixEnd_5692517 2922997354890209734758097 := by
  unfold tailWord_5692517
  simp only [CollatzResearch.WordTrace]
  refine ⟨207623151917990588347555805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138415434611993725565037203 207623151917990588347555805)
  ·
    refine ⟨77858681969246470630333427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207623151917990588347555805 77858681969246470630333427)
    ·
      refine ⟨116788022953869705945500141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77858681969246470630333427 116788022953869705945500141)
      ·
        refine ⟨43795508607701139729562553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116788022953869705945500141 43795508607701139729562553)
        ·
          refine ⟨32846631455775854797171915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43795508607701139729562553 32846631455775854797171915)
          ·
            refine ⟨49269947183663782195757873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32846631455775854797171915 49269947183663782195757873)
            ·
              refine ⟨36952460387747836646818405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49269947183663782195757873 36952460387747836646818405)
              ·
                refine ⟨6928586322702719371278451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36952460387747836646818405 6928586322702719371278451)
                ·
                  refine ⟨10392879484054079056917677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6928586322702719371278451 10392879484054079056917677)
                  ·
                    refine ⟨3897329806520279646344129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10392879484054079056917677 3897329806520279646344129)
                    ·
                      refine ⟨2922997354890209734758097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3897329806520279646344129 2922997354890209734758097)
                      ·
                        rfl

theorem cell23_5692517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_5692517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692517 prefixEnd_5692517 := by exact prefixLift 5692517
  have htrace : WordTrace (prefixWord ++ tailWord_5692517) baseStart_5692517 baseEnd_5692517 := by
    simpa [prefixWord, tailWord_5692517, baseEnd_5692517] using wordTrace_append hprefix tailTrace_5692517
  have hstable : (prefixWord ++ tailWord_5692517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692517).length < 2 ^ (prefixWord ++ tailWord_5692517).sum := by decide
  have hdescent : baseEnd_5692517 < baseStart_5692517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692534 : List Nat := [5, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2]
def baseStart_5692534 : Nat := 118140960795 + 5692534 * 2 ^ 59
def prefixEnd_5692534 : Nat := 4983230072969 + 3 ^ 40 * 5692534 * 2
def baseEnd_5692534 : Nat := 2923006084061336168245519

theorem tailTrace_5692534 : CollatzResearch.WordTrace tailWord_5692534 prefixEnd_5692534 2923006084061336168245519 := by
  unfold tailWord_5692534
  simp only [CollatzResearch.WordTrace]
  refine ⟨12976485747433062515682791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138415847972619333500616437 12976485747433062515682791)
  ·
    refine ⟨19464728621149593773524187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12976485747433062515682791 19464728621149593773524187)
    ·
      refine ⟨29197092931724390660286281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19464728621149593773524187 29197092931724390660286281)
      ·
        refine ⟨21897819698793292995214711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29197092931724390660286281 21897819698793292995214711)
        ·
          refine ⟨32846729548189939492822067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21897819698793292995214711 32846729548189939492822067)
          ·
            refine ⟨49270094322284909239233101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32846729548189939492822067 49270094322284909239233101)
            ·
              refine ⟨18476285370856840964712413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49270094322284909239233101 18476285370856840964712413)
              ·
                refine ⟨6928607014071315361767155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18476285370856840964712413 6928607014071315361767155)
                ·
                  refine ⟨10392910521106973042650733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6928607014071315361767155 10392910521106973042650733)
                  ·
                    refine ⟨3897341445415114890994025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10392910521106973042650733 3897341445415114890994025)
                    ·
                      refine ⟨2923006084061336168245519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3897341445415114890994025 2923006084061336168245519)
                      ·
                        rfl

theorem cell23_5692534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_5692534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692534 prefixEnd_5692534 := by exact prefixLift 5692534
  have htrace : WordTrace (prefixWord ++ tailWord_5692534) baseStart_5692534 baseEnd_5692534 := by
    simpa [prefixWord, tailWord_5692534, baseEnd_5692534] using wordTrace_append hprefix tailTrace_5692534
  have hstable : (prefixWord ++ tailWord_5692534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692534).length < 2 ^ (prefixWord ++ tailWord_5692534).sum := by decide
  have hdescent : baseEnd_5692534 < baseStart_5692534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692547 : List Nat := [1, 1, 1, 3, 3, 2, 3, 1, 4, 2, 2]
def baseStart_5692547 : Nat := 118140960795 + 5692547 * 2 ^ 59
def prefixEnd_5692547 : Nat := 4983230072969 + 3 ^ 40 * 5692547 * 2
def baseEnd_5692547 : Nat := 2923012759309844617382959

theorem tailTrace_5692547 : CollatzResearch.WordTrace tailWord_5692547 prefixEnd_5692547 2923012759309844617382959 := by
  unfold tailWord_5692547
  simp only [CollatzResearch.WordTrace]
  refine ⟨207624246107881903471147895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138416164071921268980765263 207624246107881903471147895)
  ·
    refine ⟨311436369161822855206721843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207624246107881903471147895 311436369161822855206721843)
    ·
      refine ⟨467154553742734282810082765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311436369161822855206721843 467154553742734282810082765)
      ·
        refine ⟨175182957653525356053781037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 467154553742734282810082765 175182957653525356053781037)
        ·
          refine ⟨65693609120072008520167889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175182957653525356053781037 65693609120072008520167889)
          ·
            refine ⟨49270206840054006390125917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65693609120072008520167889 49270206840054006390125917)
            ·
              refine ⟨18476327565020252396297219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49270206840054006390125917 18476327565020252396297219)
              ·
                refine ⟨27714491347530378594445829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18476327565020252396297219 27714491347530378594445829)
                ·
                  refine ⟨5196467127661945986458593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27714491347530378594445829 5196467127661945986458593)
                  ·
                    refine ⟨3897350345746459489843945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5196467127661945986458593 3897350345746459489843945)
                    ·
                      refine ⟨2923012759309844617382959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3897350345746459489843945 2923012759309844617382959)
                      ·
                        rfl

theorem cell23_5692547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4, 2, 2].length) (baseStart_5692547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692547 prefixEnd_5692547 := by exact prefixLift 5692547
  have htrace : WordTrace (prefixWord ++ tailWord_5692547) baseStart_5692547 baseEnd_5692547 := by
    simpa [prefixWord, tailWord_5692547, baseEnd_5692547] using wordTrace_append hprefix tailTrace_5692547
  have hstable : (prefixWord ++ tailWord_5692547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692547).length < 2 ^ (prefixWord ++ tailWord_5692547).sum := by decide
  have hdescent : baseEnd_5692547 < baseStart_5692547 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692553 : List Nat := [1, 2, 1, 1, 4, 3, 1, 3, 7]
def baseStart_5692553 : Nat := 118140960795 + 5692553 * 2 ^ 59
def prefixEnd_5692553 : Nat := 4983230072969 + 3 ^ 40 * 5692553 * 2
def baseEnd_5692553 : Nat := 324779537799307954878659

theorem tailTrace_5692553 : CollatzResearch.WordTrace tailWord_5692553 prefixEnd_5692553 324779537799307954878659 := by
  unfold tailWord_5692553
  simp only [CollatzResearch.WordTrace]
  refine ⟨207624464945860166495866313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138416309963906777663910875 207624464945860166495866313)
  ·
    refine ⟨155718348709395124871899735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207624464945860166495866313 155718348709395124871899735)
    ·
      refine ⟨233577523064092687307849603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155718348709395124871899735 233577523064092687307849603)
      ·
        refine ⟨350366284596139030961774405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233577523064092687307849603 350366284596139030961774405)
        ·
          refine ⟨65693678361776068305332701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 350366284596139030961774405 65693678361776068305332701)
          ·
            refine ⟨24635129385666025614499763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65693678361776068305332701 24635129385666025614499763)
            ·
              refine ⟨36952694078499038421749645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24635129385666025614499763 36952694078499038421749645)
              ·
                refine ⟨13857260279437139408156117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36952694078499038421749645 13857260279437139408156117)
                ·
                  refine ⟨324779537799307954878659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13857260279437139408156117 324779537799307954878659)
                  ·
                    rfl

theorem cell23_5692553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 7].length) (baseStart_5692553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692553 prefixEnd_5692553 := by exact prefixLift 5692553
  have htrace : WordTrace (prefixWord ++ tailWord_5692553) baseStart_5692553 baseEnd_5692553 := by
    simpa [prefixWord, tailWord_5692553, baseEnd_5692553] using wordTrace_append hprefix tailTrace_5692553
  have hstable : (prefixWord ++ tailWord_5692553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692553).length < 2 ^ (prefixWord ++ tailWord_5692553).sum := by decide
  have hdescent : baseEnd_5692553 < baseStart_5692553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692570 : List Nat := [3, 1, 1, 5, 1, 1, 2, 2, 7]
def baseStart_5692570 : Nat := 118140960795 + 5692570 * 2 ^ 59
def prefixEnd_5692570 : Nat := 4983230072969 + 3 ^ 40 * 5692570 * 2
def baseEnd_5692570 : Nat := 324780507707210891932817

theorem tailTrace_5692570 : CollatzResearch.WordTrace tailWord_5692570 prefixEnd_5692570 324780507707210891932817 := by
  unfold tailWord_5692570
  simp only [CollatzResearch.WordTrace]
  refine ⟨51906271246699644599808791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138416723324532385599490109 51906271246699644599808791)
  ·
    refine ⟨77859406870049466899713187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51906271246699644599808791 77859406870049466899713187)
    ·
      refine ⟨116789110305074200349569781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77859406870049466899713187 116789110305074200349569781)
      ·
        refine ⟨10948979091100706282772167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116789110305074200349569781 10948979091100706282772167)
        ·
          refine ⟨16423468636651059424158251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10948979091100706282772167 16423468636651059424158251)
          ·
            refine ⟨24635202954976589136237377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16423468636651059424158251 24635202954976589136237377)
            ·
              refine ⟨18476402216232441852178033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24635202954976589136237377 18476402216232441852178033)
              ·
                refine ⟨13857301662174331389133525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18476402216232441852178033 13857301662174331389133525)
                ·
                  refine ⟨324780507707210891932817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13857301662174331389133525 324780507707210891932817)
                  ·
                    rfl

theorem cell23_5692570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 7].length) (baseStart_5692570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692570 prefixEnd_5692570 := by exact prefixLift 5692570
  have htrace : WordTrace (prefixWord ++ tailWord_5692570) baseStart_5692570 baseEnd_5692570 := by
    simpa [prefixWord, tailWord_5692570, baseEnd_5692570] using wordTrace_append hprefix tailTrace_5692570
  have hstable : (prefixWord ++ tailWord_5692570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692570).length < 2 ^ (prefixWord ++ tailWord_5692570).sum := by decide
  have hdescent : baseEnd_5692570 < baseStart_5692570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692603 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 4]
def baseStart_5692603 : Nat := 118140960795 + 5692603 * 2 ^ 59
def prefixEnd_5692603 : Nat := 4983230072969 + 3 ^ 40 * 5692603 * 2
def baseEnd_5692603 : Nat := 2923041514226496398282701

theorem tailTrace_5692603 : CollatzResearch.WordTrace tailWord_5692603 prefixEnd_5692603 2923041514226496398282701 := by
  unfold tailWord_5692603
  simp only [CollatzResearch.WordTrace]
  refine ⟨207626288595679025035186463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138417525730452683356790975 207626288595679025035186463)
  ·
    refine ⟨311439432893518537552779695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207626288595679025035186463 311439432893518537552779695)
    ·
      refine ⟨467159149340277806329169543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311439432893518537552779695 467159149340277806329169543)
      ·
        refine ⟨700738724010416709493754315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467159149340277806329169543 700738724010416709493754315)
        ·
          refine ⟨1051108086015625064240631473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 700738724010416709493754315 1051108086015625064240631473)
          ·
            refine ⟨788331064511718798180473605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1051108086015625064240631473 788331064511718798180473605)
            ·
              refine ⟨147812074595947274658838801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 788331064511718798180473605 147812074595947274658838801)
              ·
                refine ⟨110859055946960455994129101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147812074595947274658838801 110859055946960455994129101)
                ·
                  refine ⟨41572145980110170997798413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110859055946960455994129101 41572145980110170997798413)
                  ·
                    refine ⟨15589554742541314124174405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41572145980110170997798413 15589554742541314124174405)
                    ·
                      refine ⟨2923041514226496398282701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15589554742541314124174405 2923041514226496398282701)
                      ·
                        rfl

theorem cell23_5692603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 4].length) (baseStart_5692603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692603 prefixEnd_5692603 := by exact prefixLift 5692603
  have htrace : WordTrace (prefixWord ++ tailWord_5692603) baseStart_5692603 baseEnd_5692603 := by
    simpa [prefixWord, tailWord_5692603, baseEnd_5692603] using wordTrace_append hprefix tailTrace_5692603
  have hstable : (prefixWord ++ tailWord_5692603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692603).length < 2 ^ (prefixWord ++ tailWord_5692603).sum := by decide
  have hdescent : baseEnd_5692603 < baseStart_5692603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692604 : List Nat := [2, 2, 2, 3, 2, 2, 3, 2, 5]
def baseStart_5692604 : Nat := 118140960795 + 5692604 * 2 ^ 59
def prefixEnd_5692604 : Nat := 4983230072969 + 3 ^ 40 * 5692604 * 2
def baseEnd_5692604 : Nat := 324782447523016766041133

theorem tailTrace_5692604 : CollatzResearch.WordTrace tailWord_5692604 prefixEnd_5692604 324782447523016766041133 := by
  unfold tailWord_5692604
  simp only [CollatzResearch.WordTrace]
  refine ⟨103813162534337701102986433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138417550045783601470648577 103813162534337701102986433)
  ·
    refine ⟨77859871900753275827239825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103813162534337701102986433 77859871900753275827239825)
    ·
      refine ⟨58394903925564956870429869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77859871900753275827239825 58394903925564956870429869)
      ·
        refine ⟨21898088972086858826411201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58394903925564956870429869 21898088972086858826411201)
        ·
          refine ⟨16423566729065144119808401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21898088972086858826411201 16423566729065144119808401)
          ·
            refine ⟨12317675046798858089856301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16423566729065144119808401 12317675046798858089856301)
            ·
              refine ⟨4619128142549571783696113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12317675046798858089856301 4619128142549571783696113)
              ·
                refine ⟨3464346106912178837772085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4619128142549571783696113 3464346106912178837772085)
                ·
                  refine ⟨324782447523016766041133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3464346106912178837772085 324782447523016766041133)
                  ·
                    rfl

theorem cell23_5692604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2, 5].length) (baseStart_5692604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692604 prefixEnd_5692604 := by exact prefixLift 5692604
  have htrace : WordTrace (prefixWord ++ tailWord_5692604) baseStart_5692604 baseEnd_5692604 := by
    simpa [prefixWord, tailWord_5692604, baseEnd_5692604] using wordTrace_append hprefix tailTrace_5692604
  have hstable : (prefixWord ++ tailWord_5692604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692604).length < 2 ^ (prefixWord ++ tailWord_5692604).sum := by decide
  have hdescent : baseEnd_5692604 < baseStart_5692604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692633 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 1, 3, 6]
def baseStart_5692633 : Nat := 118140960795 + 5692633 * 2 ^ 59
def prefixEnd_5692633 : Nat := 4983230072969 + 3 ^ 40 * 5692633 * 2
def baseEnd_5692633 : Nat := 2923056918646131280907563

theorem tailTrace_5692633 : CollatzResearch.WordTrace tailWord_5692633 prefixEnd_5692633 2923056918646131280907563 := by
  unfold tailWord_5692633
  simp only [CollatzResearch.WordTrace]
  refine ⟨207627382785570340158778553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138418255190380226772519035 207627382785570340158778553)
  ·
    refine ⟨155720537089177755119083915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207627382785570340158778553 155720537089177755119083915)
    ·
      refine ⟨233580805633766632678625873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155720537089177755119083915 233580805633766632678625873)
      ·
        refine ⟨175185604225324974508969405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233580805633766632678625873 175185604225324974508969405)
        ·
          refine ⟨65694601584496865440863527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175185604225324974508969405 65694601584496865440863527)
          ·
            refine ⟨98541902376745298161295291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65694601584496865440863527 98541902376745298161295291)
            ·
              refine ⟨147812853565117947241942937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98541902376745298161295291 147812853565117947241942937)
              ·
                refine ⟨110859640173838460431457203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147812853565117947241942937 110859640173838460431457203)
                ·
                  refine ⟨166289460260757690647185805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110859640173838460431457203 166289460260757690647185805)
                  ·
                    refine ⟨62358547597784133992694677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 166289460260757690647185805 62358547597784133992694677)
                    ·
                      refine ⟨2923056918646131280907563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62358547597784133992694677 2923056918646131280907563)
                      ·
                        rfl

theorem cell23_5692633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_5692633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692633 prefixEnd_5692633 := by exact prefixLift 5692633
  have htrace : WordTrace (prefixWord ++ tailWord_5692633) baseStart_5692633 baseEnd_5692633 := by
    simpa [prefixWord, tailWord_5692633, baseEnd_5692633] using wordTrace_append hprefix tailTrace_5692633
  have hstable : (prefixWord ++ tailWord_5692633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692633).length < 2 ^ (prefixWord ++ tailWord_5692633).sum := by decide
  have hdescent : baseEnd_5692633 < baseStart_5692633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692663 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 8]
def baseStart_5692663 : Nat := 118140960795 + 5692663 * 2 ^ 59
def prefixEnd_5692663 : Nat := 4983230072969 + 3 ^ 40 * 5692663 * 2
def baseEnd_5692663 : Nat := 2923072323065766163532425

theorem tailTrace_5692663 : CollatzResearch.WordTrace tailWord_5692663 prefixEnd_5692663 2923072323065766163532425 := by
  unfold tailWord_5692663
  simp only [CollatzResearch.WordTrace]
  refine ⟨207628476975461655282370643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138418984650307770188247095 207628476975461655282370643)
  ·
    refine ⟨311442715463192482923555965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207628476975461655282370643 311442715463192482923555965)
    ·
      refine ⟨116791018298697181096333487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 311442715463192482923555965 116791018298697181096333487)
      ·
        refine ⟨175186527448045771644500231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116791018298697181096333487 175186527448045771644500231)
        ·
          refine ⟨262779791172068657466750347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175186527448045771644500231 262779791172068657466750347)
          ·
            refine ⟨394169686758102986200125521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262779791172068657466750347 394169686758102986200125521)
            ·
              refine ⟨295627265068577239650094141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394169686758102986200125521 295627265068577239650094141)
              ·
                refine ⟨110860224400716464868785303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 295627265068577239650094141 110860224400716464868785303)
                ·
                  refine ⟨166290336601074697303177955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110860224400716464868785303 166290336601074697303177955)
                  ·
                    refine ⟨249435504901612045954766933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 166290336601074697303177955 249435504901612045954766933)
                    ·
                      refine ⟨2923072323065766163532425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 249435504901612045954766933 2923072323065766163532425)
                      ·
                        rfl

theorem cell23_5692663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_5692663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692663 prefixEnd_5692663 := by exact prefixLift 5692663
  have htrace : WordTrace (prefixWord ++ tailWord_5692663) baseStart_5692663 baseEnd_5692663 := by
    simpa [prefixWord, tailWord_5692663, baseEnd_5692663] using wordTrace_append hprefix tailTrace_5692663
  have hstable : (prefixWord ++ tailWord_5692663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692663).length < 2 ^ (prefixWord ++ tailWord_5692663).sum := by decide
  have hdescent : baseEnd_5692663 < baseStart_5692663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692707 : List Nat := [1, 1, 1, 4, 2, 4, 1, 3, 1, 5]
def baseStart_5692707 : Nat := 118140960795 + 5692707 * 2 ^ 59
def prefixEnd_5692707 : Nat := 4983230072969 + 3 ^ 40 * 5692707 * 2
def baseEnd_5692707 : Nat := 974364972071521330460741

theorem tailTrace_5692707 : CollatzResearch.WordTrace tailWord_5692707 prefixEnd_5692707 974364972071521330460741 := by
  unfold tailWord_5692707
  simp only [CollatzResearch.WordTrace]
  refine ⟨207630081787302250796972375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138420054524868167197981583 207630081787302250796972375)
  ·
    refine ⟨311445122680953376195458563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207630081787302250796972375 311445122680953376195458563)
    ·
      refine ⟨467167684021430064293187845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311445122680953376195458563 467167684021430064293187845)
      ·
        refine ⟨87593940754018137054972721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 467167684021430064293187845 87593940754018137054972721)
        ·
          refine ⟨65695455565513602791229541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87593940754018137054972721 65695455565513602791229541)
          ·
            refine ⟨12317897918533800523355539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65695455565513602791229541 12317897918533800523355539)
            ·
              refine ⟨18476846877800700785033309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12317897918533800523355539 18476846877800700785033309)
              ·
                refine ⟨6928817579175262794387491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18476846877800700785033309 6928817579175262794387491)
                ·
                  refine ⟨10393226368762894191581237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6928817579175262794387491 10393226368762894191581237)
                  ·
                    refine ⟨974364972071521330460741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10393226368762894191581237 974364972071521330460741)
                    ·
                      rfl

theorem cell23_5692707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 5].length) (baseStart_5692707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692707 prefixEnd_5692707 := by exact prefixLift 5692707
  have htrace : WordTrace (prefixWord ++ tailWord_5692707) baseStart_5692707 baseEnd_5692707 := by
    simpa [prefixWord, tailWord_5692707, baseEnd_5692707] using wordTrace_append hprefix tailTrace_5692707
  have hstable : (prefixWord ++ tailWord_5692707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692707).length < 2 ^ (prefixWord ++ tailWord_5692707).sum := by decide
  have hdescent : baseEnd_5692707 < baseStart_5692707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692721 : List Nat := [1, 2, 2, 3, 3, 1, 2, 4, 1, 1, 3]
def baseStart_5692721 : Nat := 118140960795 + 5692721 * 2 ^ 59
def prefixEnd_5692721 : Nat := 4983230072969 + 3 ^ 40 * 5692721 * 2
def baseEnd_5692721 : Nat := 2923102104943726936607159

theorem tailTrace_5692721 : CollatzResearch.WordTrace tailWord_5692721 prefixEnd_5692721 2923102104943726936607159 := by
  unfold tailWord_5692721
  simp only [CollatzResearch.WordTrace]
  refine ⟨207630592409251531187982017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138420394939501020791988011 207630592409251531187982017)
  ·
    refine ⟨155722944306938648390986513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207630592409251531187982017 155722944306938648390986513)
    ·
      refine ⟨116792208230203986293239885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155722944306938648390986513 116792208230203986293239885)
      ·
        refine ⟨43797078086326494859964957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116792208230203986293239885 43797078086326494859964957)
        ·
          refine ⟨16423904282372435572486859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43797078086326494859964957 16423904282372435572486859)
          ·
            refine ⟨24635856423558653358730289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16423904282372435572486859 24635856423558653358730289)
            ·
              refine ⟨18476892317668990019047717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24635856423558653358730289 18476892317668990019047717)
              ·
                refine ⟨3464417309562935628571447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18476892317668990019047717 3464417309562935628571447)
                ·
                  refine ⟨5196625964344403442857171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3464417309562935628571447 5196625964344403442857171)
                  ·
                    refine ⟨7794938946516605164285757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5196625964344403442857171 7794938946516605164285757)
                    ·
                      refine ⟨2923102104943726936607159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7794938946516605164285757 2923102104943726936607159)
                      ·
                        rfl

theorem cell23_5692721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_5692721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692721 prefixEnd_5692721 := by exact prefixLift 5692721
  have htrace : WordTrace (prefixWord ++ tailWord_5692721) baseStart_5692721 baseEnd_5692721 := by
    simpa [prefixWord, tailWord_5692721, baseEnd_5692721] using wordTrace_append hprefix tailTrace_5692721
  have hstable : (prefixWord ++ tailWord_5692721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692721).length < 2 ^ (prefixWord ++ tailWord_5692721).sum := by decide
  have hdescent : baseEnd_5692721 < baseStart_5692721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692750 : List Nat := [4, 1, 1, 1, 1, 1, 5, 9]
def baseStart_5692750 : Nat := 118140960795 + 5692750 * 2 ^ 59
def prefixEnd_5692750 : Nat := 4983230072969 + 3 ^ 40 * 5692750 * 2
def baseEnd_5692750 : Nat := 108263592440100271227575

theorem tailTrace_5692750 : CollatzResearch.WordTrace tailWord_5692750 prefixEnd_5692750 108263592440100271227575 := by
  unfold tailWord_5692750
  simp only [CollatzResearch.WordTrace]
  refine ⟨25953956265768308642598463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138421100084097646093858469 25953956265768308642598463)
  ·
    refine ⟨38930934398652462963897695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25953956265768308642598463 38930934398652462963897695)
    ·
      refine ⟨58396401597978694445846543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38930934398652462963897695 58396401597978694445846543)
      ·
        refine ⟨87594602396968041668769815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58396401597978694445846543 87594602396968041668769815)
        ·
          refine ⟨131391903595452062503154723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87594602396968041668769815 131391903595452062503154723)
          ·
            refine ⟨197087855393178093754732085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131391903595452062503154723 197087855393178093754732085)
            ·
              refine ⟨18476986443110446289506133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 197087855393178093754732085 18476986443110446289506133)
              ·
                refine ⟨108263592440100271227575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18476986443110446289506133 108263592440100271227575)
                ·
                  rfl

theorem cell23_5692750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 9].length) (baseStart_5692750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692750 prefixEnd_5692750 := by exact prefixLift 5692750
  have htrace : WordTrace (prefixWord ++ tailWord_5692750) baseStart_5692750 baseEnd_5692750 := by
    simpa [prefixWord, tailWord_5692750, baseEnd_5692750] using wordTrace_append hprefix tailTrace_5692750
  have hstable : (prefixWord ++ tailWord_5692750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692750).length < 2 ^ (prefixWord ++ tailWord_5692750).sum := by decide
  have hdescent : baseEnd_5692750 < baseStart_5692750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692765 : List Nat := [1, 4, 5, 1, 1, 1, 1, 2, 2, 3, 2]
def baseStart_5692765 : Nat := 118140960795 + 5692765 * 2 ^ 59
def prefixEnd_5692765 : Nat := 4983230072969 + 3 ^ 40 * 5692765 * 2
def baseEnd_5692765 : Nat := 2923124698092524764456957

theorem tailTrace_5692765 : CollatzResearch.WordTrace tailWord_5692765 prefixEnd_5692765 2923124698092524764456957 := by
  unfold tailWord_5692765
  simp only [CollatzResearch.WordTrace]
  refine ⟨207632197221092126702583749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138421464814061417801722499 207632197221092126702583749)
  ·
    refine ⟨38931036978954773756734453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207632197221092126702583749 38931036978954773756734453)
    ·
      refine ⟨3649784716777010039693855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38931036978954773756734453 3649784716777010039693855)
      ·
        refine ⟨5474677075165515059540783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3649784716777010039693855 5474677075165515059540783)
        ·
          refine ⟨8212015612748272589311175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5474677075165515059540783 8212015612748272589311175)
          ·
            refine ⟨12318023419122408883966763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8212015612748272589311175 12318023419122408883966763)
            ·
              refine ⟨18477035128683613325950145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12318023419122408883966763 18477035128683613325950145)
              ·
                refine ⟨13857776346512709994462609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18477035128683613325950145 13857776346512709994462609)
                ·
                  refine ⟨10393332259884532495846957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13857776346512709994462609 10393332259884532495846957)
                  ·
                    refine ⟨3897499597456699685942609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10393332259884532495846957 3897499597456699685942609)
                    ·
                      refine ⟨2923124698092524764456957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3897499597456699685942609 2923124698092524764456957)
                      ·
                        rfl

theorem cell23_5692765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_5692765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692765 prefixEnd_5692765 := by exact prefixLift 5692765
  have htrace : WordTrace (prefixWord ++ tailWord_5692765) baseStart_5692765 baseEnd_5692765 := by
    simpa [prefixWord, tailWord_5692765, baseEnd_5692765] using wordTrace_append hprefix tailTrace_5692765
  have hstable : (prefixWord ++ tailWord_5692765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692765).length < 2 ^ (prefixWord ++ tailWord_5692765).sum := by decide
  have hdescent : baseEnd_5692765 < baseStart_5692765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692794 : List Nat := [3, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3]
def baseStart_5692794 : Nat := 118140960795 + 5692794 * 2 ^ 59
def prefixEnd_5692794 : Nat := 4983230072969 + 3 ^ 40 * 5692794 * 2
def baseEnd_5692794 : Nat := 2923139589031505150994323

theorem tailTrace_5692794 : CollatzResearch.WordTrace tailWord_5692794 prefixEnd_5692794 2923139589031505150994323 := by
  unfold tailWord_5692794
  simp only [CollatzResearch.WordTrace]
  refine ⟨51908313734496766163847359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138422169958658043103592957 51908313734496766163847359)
  ·
    refine ⟨77862470601745149245771039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51908313734496766163847359 77862470601745149245771039)
    ·
      refine ⟨116793705902617723868656559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77862470601745149245771039 116793705902617723868656559)
      ·
        refine ⟨175190558853926585802984839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116793705902617723868656559 175190558853926585802984839)
        ·
          refine ⟨262785838280889878704477259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175190558853926585802984839 262785838280889878704477259)
          ·
            refine ⟨394178757421334818056715889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262785838280889878704477259 394178757421334818056715889)
            ·
              refine ⟨295634068066001113542536917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394178757421334818056715889 295634068066001113542536917)
              ·
                refine ⟨6928923470296901098653209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 295634068066001113542536917 6928923470296901098653209)
                ·
                  refine ⟨5196692602722675823989907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6928923470296901098653209 5196692602722675823989907)
                  ·
                    refine ⟨7795038904084013735984861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5196692602722675823989907 7795038904084013735984861)
                    ·
                      refine ⟨2923139589031505150994323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7795038904084013735984861 2923139589031505150994323)
                      ·
                        rfl

theorem cell23_5692794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3].length) (baseStart_5692794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692794 prefixEnd_5692794 := by exact prefixLift 5692794
  have htrace : WordTrace (prefixWord ++ tailWord_5692794) baseStart_5692794 baseEnd_5692794 := by
    simpa [prefixWord, tailWord_5692794, baseEnd_5692794] using wordTrace_append hprefix tailTrace_5692794
  have hstable : (prefixWord ++ tailWord_5692794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692794).length < 2 ^ (prefixWord ++ tailWord_5692794).sum := by decide
  have hdescent : baseEnd_5692794 < baseStart_5692794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692798 : List Nat := [4, 2, 3, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_5692798 : Nat := 118140960795 + 5692798 * 2 ^ 59
def prefixEnd_5692798 : Nat := 4983230072969 + 3 ^ 40 * 5692798 * 2
def baseEnd_5692798 : Nat := 2923141642954123135344305

theorem tailTrace_5692798 : CollatzResearch.WordTrace tailWord_5692798 prefixEnd_5692798 2923141642954123135344305 := by
  unfold tailWord_5692798
  simp only [CollatzResearch.WordTrace]
  refine ⟨25954175103746571667316881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138422267219981715559023365 25954175103746571667316881)
  ·
    refine ⟨19465631327809928750487661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25954175103746571667316881 19465631327809928750487661)
    ·
      refine ⟨7299611747928723281432873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19465631327809928750487661 7299611747928723281432873)
      ·
        refine ⟨5474708810946542461074655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7299611747928723281432873 5474708810946542461074655)
        ·
          refine ⟨8212063216419813691611983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5474708810946542461074655 8212063216419813691611983)
          ·
            refine ⟨12318094824629720537417975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8212063216419813691611983 12318094824629720537417975)
            ·
              refine ⟨18477142236944580806126963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12318094824629720537417975 18477142236944580806126963)
              ·
                refine ⟨27715713355416871209190445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18477142236944580806126963 27715713355416871209190445)
                ·
                  refine ⟨10393392508281326703446417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27715713355416871209190445 10393392508281326703446417)
                  ·
                    refine ⟨7795044381210995027584813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10393392508281326703446417 7795044381210995027584813)
                    ·
                      refine ⟨2923141642954123135344305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7795044381210995027584813 2923141642954123135344305)
                      ·
                        rfl

theorem cell23_5692798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_5692798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692798 prefixEnd_5692798 := by exact prefixLift 5692798
  have htrace : WordTrace (prefixWord ++ tailWord_5692798) baseStart_5692798 baseEnd_5692798 := by
    simpa [prefixWord, tailWord_5692798, baseEnd_5692798] using wordTrace_append hprefix tailTrace_5692798
  have hstable : (prefixWord ++ tailWord_5692798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692798).length < 2 ^ (prefixWord ++ tailWord_5692798).sum := by decide
  have hdescent : baseEnd_5692798 < baseStart_5692798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692866 : List Nat := [3, 5, 2, 1, 2, 1, 2, 1, 1, 2, 3]
def baseStart_5692866 : Nat := 118140960795 + 5692866 * 2 ^ 59
def prefixEnd_5692866 : Nat := 4983230072969 + 3 ^ 40 * 5692866 * 2
def baseEnd_5692866 : Nat := 2923176559638628869293993

theorem tailTrace_5692866 : CollatzResearch.WordTrace tailWord_5692866 prefixEnd_5692866 2923176559638628869293993 := by
  unfold tailWord_5692866
  simp only [CollatzResearch.WordTrace]
  refine ⟨51908970248431555238002613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138423920662484147301340301 51908970248431555238002613)
  ·
    refine ⟨4866465960790458303562745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51908970248431555238002613 4866465960790458303562745)
    ·
      refine ⟨3649849470592843727672059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4866465960790458303562745 3649849470592843727672059)
      ·
        refine ⟨5474774205889265591508089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3649849470592843727672059 5474774205889265591508089)
        ·
          refine ⟨4106080654416949193631067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5474774205889265591508089 4106080654416949193631067)
          ·
            refine ⟨6159120981625423790446601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4106080654416949193631067 6159120981625423790446601)
            ·
              refine ⟨4619340736219067842834951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6159120981625423790446601 4619340736219067842834951)
              ·
                refine ⟨6929011104328601764252427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4619340736219067842834951 6929011104328601764252427)
                ·
                  refine ⟨10393516656492902646378641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6929011104328601764252427 10393516656492902646378641)
                  ·
                    refine ⟨7795137492369676984783981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10393516656492902646378641 7795137492369676984783981)
                    ·
                      refine ⟨2923176559638628869293993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7795137492369676984783981 2923176559638628869293993)
                      ·
                        rfl

theorem cell23_5692866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_5692866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692866 prefixEnd_5692866 := by exact prefixLift 5692866
  have htrace : WordTrace (prefixWord ++ tailWord_5692866) baseStart_5692866 baseEnd_5692866 := by
    simpa [prefixWord, tailWord_5692866, baseEnd_5692866] using wordTrace_append hprefix tailTrace_5692866
  have hstable : (prefixWord ++ tailWord_5692866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692866).length < 2 ^ (prefixWord ++ tailWord_5692866).sum := by decide
  have hdescent : baseEnd_5692866 < baseStart_5692866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692874 : List Nat := [3, 1, 2, 1, 2, 3, 1, 5, 5]
def baseStart_5692874 : Nat := 118140960795 + 5692874 * 2 ^ 59
def prefixEnd_5692874 : Nat := 4983230072969 + 3 ^ 40 * 5692874 * 2
def baseEnd_5692874 : Nat := 324797851942651648665995

theorem tailTrace_5692874 : CollatzResearch.WordTrace tailWord_5692874 prefixEnd_5692874 324797851942651648665995 := by
  unfold tailWord_5692874
  simp only [CollatzResearch.WordTrace]
  refine ⟨51909043194424309579575419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138424115185131492212201117 51909043194424309579575419)
  ·
    refine ⟨77863564791636464369363129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51909043194424309579575419 77863564791636464369363129)
    ·
      refine ⟨58397673593727348277022347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77863564791636464369363129 58397673593727348277022347)
      ·
        refine ⟨87596510390591022415533521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58397673593727348277022347 87596510390591022415533521)
        ·
          refine ⟨65697382792943266811650141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87596510390591022415533521 65697382792943266811650141)
          ·
            refine ⟨24636518547353725054368803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65697382792943266811650141 24636518547353725054368803)
            ·
              refine ⟨36954777821030587581553205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24636518547353725054368803 36954777821030587581553205)
              ·
                refine ⟨3464510420721617585770613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36954777821030587581553205 3464510420721617585770613)
                ·
                  refine ⟨324797851942651648665995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3464510420721617585770613 324797851942651648665995)
                  ·
                    rfl

theorem cell23_5692874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5, 5].length) (baseStart_5692874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692874 prefixEnd_5692874 := by exact prefixLift 5692874
  have htrace : WordTrace (prefixWord ++ tailWord_5692874) baseStart_5692874 baseEnd_5692874 := by
    simpa [prefixWord, tailWord_5692874, baseEnd_5692874] using wordTrace_append hprefix tailTrace_5692874
  have hstable : (prefixWord ++ tailWord_5692874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692874).length < 2 ^ (prefixWord ++ tailWord_5692874).sum := by decide
  have hdescent : baseEnd_5692874 < baseStart_5692874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692887 : List Nat := [1, 1, 3, 2, 1, 1, 1, 6, 2, 5]
def baseStart_5692887 : Nat := 118140960795 + 5692887 * 2 ^ 59
def prefixEnd_5692887 : Nat := 4983230072969 + 3 ^ 40 * 5692887 * 2
def baseEnd_5692887 : Nat := 974395780910791095710465

theorem tailTrace_5692887 : CollatzResearch.WordTrace tailWord_5692887 prefixEnd_5692887 974395780910791095710465 := by
  unfold tailWord_5692887
  simp only [CollatzResearch.WordTrace]
  refine ⟨207636646926650141538524915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138424431284433427692349943 207636646926650141538524915)
  ·
    refine ⟨311454970389975212307787373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207636646926650141538524915 311454970389975212307787373)
    ·
      refine ⟨116795613896240704615420265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 311454970389975212307787373 116795613896240704615420265)
      ·
        refine ⟨87596710422180528461565199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116795613896240704615420265 87596710422180528461565199)
        ·
          refine ⟨131395065633270792692347799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87596710422180528461565199 131395065633270792692347799)
          ·
            refine ⟨197092598449906189038521699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131395065633270792692347799 197092598449906189038521699)
            ·
              refine ⟨295638897674859283557782549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197092598449906189038521699 295638897674859283557782549)
              ·
                refine ⟨13858073328509028916771057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 295638897674859283557782549 13858073328509028916771057)
                ·
                  refine ⟨10393554996381771687578293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13858073328509028916771057 10393554996381771687578293)
                  ·
                    refine ⟨974395780910791095710465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10393554996381771687578293 974395780910791095710465)
                    ·
                      rfl

theorem cell23_5692887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 5].length) (baseStart_5692887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692887 prefixEnd_5692887 := by exact prefixLift 5692887
  have htrace : WordTrace (prefixWord ++ tailWord_5692887) baseStart_5692887 baseEnd_5692887 := by
    simpa [prefixWord, tailWord_5692887, baseEnd_5692887] using wordTrace_append hprefix tailTrace_5692887
  have hstable : (prefixWord ++ tailWord_5692887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692887).length < 2 ^ (prefixWord ++ tailWord_5692887).sum := by decide
  have hdescent : baseEnd_5692887 < baseStart_5692887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692907 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 4]
def baseStart_5692907 : Nat := 118140960795 + 5692907 * 2 ^ 59
def prefixEnd_5692907 : Nat := 4983230072969 + 3 ^ 40 * 5692907 * 2
def baseEnd_5692907 : Nat := 2923197612345463208881303

theorem tailTrace_5692907 : CollatzResearch.WordTrace tailWord_5692907 prefixEnd_5692907 2923197612345463208881303 := by
  unfold tailWord_5692907
  simp only [CollatzResearch.WordTrace]
  refine ⟨207637376386577684954252975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138424917591051789969501983 207637376386577684954252975)
  ·
    refine ⟨311456064579866527431379463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207637376386577684954252975 311456064579866527431379463)
    ·
      refine ⟨467184096869799791147069195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311456064579866527431379463 467184096869799791147069195)
      ·
        refine ⟨700776145304699686720603793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467184096869799791147069195 700776145304699686720603793)
        ·
          refine ⟨525582108978524765040452845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 700776145304699686720603793 525582108978524765040452845)
          ·
            refine ⟨197093290866946786890169817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 525582108978524765040452845 197093290866946786890169817)
            ·
              refine ⟨147819968150210090167627363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197093290866946786890169817 147819968150210090167627363)
              ·
                refine ⟨221729952225315135251441045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147819968150210090167627363 221729952225315135251441045)
                ·
                  refine ⟨10393591510561646964911299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 221729952225315135251441045 10393591510561646964911299)
                  ·
                    refine ⟨15590387265842470447366949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10393591510561646964911299 15590387265842470447366949)
                    ·
                      refine ⟨2923197612345463208881303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15590387265842470447366949 2923197612345463208881303)
                      ·
                        rfl

theorem cell23_5692907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 4].length) (baseStart_5692907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692907 prefixEnd_5692907 := by exact prefixLift 5692907
  have htrace : WordTrace (prefixWord ++ tailWord_5692907) baseStart_5692907 baseEnd_5692907 := by
    simpa [prefixWord, tailWord_5692907, baseEnd_5692907] using wordTrace_append hprefix tailTrace_5692907
  have hstable : (prefixWord ++ tailWord_5692907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692907).length < 2 ^ (prefixWord ++ tailWord_5692907).sum := by decide
  have hdescent : baseEnd_5692907 < baseStart_5692907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692924 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 1, 6, 2]
def baseStart_5692924 : Nat := 118140960795 + 5692924 * 2 ^ 59
def prefixEnd_5692924 : Nat := 4983230072969 + 3 ^ 40 * 5692924 * 2
def baseEnd_5692924 : Nat := 2923206341516589642368725

theorem tailTrace_5692924 : CollatzResearch.WordTrace tailWord_5692924 prefixEnd_5692924 2923206341516589642368725 := by
  unfold tailWord_5692924
  simp only [CollatzResearch.WordTrace]
  refine ⟨103818998213758048428810913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138425330951677397905081217 103818998213758048428810913)
  ·
    refine ⟨77864248660318536321608185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103818998213758048428810913 77864248660318536321608185)
    ·
      refine ⟨58398186495238902241206139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77864248660318536321608185 58398186495238902241206139)
      ·
        refine ⟨87597279742858353361809209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58398186495238902241206139 87597279742858353361809209)
        ·
          refine ⟨65697959807143765021356907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87597279742858353361809209 65697959807143765021356907)
          ·
            refine ⟨98546939710715647532035361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65697959807143765021356907 98546939710715647532035361)
            ·
              refine ⟨73910204783036735649026521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98546939710715647532035361 73910204783036735649026521)
              ·
                refine ⟨55432653587277551736769891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73910204783036735649026521 55432653587277551736769891)
                ·
                  refine ⟨83148980380916327605154837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55432653587277551736769891 83148980380916327605154837)
                  ·
                    refine ⟨3897608455355452856491633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83148980380916327605154837 3897608455355452856491633)
                    ·
                      refine ⟨2923206341516589642368725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3897608455355452856491633 2923206341516589642368725)
                      ·
                        rfl

theorem cell23_5692924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 6, 2].length) (baseStart_5692924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692924 prefixEnd_5692924 := by exact prefixLift 5692924
  have htrace : WordTrace (prefixWord ++ tailWord_5692924) baseStart_5692924 baseEnd_5692924 := by
    simpa [prefixWord, tailWord_5692924, baseEnd_5692924] using wordTrace_append hprefix tailTrace_5692924
  have hstable : (prefixWord ++ tailWord_5692924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692924).length < 2 ^ (prefixWord ++ tailWord_5692924).sum := by decide
  have hdescent : baseEnd_5692924 < baseStart_5692924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5692947 : List Nat := [1, 1, 1, 2, 1, 6, 2, 1, 8]
def baseStart_5692947 : Nat := 118140960795 + 5692947 * 2 ^ 59
def prefixEnd_5692947 : Nat := 4983230072969 + 3 ^ 40 * 5692947 * 2
def baseEnd_5692947 : Nat := 324802016841293672486791

theorem tailTrace_5692947 : CollatzResearch.WordTrace tailWord_5692947 prefixEnd_5692947 324802016841293672486791 := by
  unfold tailWord_5692947
  simp only [CollatzResearch.WordTrace]
  refine ⟨207638835306432771785709095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138425890204288514523806063 207638835306432771785709095)
  ·
    refine ⟨311458252959649157678563643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207638835306432771785709095 311458252959649157678563643)
    ·
      refine ⟨467187379439473736517845465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311458252959649157678563643 467187379439473736517845465)
      ·
        refine ⟨350390534579605302388384099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 467187379439473736517845465 350390534579605302388384099)
        ·
          refine ⟨525585801869407953582576149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350390534579605302388384099 525585801869407953582576149)
          ·
            refine ⟨24636834462628497824183257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 525585801869407953582576149 24636834462628497824183257)
            ·
              refine ⟨18477625846971373368137443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24636834462628497824183257 18477625846971373368137443)
              ·
                refine ⟨27716438770457060052206165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18477625846971373368137443 27716438770457060052206165)
                ·
                  refine ⟨324802016841293672486791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27716438770457060052206165 324802016841293672486791)
                  ·
                    rfl

theorem cell23_5692947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 8].length) (baseStart_5692947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5692947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5692947 prefixEnd_5692947 := by exact prefixLift 5692947
  have htrace : WordTrace (prefixWord ++ tailWord_5692947) baseStart_5692947 baseEnd_5692947 := by
    simpa [prefixWord, tailWord_5692947, baseEnd_5692947] using wordTrace_append hprefix tailTrace_5692947
  have hstable : (prefixWord ++ tailWord_5692947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5692947).length < 2 ^ (prefixWord ++ tailWord_5692947).sum := by decide
  have hdescent : baseEnd_5692947 < baseStart_5692947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5692947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693007 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 5, 6]
def baseStart_5693007 : Nat := 118140960795 + 5693007 * 2 ^ 59
def prefixEnd_5693007 : Nat := 4983230072969 + 3 ^ 40 * 5693007 * 2
def baseEnd_5693007 : Nat := 974416320136970939210281

theorem tailTrace_5693007 : CollatzResearch.WordTrace tailWord_5693007 prefixEnd_5693007 974416320136970939210281 := by
  unfold tailWord_5693007
  simp only [CollatzResearch.WordTrace]
  refine ⟨207641023686215402032893275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138427349124143601355262183 207641023686215402032893275)
  ·
    refine ⟨311461535529323103049339913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207641023686215402032893275 311461535529323103049339913)
    ·
      refine ⟨233596151646992327287004935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311461535529323103049339913 233596151646992327287004935)
      ·
        refine ⟨350394227470488490930507403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233596151646992327287004935 350394227470488490930507403)
        ·
          refine ⟨525591341205732736395761105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350394227470488490930507403 525591341205732736395761105)
          ·
            refine ⟨394193505904299552296820829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 525591341205732736395761105 394193505904299552296820829)
            ·
              refine ⟨147822564714112332111307811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 394193505904299552296820829 147822564714112332111307811)
              ·
                refine ⟨221733847071168498166961717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147822564714112332111307811 221733847071168498166961717)
                ·
                  refine ⟨20787548162922046703152661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 221733847071168498166961717 20787548162922046703152661)
                  ·
                    refine ⟨974416320136970939210281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20787548162922046703152661 974416320136970939210281)
                    ·
                      rfl

theorem cell23_5693007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 6].length) (baseStart_5693007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693007 prefixEnd_5693007 := by exact prefixLift 5693007
  have htrace : WordTrace (prefixWord ++ tailWord_5693007) baseStart_5693007 baseEnd_5693007 := by
    simpa [prefixWord, tailWord_5693007, baseEnd_5693007] using wordTrace_append hprefix tailTrace_5693007
  have hstable : (prefixWord ++ tailWord_5693007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693007).length < 2 ^ (prefixWord ++ tailWord_5693007).sum := by decide
  have hdescent : baseEnd_5693007 < baseStart_5693007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693008 : List Nat := [2, 1, 1, 1, 1, 3, 5, 4, 1, 1, 3]
def baseStart_5693008 : Nat := 118140960795 + 5693008 * 2 ^ 59
def prefixEnd_5693008 : Nat := 4983230072969 + 3 ^ 40 * 5693008 * 2
def baseEnd_5693008 : Nat := 2923249473891567313718339

theorem tailTrace_5693008 : CollatzResearch.WordTrace tailWord_5693008 prefixEnd_5693008 2923249473891567313718339 := by
  unfold tailWord_5693008
  simp only [CollatzResearch.WordTrace]
  refine ⟨103820530079605889601839839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138427373439474519469119785 103820530079605889601839839)
  ·
    refine ⟨155730795119408834402759759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103820530079605889601839839 155730795119408834402759759)
    ·
      refine ⟨233596192679113251604139639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155730795119408834402759759 233596192679113251604139639)
      ·
        refine ⟨350394289018669877406209459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233596192679113251604139639 350394289018669877406209459)
        ·
          refine ⟨525591433528004816109314189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350394289018669877406209459 525591433528004816109314189)
          ·
            refine ⟨197096787573001806040992821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 525591433528004816109314189 197096787573001806040992821)
            ·
              refine ⟨18477823834968919316343077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 197096787573001806040992821 18477823834968919316343077)
              ·
                refine ⟨3464591969056672371814327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18477823834968919316343077 3464591969056672371814327)
                ·
                  refine ⟨5196887953585008557721491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3464591969056672371814327 5196887953585008557721491)
                  ·
                    refine ⟨7795331930377512836582237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5196887953585008557721491 7795331930377512836582237)
                    ·
                      refine ⟨2923249473891567313718339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7795331930377512836582237 2923249473891567313718339)
                      ·
                        rfl

theorem cell23_5693008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4, 1, 1, 3].length) (baseStart_5693008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693008 prefixEnd_5693008 := by exact prefixLift 5693008
  have htrace : WordTrace (prefixWord ++ tailWord_5693008) baseStart_5693008 baseEnd_5693008 := by
    simpa [prefixWord, tailWord_5693008, baseEnd_5693008] using wordTrace_append hprefix tailTrace_5693008
  have hstable : (prefixWord ++ tailWord_5693008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693008).length < 2 ^ (prefixWord ++ tailWord_5693008).sum := by decide
  have hdescent : baseEnd_5693008 < baseStart_5693008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693024 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 6, 4]
def baseStart_5693024 : Nat := 118140960795 + 5693024 * 2 ^ 59
def prefixEnd_5693024 : Nat := 4983230072969 + 3 ^ 40 * 5693024 * 2
def baseEnd_5693024 : Nat := 974419229860679750372755

theorem tailTrace_5693024 : CollatzResearch.WordTrace tailWord_5693024 prefixEnd_5693024 974419229860679750372755 := by
  unfold tailWord_5693024
  simp only [CollatzResearch.WordTrace]
  refine ⟨103820821863576906968131063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138427762484769209290841417 103820821863576906968131063)
  ·
    refine ⟨155731232795365360452196595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103820821863576906968131063 155731232795365360452196595)
    ·
      refine ⟨233596849193048040678294893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155731232795365360452196595 233596849193048040678294893)
      ·
        refine ⟨87598818447393015254360585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233596849193048040678294893 87598818447393015254360585)
        ·
          refine ⟨65699113835544761440770439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87598818447393015254360585 65699113835544761440770439)
          ·
            refine ⟨98548670753317142161155659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65699113835544761440770439 98548670753317142161155659)
            ·
              refine ⟨147823006129975713241733489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98548670753317142161155659 147823006129975713241733489)
              ·
                refine ⟨110867254597481784931300117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147823006129975713241733489 110867254597481784931300117)
                ·
                  refine ⟨5196902559256958668654693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110867254597481784931300117 5196902559256958668654693)
                  ·
                    refine ⟨974419229860679750372755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5196902559256958668654693 974419229860679750372755)
                    ·
                      rfl

theorem cell23_5693024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 6, 4].length) (baseStart_5693024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693024 prefixEnd_5693024 := by exact prefixLift 5693024
  have htrace : WordTrace (prefixWord ++ tailWord_5693024) baseStart_5693024 baseEnd_5693024 := by
    simpa [prefixWord, tailWord_5693024, baseEnd_5693024] using wordTrace_append hprefix tailTrace_5693024
  have hstable : (prefixWord ++ tailWord_5693024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693024).length < 2 ^ (prefixWord ++ tailWord_5693024).sum := by decide
  have hdescent : baseEnd_5693024 < baseStart_5693024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693045 : List Nat := [1, 3, 4, 2, 1, 3, 2, 1, 1, 5]
def baseStart_5693045 : Nat := 118140960795 + 5693045 * 2 ^ 59
def prefixEnd_5693045 : Nat := 4983230072969 + 3 ^ 40 * 5693045 * 2
def baseEnd_5693045 : Nat := 974422824225261222985223

theorem tailTrace_5693045 : CollatzResearch.WordTrace tailWord_5693045 prefixEnd_5693045 974422824225261222985223 := by
  unfold tailWord_5693045
  simp only [CollatzResearch.WordTrace]
  refine ⟨207642409660077734522776589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138428273106718489681851059 207642409660077734522776589)
  ·
    refine ⟨77865903622529150446041221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207642409660077734522776589 77865903622529150446041221)
    ·
      refine ⟨14599856929224215708632729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77865903622529150446041221 14599856929224215708632729)
      ·
        refine ⟨10949892696918161781474547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14599856929224215708632729 10949892696918161781474547)
        ·
          refine ⟨16424839045377242672211821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10949892696918161781474547 16424839045377242672211821)
          ·
            refine ⟨6159314642016466002079433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16424839045377242672211821 6159314642016466002079433)
            ·
              refine ⟨4619485981512349501559575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6159314642016466002079433 4619485981512349501559575)
              ·
                refine ⟨6929228972268524252339363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4619485981512349501559575 6929228972268524252339363)
                ·
                  refine ⟨10393843458402786378509045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6929228972268524252339363 10393843458402786378509045)
                  ·
                    refine ⟨974422824225261222985223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10393843458402786378509045 974422824225261222985223)
                    ·
                      rfl

theorem cell23_5693045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_5693045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693045 prefixEnd_5693045 := by exact prefixLift 5693045
  have htrace : WordTrace (prefixWord ++ tailWord_5693045) baseStart_5693045 baseEnd_5693045 := by
    simpa [prefixWord, tailWord_5693045, baseEnd_5693045] using wordTrace_append hprefix tailTrace_5693045
  have hstable : (prefixWord ++ tailWord_5693045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693045).length < 2 ^ (prefixWord ++ tailWord_5693045).sum := by decide
  have hdescent : baseEnd_5693045 < baseStart_5693045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693051 : List Nat := [1, 1, 1, 1, 1, 4, 5, 3, 1, 2, 3]
def baseStart_5693051 : Nat := 118140960795 + 5693051 * 2 ^ 59
def prefixEnd_5693051 : Nat := 4983230072969 + 3 ^ 40 * 5693051 * 2
def baseEnd_5693051 : Nat := 2923271553559710645480641

theorem tailTrace_5693051 : CollatzResearch.WordTrace tailWord_5693051 prefixEnd_5693051 2923271553559710645480641 := by
  unfold tailWord_5693051
  simp only [CollatzResearch.WordTrace]
  refine ⟨207642628498055997547495007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138428418998703998364996671 207642628498055997547495007)
  ·
    refine ⟨311463942747083996321242511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207642628498055997547495007 311463942747083996321242511)
    ·
      refine ⟨467195914120625994481863767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311463942747083996321242511 467195914120625994481863767)
      ·
        refine ⟨700793871180938991722795651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467195914120625994481863767 700793871180938991722795651)
        ·
          refine ⟨1051190806771408487584193477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 700793871180938991722795651 1051190806771408487584193477)
          ·
            refine ⟨197098276269639091422036277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1051190806771408487584193477 197098276269639091422036277)
            ·
              refine ⟨18477963400278664820815901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 197098276269639091422036277 18477963400278664820815901)
              ·
                refine ⟨6929236275104499307805963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18477963400278664820815901 6929236275104499307805963)
                ·
                  refine ⟨10393854412656748961708945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6929236275104499307805963 10393854412656748961708945)
                  ·
                    refine ⟨7795390809492561721281709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10393854412656748961708945 7795390809492561721281709)
                    ·
                      refine ⟨2923271553559710645480641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7795390809492561721281709 2923271553559710645480641)
                      ·
                        rfl

theorem cell23_5693051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 2, 3].length) (baseStart_5693051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693051 prefixEnd_5693051 := by exact prefixLift 5693051
  have htrace : WordTrace (prefixWord ++ tailWord_5693051) baseStart_5693051 baseEnd_5693051 := by
    simpa [prefixWord, tailWord_5693051, baseEnd_5693051] using wordTrace_append hprefix tailTrace_5693051
  have hstable : (prefixWord ++ tailWord_5693051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693051).length < 2 ^ (prefixWord ++ tailWord_5693051).sum := by decide
  have hdescent : baseEnd_5693051 < baseStart_5693051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693065 : List Nat := [1, 2, 1, 1, 4, 1, 4, 4, 1, 2, 2]
def baseStart_5693065 : Nat := 118140960795 + 5693065 * 2 ^ 59
def prefixEnd_5693065 : Nat := 4983230072969 + 3 ^ 40 * 5693065 * 2
def baseEnd_5693065 : Nat := 2923278742288873590705577

theorem tailTrace_5693065 : CollatzResearch.WordTrace tailWord_5693065 prefixEnd_5693065 2923278742288873590705577 := by
  unfold tailWord_5693065
  simp only [CollatzResearch.WordTrace]
  refine ⟨207643139120005277938504649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138428759413336851959003099 207643139120005277938504649)
  ·
    refine ⟨155732354340003958453878487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207643139120005277938504649 155732354340003958453878487)
    ·
      refine ⟨233598531510005937680817731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155732354340003958453878487 233598531510005937680817731)
      ·
        refine ⟨350397797265008906521226597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233598531510005937680817731 350397797265008906521226597)
        ·
          refine ⟨65699586987189169972729987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 350397797265008906521226597 65699586987189169972729987)
          ·
            refine ⟨98549380480783754959094981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65699586987189169972729987 98549380480783754959094981)
            ·
              refine ⟨18478008840146954054830309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98549380480783754959094981 18478008840146954054830309)
              ·
                refine ⟨3464626657527553885280683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18478008840146954054830309 3464626657527553885280683)
                ·
                  refine ⟨5196939986291330827921025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3464626657527553885280683 5196939986291330827921025)
                  ·
                    refine ⟨3897704989718498120940769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5196939986291330827921025 3897704989718498120940769)
                    ·
                      refine ⟨2923278742288873590705577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3897704989718498120940769 2923278742288873590705577)
                      ·
                        rfl

theorem cell23_5693065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4, 1, 2, 2].length) (baseStart_5693065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693065 prefixEnd_5693065 := by exact prefixLift 5693065
  have htrace : WordTrace (prefixWord ++ tailWord_5693065) baseStart_5693065 baseEnd_5693065 := by
    simpa [prefixWord, tailWord_5693065, baseEnd_5693065] using wordTrace_append hprefix tailTrace_5693065
  have hstable : (prefixWord ++ tailWord_5693065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693065).length < 2 ^ (prefixWord ++ tailWord_5693065).sum := by decide
  have hdescent : baseEnd_5693065 < baseStart_5693065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693144 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 9]
def baseStart_5693144 : Nat := 118140960795 + 5693144 * 2 ^ 59
def prefixEnd_5693144 : Nat := 4983230072969 + 3 ^ 40 * 5693144 * 2
def baseEnd_5693144 : Nat := 324813256362286531290857

theorem tailTrace_5693144 : CollatzResearch.WordTrace tailWord_5693144 prefixEnd_5693144 324813256362286531290857 := by
  unfold tailWord_5693144
  simp only [CollatzResearch.WordTrace]
  refine ⟨103823010243359537215315243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138430680324479382953753657 103823010243359537215315243)
  ·
    refine ⟨155734515365039305822972865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103823010243359537215315243 155734515365039305822972865)
    ·
      refine ⟨116800886523779479367229649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155734515365039305822972865 116800886523779479367229649)
      ·
        refine ⟨87600664892834609525422237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116800886523779479367229649 87600664892834609525422237)
        ·
          refine ⟨32850249334812978572033339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87600664892834609525422237 32850249334812978572033339)
          ·
            refine ⟨49275374002219467858050009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32850249334812978572033339 49275374002219467858050009)
            ·
              refine ⟨36956530501664600893537507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49275374002219467858050009 36956530501664600893537507)
              ·
                refine ⟨55434795752496901340306261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36956530501664600893537507 55434795752496901340306261)
                ·
                  refine ⟨324813256362286531290857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55434795752496901340306261 324813256362286531290857)
                  ·
                    rfl

theorem cell23_5693144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 9].length) (baseStart_5693144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693144 prefixEnd_5693144 := by exact prefixLift 5693144
  have htrace : WordTrace (prefixWord ++ tailWord_5693144) baseStart_5693144 baseEnd_5693144 := by
    simpa [prefixWord, tailWord_5693144, baseEnd_5693144] using wordTrace_append hprefix tailTrace_5693144
  have hstable : (prefixWord ++ tailWord_5693144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693144).length < 2 ^ (prefixWord ++ tailWord_5693144).sum := by decide
  have hdescent : baseEnd_5693144 < baseStart_5693144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693155 : List Nat := [1, 1, 1, 7, 2, 1, 1, 2, 1, 4, 2]
def baseStart_5693155 : Nat := 118140960795 + 5693155 * 2 ^ 59
def prefixEnd_5693155 : Nat := 4983230072969 + 3 ^ 40 * 5693155 * 2
def baseEnd_5693155 : Nat := 2923324955547778238580163

theorem tailTrace_5693155 : CollatzResearch.WordTrace tailWord_5693155 prefixEnd_5693155 2923324955547778238580163 := by
  unfold tailWord_5693155
  simp only [CollatzResearch.WordTrace]
  refine ⟨207646421689679223309280919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138430947793119482206187279 207646421689679223309280919)
  ·
    refine ⟨311469632534518834963921379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207646421689679223309280919 311469632534518834963921379)
    ·
      refine ⟨467204448801778252445882069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311469632534518834963921379 467204448801778252445882069)
      ·
        refine ⟨10950104268791677791700361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 467204448801778252445882069 10950104268791677791700361)
        ·
          refine ⟨8212578201593758343775271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10950104268791677791700361 8212578201593758343775271)
          ·
            refine ⟨12318867302390637515662907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8212578201593758343775271 12318867302390637515662907)
            ·
              refine ⟨18478300953585956273494361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12318867302390637515662907 18478300953585956273494361)
              ·
                refine ⟨13858725715189467205120771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18478300953585956273494361 13858725715189467205120771)
                ·
                  refine ⟨20788088572784200807681157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13858725715189467205120771 20788088572784200807681157)
                  ·
                    refine ⟨3897766607397037651440217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20788088572784200807681157 3897766607397037651440217)
                    ·
                      refine ⟨2923324955547778238580163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3897766607397037651440217 2923324955547778238580163)
                      ·
                        rfl

theorem cell23_5693155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_5693155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693155 prefixEnd_5693155 := by exact prefixLift 5693155
  have htrace : WordTrace (prefixWord ++ tailWord_5693155) baseStart_5693155 baseEnd_5693155 := by
    simpa [prefixWord, tailWord_5693155, baseEnd_5693155] using wordTrace_append hprefix tailTrace_5693155
  have hstable : (prefixWord ++ tailWord_5693155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693155).length < 2 ^ (prefixWord ++ tailWord_5693155).sum := by decide
  have hdescent : baseEnd_5693155 < baseStart_5693155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693159 : List Nat := [1, 1, 5, 4, 1, 1, 3, 1, 1, 3, 2]
def baseStart_5693159 : Nat := 118140960795 + 5693159 * 2 ^ 59
def prefixEnd_5693159 : Nat := 4983230072969 + 3 ^ 40 * 5693159 * 2
def baseEnd_5693159 : Nat := 2923327009470396222930145

theorem tailTrace_5693159 : CollatzResearch.WordTrace tailWord_5693159 prefixEnd_5693159 2923327009470396222930145 := by
  unfold tailWord_5693159
  simp only [CollatzResearch.WordTrace]
  refine ⟨207646567581664731992426531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138431045054443154661617687 207646567581664731992426531)
  ·
    refine ⟨311469851372497097988639797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207646567581664731992426531 311469851372497097988639797)
    ·
      refine ⟨29200298566171602936434981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 311469851372497097988639797 29200298566171602936434981)
      ·
        refine ⟨5475055981157175550581559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29200298566171602936434981 5475055981157175550581559)
        ·
          refine ⟨8212583971735763325872339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5475055981157175550581559 8212583971735763325872339)
          ·
            refine ⟨12318875957603644988808509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8212583971735763325872339 12318875957603644988808509)
            ·
              refine ⟨4619578484101366870803191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12318875957603644988808509 4619578484101366870803191)
              ·
                refine ⟨6929367726152050306204787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4619578484101366870803191 6929367726152050306204787)
                ·
                  refine ⟨10394051589228075459307181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6929367726152050306204787 10394051589228075459307181)
                  ·
                    refine ⟨3897769345960528297240193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10394051589228075459307181 3897769345960528297240193)
                    ·
                      refine ⟨2923327009470396222930145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3897769345960528297240193 2923327009470396222930145)
                      ·
                        rfl

theorem cell23_5693159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_5693159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693159 prefixEnd_5693159 := by exact prefixLift 5693159
  have htrace : WordTrace (prefixWord ++ tailWord_5693159) baseStart_5693159 baseEnd_5693159 := by
    simpa [prefixWord, tailWord_5693159, baseEnd_5693159] using wordTrace_append hprefix tailTrace_5693159
  have hstable : (prefixWord ++ tailWord_5693159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693159).length < 2 ^ (prefixWord ++ tailWord_5693159).sum := by decide
  have hdescent : baseEnd_5693159 < baseStart_5693159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693161 : List Nat := [1, 2, 1, 1, 1, 2, 3, 7, 5]
def baseStart_5693161 : Nat := 118140960795 + 5693161 * 2 ^ 59
def prefixEnd_5693161 : Nat := 4983230072969 + 3 ^ 40 * 5693161 * 2
def baseEnd_5693161 : Nat := 324814226270189468345015

theorem tailTrace_5693161 : CollatzResearch.WordTrace tailWord_5693161 prefixEnd_5693161 324814226270189468345015 := by
  unfold tailWord_5693161
  simp only [CollatzResearch.WordTrace]
  refine ⟨207646640527657486333999337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138431093685104990889332891 207646640527657486333999337)
  ·
    refine ⟨155734980395743114750499503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207646640527657486333999337 155734980395743114750499503)
    ·
      refine ⟨233602470593614672125749255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155734980395743114750499503 233602470593614672125749255)
      ·
        refine ⟨350403705890422008188623883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233602470593614672125749255 350403705890422008188623883)
        ·
          refine ⟨525605558835633012282935825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350403705890422008188623883 525605558835633012282935825)
          ·
            refine ⟨394204169126724759212201869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 525605558835633012282935825 394204169126724759212201869)
            ·
              refine ⟨147826563422521784704575701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 394204169126724759212201869 147826563422521784704575701)
              ·
                refine ⟨3464685080215354329013493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 147826563422521784704575701 3464685080215354329013493)
                ·
                  refine ⟨324814226270189468345015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3464685080215354329013493 324814226270189468345015)
                  ·
                    rfl

theorem cell23_5693161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7, 5].length) (baseStart_5693161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693161 prefixEnd_5693161 := by exact prefixLift 5693161
  have htrace : WordTrace (prefixWord ++ tailWord_5693161) baseStart_5693161 baseEnd_5693161 := by
    simpa [prefixWord, tailWord_5693161, baseEnd_5693161] using wordTrace_append hprefix tailTrace_5693161
  have hstable : (prefixWord ++ tailWord_5693161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693161).length < 2 ^ (prefixWord ++ tailWord_5693161).sum := by decide
  have hdescent : baseEnd_5693161 < baseStart_5693161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693188 : List Nat := [2, 3, 2, 2, 1, 3, 1, 1, 2, 3, 3]
def baseStart_5693188 : Nat := 118140960795 + 5693188 * 2 ^ 59
def prefixEnd_5693188 : Nat := 4983230072969 + 3 ^ 40 * 5693188 * 2
def baseEnd_5693188 : Nat := 2923341900409376609467511

theorem tailTrace_5693188 : CollatzResearch.WordTrace tailWord_5693188 prefixEnd_5693188 2923341900409376609467511 := by
  unfold tailWord_5693188
  simp only [CollatzResearch.WordTrace]
  refine ⟨103823812649279834972616109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138431750199039779963488145 103823812649279834972616109)
  ·
    refine ⟨38933929743479938114731041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103823812649279834972616109 38933929743479938114731041)
    ·
      refine ⟨29200447307609953586048281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38933929743479938114731041 29200447307609953586048281)
      ·
        refine ⟨21900335480707465189536211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29200447307609953586048281 21900335480707465189536211)
        ·
          refine ⟨32850503221061197784304317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21900335480707465189536211 32850503221061197784304317)
          ·
            refine ⟨12318938707897949169114119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32850503221061197784304317 12318938707897949169114119)
            ·
              refine ⟨18478408061846923753671179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12318938707897949169114119 18478408061846923753671179)
              ·
                refine ⟨27717612092770385630506769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18478408061846923753671179 27717612092770385630506769)
                ·
                  refine ⟨20788209069577789222880077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27717612092770385630506769 20788209069577789222880077)
                  ·
                    refine ⟨7795578401091670958580029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20788209069577789222880077 7795578401091670958580029)
                    ·
                      refine ⟨2923341900409376609467511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7795578401091670958580029 2923341900409376609467511)
                      ·
                        rfl

theorem cell23_5693188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_5693188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693188 prefixEnd_5693188 := by exact prefixLift 5693188
  have htrace : WordTrace (prefixWord ++ tailWord_5693188) baseStart_5693188 baseEnd_5693188 := by
    simpa [prefixWord, tailWord_5693188, baseEnd_5693188] using wordTrace_append hprefix tailTrace_5693188
  have hstable : (prefixWord ++ tailWord_5693188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693188).length < 2 ^ (prefixWord ++ tailWord_5693188).sum := by decide
  have hdescent : baseEnd_5693188 < baseStart_5693188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693228 : List Nat := [2, 2, 1, 1, 1, 5, 1, 2, 2, 4, 2]
def baseStart_5693228 : Nat := 118140960795 + 5693228 * 2 ^ 59
def prefixEnd_5693228 : Nat := 4983230072969 + 3 ^ 40 * 5693228 * 2
def baseEnd_5693228 : Nat := 2923362439635556452967327

theorem tailTrace_5693228 : CollatzResearch.WordTrace tailWord_5693228 prefixEnd_5693228 2923362439635556452967327 := by
  unfold tailWord_5693228
  simp only [CollatzResearch.WordTrace]
  refine ⟨103824542109207378388344169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138432722812276504517792225 103824542109207378388344169)
  ·
    refine ⟨77868406581905533791258127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103824542109207378388344169 77868406581905533791258127)
    ·
      refine ⟨116802609872858300686887191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77868406581905533791258127 116802609872858300686887191)
      ·
        refine ⟨175203914809287451030330787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116802609872858300686887191 175203914809287451030330787)
        ·
          refine ⟨262805872213931176545496181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175203914809287451030330787 262805872213931176545496181)
          ·
            refine ⟨24638050520056047801140267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 262805872213931176545496181 24638050520056047801140267)
            ·
              refine ⟨36957075780084071701710401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24638050520056047801140267 36957075780084071701710401)
              ·
                refine ⟨27717806835063053776282801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36957075780084071701710401 27717806835063053776282801)
                ·
                  refine ⟨20788355126297290332212101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27717806835063053776282801 20788355126297290332212101)
                  ·
                    refine ⟨3897816586180741937289769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20788355126297290332212101 3897816586180741937289769)
                    ·
                      refine ⟨2923362439635556452967327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3897816586180741937289769 2923362439635556452967327)
                      ·
                        rfl

theorem cell23_5693228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 4, 2].length) (baseStart_5693228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693228 prefixEnd_5693228 := by exact prefixLift 5693228
  have htrace : WordTrace (prefixWord ++ tailWord_5693228) baseStart_5693228 baseEnd_5693228 := by
    simpa [prefixWord, tailWord_5693228, baseEnd_5693228] using wordTrace_append hprefix tailTrace_5693228
  have hstable : (prefixWord ++ tailWord_5693228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693228).length < 2 ^ (prefixWord ++ tailWord_5693228).sum := by decide
  have hdescent : baseEnd_5693228 < baseStart_5693228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693245 : List Nat := [1, 4, 1, 4, 1, 1, 2, 1, 2, 4, 2]
def baseStart_5693245 : Nat := 118140960795 + 5693245 * 2 ^ 59
def prefixEnd_5693245 : Nat := 4983230072969 + 3 ^ 40 * 5693245 * 2
def baseEnd_5693245 : Nat := 2923371168806682886454749

theorem tailTrace_5693245 : CollatzResearch.WordTrace tailWord_5693245 prefixEnd_5693245 2923371168806682886454749 := by
  unfold tailWord_5693245
  simp only [CollatzResearch.WordTrace]
  refine ⟨207649704259353168680057189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138433136172902112453371459 207649704259353168680057189)
  ·
    refine ⟨38934319548628719127510723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207649704259353168680057189 38934319548628719127510723)
    ·
      refine ⟨58401479322943078691266085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38934319548628719127510723 58401479322943078691266085)
      ·
        refine ⟨10950277373051827254612391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58401479322943078691266085 10950277373051827254612391)
        ·
          refine ⟨16425416059577740881918587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10950277373051827254612391 16425416059577740881918587)
          ·
            refine ⟨24638124089366611322877881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16425416059577740881918587 24638124089366611322877881)
            ·
              refine ⟨18478593067024958492158411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24638124089366611322877881 18478593067024958492158411)
              ·
                refine ⟨27717889600537437738237617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18478593067024958492158411 27717889600537437738237617)
                ·
                  refine ⟨20788417200403078303678213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27717889600537437738237617 20788417200403078303678213)
                  ·
                    refine ⟨3897828225075577181939665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20788417200403078303678213 3897828225075577181939665)
                    ·
                      refine ⟨2923371168806682886454749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3897828225075577181939665 2923371168806682886454749)
                      ·
                        rfl

theorem cell23_5693245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_5693245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693245 prefixEnd_5693245 := by exact prefixLift 5693245
  have htrace : WordTrace (prefixWord ++ tailWord_5693245) baseStart_5693245 baseEnd_5693245 := by
    simpa [prefixWord, tailWord_5693245, baseEnd_5693245] using wordTrace_append hprefix tailTrace_5693245
  have hstable : (prefixWord ++ tailWord_5693245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693245).length < 2 ^ (prefixWord ++ tailWord_5693245).sum := by decide
  have hdescent : baseEnd_5693245 < baseStart_5693245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693311 : List Nat := [1, 1, 2, 2, 1, 1, 3, 5, 1, 6]
def baseStart_5693311 : Nat := 118140960795 + 5693311 * 2 ^ 59
def prefixEnd_5693311 : Nat := 4983230072969 + 3 ^ 40 * 5693311 * 2
def baseEnd_5693311 : Nat := 974468352843293209409815

theorem tailTrace_5693311 : CollatzResearch.WordTrace tailWord_5693311 prefixEnd_5693311 974468352843293209409815 := by
  unfold tailWord_5693311
  simp only [CollatzResearch.WordTrace]
  refine ⟨207652111477114061951959787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138434740984742707967973191 207652111477114061951959787)
  ·
    refine ⟨311478167215671092927939681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207652111477114061951959787 311478167215671092927939681)
    ·
      refine ⟨233608625411753319695954761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311478167215671092927939681 233608625411753319695954761)
      ·
        refine ⟨175206469058814989771966071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233608625411753319695954761 175206469058814989771966071)
        ·
          refine ⟨262809703588222484657949107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175206469058814989771966071 262809703588222484657949107)
          ·
            refine ⟨394214555382333726986923661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262809703588222484657949107 394214555382333726986923661)
            ·
              refine ⟨147830458268375147620096373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 394214555382333726986923661 147830458268375147620096373)
              ·
                refine ⟨13859105462660170089384035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 147830458268375147620096373 13859105462660170089384035)
                ·
                  refine ⟨20788658193990255134076053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13859105462660170089384035 20788658193990255134076053)
                  ·
                    refine ⟨974468352843293209409815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20788658193990255134076053 974468352843293209409815)
                    ·
                      rfl

theorem cell23_5693311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 6].length) (baseStart_5693311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693311 prefixEnd_5693311 := by exact prefixLift 5693311
  have htrace : WordTrace (prefixWord ++ tailWord_5693311) baseStart_5693311 baseEnd_5693311 := by
    simpa [prefixWord, tailWord_5693311, baseEnd_5693311] using wordTrace_append hprefix tailTrace_5693311
  have hstable : (prefixWord ++ tailWord_5693311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693311).length < 2 ^ (prefixWord ++ tailWord_5693311).sum := by decide
  have hdescent : baseEnd_5693311 < baseStart_5693311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693315 : List Nat := [1, 1, 1, 3, 4, 4, 1, 2, 1, 5]
def baseStart_5693315 : Nat := 118140960795 + 5693315 * 2 ^ 59
def prefixEnd_5693315 : Nat := 4983230072969 + 3 ^ 40 * 5693315 * 2
def baseEnd_5693315 : Nat := 974469037484165870859809

theorem tailTrace_5693315 : CollatzResearch.WordTrace tailWord_5693315 prefixEnd_5693315 974469037484165870859809 := by
  unfold tailWord_5693315
  simp only [CollatzResearch.WordTrace]
  refine ⟨207652257369099570635105399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138434838246066380423403599 207652257369099570635105399)
  ·
    refine ⟨311478386053649355952658099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207652257369099570635105399 311478386053649355952658099)
    ·
      refine ⟨467217579080474033928987149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311478386053649355952658099 467217579080474033928987149)
      ·
        refine ⟨175206592155177762723370181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 467217579080474033928987149 175206592155177762723370181)
        ·
          refine ⟨32851236029095830510631909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175206592155177762723370181 32851236029095830510631909)
          ·
            refine ⟨6159606755455468220743483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32851236029095830510631909 6159606755455468220743483)
            ·
              refine ⟨9239410133183202331115225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6159606755455468220743483 9239410133183202331115225)
              ·
                refine ⟨6929557599887401748336419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9239410133183202331115225 6929557599887401748336419)
                ·
                  refine ⟨10394336399831102622504629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6929557599887401748336419 10394336399831102622504629)
                  ·
                    refine ⟨974469037484165870859809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10394336399831102622504629 974469037484165870859809)
                    ·
                      rfl

theorem cell23_5693315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 5].length) (baseStart_5693315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693315 prefixEnd_5693315 := by exact prefixLift 5693315
  have htrace : WordTrace (prefixWord ++ tailWord_5693315) baseStart_5693315 baseEnd_5693315 := by
    simpa [prefixWord, tailWord_5693315, baseEnd_5693315] using wordTrace_append hprefix tailTrace_5693315
  have hstable : (prefixWord ++ tailWord_5693315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693315).length < 2 ^ (prefixWord ++ tailWord_5693315).sum := by decide
  have hdescent : baseEnd_5693315 < baseStart_5693315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693332 : List Nat := [2, 4, 2, 1, 1, 3, 3, 1, 1, 5]
def baseStart_5693332 : Nat := 118140960795 + 5693332 * 2 ^ 59
def prefixEnd_5693332 : Nat := 4983230072969 + 3 ^ 40 * 5693332 * 2
def baseEnd_5693332 : Nat := 974471947207874682022283

theorem tailTrace_5693332 : CollatzResearch.WordTrace tailWord_5693332 prefixEnd_5693332 974471947207874682022283 := by
  unfold tailWord_5693332
  simp only [CollatzResearch.WordTrace]
  refine ⟨103826438705018991269237125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138435251606691988358982833 103826438705018991269237125)
  ·
    refine ⟨19467457257191060862981961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103826438705018991269237125 19467457257191060862981961)
    ·
      refine ⟨14600592942893295647236471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19467457257191060862981961 14600592942893295647236471)
      ·
        refine ⟨21900889414339943470854707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14600592942893295647236471 21900889414339943470854707)
        ·
          refine ⟨32851334121509915206282061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21900889414339943470854707 32851334121509915206282061)
          ·
            refine ⟨12319250295566218202355773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32851334121509915206282061 12319250295566218202355773)
            ·
              refine ⟨4619718860837331825883415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12319250295566218202355773 4619718860837331825883415)
              ·
                refine ⟨6929578291255997738825123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4619718860837331825883415 6929578291255997738825123)
                ·
                  refine ⟨10394367436883996608237685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6929578291255997738825123 10394367436883996608237685)
                  ·
                    refine ⟨974471947207874682022283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10394367436883996608237685 974471947207874682022283)
                    ·
                      rfl

theorem cell23_5693332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_5693332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693332 prefixEnd_5693332 := by exact prefixLift 5693332
  have htrace : WordTrace (prefixWord ++ tailWord_5693332) baseStart_5693332 baseEnd_5693332 := by
    simpa [prefixWord, tailWord_5693332, baseEnd_5693332] using wordTrace_append hprefix tailTrace_5693332
  have hstable : (prefixWord ++ tailWord_5693332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693332).length < 2 ^ (prefixWord ++ tailWord_5693332).sum := by decide
  have hdescent : baseEnd_5693332 < baseStart_5693332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693341 : List Nat := [1, 4, 2, 1, 2, 13]
def baseStart_5693341 : Nat := 118140960795 + 5693341 * 2 ^ 59
def prefixEnd_5693341 : Nat := 4983230072969 + 3 ^ 40 * 5693341 * 2
def baseEnd_5693341 : Nat := 12030536884565903336849

theorem tailTrace_5693341 : CollatzResearch.WordTrace tailWord_5693341 prefixEnd_5693341 12030536884565903336849 := by
  unfold tailWord_5693341
  simp only [CollatzResearch.WordTrace]
  refine ⟨207653205667005377075551877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138435470444670251383701251 207653205667005377075551877)
  ·
    refine ⟨38934976062563508201665977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207653205667005377075551877 38934976062563508201665977)
    ·
      refine ⟨29201232046922631151249483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38934976062563508201665977 29201232046922631151249483)
      ·
        refine ⟨43801848070383946726874225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29201232046922631151249483 43801848070383946726874225)
        ·
          refine ⟨32851386052787960045155669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43801848070383946726874225 32851386052787960045155669)
          ·
            refine ⟨12030536884565903336849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 32851386052787960045155669 12030536884565903336849)
            ·
              rfl

theorem cell23_5693341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 13].length) (baseStart_5693341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693341 prefixEnd_5693341 := by exact prefixLift 5693341
  have htrace : WordTrace (prefixWord ++ tailWord_5693341) baseStart_5693341 baseEnd_5693341 := by
    simpa [prefixWord, tailWord_5693341, baseEnd_5693341] using wordTrace_append hprefix tailTrace_5693341
  have hstable : (prefixWord ++ tailWord_5693341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693341).length < 2 ^ (prefixWord ++ tailWord_5693341).sum := by decide
  have hdescent : baseEnd_5693341 < baseStart_5693341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693365 : List Nat := [1, 3, 3, 2, 1, 3, 2, 1, 1, 2, 4]
def baseStart_5693365 : Nat := 118140960795 + 5693365 * 2 ^ 59
def prefixEnd_5693365 : Nat := 4983230072969 + 3 ^ 40 * 5693365 * 2
def baseEnd_5693365 : Nat := 2923432786485222416954197

theorem tailTrace_5693365 : CollatzResearch.WordTrace tailWord_5693365 prefixEnd_5693365 2923432786485222416954197 := by
  unfold tailWord_5693365
  simp only [CollatzResearch.WordTrace]
  refine ⟨207654081018918429174425549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138436054012612286116283699 207654081018918429174425549)
  ·
    refine ⟨77870280382094410940409581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207654081018918429174425549 77870280382094410940409581)
    ·
      refine ⟨29201355143285404102653593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77870280382094410940409581 29201355143285404102653593)
      ·
        refine ⟨21901016357464053076990195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29201355143285404102653593 21901016357464053076990195)
        ·
          refine ⟨32851524536196079615485293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21901016357464053076990195 32851524536196079615485293)
          ·
            refine ⟨12319321701073529855806985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32851524536196079615485293 12319321701073529855806985)
            ·
              refine ⟨9239491275805147391855239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12319321701073529855806985 9239491275805147391855239)
              ·
                refine ⟨13859236913707721087782859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9239491275805147391855239 13859236913707721087782859)
                ·
                  refine ⟨20788855370561581631674289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13859236913707721087782859 20788855370561581631674289)
                  ·
                    refine ⟨15591641527921186223755717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20788855370561581631674289 15591641527921186223755717)
                    ·
                      refine ⟨2923432786485222416954197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15591641527921186223755717 2923432786485222416954197)
                      ·
                        rfl

theorem cell23_5693365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_5693365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693365 prefixEnd_5693365 := by exact prefixLift 5693365
  have htrace : WordTrace (prefixWord ++ tailWord_5693365) baseStart_5693365 baseEnd_5693365 := by
    simpa [prefixWord, tailWord_5693365, baseEnd_5693365] using wordTrace_append hprefix tailTrace_5693365
  have hstable : (prefixWord ++ tailWord_5693365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693365).length < 2 ^ (prefixWord ++ tailWord_5693365).sum := by decide
  have hdescent : baseEnd_5693365 < baseStart_5693365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693402 : List Nat := [3, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3]
def baseStart_5693402 : Nat := 118140960795 + 5693402 * 2 ^ 59
def prefixEnd_5693402 : Nat := 4983230072969 + 3 ^ 40 * 5693402 * 2
def baseEnd_5693402 : Nat := 2923451785269438772191527

theorem tailTrace_5693402 : CollatzResearch.WordTrace tailWord_5693402 prefixEnd_5693402 2923451785269438772191527 := by
  unfold tailWord_5693402
  simp only [CollatzResearch.WordTrace]
  refine ⟨51913857629946096123380615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138436953679856256329014973 51913857629946096123380615)
  ·
    refine ⟨77870786444919144185070923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51913857629946096123380615 77870786444919144185070923)
    ·
      refine ⟨116806179667378716277606385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77870786444919144185070923 116806179667378716277606385)
      ·
        refine ⟨87604634750534037208204789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116806179667378716277606385 87604634750534037208204789)
        ·
          refine ⟨8212934507862565988269199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87604634750534037208204789 8212934507862565988269199)
          ·
            refine ⟨12319401761793848982403799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8212934507862565988269199 12319401761793848982403799)
            ·
              refine ⟨18479102642690773473605699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12319401761793848982403799 18479102642690773473605699)
              ·
                refine ⟨27718653964036160210408549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18479102642690773473605699 27718653964036160210408549)
                ·
                  refine ⟨5197247618256780039451603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27718653964036160210408549 5197247618256780039451603)
                  ·
                    refine ⟨7795871427385170059177405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5197247618256780039451603 7795871427385170059177405)
                    ·
                      refine ⟨2923451785269438772191527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7795871427385170059177405 2923451785269438772191527)
                      ·
                        rfl

theorem cell23_5693402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_5693402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693402 prefixEnd_5693402 := by exact prefixLift 5693402
  have htrace : WordTrace (prefixWord ++ tailWord_5693402) baseStart_5693402 baseEnd_5693402 := by
    simpa [prefixWord, tailWord_5693402, baseEnd_5693402] using wordTrace_append hprefix tailTrace_5693402
  have hstable : (prefixWord ++ tailWord_5693402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693402).length < 2 ^ (prefixWord ++ tailWord_5693402).sum := by decide
  have hdescent : baseEnd_5693402 < baseStart_5693402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693418 : List Nat := [3, 1, 3, 1, 2, 1, 1, 3, 2, 6]
def baseStart_5693418 : Nat := 118140960795 + 5693418 * 2 ^ 59
def prefixEnd_5693418 : Nat := 4983230072969 + 3 ^ 40 * 5693418 * 2
def baseEnd_5693418 : Nat := 974486666986636903197151

theorem tailTrace_5693418 : CollatzResearch.WordTrace tailWord_5693418 prefixEnd_5693418 974486666986636903197151 := by
  unfold tailWord_5693418
  simp only [CollatzResearch.WordTrace]
  refine ⟨51914003521931604806526227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138437342725150946150736605 51914003521931604806526227)
  ·
    refine ⟨77871005282897407209789341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51914003521931604806526227 77871005282897407209789341)
    ·
      refine ⟨29201626981086527703671003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77871005282897407209789341 29201626981086527703671003)
      ·
        refine ⟨43802440471629791555506505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29201626981086527703671003 43802440471629791555506505)
        ·
          refine ⟨32851830353722343666629879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43802440471629791555506505 32851830353722343666629879)
          ·
            refine ⟨49277745530583515499944819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32851830353722343666629879 49277745530583515499944819)
            ·
              refine ⟨73916618295875273249917229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49277745530583515499944819 73916618295875273249917229)
              ·
                refine ⟨27718731860953227468718961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73916618295875273249917229 27718731860953227468718961)
                ·
                  refine ⟨20789048895714920601539221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27718731860953227468718961 20789048895714920601539221)
                  ·
                    refine ⟨974486666986636903197151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20789048895714920601539221 974486666986636903197151)
                    ·
                      rfl

theorem cell23_5693418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_5693418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693418 prefixEnd_5693418 := by exact prefixLift 5693418
  have htrace : WordTrace (prefixWord ++ tailWord_5693418) baseStart_5693418 baseEnd_5693418 := by
    simpa [prefixWord, tailWord_5693418, baseEnd_5693418] using wordTrace_append hprefix tailTrace_5693418
  have hstable : (prefixWord ++ tailWord_5693418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693418).length < 2 ^ (prefixWord ++ tailWord_5693418).sum := by decide
  have hdescent : baseEnd_5693418 < baseStart_5693418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693476 : List Nat := [2, 3, 1, 4, 2, 1, 1, 3, 2, 2, 2]
def baseStart_5693476 : Nat := 118140960795 + 5693476 * 2 ^ 59
def prefixEnd_5693476 : Nat := 4983230072969 + 3 ^ 40 * 5693476 * 2
def baseEnd_5693476 : Nat := 2923489782837871482666187

theorem tailTrace_5693476 : CollatzResearch.WordTrace tailWord_5693476 prefixEnd_5693476 2923489782837871482666187 := by
  unfold tailWord_5693476
  simp only [CollatzResearch.WordTrace]
  refine ⟨103829064760758147565858141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138438753014344196754477521 103829064760758147565858141)
  ·
    refine ⟨38935899285284305337196803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103829064760758147565858141 38935899285284305337196803)
    ·
      refine ⟨58403848927926458005795205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38935899285284305337196803 58403848927926458005795205)
      ·
        refine ⟨10950721673986210876086601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58403848927926458005795205 10950721673986210876086601)
        ·
          refine ⟨8213041255489658157064951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10950721673986210876086601 8213041255489658157064951)
          ·
            refine ⟨12319561883234487235597427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8213041255489658157064951 12319561883234487235597427)
            ·
              refine ⟨18479342824851730853396141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12319561883234487235597427 18479342824851730853396141)
              ·
                refine ⟨6929753559319399070023553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18479342824851730853396141 6929753559319399070023553)
                ·
                  refine ⟨5197315169489549302517665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6929753559319399070023553 5197315169489549302517665)
                  ·
                    refine ⟨3897986377117161976888249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5197315169489549302517665 3897986377117161976888249)
                    ·
                      refine ⟨2923489782837871482666187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3897986377117161976888249 2923489782837871482666187)
                      ·
                        rfl

theorem cell23_5693476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_5693476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693476 prefixEnd_5693476 := by exact prefixLift 5693476
  have htrace : WordTrace (prefixWord ++ tailWord_5693476) baseStart_5693476 baseEnd_5693476 := by
    simpa [prefixWord, tailWord_5693476, baseEnd_5693476] using wordTrace_append hprefix tailTrace_5693476
  have hstable : (prefixWord ++ tailWord_5693476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693476).length < 2 ^ (prefixWord ++ tailWord_5693476).sum := by decide
  have hdescent : baseEnd_5693476 < baseStart_5693476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693505 : List Nat := [1, 2, 5, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_5693505 : Nat := 118140960795 + 5693505 * 2 ^ 59
def prefixEnd_5693505 : Nat := 4983230072969 + 3 ^ 40 * 5693505 * 2
def baseEnd_5693505 : Nat := 2923504673776851869203553

theorem tailTrace_5693505 : CollatzResearch.WordTrace tailWord_5693505 prefixEnd_5693505 2923504673776851869203553 := by
  unfold tailWord_5693505
  simp only [CollatzResearch.WordTrace]
  refine ⟨207659187238411233084521969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138439458158940822056347979 207659187238411233084521969)
  ·
    refine ⟨155744390428808424813391477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207659187238411233084521969 155744390428808424813391477)
    ·
      refine ⟨14601036602700789826255451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 155744390428808424813391477 14601036602700789826255451)
      ·
        refine ⟨21901554904051184739383177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14601036602700789826255451 21901554904051184739383177)
        ·
          refine ⟨16426166178038388554537383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21901554904051184739383177 16426166178038388554537383)
          ·
            refine ⟨24639249267057582831806075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16426166178038388554537383 24639249267057582831806075)
            ·
              refine ⟨36958873900586374247709113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24639249267057582831806075 36958873900586374247709113)
              ·
                refine ⟨27719155425439780685781835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36958873900586374247709113 27719155425439780685781835)
                ·
                  refine ⟨41578733138159671028672753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27719155425439780685781835 41578733138159671028672753)
                  ·
                    refine ⟨31184049853619753271504565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41578733138159671028672753 31184049853619753271504565)
                    ·
                      refine ⟨2923504673776851869203553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31184049853619753271504565 2923504673776851869203553)
                      ·
                        rfl

theorem cell23_5693505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_5693505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693505 prefixEnd_5693505 := by exact prefixLift 5693505
  have htrace : WordTrace (prefixWord ++ tailWord_5693505) baseStart_5693505 baseEnd_5693505 := by
    simpa [prefixWord, tailWord_5693505, baseEnd_5693505] using wordTrace_append hprefix tailTrace_5693505
  have hstable : (prefixWord ++ tailWord_5693505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693505).length < 2 ^ (prefixWord ++ tailWord_5693505).sum := by decide
  have hdescent : baseEnd_5693505 < baseStart_5693505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693515 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 4, 4, 2]
def baseStart_5693515 : Nat := 118140960795 + 5693515 * 2 ^ 59
def prefixEnd_5693515 : Nat := 4983230072969 + 3 ^ 40 * 5693515 * 2
def baseEnd_5693515 : Nat := 2923509808583396830078507

theorem tailTrace_5693515 : CollatzResearch.WordTrace tailWord_5693515 prefixEnd_5693515 2923509808583396830078507 := by
  unfold tailWord_5693515
  simp only [CollatzResearch.WordTrace]
  refine ⟨207659551968375004792385999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138439701312250003194923999 207659551968375004792385999)
  ·
    refine ⟨311489327952562507188578999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207659551968375004792385999 311489327952562507188578999)
    ·
      refine ⟨467233991928843760782868499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311489327952562507188578999 467233991928843760782868499)
      ·
        refine ⟨700850987893265641174302749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467233991928843760782868499 700850987893265641174302749)
        ·
          refine ⟨262819120459974615440363531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 700850987893265641174302749 262819120459974615440363531)
          ·
            refine ⟨394228680689961923160545297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262819120459974615440363531 394228680689961923160545297)
            ·
              refine ⟨295671510517471442370408973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394228680689961923160545297 295671510517471442370408973)
              ·
                refine ⟨110876816444051790888903365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 295671510517471442370408973 110876816444051790888903365)
                ·
                  refine ⟨20789403083259710791669381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110876816444051790888903365 20789403083259710791669381)
                  ·
                    refine ⟨3898013078111195773438009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20789403083259710791669381 3898013078111195773438009)
                    ·
                      refine ⟨2923509808583396830078507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3898013078111195773438009 2923509808583396830078507)
                      ·
                        rfl

theorem cell23_5693515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 4, 2].length) (baseStart_5693515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693515 prefixEnd_5693515 := by exact prefixLift 5693515
  have htrace : WordTrace (prefixWord ++ tailWord_5693515) baseStart_5693515 baseEnd_5693515 := by
    simpa [prefixWord, tailWord_5693515, baseEnd_5693515] using wordTrace_append hprefix tailTrace_5693515
  have hstable : (prefixWord ++ tailWord_5693515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693515).length < 2 ^ (prefixWord ++ tailWord_5693515).sum := by decide
  have hdescent : baseEnd_5693515 < baseStart_5693515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693532 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 1, 6, 2]
def baseStart_5693532 : Nat := 118140960795 + 5693532 * 2 ^ 59
def prefixEnd_5693532 : Nat := 4983230072969 + 3 ^ 40 * 5693532 * 2
def baseEnd_5693532 : Nat := 2923518537754523263565929

theorem tailTrace_5693532 : CollatzResearch.WordTrace tailWord_5693532 prefixEnd_5693532 2923518537754523263565929 := by
  unfold tailWord_5693532
  simp only [CollatzResearch.WordTrace]
  refine ⟨103830086004656708347877425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138440114672875611130503233 103830086004656708347877425)
  ·
    refine ⟨77872564503492531260908069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103830086004656708347877425 77872564503492531260908069)
    ·
      refine ⟨14601105844404849611420263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77872564503492531260908069 14601105844404849611420263)
      ·
        refine ⟨21901658766607274417130395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14601105844404849611420263 21901658766607274417130395)
        ·
          refine ⟨32852488149910911625695593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21901658766607274417130395 32852488149910911625695593)
          ·
            refine ⟨24639366112433183719271695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32852488149910911625695593 24639366112433183719271695)
            ·
              refine ⟨36959049168649775578907543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24639366112433183719271695 36959049168649775578907543)
              ·
                refine ⟨55438573752974663368361315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36959049168649775578907543 55438573752974663368361315)
                ·
                  refine ⟨83157860629461995052541973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55438573752974663368361315 83157860629461995052541973)
                  ·
                    refine ⟨3898024717006031018087905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83157860629461995052541973 3898024717006031018087905)
                    ·
                      refine ⟨2923518537754523263565929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3898024717006031018087905 2923518537754523263565929)
                      ·
                        rfl

theorem cell23_5693532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_5693532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693532 prefixEnd_5693532 := by exact prefixLift 5693532
  have htrace : WordTrace (prefixWord ++ tailWord_5693532) baseStart_5693532 baseEnd_5693532 := by
    simpa [prefixWord, tailWord_5693532, baseEnd_5693532] using wordTrace_append hprefix tailTrace_5693532
  have hstable : (prefixWord ++ tailWord_5693532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693532).length < 2 ^ (prefixWord ++ tailWord_5693532).sum := by decide
  have hdescent : baseEnd_5693532 < baseStart_5693532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693552 : List Nat := [2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 3]
def baseStart_5693552 : Nat := 118140960795 + 5693552 * 2 ^ 59
def prefixEnd_5693552 : Nat := 4983230072969 + 3 ^ 40 * 5693552 * 2
def baseEnd_5693552 : Nat := 2923528807367613185315837

theorem tailTrace_5693552 : CollatzResearch.WordTrace tailWord_5693552 prefixEnd_5693552 2923528807367613185315837 := by
  unfold tailWord_5693552
  simp only [CollatzResearch.WordTrace]
  refine ⟨103830450734620480055741455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138440600979493973407655273 103830450734620480055741455)
  ·
    refine ⟨155745676101930720083612183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103830450734620480055741455 155745676101930720083612183)
    ·
      refine ⟨233618514152896080125418275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155745676101930720083612183 233618514152896080125418275)
      ·
        refine ⟨350427771229344120188127413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233618514152896080125418275 350427771229344120188127413)
        ·
          refine ⟨32852603552751011267636945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 350427771229344120188127413 32852603552751011267636945)
          ·
            refine ⟨24639452664563258450727709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32852603552751011267636945 24639452664563258450727709)
            ·
              refine ⟨9239794749211221919022891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24639452664563258450727709 9239794749211221919022891)
              ·
                refine ⟨13859692123816832878534337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9239794749211221919022891 13859692123816832878534337)
                ·
                  refine ⟨10394769092862624658900753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13859692123816832878534337 10394769092862624658900753)
                  ·
                    refine ⟨7796076819646968494175565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10394769092862624658900753 7796076819646968494175565)
                    ·
                      refine ⟨2923528807367613185315837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7796076819646968494175565 2923528807367613185315837)
                      ·
                        rfl

theorem cell23_5693552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 3].length) (baseStart_5693552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693552 prefixEnd_5693552 := by exact prefixLift 5693552
  have htrace : WordTrace (prefixWord ++ tailWord_5693552) baseStart_5693552 baseEnd_5693552 := by
    simpa [prefixWord, tailWord_5693552, baseEnd_5693552] using wordTrace_append hprefix tailTrace_5693552
  have hstable : (prefixWord ++ tailWord_5693552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693552).length < 2 ^ (prefixWord ++ tailWord_5693552).sum := by decide
  have hdescent : baseEnd_5693552 < baseStart_5693552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693559 : List Nat := [1, 1, 3, 1, 1, 6, 2, 3, 1, 4]
def baseStart_5693559 : Nat := 118140960795 + 5693559 * 2 ^ 59
def prefixEnd_5693559 : Nat := 4983230072969 + 3 ^ 40 * 5693559 * 2
def baseEnd_5693559 : Nat := 974510800577398219309435

theorem tailTrace_5693559 : CollatzResearch.WordTrace tailWord_5693559 prefixEnd_5693559 974510800577398219309435 := by
  unfold tailWord_5693559
  simp only [CollatzResearch.WordTrace]
  refine ⟨207661156780215600306987731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138440771186810400204658487 207661156780215600306987731)
  ·
    refine ⟨311491735170323400460481597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207661156780215600306987731 311491735170323400460481597)
    ·
      refine ⟨116809400688871275172680599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 311491735170323400460481597 116809400688871275172680599)
      ·
        refine ⟨175214101033306912759020899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116809400688871275172680599 175214101033306912759020899)
        ·
          refine ⟨262821151549960369138531349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175214101033306912759020899 262821151549960369138531349)
          ·
            refine ⟨12319741478904392303368657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 262821151549960369138531349 12319741478904392303368657)
            ·
              refine ⟨9239806109178294227526493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12319741478904392303368657 9239806109178294227526493)
              ·
                refine ⟨3464927290941860335322435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9239806109178294227526493 3464927290941860335322435)
                ·
                  refine ⟨5197390936412790502983653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3464927290941860335322435 5197390936412790502983653)
                  ·
                    refine ⟨974510800577398219309435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5197390936412790502983653 974510800577398219309435)
                    ·
                      rfl

theorem cell23_5693559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3, 1, 4].length) (baseStart_5693559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693559 prefixEnd_5693559 := by exact prefixLift 5693559
  have htrace : WordTrace (prefixWord ++ tailWord_5693559) baseStart_5693559 baseEnd_5693559 := by
    simpa [prefixWord, tailWord_5693559, baseEnd_5693559] using wordTrace_append hprefix tailTrace_5693559
  have hstable : (prefixWord ++ tailWord_5693559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693559).length < 2 ^ (prefixWord ++ tailWord_5693559).sum := by decide
  have hdescent : baseEnd_5693559 < baseStart_5693559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693599 : List Nat := [1, 1, 2, 6, 1, 1, 2, 2, 3, 1, 3]
def baseStart_5693599 : Nat := 118140960795 + 5693599 * 2 ^ 59
def prefixEnd_5693599 : Nat := 4983230072969 + 3 ^ 40 * 5693599 * 2
def baseEnd_5693599 : Nat := 2923552940958374501428121

theorem tailTrace_5693599 : CollatzResearch.WordTrace tailWord_5693599 prefixEnd_5693599 2923552940958374501428121 := by
  unfold tailWord_5693599
  simp only [CollatzResearch.WordTrace]
  refine ⟨207662615700070687138443851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138441743800047124758962567 207662615700070687138443851)
  ·
    refine ⟨311493923550106030707665777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207662615700070687138443851 311493923550106030707665777)
    ·
      refine ⟨233620442662579523030749333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311493923550106030707665777 233620442662579523030749333)
      ·
        refine ⟨10950958249808415142066375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 233620442662579523030749333 10950958249808415142066375)
        ·
          refine ⟨16426437374712622713099563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10950958249808415142066375 16426437374712622713099563)
          ·
            refine ⟨24639656062068934069649345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16426437374712622713099563 24639656062068934069649345)
            ·
              refine ⟨18479742046551700552237009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24639656062068934069649345 18479742046551700552237009)
              ·
                refine ⟨13859806534913775414177757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18479742046551700552237009 13859806534913775414177757)
                ·
                  refine ⟨5197427450592665780316659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13859806534913775414177757 5197427450592665780316659)
                  ·
                    refine ⟨7796141175888998670474989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5197427450592665780316659 7796141175888998670474989)
                    ·
                      refine ⟨2923552940958374501428121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7796141175888998670474989 2923552940958374501428121)
                      ·
                        rfl

theorem cell23_5693599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_5693599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693599 prefixEnd_5693599 := by exact prefixLift 5693599
  have htrace : WordTrace (prefixWord ++ tailWord_5693599) baseStart_5693599 baseEnd_5693599 := by
    simpa [prefixWord, tailWord_5693599, baseEnd_5693599] using wordTrace_append hprefix tailTrace_5693599
  have hstable : (prefixWord ++ tailWord_5693599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693599).length < 2 ^ (prefixWord ++ tailWord_5693599).sum := by decide
  have hdescent : baseEnd_5693599 < baseStart_5693599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693610 : List Nat := [3, 1, 5, 1, 3, 1, 1, 3, 1, 4]
def baseStart_5693610 : Nat := 118140960795 + 5693610 * 2 ^ 59
def prefixEnd_5693610 : Nat := 4983230072969 + 3 ^ 40 * 5693610 * 2
def baseEnd_5693610 : Nat := 974519529748524652796857

theorem tailTrace_5693610 : CollatzResearch.WordTrace tailWord_5693610 prefixEnd_5693610 974519529748524652796857 := by
  unfold tailWord_5693610
  simp only [CollatzResearch.WordTrace]
  refine ⟨51915754225757709004273571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138442011268687224011396189 51915754225757709004273571)
  ·
    refine ⟨77873631338636563506410357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51915754225757709004273571 77873631338636563506410357)
    ·
      refine ⟨7300652937997177828725971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77873631338636563506410357 7300652937997177828725971)
      ·
        refine ⟨10950979406995766743088957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7300652937997177828725971 10950979406995766743088957)
        ·
          refine ⟨4106617277623412528658359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10950979406995766743088957 4106617277623412528658359)
          ·
            refine ⟨6159925916435118792987539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4106617277623412528658359 6159925916435118792987539)
            ·
              refine ⟨9239888874652678189481309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6159925916435118792987539 9239888874652678189481309)
              ·
                refine ⟨3464958327994754321055491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9239888874652678189481309 3464958327994754321055491)
                ·
                  refine ⟨5197437491992131481583237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3464958327994754321055491 5197437491992131481583237)
                  ·
                    refine ⟨974519529748524652796857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5197437491992131481583237 974519529748524652796857)
                    ·
                      rfl

theorem cell23_5693610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_5693610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693610 prefixEnd_5693610 := by exact prefixLift 5693610
  have htrace : WordTrace (prefixWord ++ tailWord_5693610) baseStart_5693610 baseEnd_5693610 := by
    simpa [prefixWord, tailWord_5693610, baseEnd_5693610] using wordTrace_append hprefix tailTrace_5693610
  have hstable : (prefixWord ++ tailWord_5693610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693610).length < 2 ^ (prefixWord ++ tailWord_5693610).sum := by decide
  have hdescent : baseEnd_5693610 < baseStart_5693610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693632 : List Nat := [2, 1, 1, 2, 5, 1, 2, 1, 4, 4]
def baseStart_5693632 : Nat := 118140960795 + 5693632 * 2 ^ 59
def prefixEnd_5693632 : Nat := 4983230072969 + 3 ^ 40 * 5693632 * 2
def baseEnd_5693632 : Nat := 974523295273324290771823

theorem tailTrace_5693632 : CollatzResearch.WordTrace tailWord_5693632 prefixEnd_5693632 974523295273324290771823 := by
  unfold tailWord_5693632
  simp only [CollatzResearch.WordTrace]
  refine ⟨103831909654475566887197575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138442546205967422516263433 103831909654475566887197575)
  ·
    refine ⟨155747864481713350330796363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103831909654475566887197575 155747864481713350330796363)
    ·
      refine ⟨233621796722570025496194545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155747864481713350330796363 233621796722570025496194545)
      ·
        refine ⟨175216347541927519122145909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233621796722570025496194545 175216347541927519122145909)
        ·
          refine ⟨16426532582055704917701179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 175216347541927519122145909 16426532582055704917701179)
          ·
            refine ⟨24639798873083557376551769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16426532582055704917701179 24639798873083557376551769)
            ·
              refine ⟨18479849154812668032413827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24639798873083557376551769 18479849154812668032413827)
              ·
                refine ⟨27719773732219002048620741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18479849154812668032413827 27719773732219002048620741)
                ·
                  refine ⟨5197457574791062884116389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27719773732219002048620741 5197457574791062884116389)
                  ·
                    refine ⟨974523295273324290771823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5197457574791062884116389 974523295273324290771823)
                    ·
                      rfl

theorem cell23_5693632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 4, 4].length) (baseStart_5693632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693632 prefixEnd_5693632 := by exact prefixLift 5693632
  have htrace : WordTrace (prefixWord ++ tailWord_5693632) baseStart_5693632 baseEnd_5693632 := by
    simpa [prefixWord, tailWord_5693632, baseEnd_5693632] using wordTrace_append hprefix tailTrace_5693632
  have hstable : (prefixWord ++ tailWord_5693632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693632).length < 2 ^ (prefixWord ++ tailWord_5693632).sum := by decide
  have hdescent : baseEnd_5693632 < baseStart_5693632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693633 : List Nat := [1, 2, 6, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_5693633 : Nat := 118140960795 + 5693633 * 2 ^ 59
def prefixEnd_5693633 : Nat := 4983230072969 + 3 ^ 40 * 5693633 * 2
def baseEnd_5693633 : Nat := 2923570399300627368402965

theorem tailTrace_5693633 : CollatzResearch.WordTrace tailWord_5693633 prefixEnd_5693633 2923570399300627368402965 := by
  unfold tailWord_5693633
  simp only [CollatzResearch.WordTrace]
  refine ⟨207663855781947510945181553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138442570521298340630121035 207663855781947510945181553)
  ·
    refine ⟨155747891836460633208886165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207663855781947510945181553 155747891836460633208886165)
    ·
      refine ⟨7300682429834092181666539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 155747891836460633208886165 7300682429834092181666539)
      ·
        refine ⟨10951023644751138272499809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7300682429834092181666539 10951023644751138272499809)
        ·
          refine ⟨8213267733563353704374857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10951023644751138272499809 8213267733563353704374857)
          ·
            refine ⟨6159950800172515278281143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8213267733563353704374857 6159950800172515278281143)
            ·
              refine ⟨9239926200258772917421715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6159950800172515278281143 9239926200258772917421715)
              ·
                refine ⟨13859889300388159376132573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9239926200258772917421715 13859889300388159376132573)
                ·
                  refine ⟨5197458487645559766049715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13859889300388159376132573 5197458487645559766049715)
                  ·
                    refine ⟨7796187731468339649074573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5197458487645559766049715 7796187731468339649074573)
                    ·
                      refine ⟨2923570399300627368402965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7796187731468339649074573 2923570399300627368402965)
                      ·
                        rfl

theorem cell23_5693633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_5693633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693633 prefixEnd_5693633 := by exact prefixLift 5693633
  have htrace : WordTrace (prefixWord ++ tailWord_5693633) baseStart_5693633 baseEnd_5693633 := by
    simpa [prefixWord, tailWord_5693633, baseEnd_5693633] using wordTrace_append hprefix tailTrace_5693633
  have hstable : (prefixWord ++ tailWord_5693633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693633).length < 2 ^ (prefixWord ++ tailWord_5693633).sum := by decide
  have hdescent : baseEnd_5693633 < baseStart_5693633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693642 : List Nat := [3, 1, 2, 1, 3, 1, 2, 2, 3, 2, 3]
def baseStart_5693642 : Nat := 118140960795 + 5693642 * 2 ^ 59
def prefixEnd_5693642 : Nat := 4983230072969 + 3 ^ 40 * 5693642 * 2
def baseEnd_5693642 : Nat := 2923575020626517833190423

theorem tailTrace_5693642 : CollatzResearch.WordTrace tailWord_5693642 prefixEnd_5693642 2923575020626517833190423 := by
  unfold tailWord_5693642
  simp only [CollatzResearch.WordTrace]
  refine ⟨51916046009728726370564795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138442789359276603654839453 51916046009728726370564795)
  ·
    refine ⟨77874069014593089555847193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51916046009728726370564795 77874069014593089555847193)
    ·
      refine ⟨58405551760944817166885395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77874069014593089555847193 58405551760944817166885395)
      ·
        refine ⟨87608327641417225750328093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58405551760944817166885395 87608327641417225750328093)
        ·
          refine ⟨32853122865531459656373035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87608327641417225750328093 32853122865531459656373035)
          ·
            refine ⟨49279684298297189484559553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32853122865531459656373035 49279684298297189484559553)
            ·
              refine ⟨36959763223722892113419665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49279684298297189484559553 36959763223722892113419665)
              ·
                refine ⟨27719822417792169085064749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36959763223722892113419665 27719822417792169085064749)
                ·
                  refine ⟨10394933406672063406899281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27719822417792169085064749 10394933406672063406899281)
                  ·
                    refine ⟨7796200055004047555174461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10394933406672063406899281 7796200055004047555174461)
                    ·
                      refine ⟨2923575020626517833190423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7796200055004047555174461 2923575020626517833190423)
                      ·
                        rfl

theorem cell23_5693642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_5693642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693642 prefixEnd_5693642 := by exact prefixLift 5693642
  have htrace : WordTrace (prefixWord ++ tailWord_5693642) baseStart_5693642 baseEnd_5693642 := by
    simpa [prefixWord, tailWord_5693642, baseEnd_5693642] using wordTrace_append hprefix tailTrace_5693642
  have hstable : (prefixWord ++ tailWord_5693642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693642).length < 2 ^ (prefixWord ++ tailWord_5693642).sum := by decide
  have hdescent : baseEnd_5693642 < baseStart_5693642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693649 : List Nat := [1, 2, 2, 1, 2, 2, 6, 1, 2, 4]
def baseStart_5693649 : Nat := 118140960795 + 5693649 * 2 ^ 59
def prefixEnd_5693649 : Nat := 4983230072969 + 3 ^ 40 * 5693649 * 2
def baseEnd_5693649 : Nat := 974526204997033101934297

theorem tailTrace_5693649 : CollatzResearch.WordTrace tailWord_5693649 prefixEnd_5693649 974526204997033101934297 := by
  unfold tailWord_5693649
  simp only [CollatzResearch.WordTrace]
  refine ⟨207664439349889545677764001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138442959566593030451842667 207664439349889545677764001)
  ·
    refine ⟨155748329512417159258323001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207664439349889545677764001 155748329512417159258323001)
    ·
      refine ⟨116811247134312869443742251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155748329512417159258323001 116811247134312869443742251)
      ·
        refine ⟨175216870701469304165613377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116811247134312869443742251 175216870701469304165613377)
        ·
          refine ⟨131412653026101978124210033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175216870701469304165613377 131412653026101978124210033)
          ·
            refine ⟨98559489769576483593157525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131412653026101978124210033 98559489769576483593157525)
            ·
              refine ⟨4619976082948897668429259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 98559489769576483593157525 4619976082948897668429259)
              ·
                refine ⟨6929964124423346502643889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4619976082948897668429259 6929964124423346502643889)
                ·
                  refine ⟨5197473093317509876982917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6929964124423346502643889 5197473093317509876982917)
                  ·
                    refine ⟨974526204997033101934297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5197473093317509876982917 974526204997033101934297)
                    ·
                      rfl

theorem cell23_5693649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 2, 4].length) (baseStart_5693649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693649 prefixEnd_5693649 := by exact prefixLift 5693649
  have htrace : WordTrace (prefixWord ++ tailWord_5693649) baseStart_5693649 baseEnd_5693649 := by
    simpa [prefixWord, tailWord_5693649, baseEnd_5693649] using wordTrace_append hprefix tailTrace_5693649
  have hstable : (prefixWord ++ tailWord_5693649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693649).length < 2 ^ (prefixWord ++ tailWord_5693649).sum := by decide
  have hdescent : baseEnd_5693649 < baseStart_5693649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693672 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 3, 3, 3]
def baseStart_5693672 : Nat := 118140960795 + 5693672 * 2 ^ 59
def prefixEnd_5693672 : Nat := 4983230072969 + 3 ^ 40 * 5693672 * 2
def baseEnd_5693672 : Nat := 2923590425046152715815285

theorem tailTrace_5693672 : CollatzResearch.WordTrace tailWord_5693672 prefixEnd_5693672 2923590425046152715815285 := by
  unfold tailWord_5693672
  simp only [CollatzResearch.WordTrace]
  refine ⟨103832639114403110302925635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138443518819204147070567513 103832639114403110302925635)
  ·
    refine ⟨155748958671604665454388453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103832639114403110302925635 155748958671604665454388453)
    ·
      refine ⟨29202929750925874772697835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155748958671604665454388453 29202929750925874772697835)
      ·
        refine ⟨43804394626388812159046753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29202929750925874772697835 43804394626388812159046753)
        ·
          refine ⟨32853295969791609119285065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43804394626388812159046753 32853295969791609119285065)
          ·
            refine ⟨24639971977343706839463799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32853295969791609119285065 24639971977343706839463799)
            ·
              refine ⟨36959957966015560259195699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24639971977343706839463799 36959957966015560259195699)
              ·
                refine ⟨55439936949023340388793549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36959957966015560259195699 55439936949023340388793549)
                ·
                  refine ⟨20789976355883752645797581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55439936949023340388793549 20789976355883752645797581)
                  ·
                    refine ⟨7796241133456407242174093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20789976355883752645797581 7796241133456407242174093)
                    ·
                      refine ⟨2923590425046152715815285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7796241133456407242174093 2923590425046152715815285)
                      ·
                        rfl

theorem cell23_5693672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_5693672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693672 prefixEnd_5693672 := by exact prefixLift 5693672
  have htrace : WordTrace (prefixWord ++ tailWord_5693672) baseStart_5693672 baseEnd_5693672 := by
    simpa [prefixWord, tailWord_5693672, baseEnd_5693672] using wordTrace_append hprefix tailTrace_5693672
  have hstable : (prefixWord ++ tailWord_5693672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693672).length < 2 ^ (prefixWord ++ tailWord_5693672).sum := by decide
  have hdescent : baseEnd_5693672 < baseStart_5693672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693690 : List Nat := [3, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2]
def baseStart_5693690 : Nat := 118140960795 + 5693690 * 2 ^ 59
def prefixEnd_5693690 : Nat := 4983230072969 + 3 ^ 40 * 5693690 * 2
def baseEnd_5693690 : Nat := 2923599667697933645390203

theorem tailTrace_5693690 : CollatzResearch.WordTrace tailWord_5693690 prefixEnd_5693690 2923599667697933645390203 := by
  unfold tailWord_5693690
  simp only [CollatzResearch.WordTrace]
  refine ⟨51916483685685252420001631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138443956495160673120004349 51916483685685252420001631)
  ·
    refine ⟨77874725528527878630002447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51916483685685252420001631 77874725528527878630002447)
    ·
      refine ⟨116812088292791817945003671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77874725528527878630002447 116812088292791817945003671)
      ·
        refine ⟨175218132439187726917505507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116812088292791817945003671 175218132439187726917505507)
        ·
          refine ⟨262827198658781590376258261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175218132439187726917505507 262827198658781590376258261)
          ·
            refine ⟨6160012468565193524443553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 262827198658781590376258261 6160012468565193524443553)
            ·
              refine ⟨4620009351423895143332665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6160012468565193524443553 4620009351423895143332665)
              ·
                refine ⟨3465007013567921357499499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4620009351423895143332665 3465007013567921357499499)
                ·
                  refine ⟨5197510520351882036249249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3465007013567921357499499 5197510520351882036249249)
                  ·
                    refine ⟨3898132890263911527186937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5197510520351882036249249 3898132890263911527186937)
                    ·
                      refine ⟨2923599667697933645390203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3898132890263911527186937 2923599667697933645390203)
                      ·
                        rfl

theorem cell23_5693690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2].length) (baseStart_5693690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693690 prefixEnd_5693690 := by exact prefixLift 5693690
  have htrace : WordTrace (prefixWord ++ tailWord_5693690) baseStart_5693690 baseEnd_5693690 := by
    simpa [prefixWord, tailWord_5693690, baseEnd_5693690] using wordTrace_append hprefix tailTrace_5693690
  have hstable : (prefixWord ++ tailWord_5693690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693690).length < 2 ^ (prefixWord ++ tailWord_5693690).sum := by decide
  have hdescent : baseEnd_5693690 < baseStart_5693690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693695 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 4]
def baseStart_5693695 : Nat := 118140960795 + 5693695 * 2 ^ 59
def prefixEnd_5693695 : Nat := 4983230072969 + 3 ^ 40 * 5693695 * 2
def baseEnd_5693695 : Nat := 2923602235101206125827679

theorem tailTrace_5693695 : CollatzResearch.WordTrace tailWord_5693695 prefixEnd_5693695 2923602235101206125827679 := by
  unfold tailWord_5693695
  simp only [CollatzResearch.WordTrace]
  refine ⟨207666117107722895533938539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138444078071815263689292359 207666117107722895533938539)
  ·
    refine ⟨311499175661584343300907809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207666117107722895533938539 311499175661584343300907809)
    ·
      refine ⟨233624381746188257475680857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311499175661584343300907809 233624381746188257475680857)
      ·
        refine ⟨175218286309641193106760643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233624381746188257475680857 175218286309641193106760643)
        ·
          refine ⟨262827429464461789660140965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175218286309641193106760643 262827429464461789660140965)
          ·
            refine ⟨49280143024586585561276431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 262827429464461789660140965 49280143024586585561276431)
            ·
              refine ⟨73920214536879878341914647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49280143024586585561276431 73920214536879878341914647)
              ·
                refine ⟨110880321805319817512871971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73920214536879878341914647 110880321805319817512871971)
                ·
                  refine ⟨166320482707979726269307957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110880321805319817512871971 166320482707979726269307957)
                  ·
                    refine ⟨15592545253873099337747621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 166320482707979726269307957 15592545253873099337747621)
                    ·
                      refine ⟨2923602235101206125827679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15592545253873099337747621 2923602235101206125827679)
                      ·
                        rfl

theorem cell23_5693695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_5693695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693695 prefixEnd_5693695 := by exact prefixLift 5693695
  have htrace : WordTrace (prefixWord ++ tailWord_5693695) baseStart_5693695 baseEnd_5693695 := by
    simpa [prefixWord, tailWord_5693695, baseEnd_5693695] using wordTrace_append hprefix tailTrace_5693695
  have hstable : (prefixWord ++ tailWord_5693695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693695).length < 2 ^ (prefixWord ++ tailWord_5693695).sum := by decide
  have hdescent : baseEnd_5693695 < baseStart_5693695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693705 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 1, 8]
def baseStart_5693705 : Nat := 118140960795 + 5693705 * 2 ^ 59
def prefixEnd_5693705 : Nat := 4983230072969 + 3 ^ 40 * 5693705 * 2
def baseEnd_5693705 : Nat := 974535789969250362234211

theorem tailTrace_5693705 : CollatzResearch.WordTrace tailWord_5693705 prefixEnd_5693705 974535789969250362234211 := by
  unfold tailWord_5693705
  simp only [CollatzResearch.WordTrace]
  refine ⟨207666481837686667241802569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138444321225124444827868379 207666481837686667241802569)
  ·
    refine ⟨155749861378265000431351927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207666481837686667241802569 155749861378265000431351927)
    ·
      refine ⟨233624792067397500647027891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155749861378265000431351927 233624792067397500647027891)
      ·
        refine ⟨350437188101096250970541837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233624792067397500647027891 350437188101096250970541837)
        ·
          refine ⟨131413945537911094113953189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 350437188101096250970541837 131413945537911094113953189)
          ·
            refine ⟨24640114788358330146366223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131413945537911094113953189 24640114788358330146366223)
            ·
              refine ⟨36960172182537495219549335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24640114788358330146366223 36960172182537495219549335)
              ·
                refine ⟨55440258273806242829324003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36960172182537495219549335 55440258273806242829324003)
                ·
                  refine ⟨83160387410709364243986005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55440258273806242829324003 83160387410709364243986005)
                  ·
                    refine ⟨974535789969250362234211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83160387410709364243986005 974535789969250362234211)
                    ·
                      rfl

theorem cell23_5693705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 8].length) (baseStart_5693705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693705 prefixEnd_5693705 := by exact prefixLift 5693705
  have htrace : WordTrace (prefixWord ++ tailWord_5693705) baseStart_5693705 baseEnd_5693705 := by
    simpa [prefixWord, tailWord_5693705, baseEnd_5693705] using wordTrace_append hprefix tailTrace_5693705
  have hstable : (prefixWord ++ tailWord_5693705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693705).length < 2 ^ (prefixWord ++ tailWord_5693705).sum := by decide
  have hdescent : baseEnd_5693705 < baseStart_5693705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693715 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 5]
def baseStart_5693715 : Nat := 118140960795 + 5693715 * 2 ^ 59
def prefixEnd_5693715 : Nat := 4983230072969 + 3 ^ 40 * 5693715 * 2
def baseEnd_5693715 : Nat := 2923612504714296047577587

theorem tailTrace_5693715 : CollatzResearch.WordTrace tailWord_5693715 prefixEnd_5693715 2923612504714296047577587 := by
  unfold tailWord_5693715
  simp only [CollatzResearch.WordTrace]
  refine ⟨207666846567650438949666599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138444564378433625966444399 207666846567650438949666599)
  ·
    refine ⟨311500269851475658424499899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207666846567650438949666599 311500269851475658424499899)
    ·
      refine ⟨467250404777213487636749849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311500269851475658424499899 467250404777213487636749849)
      ·
        refine ⟨350437803582910115727562387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 467250404777213487636749849 350437803582910115727562387)
        ·
          refine ⟨525656705374365173591343581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350437803582910115727562387 525656705374365173591343581)
          ·
            refine ⟨197121264515386940096753843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 525656705374365173591343581 197121264515386940096753843)
            ·
              refine ⟨295681896773080410145130765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197121264515386940096753843 295681896773080410145130765)
              ·
                refine ⟨110880711289905153804424037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 295681896773080410145130765 110880711289905153804424037)
                ·
                  refine ⟨20790133366857216338329507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110880711289905153804424037 20790133366857216338329507)
                  ·
                    refine ⟨31185200050285824507494261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20790133366857216338329507 31185200050285824507494261)
                    ·
                      refine ⟨2923612504714296047577587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31185200050285824507494261 2923612504714296047577587)
                      ·
                        rfl

theorem cell23_5693715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 5].length) (baseStart_5693715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693715 prefixEnd_5693715 := by exact prefixLift 5693715
  have htrace : WordTrace (prefixWord ++ tailWord_5693715) baseStart_5693715 baseEnd_5693715 := by
    simpa [prefixWord, tailWord_5693715, baseEnd_5693715] using wordTrace_append hprefix tailTrace_5693715
  have hstable : (prefixWord ++ tailWord_5693715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693715).length < 2 ^ (prefixWord ++ tailWord_5693715).sum := by decide
  have hdescent : baseEnd_5693715 < baseStart_5693715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693729 : List Nat := [1, 2, 3, 2, 1, 1, 4, 2, 1, 4, 2]
def baseStart_5693729 : Nat := 118140960795 + 5693729 * 2 ^ 59
def prefixEnd_5693729 : Nat := 4983230072969 + 3 ^ 40 * 5693729 * 2
def baseEnd_5693729 : Nat := 2923619693443458992802523

theorem tailTrace_5693729 : CollatzResearch.WordTrace tailWord_5693729 prefixEnd_5693729 2923619693443458992802523 := by
  unfold tailWord_5693729
  simp only [CollatzResearch.WordTrace]
  refine ⟨207667357189599719340676241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138444904793066479560450827 207667357189599719340676241)
  ·
    refine ⟨155750517892199789505507181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207667357189599719340676241 155750517892199789505507181)
    ·
      refine ⟨58406444209574921064565193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155750517892199789505507181 58406444209574921064565193)
      ·
        refine ⟨43804833157181190798423895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58406444209574921064565193 43804833157181190798423895)
        ·
          refine ⟨65707249735771786197635843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43804833157181190798423895 65707249735771786197635843)
          ·
            refine ⟨98560874603657679296453765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65707249735771786197635843 98560874603657679296453765)
            ·
              refine ⟨18480163988185814868085081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98560874603657679296453765 18480163988185814868085081)
              ·
                refine ⟨13860122991139361151063811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18480163988185814868085081 13860122991139361151063811)
                ·
                  refine ⟨20790184486709041726595717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13860122991139361151063811 20790184486709041726595717)
                  ·
                    refine ⟨3898159591257945323736697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20790184486709041726595717 3898159591257945323736697)
                    ·
                      refine ⟨2923619693443458992802523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3898159591257945323736697 2923619693443458992802523)
                      ·
                        rfl

theorem cell23_5693729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_5693729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693729 prefixEnd_5693729 := by exact prefixLift 5693729
  have htrace : WordTrace (prefixWord ++ tailWord_5693729) baseStart_5693729 baseEnd_5693729 := by
    simpa [prefixWord, tailWord_5693729, baseEnd_5693729] using wordTrace_append hprefix tailTrace_5693729
  have hstable : (prefixWord ++ tailWord_5693729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693729).length < 2 ^ (prefixWord ++ tailWord_5693729).sum := by decide
  have hdescent : baseEnd_5693729 < baseStart_5693729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693775 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 7]
def baseStart_5693775 : Nat := 118140960795 + 5693775 * 2 ^ 59
def prefixEnd_5693775 : Nat := 4983230072969 + 3 ^ 40 * 5693775 * 2
def baseEnd_5693775 : Nat := 2923643313553565812827311

theorem tailTrace_5693775 : CollatzResearch.WordTrace tailWord_5693775 prefixEnd_5693775 2923643313553565812827311 := by
  unfold tailWord_5693775
  simp only [CollatzResearch.WordTrace]
  refine ⟨207669034947433069196850779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138446023298288712797900519 207669034947433069196850779)
  ·
    refine ⟨311503552421149603795276169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207669034947433069196850779 311503552421149603795276169)
    ·
      refine ⟨233627664315862202846457127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311503552421149603795276169 233627664315862202846457127)
      ·
        refine ⟨350441496473793304269685691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233627664315862202846457127 350441496473793304269685691)
        ·
          refine ⟨525662244710689956404528537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350441496473793304269685691 525662244710689956404528537)
          ·
            refine ⟨394246683533017467303396403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 525662244710689956404528537 394246683533017467303396403)
            ·
              refine ⟨591370025299526200955094605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394246683533017467303396403 591370025299526200955094605)
              ·
                refine ⟨221763759487322325358160477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 591370025299526200955094605 221763759487322325358160477)
                ·
                  refine ⟨83161409807745872009310179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221763759487322325358160477 83161409807745872009310179)
                  ·
                    refine ⟨124742114711618808013965269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 83161409807745872009310179 124742114711618808013965269)
                    ·
                      refine ⟨2923643313553565812827311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124742114711618808013965269 2923643313553565812827311)
                      ·
                        rfl

theorem cell23_5693775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 7].length) (baseStart_5693775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693775 prefixEnd_5693775 := by exact prefixLift 5693775
  have htrace : WordTrace (prefixWord ++ tailWord_5693775) baseStart_5693775 baseEnd_5693775 := by
    simpa [prefixWord, tailWord_5693775, baseEnd_5693775] using wordTrace_append hprefix tailTrace_5693775
  have hstable : (prefixWord ++ tailWord_5693775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693775).length < 2 ^ (prefixWord ++ tailWord_5693775).sum := by decide
  have hdescent : baseEnd_5693775 < baseStart_5693775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693799 : List Nat := [1, 1, 5, 1, 3, 2, 1, 2, 2, 5]
def baseStart_5693799 : Nat := 118140960795 + 5693799 * 2 ^ 59
def prefixEnd_5693799 : Nat := 4983230072969 + 3 ^ 40 * 5693799 * 2
def baseEnd_5693799 : Nat := 974551879029757906309067

theorem tailTrace_5693799 : CollatzResearch.WordTrace tailWord_5693799 prefixEnd_5693799 974551879029757906309067 := by
  unfold tailWord_5693799
  simp only [CollatzResearch.WordTrace]
  refine ⟨207669910299346121295724451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138446606866230747530482967 207669910299346121295724451)
  ·
    refine ⟨311504865449019181943586677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207669910299346121295724451 311504865449019181943586677)
    ·
      refine ⟨29203581135845548307211251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 311504865449019181943586677 29203581135845548307211251)
      ·
        refine ⟨43805371703768322460816877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29203581135845548307211251 43805371703768322460816877)
        ·
          refine ⟨16427014388913120922806329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43805371703768322460816877 16427014388913120922806329)
          ·
            refine ⟨12320260791684840692104747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16427014388913120922806329 12320260791684840692104747)
            ·
              refine ⟨18480391187527261038157121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12320260791684840692104747 18480391187527261038157121)
              ·
                refine ⟨13860293390645445778617841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18480391187527261038157121 13860293390645445778617841)
                ·
                  refine ⟨10395220042984084333963381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13860293390645445778617841 10395220042984084333963381)
                  ·
                    refine ⟨974551879029757906309067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10395220042984084333963381 974551879029757906309067)
                    ·
                      rfl

theorem cell23_5693799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_5693799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693799 prefixEnd_5693799 := by exact prefixLift 5693799
  have htrace : WordTrace (prefixWord ++ tailWord_5693799) baseStart_5693799 baseEnd_5693799 := by
    simpa [prefixWord, tailWord_5693799, baseEnd_5693799] using wordTrace_append hprefix tailTrace_5693799
  have hstable : (prefixWord ++ tailWord_5693799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693799).length < 2 ^ (prefixWord ++ tailWord_5693799).sum := by decide
  have hdescent : baseEnd_5693799 < baseStart_5693799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693814 : List Nat := [5, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2]
def baseStart_5693814 : Nat := 118140960795 + 5693814 * 2 ^ 59
def prefixEnd_5693814 : Nat := 4983230072969 + 3 ^ 40 * 5693814 * 2
def baseEnd_5693814 : Nat := 2923663339299091160239633

theorem tailTrace_5693814 : CollatzResearch.WordTrace tailWord_5693814 prefixEnd_5693814 2923663339299091160239633 := by
  unfold tailWord_5693814
  simp only [CollatzResearch.WordTrace]
  refine ⟨12979403587143236178595031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138446971596194519238346997 12979403587143236178595031)
  ·
    refine ⟨19469105380714854267892547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12979403587143236178595031 19469105380714854267892547)
    ·
      refine ⟨29203658071072281401838821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19469105380714854267892547 29203658071072281401838821)
      ·
        refine ⟨5475685888326052762844779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29203658071072281401838821 5475685888326052762844779)
        ·
          refine ⟨8213528832489079144267169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5475685888326052762844779 8213528832489079144267169)
          ·
            refine ⟨6160146624366809358200377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8213528832489079144267169 6160146624366809358200377)
            ·
              refine ⟨4620109968275107018650283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6160146624366809358200377 4620109968275107018650283)
              ·
                refine ⟨6930164952412660527975425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4620109968275107018650283 6930164952412660527975425)
                ·
                  refine ⟨5197623714309495395981569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6930164952412660527975425 5197623714309495395981569)
                  ·
                    refine ⟨3898217785732121546986177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5197623714309495395981569 3898217785732121546986177)
                    ·
                      refine ⟨2923663339299091160239633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3898217785732121546986177 2923663339299091160239633)
                      ·
                        rfl

theorem cell23_5693814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_5693814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693814 prefixEnd_5693814 := by exact prefixLift 5693814
  have htrace : WordTrace (prefixWord ++ tailWord_5693814) baseStart_5693814 baseEnd_5693814 := by
    simpa [prefixWord, tailWord_5693814, baseEnd_5693814] using wordTrace_append hprefix tailTrace_5693814
  have hstable : (prefixWord ++ tailWord_5693814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693814).length < 2 ^ (prefixWord ++ tailWord_5693814).sum := by decide
  have hdescent : baseEnd_5693814 < baseStart_5693814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693859 : List Nat := [1, 1, 1, 4, 1, 5, 2, 2, 6]
def baseStart_5693859 : Nat := 118140960795 + 5693859 * 2 ^ 59
def prefixEnd_5693859 : Nat := 4983230072969 + 3 ^ 40 * 5693859 * 2
def baseEnd_5693859 : Nat := 324854049547615942686325

theorem tailTrace_5693859 : CollatzResearch.WordTrace tailWord_5693859 prefixEnd_5693859 324854049547615942686325 := by
  unfold tailWord_5693859
  simp only [CollatzResearch.WordTrace]
  refine ⟨207672098679128751542908631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138448065786085834361939087 207672098679128751542908631)
  ·
    refine ⟨311508148018693127314362947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207672098679128751542908631 311508148018693127314362947)
    ·
      refine ⟨467262222028039690971544421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311508148018693127314362947 467262222028039690971544421)
      ·
        refine ⟨87611666630257442057164579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 467262222028039690971544421 87611666630257442057164579)
        ·
          refine ⟨131417499945386163085746869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87611666630257442057164579 131417499945386163085746869)
          ·
            refine ⟨12320390619879952789288769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131417499945386163085746869 12320390619879952789288769)
            ·
              refine ⟨9240292964909964591966577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12320390619879952789288769 9240292964909964591966577)
              ·
                refine ⟨6930219723682473443974933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9240292964909964591966577 6930219723682473443974933)
                ·
                  refine ⟨324854049547615942686325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6930219723682473443974933 324854049547615942686325)
                  ·
                    rfl

theorem cell23_5693859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 6].length) (baseStart_5693859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693859 prefixEnd_5693859 := by exact prefixLift 5693859
  have htrace : WordTrace (prefixWord ++ tailWord_5693859) baseStart_5693859 baseEnd_5693859 := by
    simpa [prefixWord, tailWord_5693859, baseEnd_5693859] using wordTrace_append hprefix tailTrace_5693859
  have hstable : (prefixWord ++ tailWord_5693859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693859).length < 2 ^ (prefixWord ++ tailWord_5693859).sum := by decide
  have hdescent : baseEnd_5693859 < baseStart_5693859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693863 : List Nat := [1, 1, 6, 1, 1, 3, 1, 4, 1, 4]
def baseStart_5693863 : Nat := 118140960795 + 5693863 * 2 ^ 59
def prefixEnd_5693863 : Nat := 4983230072969 + 3 ^ 40 * 5693863 * 2
def baseEnd_5693863 : Nat := 974562833283720489508969

theorem tailTrace_5693863 : CollatzResearch.WordTrace tailWord_5693863 prefixEnd_5693863 974562833283720489508969 := by
  unfold tailWord_5693863
  simp only [CollatzResearch.WordTrace]
  refine ⟨207672244571114260226054243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138448163047409506817369495 207672244571114260226054243)
  ·
    refine ⟨311508366856671390339081365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207672244571114260226054243 311508366856671390339081365)
    ·
      refine ⟨14601954696406471422144439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 311508366856671390339081365 14601954696406471422144439)
      ·
        refine ⟨21902932044609707133216659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14601954696406471422144439 21902932044609707133216659)
        ·
          refine ⟨32854398066914560699824989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21902932044609707133216659 32854398066914560699824989)
          ·
            refine ⟨12320399275092960262434371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32854398066914560699824989 12320399275092960262434371)
            ·
              refine ⟨18480598912639440393651557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12320399275092960262434371 18480598912639440393651557)
              ·
                refine ⟨3465112296119895073809667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18480598912639440393651557 3465112296119895073809667)
                ·
                  refine ⟨5197668444179842610714501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3465112296119895073809667 5197668444179842610714501)
                  ·
                    refine ⟨974562833283720489508969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5197668444179842610714501 974562833283720489508969)
                    ·
                      rfl

theorem cell23_5693863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_5693863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693863 prefixEnd_5693863 := by exact prefixLift 5693863
  have htrace : WordTrace (prefixWord ++ tailWord_5693863) baseStart_5693863 baseEnd_5693863 := by
    simpa [prefixWord, tailWord_5693863, baseEnd_5693863] using wordTrace_append hprefix tailTrace_5693863
  have hstable : (prefixWord ++ tailWord_5693863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693863).length < 2 ^ (prefixWord ++ tailWord_5693863).sum := by decide
  have hdescent : baseEnd_5693863 < baseStart_5693863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693886 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3]
def baseStart_5693886 : Nat := 118140960795 + 5693886 * 2 ^ 59
def prefixEnd_5693886 : Nat := 4983230072969 + 3 ^ 40 * 5693886 * 2
def baseEnd_5693886 : Nat := 2923700309906214878539301

theorem tailTrace_5693886 : CollatzResearch.WordTrace tailWord_5693886 prefixEnd_5693886 2923700309906214878539301 := by
  unfold tailWord_5693886
  simp only [CollatzResearch.WordTrace]
  refine ⟨25959135431253866894267689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138448722300020623436094341 25959135431253866894267689)
  ·
    refine ⟨19469351573440400170700767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25959135431253866894267689 19469351573440400170700767)
    ·
      refine ⟨29204027360160600256051151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19469351573440400170700767 29204027360160600256051151)
      ·
        refine ⟨43806041040240900384076727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29204027360160600256051151 43806041040240900384076727)
        ·
          refine ⟨65709061560361350576115091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43806041040240900384076727 65709061560361350576115091)
          ·
            refine ⟨98563592340542025864172637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65709061560361350576115091 98563592340542025864172637)
            ·
              refine ⟨36961347127703259699064739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98563592340542025864172637 36961347127703259699064739)
              ·
                refine ⟨55442020691554889548597109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36961347127703259699064739 55442020691554889548597109)
                ·
                  refine ⟨5197689439833270895180979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55442020691554889548597109 5197689439833270895180979)
                  ·
                    refine ⟨7796534159749906342771469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5197689439833270895180979 7796534159749906342771469)
                    ·
                      refine ⟨2923700309906214878539301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7796534159749906342771469 2923700309906214878539301)
                      ·
                        rfl

theorem cell23_5693886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_5693886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693886 prefixEnd_5693886 := by exact prefixLift 5693886
  have htrace : WordTrace (prefixWord ++ tailWord_5693886) baseStart_5693886 baseEnd_5693886 := by
    simpa [prefixWord, tailWord_5693886, baseEnd_5693886] using wordTrace_append hprefix tailTrace_5693886
  have hstable : (prefixWord ++ tailWord_5693886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693886).length < 2 ^ (prefixWord ++ tailWord_5693886).sum := by decide
  have hdescent : baseEnd_5693886 < baseStart_5693886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693896 : List Nat := [2, 1, 3, 1, 3, 3, 1, 1, 1, 5, 2]
def baseStart_5693896 : Nat := 118140960795 + 5693896 * 2 ^ 59
def prefixEnd_5693896 : Nat := 4983230072969 + 3 ^ 40 * 5693896 * 2
def baseEnd_5693896 : Nat := 2923705444712759839414255

theorem tailTrace_5693896 : CollatzResearch.WordTrace tailWord_5693896 prefixEnd_5693896 2923705444712759839414255 := by
  unfold tailWord_5693896
  simp only [CollatzResearch.WordTrace]
  refine ⟨103836724089997353431002771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138448965453329804574670361 103836724089997353431002771)
  ·
    refine ⟨155755086134996030146504157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103836724089997353431002771 155755086134996030146504157)
    ·
      refine ⟨58408157300623511304939059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155755086134996030146504157 58408157300623511304939059)
      ·
        refine ⟨87612235950935266957408589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58408157300623511304939059 87612235950935266957408589)
        ·
          refine ⟨32854588481600725109028221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87612235950935266957408589 32854588481600725109028221)
          ·
            refine ⟨12320470680600271915885583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32854588481600725109028221 12320470680600271915885583)
            ·
              refine ⟨18480706020900407873828375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12320470680600271915885583 18480706020900407873828375)
              ·
                refine ⟨27721059031350611810742563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18480706020900407873828375 27721059031350611810742563)
                ·
                  refine ⟨41581588547025917716113845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27721059031350611810742563 41581588547025917716113845)
                  ·
                    refine ⟨3898273926283679785885673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41581588547025917716113845 3898273926283679785885673)
                    ·
                      refine ⟨2923705444712759839414255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3898273926283679785885673 2923705444712759839414255)
                      ·
                        rfl

theorem cell23_5693896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 1, 5, 2].length) (baseStart_5693896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693896 prefixEnd_5693896 := by exact prefixLift 5693896
  have htrace : WordTrace (prefixWord ++ tailWord_5693896) baseStart_5693896 baseEnd_5693896 := by
    simpa [prefixWord, tailWord_5693896, baseEnd_5693896] using wordTrace_append hprefix tailTrace_5693896
  have hstable : (prefixWord ++ tailWord_5693896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693896).length < 2 ^ (prefixWord ++ tailWord_5693896).sum := by decide
  have hdescent : baseEnd_5693896 < baseStart_5693896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693929 : List Nat := [1, 2, 1, 1, 1, 2, 1, 6, 3, 2, 3]
def baseStart_5693929 : Nat := 118140960795 + 5693929 * 2 ^ 59
def prefixEnd_5693929 : Nat := 4983230072969 + 3 ^ 40 * 5693929 * 2
def baseEnd_5693929 : Nat := 2923722389574358210301603

theorem tailTrace_5693929 : CollatzResearch.WordTrace tailWord_5693929 prefixEnd_5693929 2923722389574358210301603 := by
  unfold tailWord_5693929
  simp only [CollatzResearch.WordTrace]
  refine ⟨207674651788875153497956841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138449767859250102331971227 207674651788875153497956841)
  ·
    refine ⟨155755988841656365123467631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207674651788875153497956841 155755988841656365123467631)
    ·
      refine ⟨233633983262484547685201447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155755988841656365123467631 233633983262484547685201447)
      ·
        refine ⟨350450974893726821527802171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233633983262484547685201447 350450974893726821527802171)
        ·
          refine ⟨525676462340590232291703257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350450974893726821527802171 525676462340590232291703257)
          ·
            refine ⟨394257346755442674218777443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 525676462340590232291703257 394257346755442674218777443)
            ·
              refine ⟨591386020133164011328166165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394257346755442674218777443 591386020133164011328166165)
              ·
                refine ⟨27721219693742063031007789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 591386020133164011328166165 27721219693742063031007789)
                ·
                  refine ⟨10395457385153273636627921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27721219693742063031007789 10395457385153273636627921)
                  ·
                    refine ⟨7796593038864955227470941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10395457385153273636627921 7796593038864955227470941)
                    ·
                      refine ⟨2923722389574358210301603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7796593038864955227470941 2923722389574358210301603)
                      ·
                        rfl

theorem cell23_5693929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 2, 3].length) (baseStart_5693929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693929 prefixEnd_5693929 := by exact prefixLift 5693929
  have htrace : WordTrace (prefixWord ++ tailWord_5693929) baseStart_5693929 baseEnd_5693929 := by
    simpa [prefixWord, tailWord_5693929, baseEnd_5693929] using wordTrace_append hprefix tailTrace_5693929
  have hstable : (prefixWord ++ tailWord_5693929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693929).length < 2 ^ (prefixWord ++ tailWord_5693929).sum := by decide
  have hdescent : baseEnd_5693929 < baseStart_5693929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693932 : List Nat := [2, 2, 1, 1, 2, 1, 4, 10]
def baseStart_5693932 : Nat := 118140960795 + 5693932 * 2 ^ 59
def prefixEnd_5693932 : Nat := 4983230072969 + 3 ^ 40 * 5693932 * 2
def baseEnd_5693932 : Nat := 108286071482085988835707

theorem tailTrace_5693932 : CollatzResearch.WordTrace tailWord_5693932 prefixEnd_5693932 108286071482085988835707 := by
  unfold tailWord_5693932
  simp only [CollatzResearch.WordTrace]
  refine ⟨103837380603932142505158025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138449840805242856673544033 103837380603932142505158025)
  ·
    refine ⟨77878035452949106878868519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103837380603932142505158025 77878035452949106878868519)
    ·
      refine ⟨116817053179423660318302779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77878035452949106878868519 116817053179423660318302779)
      ·
        refine ⟨175225579769135490477454169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116817053179423660318302779 175225579769135490477454169)
        ·
          refine ⟨131419184826851617858090627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175225579769135490477454169 131419184826851617858090627)
          ·
            refine ⟨197128777240277426787135941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131419184826851617858090627 197128777240277426787135941)
            ·
              refine ⟨36961645732552017522587989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 197128777240277426787135941 36961645732552017522587989)
              ·
                refine ⟨108286071482085988835707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36961645732552017522587989 108286071482085988835707)
                ·
                  rfl

theorem cell23_5693932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 10].length) (baseStart_5693932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693932 prefixEnd_5693932 := by exact prefixLift 5693932
  have htrace : WordTrace (prefixWord ++ tailWord_5693932) baseStart_5693932 baseEnd_5693932 := by
    simpa [prefixWord, tailWord_5693932, baseEnd_5693932] using wordTrace_append hprefix tailTrace_5693932
  have hstable : (prefixWord ++ tailWord_5693932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693932).length < 2 ^ (prefixWord ++ tailWord_5693932).sum := by decide
  have hdescent : baseEnd_5693932 < baseStart_5693932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693952 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 6]
def baseStart_5693952 : Nat := 118140960795 + 5693952 * 2 ^ 59
def prefixEnd_5693952 : Nat := 4983230072969 + 3 ^ 40 * 5693952 * 2
def baseEnd_5693952 : Nat := 2923734199629411620313997

theorem tailTrace_5693952 : CollatzResearch.WordTrace tailWord_5693952 prefixEnd_5693952 2923734199629411620313997 := by
  unfold tailWord_5693952
  simp only [CollatzResearch.WordTrace]
  refine ⟨103837745333895914213022055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138450327111861218950696073 103837745333895914213022055)
  ·
    refine ⟨155756618000843871319533083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103837745333895914213022055 155756618000843871319533083)
    ·
      refine ⟨233634927001265806979299625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155756618000843871319533083 233634927001265806979299625)
      ·
        refine ⟨175226195250949355234474719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233634927001265806979299625 175226195250949355234474719)
        ·
          refine ⟨262839292876424032851712079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175226195250949355234474719 262839292876424032851712079)
          ·
            refine ⟨394258939314636049277568119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262839292876424032851712079 394258939314636049277568119)
            ·
              refine ⟨591388408971954073916352179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394258939314636049277568119 591388408971954073916352179)
              ·
                refine ⟨887082613457931110874528269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 591388408971954073916352179 887082613457931110874528269)
                ·
                  refine ⟨332655980046724166577948101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 887082613457931110874528269 332655980046724166577948101)
                  ·
                    refine ⟨62372996258760781233365269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 332655980046724166577948101 62372996258760781233365269)
                    ·
                      refine ⟨2923734199629411620313997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62372996258760781233365269 2923734199629411620313997)
                      ·
                        rfl

theorem cell23_5693952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_5693952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693952 prefixEnd_5693952 := by exact prefixLift 5693952
  have htrace : WordTrace (prefixWord ++ tailWord_5693952) baseStart_5693952 baseEnd_5693952 := by
    simpa [prefixWord, tailWord_5693952, baseEnd_5693952] using wordTrace_append hprefix tailTrace_5693952
  have hstable : (prefixWord ++ tailWord_5693952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693952).length < 2 ^ (prefixWord ++ tailWord_5693952).sum := by decide
  have hdescent : baseEnd_5693952 < baseStart_5693952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693954 : List Nat := [3, 4, 1, 2, 2, 2, 1, 3, 1, 1, 3]
def baseStart_5693954 : Nat := 118140960795 + 5693954 * 2 ^ 59
def prefixEnd_5693954 : Nat := 4983230072969 + 3 ^ 40 * 5693954 * 2
def baseEnd_5693954 : Nat := 2923735226590720612488989

theorem tailTrace_5693954 : CollatzResearch.WordTrace tailWord_5693954 prefixEnd_5693954 2923735226590720612488989 := by
  unfold tailWord_5693954
  simp only [CollatzResearch.WordTrace]
  refine ⟨51918890903446145691904229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138450375742523055178411277 51918890903446145691904229)
  ·
    refine ⟨9734792044396152317232043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51918890903446145691904229 9734792044396152317232043)
    ·
      refine ⟨14602188066594228475848065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9734792044396152317232043 14602188066594228475848065)
      ·
        refine ⟨10951641049945671356886049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14602188066594228475848065 10951641049945671356886049)
        ·
          refine ⟨8213730787459253517664537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10951641049945671356886049 8213730787459253517664537)
          ·
            refine ⟨6160298090594440138248403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8213730787459253517664537 6160298090594440138248403)
            ·
              refine ⟨9240447135891660207372605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6160298090594440138248403 9240447135891660207372605)
              ·
                refine ⟨3465167675959372577764727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9240447135891660207372605 3465167675959372577764727)
                ·
                  refine ⟨5197751513939058866647091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3465167675959372577764727 5197751513939058866647091)
                  ·
                    refine ⟨7796627270908588299970637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5197751513939058866647091 7796627270908588299970637)
                    ·
                      refine ⟨2923735226590720612488989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7796627270908588299970637 2923735226590720612488989)
                      ·
                        rfl

theorem cell23_5693954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_5693954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693954 prefixEnd_5693954 := by exact prefixLift 5693954
  have htrace : WordTrace (prefixWord ++ tailWord_5693954) baseStart_5693954 baseEnd_5693954 := by
    simpa [prefixWord, tailWord_5693954, baseEnd_5693954] using wordTrace_append hprefix tailTrace_5693954
  have hstable : (prefixWord ++ tailWord_5693954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693954).length < 2 ^ (prefixWord ++ tailWord_5693954).sum := by decide
  have hdescent : baseEnd_5693954 < baseStart_5693954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693986 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 2, 7, 2]
def baseStart_5693986 : Nat := 118140960795 + 5693986 * 2 ^ 59
def prefixEnd_5693986 : Nat := 4983230072969 + 3 ^ 40 * 5693986 * 2
def baseEnd_5693986 : Nat := 2923751657971664487288841

theorem tailTrace_5693986 : CollatzResearch.WordTrace tailWord_5693986 prefixEnd_5693986 2923751657971664487288841 := by
  unfold tailWord_5693986
  simp only [CollatzResearch.WordTrace]
  refine ⟨51919182687417163058195453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138451153833112434821854541 51919182687417163058195453)
  ·
    refine ⟨19469693507781436146823295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51919182687417163058195453 19469693507781436146823295)
    ·
      refine ⟨29204540261672154220234943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19469693507781436146823295 29204540261672154220234943)
      ·
        refine ⟨43806810392508231330352415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29204540261672154220234943 43806810392508231330352415)
        ·
          refine ⟨65710215588762346995528623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43806810392508231330352415 65710215588762346995528623)
          ·
            refine ⟨98565323383143520493292935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65710215588762346995528623 98565323383143520493292935)
            ·
              refine ⟨147847985074715280739939403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98565323383143520493292935 147847985074715280739939403)
              ·
                refine ⟨221771977612072921109909105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147847985074715280739939403 221771977612072921109909105)
                ·
                  refine ⟨166328983209054690832431829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221771977612072921109909105 166328983209054690832431829)
                  ·
                    refine ⟨3898335543962219316385121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 166328983209054690832431829 3898335543962219316385121)
                    ·
                      refine ⟨2923751657971664487288841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3898335543962219316385121 2923751657971664487288841)
                      ·
                        rfl

theorem cell23_5693986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_5693986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693986 prefixEnd_5693986 := by exact prefixLift 5693986
  have htrace : WordTrace (prefixWord ++ tailWord_5693986) baseStart_5693986 baseEnd_5693986 := by
    simpa [prefixWord, tailWord_5693986, baseEnd_5693986] using wordTrace_append hprefix tailTrace_5693986
  have hstable : (prefixWord ++ tailWord_5693986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693986).length < 2 ^ (prefixWord ++ tailWord_5693986).sum := by decide
  have hdescent : baseEnd_5693986 < baseStart_5693986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5693997 : List Nat := [1, 5, 4, 1, 1, 1, 1, 1, 3, 2, 3]
def baseStart_5693997 : Nat := 118140960795 + 5693997 * 2 ^ 59
def prefixEnd_5693997 : Nat := 4983230072969 + 3 ^ 40 * 5693997 * 2
def baseEnd_5693997 : Nat := 2923757306258863944251291

theorem tailTrace_5693997 : CollatzResearch.WordTrace tailWord_5693997 prefixEnd_5693997 2923757306258863944251291 := by
  unfold tailWord_5693997
  simp only [CollatzResearch.WordTrace]
  refine ⟨207677131952628801111432245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138451421301752534074288163 207677131952628801111432245)
  ·
    refine ⟨19469731120558950104196773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 207677131952628801111432245 19469731120558950104196773)
    ·
      refine ⟨3650574585104803144536895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19469731120558950104196773 3650574585104803144536895)
      ·
        refine ⟨5475861877657204716805343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3650574585104803144536895 5475861877657204716805343)
        ·
          refine ⟨8213792816485807075208015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5475861877657204716805343 8213792816485807075208015)
          ·
            refine ⟨12320689224728710612812023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8213792816485807075208015 12320689224728710612812023)
            ·
              refine ⟨18481033837093065919218035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12320689224728710612812023 18481033837093065919218035)
              ·
                refine ⟨27721550755639598878827053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18481033837093065919218035 27721550755639598878827053)
                ·
                  refine ⟨10395581533364849579560145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27721550755639598878827053 10395581533364849579560145)
                  ·
                    refine ⟨7796686150023637184670109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10395581533364849579560145 7796686150023637184670109)
                    ·
                      refine ⟨2923757306258863944251291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7796686150023637184670109 2923757306258863944251291)
                      ·
                        rfl

theorem cell23_5693997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_5693997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5693997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5693997 prefixEnd_5693997 := by exact prefixLift 5693997
  have htrace : WordTrace (prefixWord ++ tailWord_5693997) baseStart_5693997 baseEnd_5693997 := by
    simpa [prefixWord, tailWord_5693997, baseEnd_5693997] using wordTrace_append hprefix tailTrace_5693997
  have hstable : (prefixWord ++ tailWord_5693997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5693997).length < 2 ^ (prefixWord ++ tailWord_5693997).sum := by decide
  have hdescent : baseEnd_5693997 < baseStart_5693997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5693997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694016 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 3, 4, 2]
def baseStart_5694016 : Nat := 118140960795 + 5694016 * 2 ^ 59
def prefixEnd_5694016 : Nat := 4983230072969 + 3 ^ 40 * 5694016 * 2
def baseEnd_5694016 : Nat := 2923767062391299369913703

theorem tailTrace_5694016 : CollatzResearch.WordTrace tailWord_5694016 prefixEnd_5694016 2923767062391299369913703 := by
  unfold tailWord_5694016
  simp only [CollatzResearch.WordTrace]
  refine ⟨103838912469779983678186951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138451883293039978237582601 103838912469779983678186951)
  ·
    refine ⟨155758368704669975517280427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103838912469779983678186951 155758368704669975517280427)
    ·
      refine ⟨233637553057004963275920641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155758368704669975517280427 233637553057004963275920641)
      ·
        refine ⟨175228164792753722456940481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233637553057004963275920641 175228164792753722456940481)
        ·
          refine ⟨131421123594565291842705361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175228164792753722456940481 131421123594565291842705361)
          ·
            refine ⟨98565842695923968882029021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131421123594565291842705361 98565842695923968882029021)
            ·
              refine ⟨36962191010971488330760883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98565842695923968882029021 36962191010971488330760883)
              ·
                refine ⟨55443286516457232496141325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36962191010971488330760883 55443286516457232496141325)
                ·
                  refine ⟨20791232443671462186052997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55443286516457232496141325 20791232443671462186052997)
                  ·
                    refine ⟨3898356083188399159884937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20791232443671462186052997 3898356083188399159884937)
                    ·
                      refine ⟨2923767062391299369913703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3898356083188399159884937 2923767062391299369913703)
                      ·
                        rfl

theorem cell23_5694016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 3, 4, 2].length) (baseStart_5694016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694016 prefixEnd_5694016 := by exact prefixLift 5694016
  have htrace : WordTrace (prefixWord ++ tailWord_5694016) baseStart_5694016 baseEnd_5694016 := by
    simpa [prefixWord, tailWord_5694016, baseEnd_5694016] using wordTrace_append hprefix tailTrace_5694016
  have hstable : (prefixWord ++ tailWord_5694016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694016).length < 2 ^ (prefixWord ++ tailWord_5694016).sum := by decide
  have hdescent : baseEnd_5694016 < baseStart_5694016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694019 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 4, 4, 3]
def baseStart_5694019 : Nat := 118140960795 + 5694019 * 2 ^ 59
def prefixEnd_5694019 : Nat := 4983230072969 + 3 ^ 40 * 5694019 * 2
def baseEnd_5694019 : Nat := 2923768602833262858176189

theorem tailTrace_5694019 : CollatzResearch.WordTrace tailWord_5694019 prefixEnd_5694019 2923768602833262858176189 := by
  unfold tailWord_5694019
  simp only [CollatzResearch.WordTrace]
  refine ⟨207677934358549098868733111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138451956239032732579155407 207677934358549098868733111)
  ·
    refine ⟨311516901537823648303099667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207677934358549098868733111 311516901537823648303099667)
    ·
      refine ⟨467275352306735472454649501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311516901537823648303099667 467275352306735472454649501)
      ·
        refine ⟨175228257115025802170493563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 467275352306735472454649501 175228257115025802170493563)
        ·
          refine ⟨262842385672538703255740345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175228257115025802170493563 262842385672538703255740345)
          ·
            refine ⟨197131789254404027441805259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262842385672538703255740345 197131789254404027441805259)
            ·
              refine ⟨295697683881606041162707889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197131789254404027441805259 295697683881606041162707889)
              ·
                refine ⟨221773262911204530872030917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295697683881606041162707889 221773262911204530872030917)
                ·
                  refine ⟨41582486795850849538505797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 221773262911204530872030917 41582486795850849538505797)
                  ·
                    refine ⟨7796716274222034288469837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41582486795850849538505797 7796716274222034288469837)
                    ·
                      refine ⟨2923768602833262858176189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7796716274222034288469837 2923768602833262858176189)
                      ·
                        rfl

theorem cell23_5694019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4, 3].length) (baseStart_5694019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694019 prefixEnd_5694019 := by exact prefixLift 5694019
  have htrace : WordTrace (prefixWord ++ tailWord_5694019) baseStart_5694019 baseEnd_5694019 := by
    simpa [prefixWord, tailWord_5694019, baseEnd_5694019] using wordTrace_append hprefix tailTrace_5694019
  have hstable : (prefixWord ++ tailWord_5694019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694019).length < 2 ^ (prefixWord ++ tailWord_5694019).sum := by decide
  have hdescent : baseEnd_5694019 < baseStart_5694019 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694036 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 2, 4, 3]
def baseStart_5694036 : Nat := 118140960795 + 5694036 * 2 ^ 59
def prefixEnd_5694036 : Nat := 4983230072969 + 3 ^ 40 * 5694036 * 2
def baseEnd_5694036 : Nat := 2923777332004389291663611

theorem tailTrace_5694036 : CollatzResearch.WordTrace tailWord_5694036 prefixEnd_5694036 2923777332004389291663611 := by
  unfold tailWord_5694036
  simp only [CollatzResearch.WordTrace]
  refine ⟨103839277199743755386050981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138452369599658340514734641 103839277199743755386050981)
  ·
    refine ⟨19469864474951954134884559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103839277199743755386050981 19469864474951954134884559)
    ·
      refine ⟨29204796712427931202326839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19469864474951954134884559 29204796712427931202326839)
      ·
        refine ⟨43807195068641896803490259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29204796712427931202326839 43807195068641896803490259)
        ·
          refine ⟨65710792602962845205235389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43807195068641896803490259 65710792602962845205235389)
          ·
            refine ⟨24641547226111066951963271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65710792602962845205235389 24641547226111066951963271)
            ·
              refine ⟨36962320839166600427944907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24641547226111066951963271 36962320839166600427944907)
              ·
                refine ⟨55443481258749900641917361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36962320839166600427944907 55443481258749900641917361)
                ·
                  refine ⟨41582610944062425481438021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55443481258749900641917361 41582610944062425481438021)
                  ·
                    refine ⟨7796739552011704777769629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41582610944062425481438021 7796739552011704777769629)
                    ·
                      refine ⟨2923777332004389291663611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7796739552011704777769629 2923777332004389291663611)
                      ·
                        rfl

theorem cell23_5694036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_5694036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694036 prefixEnd_5694036 := by exact prefixLift 5694036
  have htrace : WordTrace (prefixWord ++ tailWord_5694036) baseStart_5694036 baseEnd_5694036 := by
    simpa [prefixWord, tailWord_5694036, baseEnd_5694036] using wordTrace_append hprefix tailTrace_5694036
  have hstable : (prefixWord ++ tailWord_5694036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694036).length < 2 ^ (prefixWord ++ tailWord_5694036).sum := by decide
  have hdescent : baseEnd_5694036 < baseStart_5694036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694039 : List Nat := [1, 1, 3, 2, 2, 2, 2, 3, 7]
def baseStart_5694039 : Nat := 118140960795 + 5694039 * 2 ^ 59
def prefixEnd_5694039 : Nat := 4983230072969 + 3 ^ 40 * 5694039 * 2
def baseEnd_5694039 : Nat := 324864319160705864436233

theorem tailTrace_5694039 : CollatzResearch.WordTrace tailWord_5694039 prefixEnd_5694039 324864319160705864436233 := by
  unfold tailWord_5694039
  simp only [CollatzResearch.WordTrace]
  refine ⟨207678663818476642284461171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138452442545651094856307447 207678663818476642284461171)
  ·
    refine ⟨311517995727714963426691757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207678663818476642284461171 311517995727714963426691757)
    ·
      refine ⟨116819248397893111285009409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 311517995727714963426691757 116819248397893111285009409)
      ·
        refine ⟨87614436298419833463757057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116819248397893111285009409 87614436298419833463757057)
        ·
          refine ⟨65710827223814875097817793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87614436298419833463757057 65710827223814875097817793)
          ·
            refine ⟨49283120417861156323363345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65710827223814875097817793 49283120417861156323363345)
            ·
              refine ⟨36962340313395867242522509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49283120417861156323363345 36962340313395867242522509)
              ·
                refine ⟨13860877617523450215945941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36962340313395867242522509 13860877617523450215945941)
                ·
                  refine ⟨324864319160705864436233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13860877617523450215945941 324864319160705864436233)
                  ·
                    rfl

theorem cell23_5694039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 7].length) (baseStart_5694039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694039 prefixEnd_5694039 := by exact prefixLift 5694039
  have htrace : WordTrace (prefixWord ++ tailWord_5694039) baseStart_5694039 baseEnd_5694039 := by
    simpa [prefixWord, tailWord_5694039, baseEnd_5694039] using wordTrace_append hprefix tailTrace_5694039
  have hstable : (prefixWord ++ tailWord_5694039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694039).length < 2 ^ (prefixWord ++ tailWord_5694039).sum := by decide
  have hdescent : baseEnd_5694039 < baseStart_5694039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694073 : List Nat := [1, 2, 1, 3, 3, 3, 2, 3, 5]
def baseStart_5694073 : Nat := 118140960795 + 5694073 * 2 ^ 59
def prefixEnd_5694073 : Nat := 4983230072969 + 3 ^ 40 * 5694073 * 2
def baseEnd_5694073 : Nat := 324866258976511738544549

theorem tailTrace_5694073 : CollatzResearch.WordTrace tailWord_5694073 prefixEnd_5694073 324866258976511738544549 := by
  unfold tailWord_5694073
  simp only [CollatzResearch.WordTrace]
  refine ⟨207679903900353466091198873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138453269266902310727465915 207679903900353466091198873)
  ·
    refine ⟨155759927925265099568399155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207679903900353466091198873 155759927925265099568399155)
    ·
      refine ⟨233639891887897649352598733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155759927925265099568399155 233639891887897649352598733)
      ·
        refine ⟨87614959457961618507224525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233639891887897649352598733 87614959457961618507224525)
        ·
          refine ⟨32855609796735606940209197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87614959457961618507224525 32855609796735606940209197)
          ·
            refine ⟨12320853673775852602578449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32855609796735606940209197 12320853673775852602578449)
            ·
              refine ⟨9240640255331889451933837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12320853673775852602578449 9240640255331889451933837)
              ·
                refine ⟨3465240095749458544475189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9240640255331889451933837 3465240095749458544475189)
                ·
                  refine ⟨324866258976511738544549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3465240095749458544475189 324866258976511738544549)
                  ·
                    rfl

theorem cell23_5694073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3, 5].length) (baseStart_5694073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694073 prefixEnd_5694073 := by exact prefixLift 5694073
  have htrace : WordTrace (prefixWord ++ tailWord_5694073) baseStart_5694073 baseEnd_5694073 := by
    simpa [prefixWord, tailWord_5694073, baseEnd_5694073] using wordTrace_append hprefix tailTrace_5694073
  have hstable : (prefixWord ++ tailWord_5694073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694073).length < 2 ^ (prefixWord ++ tailWord_5694073).sum := by decide
  have hdescent : baseEnd_5694073 < baseStart_5694073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694079 : List Nat := [1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 5]
def baseStart_5694079 : Nat := 118140960795 + 5694079 * 2 ^ 59
def prefixEnd_5694079 : Nat := 4983230072969 + 3 ^ 40 * 5694079 * 2
def baseEnd_5694079 : Nat := 2923799411672532623425913

theorem tailTrace_5694079 : CollatzResearch.WordTrace tailWord_5694079 prefixEnd_5694079 2923799411672532623425913 := by
  unfold tailWord_5694079
  simp only [CollatzResearch.WordTrace]
  refine ⟨207680122738331729115917291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138453415158887819410611527 207680122738331729115917291)
  ·
    refine ⟨311520184107497593673875937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207680122738331729115917291 311520184107497593673875937)
    ·
      refine ⟨233640138080623195255406953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311520184107497593673875937 233640138080623195255406953)
      ·
        refine ⟨175230103560467396441555215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233640138080623195255406953 175230103560467396441555215)
        ·
          refine ⟨262845155340701094662332823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175230103560467396441555215 262845155340701094662332823)
          ·
            refine ⟨394267733011051641993499235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262845155340701094662332823 394267733011051641993499235)
            ·
              refine ⟨591401599516577462990248853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394267733011051641993499235 591401599516577462990248853)
              ·
                refine ⟨27721949977339568577667915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 591401599516577462990248853 27721949977339568577667915)
                ·
                  refine ⟨41582924966009352866501873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27721949977339568577667915 41582924966009352866501873)
                  ·
                    refine ⟨31187193724507014649876405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41582924966009352866501873 31187193724507014649876405)
                    ·
                      refine ⟨2923799411672532623425913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31187193724507014649876405 2923799411672532623425913)
                      ·
                        rfl

theorem cell23_5694079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_5694079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694079 prefixEnd_5694079 := by exact prefixLift 5694079
  have htrace : WordTrace (prefixWord ++ tailWord_5694079) baseStart_5694079 baseEnd_5694079 := by
    simpa [prefixWord, tailWord_5694079, baseEnd_5694079] using wordTrace_append hprefix tailTrace_5694079
  have hstable : (prefixWord ++ tailWord_5694079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694079).length < 2 ^ (prefixWord ++ tailWord_5694079).sum := by decide
  have hdescent : baseEnd_5694079 < baseStart_5694079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694143 : List Nat := [1, 1, 2, 2, 2, 5, 1, 2, 2, 2, 3]
def baseStart_5694143 : Nat := 118140960795 + 5694143 * 2 ^ 59
def prefixEnd_5694143 : Nat := 4983230072969 + 3 ^ 40 * 5694143 * 2
def baseEnd_5694143 : Nat := 2923832274434420373025619

theorem tailTrace_5694143 : CollatzResearch.WordTrace tailWord_5694143 prefixEnd_5694143 2923832274434420373025619 := by
  unfold tailWord_5694143
  simp only [CollatzResearch.WordTrace]
  refine ⟨207682457010099868046247083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138454971340066578697498055 207682457010099868046247083)
  ·
    refine ⟨311523685515149802069370625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207682457010099868046247083 311523685515149802069370625)
    ·
      refine ⟨233642764136362351552027969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311523685515149802069370625 233642764136362351552027969)
      ·
        refine ⟨175232073102271763664020977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233642764136362351552027969 175232073102271763664020977)
        ·
          refine ⟨131424054826703822748015733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175232073102271763664020977 131424054826703822748015733)
          ·
            refine ⟨12321005140003483382626475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131424054826703822748015733 12321005140003483382626475)
            ·
              refine ⟨18481507710005225073939713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12321005140003483382626475 18481507710005225073939713)
              ·
                refine ⟨13861130782503918805454785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18481507710005225073939713 13861130782503918805454785)
                ·
                  refine ⟨10395848086877939104091089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13861130782503918805454785 10395848086877939104091089)
                  ·
                    refine ⟨7796886065158454328068317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10395848086877939104091089 7796886065158454328068317)
                    ·
                      refine ⟨2923832274434420373025619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7796886065158454328068317 2923832274434420373025619)
                      ·
                        rfl

theorem cell23_5694143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2, 3].length) (baseStart_5694143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694143 prefixEnd_5694143 := by exact prefixLift 5694143
  have htrace : WordTrace (prefixWord ++ tailWord_5694143) baseStart_5694143 baseEnd_5694143 := by
    simpa [prefixWord, tailWord_5694143, baseEnd_5694143] using wordTrace_append hprefix tailTrace_5694143
  have hstable : (prefixWord ++ tailWord_5694143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694143).length < 2 ^ (prefixWord ++ tailWord_5694143).sum := by decide
  have hdescent : baseEnd_5694143 < baseStart_5694143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694159 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 1, 11]
def baseStart_5694159 : Nat := 118140960795 + 5694159 * 2 ^ 59
def prefixEnd_5694159 : Nat := 4983230072969 + 3 ^ 40 * 5694159 * 2
def baseEnd_5694159 : Nat := 974613496708297436808515

theorem tailTrace_5694159 : CollatzResearch.WordTrace tailWord_5694159 prefixEnd_5694159 974613496708297436808515 := by
  unfold tailWord_5694159
  simp only [CollatzResearch.WordTrace]
  refine ⟨207683040578041902778829531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138455360385361268519219687 207683040578041902778829531)
  ·
    refine ⟨311524560867062854168244297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207683040578041902778829531 311524560867062854168244297)
    ·
      refine ⟨233643420650297140626183223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311524560867062854168244297 233643420650297140626183223)
      ·
        refine ⟨350465130975445710939274835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233643420650297140626183223 350465130975445710939274835)
        ·
          refine ⟨525697696463168566408912253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350465130975445710939274835 525697696463168566408912253)
          ·
            refine ⟨197136636173688212403342095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 525697696463168566408912253 197136636173688212403342095)
            ·
              refine ⟨295704954260532318605013143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197136636173688212403342095 295704954260532318605013143)
              ·
                refine ⟨443557431390798477907519715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295704954260532318605013143 443557431390798477907519715)
                ·
                  refine ⟨665336147086197716861279573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 443557431390798477907519715 665336147086197716861279573)
                  ·
                    refine ⟨974613496708297436808515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 665336147086197716861279573 974613496708297436808515)
                    ·
                      rfl

theorem cell23_5694159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 11].length) (baseStart_5694159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694159 prefixEnd_5694159 := by exact prefixLift 5694159
  have htrace : WordTrace (prefixWord ++ tailWord_5694159) baseStart_5694159 baseEnd_5694159 := by
    simpa [prefixWord, tailWord_5694159, baseEnd_5694159] using wordTrace_append hprefix tailTrace_5694159
  have hstable : (prefixWord ++ tailWord_5694159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694159).length < 2 ^ (prefixWord ++ tailWord_5694159).sum := by decide
  have hdescent : baseEnd_5694159 < baseStart_5694159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694223 : List Nat := [1, 1, 2, 1, 1, 1, 5, 5, 2, 4]
def baseStart_5694223 : Nat := 118140960795 + 5694223 * 2 ^ 59
def prefixEnd_5694223 : Nat := 4983230072969 + 3 ^ 40 * 5694223 * 2
def baseEnd_5694223 : Nat := 974624450962260020008417

theorem tailTrace_5694223 : CollatzResearch.WordTrace tailWord_5694223 prefixEnd_5694223 974624450962260020008417 := by
  unfold tailWord_5694223
  simp only [CollatzResearch.WordTrace]
  refine ⟨207685374849810041709159323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138456916566540027806106215 207685374849810041709159323)
  ·
    refine ⟨311528062274715062563738985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207685374849810041709159323 311528062274715062563738985)
    ·
      refine ⟨233646046706036296922804239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311528062274715062563738985 233646046706036296922804239)
      ·
        refine ⟨350469070059054445384206359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233646046706036296922804239 350469070059054445384206359)
        ·
          refine ⟨525703605088581668076309539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350469070059054445384206359 525703605088581668076309539)
          ·
            refine ⟨788555407632872502114464309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525703605088581668076309539 788555407632872502114464309)
            ·
              refine ⟨73927069465581797073231029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 788555407632872502114464309 73927069465581797073231029)
              ·
                refine ⟨6930662762398293475615409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73927069465581797073231029 6930662762398293475615409)
                ·
                  refine ⟨5197997071798720106711557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6930662762398293475615409 5197997071798720106711557)
                  ·
                    refine ⟨974624450962260020008417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5197997071798720106711557 974624450962260020008417)
                    ·
                      rfl

theorem cell23_5694223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 5, 2, 4].length) (baseStart_5694223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694223 prefixEnd_5694223 := by exact prefixLift 5694223
  have htrace : WordTrace (prefixWord ++ tailWord_5694223) baseStart_5694223 baseEnd_5694223 := by
    simpa [prefixWord, tailWord_5694223, baseEnd_5694223] using wordTrace_append hprefix tailTrace_5694223
  have hstable : (prefixWord ++ tailWord_5694223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694223).length < 2 ^ (prefixWord ++ tailWord_5694223).sum := by decide
  have hdescent : baseEnd_5694223 < baseStart_5694223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694244 : List Nat := [2, 3, 1, 3, 4, 1, 2, 1, 1, 5]
def baseStart_5694244 : Nat := 118140960795 + 5694244 * 2 ^ 59
def prefixEnd_5694244 : Nat := 4983230072969 + 3 ^ 40 * 5694244 * 2
def baseEnd_5694244 : Nat := 974628045326841492620885

theorem tailTrace_5694244 : CollatzResearch.WordTrace tailWord_5694244 prefixEnd_5694244 974628045326841492620885 := by
  unfold tailWord_5694244
  simp only [CollatzResearch.WordTrace]
  refine ⟨103843070391366981147836893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138457427188489308197115857 103843070391366981147836893)
  ·
    refine ⟨38941151396762617930438835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103843070391366981147836893 38941151396762617930438835)
    ·
      refine ⟨58411727095143926895658253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38941151396762617930438835 58411727095143926895658253)
      ·
        refine ⟨21904397660678972585871845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58411727095143926895658253 21904397660678972585871845)
        ·
          refine ⟨4107074561377307359850971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21904397660678972585871845 4107074561377307359850971)
          ·
            refine ⟨6160611842065961039776457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4107074561377307359850971 6160611842065961039776457)
            ·
              refine ⟨4620458881549470779832343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6160611842065961039776457 4620458881549470779832343)
              ·
                refine ⟨6930688322324206169748515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4620458881549470779832343 6930688322324206169748515)
                ·
                  refine ⟨10396032483486309254622773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6930688322324206169748515 10396032483486309254622773)
                  ·
                    refine ⟨974628045326841492620885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10396032483486309254622773 974628045326841492620885)
                    ·
                      rfl

theorem cell23_5694244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_5694244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694244 prefixEnd_5694244 := by exact prefixLift 5694244
  have htrace : WordTrace (prefixWord ++ tailWord_5694244) baseStart_5694244 baseEnd_5694244 := by
    simpa [prefixWord, tailWord_5694244, baseEnd_5694244] using wordTrace_append hprefix tailTrace_5694244
  have hstable : (prefixWord ++ tailWord_5694244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694244).length < 2 ^ (prefixWord ++ tailWord_5694244).sum := by decide
  have hdescent : baseEnd_5694244 < baseStart_5694244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694296 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 1, 8]
def baseStart_5694296 : Nat := 118140960795 + 5694296 * 2 ^ 59
def prefixEnd_5694296 : Nat := 4983230072969 + 3 ^ 40 * 5694296 * 2
def baseEnd_5694296 : Nat := 974636945658186091470805

theorem tailTrace_5694296 : CollatzResearch.WordTrace tailWord_5694296 prefixEnd_5694296 974636945658186091470805 := by
  unfold tailWord_5694296
  simp only [CollatzResearch.WordTrace]
  refine ⟨103844018689272787588283371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138458691585697050117711161 103844018689272787588283371)
  ·
    refine ⟨155766028033909181382425057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103844018689272787588283371 155766028033909181382425057)
    ·
      refine ⟨116824521025431886036818793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155766028033909181382425057 116824521025431886036818793)
      ·
        refine ⟨87618390769073914527614095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116824521025431886036818793 87618390769073914527614095)
        ·
          refine ⟨131427586153610871791421143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87618390769073914527614095 131427586153610871791421143)
          ·
            refine ⟨197141379230416307687131715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131427586153610871791421143 197141379230416307687131715)
            ·
              refine ⟨295712068845624461530697573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197141379230416307687131715 295712068845624461530697573)
              ·
                refine ⟨55446012908554586537005795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 295712068845624461530697573 55446012908554586537005795)
                ·
                  refine ⟨83169019362831879805508693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55446012908554586537005795 83169019362831879805508693)
                  ·
                    refine ⟨974636945658186091470805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83169019362831879805508693 974636945658186091470805)
                    ·
                      rfl

theorem cell23_5694296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_5694296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694296 prefixEnd_5694296 := by exact prefixLift 5694296
  have htrace : WordTrace (prefixWord ++ tailWord_5694296) baseStart_5694296 baseEnd_5694296 := by
    simpa [prefixWord, tailWord_5694296, baseEnd_5694296] using wordTrace_append hprefix tailTrace_5694296
  have hstable : (prefixWord ++ tailWord_5694296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694296).length < 2 ^ (prefixWord ++ tailWord_5694296).sum := by decide
  have hdescent : baseEnd_5694296 < baseStart_5694296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694307 : List Nat := [1, 1, 1, 5, 3, 1, 2, 3, 1, 3, 2]
def baseStart_5694307 : Nat := 118140960795 + 5694307 * 2 ^ 59
def prefixEnd_5694307 : Nat := 4983230072969 + 3 ^ 40 * 5694307 * 2
def baseEnd_5694307 : Nat := 2923916485261757731374865

theorem tailTrace_5694307 : CollatzResearch.WordTrace tailWord_5694307 prefixEnd_5694307 2923916485261757731374865 := by
  unfold tailWord_5694307
  simp only [CollatzResearch.WordTrace]
  refine ⟨207688438581505724055217175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138458959054337149370144783 207688438581505724055217175)
  ·
    refine ⟨311532657872258586082825763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207688438581505724055217175 311532657872258586082825763)
    ·
      refine ⟨467298986808387879124238645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311532657872258586082825763 467298986808387879124238645)
      ·
        refine ⟨43809280013286363667897373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 467298986808387879124238645 43809280013286363667897373)
        ·
          refine ⟨16428480004982386375461515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43809280013286363667897373 16428480004982386375461515)
          ·
            refine ⟨24642720007473579563192273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16428480004982386375461515 24642720007473579563192273)
            ·
              refine ⟨18482040005605184672394205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24642720007473579563192273 18482040005605184672394205)
              ·
                refine ⟨6930765002101944252147827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18482040005605184672394205 6930765002101944252147827)
                ·
                  refine ⟨10396147503152916378221741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6930765002101944252147827 10396147503152916378221741)
                  ·
                    refine ⟨3898555313682343641833153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10396147503152916378221741 3898555313682343641833153)
                    ·
                      refine ⟨2923916485261757731374865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3898555313682343641833153 2923916485261757731374865)
                      ·
                        rfl

theorem cell23_5694307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_5694307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694307 prefixEnd_5694307 := by exact prefixLift 5694307
  have htrace : WordTrace (prefixWord ++ tailWord_5694307) baseStart_5694307 baseEnd_5694307 := by
    simpa [prefixWord, tailWord_5694307, baseEnd_5694307] using wordTrace_append hprefix tailTrace_5694307
  have hstable : (prefixWord ++ tailWord_5694307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694307).length < 2 ^ (prefixWord ++ tailWord_5694307).sum := by decide
  have hdescent : baseEnd_5694307 < baseStart_5694307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694333 : List Nat := [1, 4, 1, 1, 2, 1, 2, 3, 2, 2, 4]
def baseStart_5694333 : Nat := 118140960795 + 5694333 * 2 ^ 59
def prefixEnd_5694333 : Nat := 4983230072969 + 3 ^ 40 * 5694333 * 2
def baseEnd_5694333 : Nat := 2923929835758774629649745

theorem tailTrace_5694333 : CollatzResearch.WordTrace tailWord_5694333 prefixEnd_5694333 2923929835758774629649745 := by
  unfold tailWord_5694333
  simp only [CollatzResearch.WordTrace]
  refine ⟨207689386879411530495663653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138459591252941020330442435 207689386879411530495663653)
  ·
    refine ⟨38941760039889661967936935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207689386879411530495663653 38941760039889661967936935)
    ·
      refine ⟨58412640059834492951905403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38941760039889661967936935 58412640059834492951905403)
      ·
        refine ⟨87618960089751739427858105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58412640059834492951905403 87618960089751739427858105)
        ·
          refine ⟨65714220067313804570893579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87618960089751739427858105 65714220067313804570893579)
          ·
            refine ⟨98571330100970706856340369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65714220067313804570893579 98571330100970706856340369)
            ·
              refine ⟨73928497575728030142255277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98571330100970706856340369 73928497575728030142255277)
              ·
                refine ⟨27723186590898011303345729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73928497575728030142255277 27723186590898011303345729)
                ·
                  refine ⟨20792389943173508477509297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27723186590898011303345729 20792389943173508477509297)
                  ·
                    refine ⟨15594292457380131358131973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20792389943173508477509297 15594292457380131358131973)
                    ·
                      refine ⟨2923929835758774629649745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15594292457380131358131973 2923929835758774629649745)
                      ·
                        rfl

theorem cell23_5694333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_5694333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694333 prefixEnd_5694333 := by exact prefixLift 5694333
  have htrace : WordTrace (prefixWord ++ tailWord_5694333) baseStart_5694333 baseEnd_5694333 := by
    simpa [prefixWord, tailWord_5694333, baseEnd_5694333] using wordTrace_append hprefix tailTrace_5694333
  have hstable : (prefixWord ++ tailWord_5694333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694333).length < 2 ^ (prefixWord ++ tailWord_5694333).sum := by decide
  have hdescent : baseEnd_5694333 < baseStart_5694333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694353 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 3]
def baseStart_5694353 : Nat := 118140960795 + 5694353 * 2 ^ 59
def prefixEnd_5694353 : Nat := 4983230072969 + 3 ^ 40 * 5694353 * 2
def baseEnd_5694353 : Nat := 2923940105371864551399653

theorem tailTrace_5694353 : CollatzResearch.WordTrace tailWord_5694353 prefixEnd_5694353 2923940105371864551399653 := by
  unfold tailWord_5694353
  simp only [CollatzResearch.WordTrace]
  refine ⟨207690116339339073911391713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138460077559559382607594475 207690116339339073911391713)
  ·
    refine ⟨155767587254504305433543785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207690116339339073911391713 155767587254504305433543785)
    ·
      refine ⟨116825690440878229075157839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155767587254504305433543785 116825690440878229075157839)
      ·
        refine ⟨175238535661317343612736759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116825690440878229075157839 175238535661317343612736759)
        ·
          refine ⟨262857803491976015419105139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175238535661317343612736759 262857803491976015419105139)
          ·
            refine ⟨394286705237964023128657709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262857803491976015419105139 394286705237964023128657709)
            ·
              refine ⟨147857514464236508673246641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 394286705237964023128657709 147857514464236508673246641)
              ·
                refine ⟨110893135848177381504934981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147857514464236508673246641 110893135848177381504934981)
                ·
                  refine ⟨20792462971533259032175309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110893135848177381504934981 20792462971533259032175309)
                  ·
                    refine ⟨7797173614324972137065741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20792462971533259032175309 7797173614324972137065741)
                    ·
                      refine ⟨2923940105371864551399653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7797173614324972137065741 2923940105371864551399653)
                      ·
                        rfl

theorem cell23_5694353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 3].length) (baseStart_5694353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694353 prefixEnd_5694353 := by exact prefixLift 5694353
  have htrace : WordTrace (prefixWord ++ tailWord_5694353) baseStart_5694353 baseEnd_5694353 := by
    simpa [prefixWord, tailWord_5694353, baseEnd_5694353] using wordTrace_append hprefix tailTrace_5694353
  have hstable : (prefixWord ++ tailWord_5694353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694353).length < 2 ^ (prefixWord ++ tailWord_5694353).sum := by decide
  have hdescent : baseEnd_5694353 < baseStart_5694353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694354 : List Nat := [3, 2, 3, 2, 2, 1, 1, 2, 1, 4, 2]
def baseStart_5694354 : Nat := 118140960795 + 5694354 * 2 ^ 59
def prefixEnd_5694354 : Nat := 4983230072969 + 3 ^ 40 * 5694354 * 2
def baseEnd_5694354 : Nat := 2923940618852519047487149

theorem tailTrace_5694354 : CollatzResearch.WordTrace tailWord_5694354 prefixEnd_5694354 2923940618852519047487149 := by
  unfold tailWord_5694354
  simp only [CollatzResearch.WordTrace]
  refine ⟨51922538203083862770544529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138460101874890300721452077 51922538203083862770544529)
  ·
    refine ⟨38941903652312897077908397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51922538203083862770544529 38941903652312897077908397)
    ·
      refine ⟨14603213869617336404215649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38941903652312897077908397 14603213869617336404215649)
      ·
        refine ⟨10952410402213002303161737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14603213869617336404215649 10952410402213002303161737)
        ·
          refine ⟨8214307801659751727371303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10952410402213002303161737 8214307801659751727371303)
          ·
            refine ⟨12321461702489627591056955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8214307801659751727371303 12321461702489627591056955)
            ·
              refine ⟨18482192553734441386585433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12321461702489627591056955 18482192553734441386585433)
              ·
                refine ⟨13861644415300831039939075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18482192553734441386585433 13861644415300831039939075)
                ·
                  refine ⟨20792466622951246559908613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13861644415300831039939075 20792466622951246559908613)
                  ·
                    refine ⟨3898587491803358729982865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20792466622951246559908613 3898587491803358729982865)
                    ·
                      refine ⟨2923940618852519047487149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3898587491803358729982865 2923940618852519047487149)
                      ·
                        rfl

theorem cell23_5694354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_5694354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694354 prefixEnd_5694354 := by exact prefixLift 5694354
  have htrace : WordTrace (prefixWord ++ tailWord_5694354) baseStart_5694354 baseEnd_5694354 := by
    simpa [prefixWord, tailWord_5694354, baseEnd_5694354] using wordTrace_append hprefix tailTrace_5694354
  have hstable : (prefixWord ++ tailWord_5694354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694354).length < 2 ^ (prefixWord ++ tailWord_5694354).sum := by decide
  have hdescent : baseEnd_5694354 < baseStart_5694354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694410 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 3, 6, 2]
def baseStart_5694410 : Nat := 118140960795 + 5694410 * 2 ^ 59
def prefixEnd_5694410 : Nat := 4983230072969 + 3 ^ 40 * 5694410 * 2
def baseEnd_5694410 : Nat := 2923969373769170828386891

theorem tailTrace_5694410 : CollatzResearch.WordTrace tailWord_5694410 prefixEnd_5694410 2923969373769170828386891 := by
  unfold tailWord_5694410
  simp only [CollatzResearch.WordTrace]
  refine ⟨51923048825033143161554171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138461463533421715097477789 51923048825033143161554171)
  ·
    refine ⟨77884573237549714742331257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51923048825033143161554171 77884573237549714742331257)
    ·
      refine ⟨58413429928162286056748443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77884573237549714742331257 58413429928162286056748443)
      ·
        refine ⟨87620144892243429085122665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58413429928162286056748443 87620144892243429085122665)
        ·
          refine ⟨65715108669182571813841999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87620144892243429085122665 65715108669182571813841999)
          ·
            refine ⟨98572663003773857720762999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65715108669182571813841999 98572663003773857720762999)
            ·
              refine ⟨147858994505660786581144499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98572663003773857720762999 147858994505660786581144499)
              ·
                refine ⟨221788491758491179871716749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147858994505660786581144499 221788491758491179871716749)
                ·
                  refine ⟨83170684409434192451893781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 221788491758491179871716749 83170684409434192451893781)
                  ·
                    refine ⟨3898625831692227771182521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83170684409434192451893781 3898625831692227771182521)
                    ·
                      refine ⟨2923969373769170828386891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3898625831692227771182521 2923969373769170828386891)
                      ·
                        rfl

theorem cell23_5694410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 3, 6, 2].length) (baseStart_5694410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694410 prefixEnd_5694410 := by exact prefixLift 5694410
  have htrace : WordTrace (prefixWord ++ tailWord_5694410) baseStart_5694410 baseEnd_5694410 := by
    simpa [prefixWord, tailWord_5694410, baseEnd_5694410] using wordTrace_append hprefix tailTrace_5694410
  have hstable : (prefixWord ++ tailWord_5694410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694410).length < 2 ^ (prefixWord ++ tailWord_5694410).sum := by decide
  have hdescent : baseEnd_5694410 < baseStart_5694410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694567 : List Nat := [1, 1, 5, 1, 1, 3, 1, 3, 1, 3, 3]
def baseStart_5694567 : Nat := 118140960795 + 5694567 * 2 ^ 59
def prefixEnd_5694567 : Nat := 4983230072969 + 3 ^ 40 * 5694567 * 2
def baseEnd_5694567 : Nat := 2924049990231926714123669

theorem tailTrace_5694567 : CollatzResearch.WordTrace tailWord_5694567 prefixEnd_5694567 2924049990231926714123669 := by
  unfold tailWord_5694567
  simp only [CollatzResearch.WordTrace]
  refine ⟨207697921560563788459681955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138465281040375858973121303 207697921560563788459681955)
  ·
    refine ⟨311546882340845682689522933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207697921560563788459681955 311546882340845682689522933)
    ·
      refine ⟨29207520219454282752142775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 311546882340845682689522933 29207520219454282752142775)
      ·
        refine ⟨43811280329181424128214163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29207520219454282752142775 43811280329181424128214163)
        ·
          refine ⟨65716920493772136192321245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43811280329181424128214163 65716920493772136192321245)
          ·
            refine ⟨24643845185164551072120467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65716920493772136192321245 24643845185164551072120467)
            ·
              refine ⟨36965767777746826608180701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24643845185164551072120467 36965767777746826608180701)
              ·
                refine ⟨13862162916655059978067763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36965767777746826608180701 13862162916655059978067763)
                ·
                  refine ⟨20793244374982589967101645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13862162916655059978067763 20793244374982589967101645)
                  ·
                    refine ⟨7797466640618471237663117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20793244374982589967101645 7797466640618471237663117)
                    ·
                      refine ⟨2924049990231926714123669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7797466640618471237663117 2924049990231926714123669)
                      ·
                        rfl

theorem cell23_5694567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_5694567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694567 prefixEnd_5694567 := by exact prefixLift 5694567
  have htrace : WordTrace (prefixWord ++ tailWord_5694567) baseStart_5694567 baseEnd_5694567 := by
    simpa [prefixWord, tailWord_5694567, baseEnd_5694567] using wordTrace_append hprefix tailTrace_5694567
  have hstable : (prefixWord ++ tailWord_5694567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694567).length < 2 ^ (prefixWord ++ tailWord_5694567).sum := by decide
  have hdescent : baseEnd_5694567 < baseStart_5694567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694568 : List Nat := [2, 1, 4, 4, 1, 1, 1, 2, 3, 2, 2]
def baseStart_5694568 : Nat := 118140960795 + 5694568 * 2 ^ 59
def prefixEnd_5694568 : Nat := 4983230072969 + 3 ^ 40 * 5694568 * 2
def baseEnd_5694568 : Nat := 2924050503712581210211165

theorem tailTrace_5694568 : CollatzResearch.WordTrace tailWord_5694568 prefixEnd_5694568 2924050503712581210211165 := by
  unfold tailWord_5694568
  simp only [CollatzResearch.WordTrace]
  refine ⟨103848979016780082815234179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138465305355706777086978905 103848979016780082815234179)
  ·
    refine ⟨155773468525170124222851269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103848979016780082815234179 155773468525170124222851269)
    ·
      refine ⟨29207525348469398291784613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155773468525170124222851269 29207525348469398291784613)
      ·
        refine ⟨5476411002838012179709615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29207525348469398291784613 5476411002838012179709615)
        ·
          refine ⟨8214616504257018269564423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5476411002838012179709615 8214616504257018269564423)
          ·
            refine ⟨12321924756385527404346635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8214616504257018269564423 12321924756385527404346635)
            ·
              refine ⟨18482887134578291106519953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12321924756385527404346635 18482887134578291106519953)
              ·
                refine ⟨13862165350933718329889965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18482887134578291106519953 13862165350933718329889965)
                ·
                  refine ⟨5198312006600144373708737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13862165350933718329889965 5198312006600144373708737)
                  ·
                    refine ⟨3898734004950108280281553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5198312006600144373708737 3898734004950108280281553)
                    ·
                      refine ⟨2924050503712581210211165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3898734004950108280281553 2924050503712581210211165)
                      ·
                        rfl

theorem cell23_5694568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_5694568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694568 prefixEnd_5694568 := by exact prefixLift 5694568
  have htrace : WordTrace (prefixWord ++ tailWord_5694568) baseStart_5694568 baseEnd_5694568 := by
    simpa [prefixWord, tailWord_5694568, baseEnd_5694568] using wordTrace_append hprefix tailTrace_5694568
  have hstable : (prefixWord ++ tailWord_5694568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694568).length < 2 ^ (prefixWord ++ tailWord_5694568).sum := by decide
  have hdescent : baseEnd_5694568 < baseStart_5694568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694601 : List Nat := [1, 2, 1, 1, 4, 5, 1, 2, 2, 1, 3]
def baseStart_5694601 : Nat := 118140960795 + 5694601 * 2 ^ 59
def prefixEnd_5694601 : Nat := 4983230072969 + 3 ^ 40 * 5694601 * 2
def baseEnd_5694601 : Nat := 2924067448574179581098513

theorem tailTrace_5694601 : CollatzResearch.WordTrace tailWord_5694601 prefixEnd_5694601 2924067448574179581098513 := by
  unfold tailWord_5694601
  simp only [CollatzResearch.WordTrace]
  refine ⟨207699161642440612266419657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138466107761627074844279771 207699161642440612266419657)
  ·
    refine ⟨155774371231830459199814743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207699161642440612266419657 155774371231830459199814743)
    ·
      refine ⟨233661556847745688799722115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155774371231830459199814743 233661556847745688799722115)
      ·
        refine ⟨350492335271618533199583173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233661556847745688799722115 350492335271618533199583173)
        ·
          refine ⟨65717312863428474974921845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 350492335271618533199583173 65717312863428474974921845)
          ·
            refine ⟨6160998080946419528898923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65717312863428474974921845 6160998080946419528898923)
            ·
              refine ⟨9241497121419629293348385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6160998080946419528898923 9241497121419629293348385)
              ·
                refine ⟨6931122841064721970011289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9241497121419629293348385 6931122841064721970011289)
                ·
                  refine ⟨5198342130798541477508467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6931122841064721970011289 5198342130798541477508467)
                  ·
                    refine ⟨7797513196197812216262701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5198342130798541477508467 7797513196197812216262701)
                    ·
                      refine ⟨2924067448574179581098513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7797513196197812216262701 2924067448574179581098513)
                      ·
                        rfl

theorem cell23_5694601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2, 1, 3].length) (baseStart_5694601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694601 prefixEnd_5694601 := by exact prefixLift 5694601
  have htrace : WordTrace (prefixWord ++ tailWord_5694601) baseStart_5694601 baseEnd_5694601 := by
    simpa [prefixWord, tailWord_5694601, baseEnd_5694601] using wordTrace_append hprefix tailTrace_5694601
  have hstable : (prefixWord ++ tailWord_5694601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694601).length < 2 ^ (prefixWord ++ tailWord_5694601).sum := by decide
  have hdescent : baseEnd_5694601 < baseStart_5694601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694618 : List Nat := [3, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3]
def baseStart_5694618 : Nat := 118140960795 + 5694618 * 2 ^ 59
def prefixEnd_5694618 : Nat := 4983230072969 + 3 ^ 40 * 5694618 * 2
def baseEnd_5694618 : Nat := 2924076177745306014585935

theorem tailTrace_5694618 : CollatzResearch.WordTrace tailWord_5694618 prefixEnd_5694618 2924076177745306014585935 := by
  unfold tailWord_5694618
  simp only [CollatzResearch.WordTrace]
  refine ⟨51924945420844756042447127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138466521122252682779859005 51924945420844756042447127)
  ·
    refine ⟨77887418131267134063670691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51924945420844756042447127 77887418131267134063670691)
    ·
      refine ⟨116831127196900701095506037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77887418131267134063670691 116831127196900701095506037)
      ·
        refine ⟨10952918174709440727703691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116831127196900701095506037 10952918174709440727703691)
        ·
          refine ⟨16429377262064161091555537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10952918174709440727703691 16429377262064161091555537)
          ·
            refine ⟨12322032946548120818666653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16429377262064161091555537 12322032946548120818666653)
            ·
              refine ⟨4620762354955545306999995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12322032946548120818666653 4620762354955545306999995)
              ·
                refine ⟨6931143532433317960499993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4620762354955545306999995 6931143532433317960499993)
                ·
                  refine ⟨5198357649324988470374995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6931143532433317960499993 5198357649324988470374995)
                  ·
                    refine ⟨7797536473987482705562493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5198357649324988470374995 7797536473987482705562493)
                    ·
                      refine ⟨2924076177745306014585935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7797536473987482705562493 2924076177745306014585935)
                      ·
                        rfl

theorem cell23_5694618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_5694618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694618 prefixEnd_5694618 := by exact prefixLift 5694618
  have htrace : WordTrace (prefixWord ++ tailWord_5694618) baseStart_5694618 baseEnd_5694618 := by
    simpa [prefixWord, tailWord_5694618, baseEnd_5694618] using wordTrace_append hprefix tailTrace_5694618
  have hstable : (prefixWord ++ tailWord_5694618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694618).length < 2 ^ (prefixWord ++ tailWord_5694618).sum := by decide
  have hdescent : baseEnd_5694618 < baseStart_5694618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694641 : List Nat := [1, 2, 2, 5, 1, 1, 1, 2, 4, 2, 2]
def baseStart_5694641 : Nat := 118140960795 + 5694641 * 2 ^ 59
def prefixEnd_5694641 : Nat := 4983230072969 + 3 ^ 40 * 5694641 * 2
def baseEnd_5694641 : Nat := 2924087987800359424598329

theorem tailTrace_5694641 : CollatzResearch.WordTrace tailWord_5694641 prefixEnd_5694641 2924087987800359424598329 := by
  unfold tailWord_5694641
  simp only [CollatzResearch.WordTrace]
  refine ⟨207700620562295699097875777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138467080374863799398583851 207700620562295699097875777)
  ·
    refine ⟨155775465421721774323406833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207700620562295699097875777 155775465421721774323406833)
    ·
      refine ⟨116831599066291330742555125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155775465421721774323406833 116831599066291330742555125)
      ·
        refine ⟨10952962412464812257114543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116831599066291330742555125 10952962412464812257114543)
        ·
          refine ⟨16429443618697218385671815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10952962412464812257114543 16429443618697218385671815)
          ·
            refine ⟨24644165428045827578507723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16429443618697218385671815 24644165428045827578507723)
            ·
              refine ⟨36966248142068741367761585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24644165428045827578507723 36966248142068741367761585)
              ·
                refine ⟨27724686106551556025821189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36966248142068741367761585 27724686106551556025821189)
                ·
                  refine ⟨5198378644978416754841473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27724686106551556025821189 5198378644978416754841473)
                  ·
                    refine ⟨3898783983733812566131105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5198378644978416754841473 3898783983733812566131105)
                    ·
                      refine ⟨2924087987800359424598329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3898783983733812566131105 2924087987800359424598329)
                      ·
                        rfl

theorem cell23_5694641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_5694641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694641 prefixEnd_5694641 := by exact prefixLift 5694641
  have htrace : WordTrace (prefixWord ++ tailWord_5694641) baseStart_5694641 baseEnd_5694641 := by
    simpa [prefixWord, tailWord_5694641, baseEnd_5694641] using wordTrace_append hprefix tailTrace_5694641
  have hstable : (prefixWord ++ tailWord_5694641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694641).length < 2 ^ (prefixWord ++ tailWord_5694641).sum := by decide
  have hdescent : baseEnd_5694641 < baseStart_5694641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694669 : List Nat := [1, 6, 2, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_5694669 : Nat := 118140960795 + 5694669 * 2 ^ 59
def prefixEnd_5694669 : Nat := 4983230072969 + 3 ^ 40 * 5694669 * 2
def baseEnd_5694669 : Nat := 2924102365258685315048201

theorem tailTrace_5694669 : CollatzResearch.WordTrace tailWord_5694669 prefixEnd_5694669 2924102365258685315048201 := by
  unfold tailWord_5694669
  simp only [CollatzResearch.WordTrace]
  refine ⟨207701641806194259879895061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138467761204129506586596707 207701641806194259879895061)
  ·
    refine ⟨9736014459665355931870081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 207701641806194259879895061 9736014459665355931870081)
    ·
      refine ⟨7302010844749016948902561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9736014459665355931870081 7302010844749016948902561)
      ·
        refine ⟨5476508133561762711676921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7302010844749016948902561 5476508133561762711676921)
        ·
          refine ⟨4107381100171322033757691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5476508133561762711676921 4107381100171322033757691)
          ·
            refine ⟨6161071650256983050636537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4107381100171322033757691 6161071650256983050636537)
            ·
              refine ⟨4620803737692737287977403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6161071650256983050636537 4620803737692737287977403)
              ·
                refine ⟨6931205606539105931966105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4620803737692737287977403 6931205606539105931966105)
                ·
                  refine ⟨5198404204904329448974579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6931205606539105931966105 5198404204904329448974579)
                  ·
                    refine ⟨7797606307356494173461869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5198404204904329448974579 7797606307356494173461869)
                    ·
                      refine ⟨2924102365258685315048201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7797606307356494173461869 2924102365258685315048201)
                      ·
                        rfl

theorem cell23_5694669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_5694669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694669 prefixEnd_5694669 := by exact prefixLift 5694669
  have htrace : WordTrace (prefixWord ++ tailWord_5694669) baseStart_5694669 baseEnd_5694669 := by
    simpa [prefixWord, tailWord_5694669, baseEnd_5694669] using wordTrace_append hprefix tailTrace_5694669
  have hstable : (prefixWord ++ tailWord_5694669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694669).length < 2 ^ (prefixWord ++ tailWord_5694669).sum := by decide
  have hdescent : baseEnd_5694669 < baseStart_5694669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694714 : List Nat := [3, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2]
def baseStart_5694714 : Nat := 118140960795 + 5694714 * 2 ^ 59
def prefixEnd_5694714 : Nat := 4983230072969 + 3 ^ 40 * 5694714 * 2
def baseEnd_5694714 : Nat := 2924125471888137638985493

theorem tailTrace_5694714 : CollatzResearch.WordTrace tailWord_5694714 prefixEnd_5694714 2924125471888137638985493 := by
  unfold tailWord_5694714
  simp only [CollatzResearch.WordTrace]
  refine ⟨51925820772757808141320799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138468855394020821710188797 51925820772757808141320799)
  ·
    refine ⟨77888731159136712211981199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51925820772757808141320799 77888731159136712211981199)
    ·
      refine ⟨116833096738705068317971799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77888731159136712211981199 116833096738705068317971799)
      ·
        refine ⟨175249645108057602476957699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116833096738705068317971799 175249645108057602476957699)
        ·
          refine ⟨262874467662086403715436549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175249645108057602476957699 262874467662086403715436549)
          ·
            refine ⟨49288962686641200696644353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 262874467662086403715436549 49288962686641200696644353)
            ·
              refine ⟨36966722014980900522483265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49288962686641200696644353 36966722014980900522483265)
              ·
                refine ⟨27725041511235675391862449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36966722014980900522483265 27725041511235675391862449)
                ·
                  refine ⟨20793781133426756543896837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27725041511235675391862449 20793781133426756543896837)
                  ·
                    refine ⟨3898833962517516851980657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20793781133426756543896837 3898833962517516851980657)
                    ·
                      refine ⟨2924125471888137638985493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3898833962517516851980657 2924125471888137638985493)
                      ·
                        rfl

theorem cell23_5694714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2].length) (baseStart_5694714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694714 prefixEnd_5694714 := by exact prefixLift 5694714
  have htrace : WordTrace (prefixWord ++ tailWord_5694714) baseStart_5694714 baseEnd_5694714 := by
    simpa [prefixWord, tailWord_5694714, baseEnd_5694714] using wordTrace_append hprefix tailTrace_5694714
  have hstable : (prefixWord ++ tailWord_5694714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694714).length < 2 ^ (prefixWord ++ tailWord_5694714).sum := by decide
  have hdescent : baseEnd_5694714 < baseStart_5694714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694717 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 5, 4, 3]
def baseStart_5694717 : Nat := 118140960795 + 5694717 * 2 ^ 59
def prefixEnd_5694717 : Nat := 4983230072969 + 3 ^ 40 * 5694717 * 2
def baseEnd_5694717 : Nat := 2924127012330101127247979

theorem tailTrace_5694717 : CollatzResearch.WordTrace tailWord_5694717 prefixEnd_5694717 2924127012330101127247979 := by
  unfold tailWord_5694717
  simp only [CollatzResearch.WordTrace]
  refine ⟨207703392510020364077642405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138468928340013576051761603 207703392510020364077642405)
  ·
    refine ⟨38944386095628818264557951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207703392510020364077642405 38944386095628818264557951)
    ·
      refine ⟨58416579143443227396836927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38944386095628818264557951 58416579143443227396836927)
      ·
        refine ⟨87624868715164841095255391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58416579143443227396836927 87624868715164841095255391)
        ·
          refine ⟨131437303072747261642883087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87624868715164841095255391 131437303072747261642883087)
          ·
            refine ⟨197155954609120892464324631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131437303072747261642883087 197155954609120892464324631)
            ·
              refine ⟨295733931913681338696486947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197155954609120892464324631 295733931913681338696486947)
              ·
                refine ⟨443600897870522008044730421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295733931913681338696486947 443600897870522008044730421)
                ·
                  refine ⟨41587584175361438254193477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 443600897870522008044730421 41587584175361438254193477)
                  ·
                    refine ⟨7797672032880269672661277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41587584175361438254193477 7797672032880269672661277)
                    ·
                      refine ⟨2924127012330101127247979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7797672032880269672661277 2924127012330101127247979)
                      ·
                        rfl

theorem cell23_5694717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_5694717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694717 prefixEnd_5694717 := by exact prefixLift 5694717
  have htrace : WordTrace (prefixWord ++ tailWord_5694717) baseStart_5694717 baseEnd_5694717 := by
    simpa [prefixWord, tailWord_5694717, baseEnd_5694717] using wordTrace_append hprefix tailTrace_5694717
  have hstable : (prefixWord ++ tailWord_5694717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694717).length < 2 ^ (prefixWord ++ tailWord_5694717).sum := by decide
  have hdescent : baseEnd_5694717 < baseStart_5694717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694737 : List Nat := [1, 2, 2, 1, 1, 4, 1, 5, 6]
def baseStart_5694737 : Nat := 118140960795 + 5694737 * 2 ^ 59
def prefixEnd_5694737 : Nat := 4983230072969 + 3 ^ 40 * 5694737 * 2
def baseEnd_5694737 : Nat := 324904142438132338777543

theorem tailTrace_5694737 : CollatzResearch.WordTrace tailWord_5694737 prefixEnd_5694737 324904142438132338777543 := by
  unfold tailWord_5694737
  simp only [CollatzResearch.WordTrace]
  refine ⟨207704121969947907493370465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138469414646631938328913643 207704121969947907493370465)
  ·
    refine ⟨155778091477460930620027849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207704121969947907493370465 155778091477460930620027849)
    ·
      refine ⟨116833568608095697965020887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155778091477460930620027849 116833568608095697965020887)
      ·
        refine ⟨175250352912143546947531331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116833568608095697965020887 175250352912143546947531331)
        ·
          refine ⟨262875529368215320421296997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175250352912143546947531331 262875529368215320421296997)
          ·
            refine ⟨49289161756540372578993187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 262875529368215320421296997 49289161756540372578993187)
            ·
              refine ⟨73933742634810558868489781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49289161756540372578993187 73933742634810558868489781)
              ·
                refine ⟨6931288372013489893920917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73933742634810558868489781 6931288372013489893920917)
                ·
                  refine ⟨324904142438132338777543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6931288372013489893920917 324904142438132338777543)
                  ·
                    rfl

theorem cell23_5694737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 6].length) (baseStart_5694737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694737 prefixEnd_5694737 := by exact prefixLift 5694737
  have htrace : WordTrace (prefixWord ++ tailWord_5694737) baseStart_5694737 baseEnd_5694737 := by
    simpa [prefixWord, tailWord_5694737, baseEnd_5694737] using wordTrace_append hprefix tailTrace_5694737
  have hstable : (prefixWord ++ tailWord_5694737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694737).length < 2 ^ (prefixWord ++ tailWord_5694737).sum := by decide
  have hdescent : baseEnd_5694737 < baseStart_5694737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694764 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 3]
def baseStart_5694764 : Nat := 118140960795 + 5694764 * 2 ^ 59
def prefixEnd_5694764 : Nat := 4983230072969 + 3 ^ 40 * 5694764 * 2
def baseEnd_5694764 : Nat := 2924151145920862443360263

theorem tailTrace_5694764 : CollatzResearch.WordTrace tailWord_5694764 prefixEnd_5694764 2924151145920862443360263 := by
  unfold tailWord_5694764
  simp only [CollatzResearch.WordTrace]
  refine ⟨103852553370425045552301673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138470071160566727403068897 103852553370425045552301673)
  ·
    refine ⟨77889415027818784164226255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103852553370425045552301673 77889415027818784164226255)
    ·
      refine ⟨116834122541728176246339383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77889415027818784164226255 116834122541728176246339383)
      ·
        refine ⟨175251183812592264369509075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116834122541728176246339383 175251183812592264369509075)
        ·
          refine ⟨262876775718888396554263613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175251183812592264369509075 262876775718888396554263613)
          ·
            refine ⟨98578790894583148707848855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 262876775718888396554263613 98578790894583148707848855)
            ·
              refine ⟨147868186341874723061773283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98578790894583148707848855 147868186341874723061773283)
              ·
                refine ⟨221802279512812084592659925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147868186341874723061773283 221802279512812084592659925)
                ·
                  refine ⟨5198490926081533232640467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 221802279512812084592659925 5198490926081533232640467)
                  ·
                    refine ⟨7797736389122299848960701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5198490926081533232640467 7797736389122299848960701)
                    ·
                      refine ⟨2924151145920862443360263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7797736389122299848960701 2924151145920862443360263)
                      ·
                        rfl

theorem cell23_5694764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 3].length) (baseStart_5694764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694764 prefixEnd_5694764 := by exact prefixLift 5694764
  have htrace : WordTrace (prefixWord ++ tailWord_5694764) baseStart_5694764 baseEnd_5694764 := by
    simpa [prefixWord, tailWord_5694764, baseEnd_5694764] using wordTrace_append hprefix tailTrace_5694764
  have hstable : (prefixWord ++ tailWord_5694764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694764).length < 2 ^ (prefixWord ++ tailWord_5694764).sum := by decide
  have hdescent : baseEnd_5694764 < baseStart_5694764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694788 : List Nat := [2, 3, 4, 1, 1, 2, 3, 1, 6]
def baseStart_5694788 : Nat := 118140960795 + 5694788 * 2 ^ 59
def prefixEnd_5694788 : Nat := 4983230072969 + 3 ^ 40 * 5694788 * 2
def baseEnd_5694788 : Nat := 324907052161841149940017

theorem tailTrace_5694788 : CollatzResearch.WordTrace tailWord_5694788 prefixEnd_5694788 324907052161841149940017 := by
  unfold tailWord_5694788
  simp only [CollatzResearch.WordTrace]
  refine ⟨103852991046381571601738509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138470654728508762135651345 103852991046381571601738509)
  ·
    refine ⟨38944871642393089350651941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103852991046381571601738509 38944871642393089350651941)
    ·
      refine ⟨7302163432948704253247239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38944871642393089350651941 7302163432948704253247239)
      ·
        refine ⟨10953245149423056379870859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7302163432948704253247239 10953245149423056379870859)
        ·
          refine ⟨16429867724134584569806289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10953245149423056379870859 16429867724134584569806289)
          ·
            refine ⟨12322400793100938427354717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16429867724134584569806289 12322400793100938427354717)
            ·
              refine ⟨4620900297412851910258019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12322400793100938427354717 4620900297412851910258019)
              ·
                refine ⟨6931350446119277865387029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4620900297412851910258019 6931350446119277865387029)
                ·
                  refine ⟨324907052161841149940017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6931350446119277865387029 324907052161841149940017)
                  ·
                    rfl

theorem cell23_5694788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 6].length) (baseStart_5694788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694788 prefixEnd_5694788 := by exact prefixLift 5694788
  have htrace : WordTrace (prefixWord ++ tailWord_5694788) baseStart_5694788 baseEnd_5694788 := by
    simpa [prefixWord, tailWord_5694788, baseEnd_5694788] using wordTrace_append hprefix tailTrace_5694788
  have hstable : (prefixWord ++ tailWord_5694788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694788).length < 2 ^ (prefixWord ++ tailWord_5694788).sum := by decide
  have hdescent : baseEnd_5694788 < baseStart_5694788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694907 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 10]
def baseStart_5694907 : Nat := 118140960795 + 5694907 * 2 ^ 59
def prefixEnd_5694907 : Nat := 4983230072969 + 3 ^ 40 * 5694907 * 2
def baseEnd_5694907 : Nat := 2924224573654455383872105

theorem tailTrace_5694907 : CollatzResearch.WordTrace tailWord_5694907 prefixEnd_5694907 2924224573654455383872105 := by
  unfold tailWord_5694907
  simp only [CollatzResearch.WordTrace]
  refine ⟨207710322379332026527058975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138473548252888017684705983 207710322379332026527058975)
  ·
    refine ⟨311565483568998039790588463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207710322379332026527058975 311565483568998039790588463)
    ·
      refine ⟨467348225353497059685882695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311565483568998039790588463 467348225353497059685882695)
      ·
        refine ⟨701022338030245589528824043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467348225353497059685882695 701022338030245589528824043)
        ·
          refine ⟨1051533507045368384293236065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701022338030245589528824043 1051533507045368384293236065)
          ·
            refine ⟨788650130284026288219927049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1051533507045368384293236065 788650130284026288219927049)
            ·
              refine ⟨591487597713019716164945287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 788650130284026288219927049 591487597713019716164945287)
              ·
                refine ⟨887231396569529574247417931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 591487597713019716164945287 887231396569529574247417931)
                ·
                  refine ⟨1330847094854294361371126897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 887231396569529574247417931 1330847094854294361371126897)
                  ·
                    refine ⟨998135321140720771028345173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1330847094854294361371126897 998135321140720771028345173)
                    ·
                      refine ⟨2924224573654455383872105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 998135321140720771028345173 2924224573654455383872105)
                      ·
                        rfl

theorem cell23_5694907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 10].length) (baseStart_5694907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694907 prefixEnd_5694907 := by exact prefixLift 5694907
  have htrace : WordTrace (prefixWord ++ tailWord_5694907) baseStart_5694907 baseEnd_5694907 := by
    simpa [prefixWord, tailWord_5694907, baseEnd_5694907] using wordTrace_append hprefix tailTrace_5694907
  have hstable : (prefixWord ++ tailWord_5694907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694907).length < 2 ^ (prefixWord ++ tailWord_5694907).sum := by decide
  have hdescent : baseEnd_5694907 < baseStart_5694907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694941 : List Nat := [1, 4, 3, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_5694941 : Nat := 118140960795 + 5694941 * 2 ^ 59
def prefixEnd_5694941 : Nat := 4983230072969 + 3 ^ 40 * 5694941 * 2
def baseEnd_5694941 : Nat := 2924242031996708250846949

theorem tailTrace_5694941 : CollatzResearch.WordTrace tailWord_5694941 prefixEnd_5694941 2924242031996708250846949 := by
  unfold tailWord_5694941
  simp only [CollatzResearch.WordTrace]
  refine ⟨207711562461208850333796677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138474374974139233555864451 207711562461208850333796677)
  ·
    refine ⟨38945917961476659437586877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207711562461208850333796677 38945917961476659437586877)
    ·
      refine ⟨14604719235553747289095079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38945917961476659437586877 14604719235553747289095079)
      ·
        refine ⟨21907078853330620933642619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14604719235553747289095079 21907078853330620933642619)
        ·
          refine ⟨32860618279995931400463929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21907078853330620933642619 32860618279995931400463929)
          ·
            refine ⟨24645463709996948550347947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32860618279995931400463929 24645463709996948550347947)
            ·
              refine ⟨36968195564995422825521921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24645463709996948550347947 36968195564995422825521921)
              ·
                refine ⟨27726146673746567119141441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36968195564995422825521921 27726146673746567119141441)
                ·
                  refine ⟨20794610005309925339356081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27726146673746567119141441 20794610005309925339356081)
                  ·
                    refine ⟨15595957503982444004517061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20794610005309925339356081 15595957503982444004517061)
                    ·
                      refine ⟨2924242031996708250846949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15595957503982444004517061 2924242031996708250846949)
                      ·
                        rfl

theorem cell23_5694941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_5694941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694941 prefixEnd_5694941 := by exact prefixLift 5694941
  have htrace : WordTrace (prefixWord ++ tailWord_5694941) baseStart_5694941 baseEnd_5694941 := by
    simpa [prefixWord, tailWord_5694941, baseEnd_5694941] using wordTrace_append hprefix tailTrace_5694941
  have hstable : (prefixWord ++ tailWord_5694941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694941).length < 2 ^ (prefixWord ++ tailWord_5694941).sum := by decide
  have hdescent : baseEnd_5694941 < baseStart_5694941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694945 : List Nat := [1, 2, 3, 1, 2, 3, 3, 2, 2, 2, 2]
def baseStart_5694945 : Nat := 118140960795 + 5694945 * 2 ^ 59
def prefixEnd_5694945 : Nat := 4983230072969 + 3 ^ 40 * 5694945 * 2
def baseEnd_5694945 : Nat := 2924244085919326235196931

theorem tailTrace_5694945 : CollatzResearch.WordTrace tailWord_5694945 prefixEnd_5694945 2924244085919326235196931 := by
  unfold tailWord_5694945
  simp only [CollatzResearch.WordTrace]
  refine ⟨207711708353194359016942289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138474472235462906011294859 207711708353194359016942289)
  ·
    refine ⟨155783781264895769262706717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207711708353194359016942289 155783781264895769262706717)
    ·
      refine ⟨58418917974335913473515019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155783781264895769262706717 58418917974335913473515019)
      ·
        refine ⟨87628376961503870210272529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58418917974335913473515019 87628376961503870210272529)
        ·
          refine ⟨65721282721127902657704397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87628376961503870210272529 65721282721127902657704397)
          ·
            refine ⟨24645481020422963496639149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65721282721127902657704397 24645481020422963496639149)
            ·
              refine ⟨9242055382658611311239681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24645481020422963496639149 9242055382658611311239681)
              ·
                refine ⟨6931541536993958483429761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9242055382658611311239681 6931541536993958483429761)
                ·
                  refine ⟨5198656152745468862572321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6931541536993958483429761 5198656152745468862572321)
                  ·
                    refine ⟨3898992114559101646929241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5198656152745468862572321 3898992114559101646929241)
                    ·
                      refine ⟨2924244085919326235196931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3898992114559101646929241 2924244085919326235196931)
                      ·
                        rfl

theorem cell23_5694945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2, 2, 2].length) (baseStart_5694945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694945 prefixEnd_5694945 := by exact prefixLift 5694945
  have htrace : WordTrace (prefixWord ++ tailWord_5694945) baseStart_5694945 baseEnd_5694945 := by
    simpa [prefixWord, tailWord_5694945, baseEnd_5694945] using wordTrace_append hprefix tailTrace_5694945
  have hstable : (prefixWord ++ tailWord_5694945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694945).length < 2 ^ (prefixWord ++ tailWord_5694945).sum := by decide
  have hdescent : baseEnd_5694945 < baseStart_5694945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694951 : List Nat := [1, 1, 5, 2, 1, 3, 2, 1, 7]
def baseStart_5694951 : Nat := 118140960795 + 5694951 * 2 ^ 59
def prefixEnd_5694951 : Nat := 4983230072969 + 3 ^ 40 * 5694951 * 2
def baseEnd_5694951 : Nat := 324916351867028134635767

theorem tailTrace_5694951 : CollatzResearch.WordTrace tailWord_5694951 prefixEnd_5694951 324916351867028134635767 := by
  unfold tailWord_5694951
  simp only [CollatzResearch.WordTrace]
  refine ⟨207711927191172622041660707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138474618127448414694440471 207711927191172622041660707)
  ·
    refine ⟨311567890786758933062491061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207711927191172622041660707 311567890786758933062491061)
    ·
      refine ⟨29209489761258649974608537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 311567890786758933062491061 29209489761258649974608537)
      ·
        refine ⟨21907117320943987480956403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29209489761258649974608537 21907117320943987480956403)
        ·
          refine ⟨32860675981415981221434605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21907117320943987480956403 32860675981415981221434605)
          ·
            refine ⟨12322753493030992958037977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32860675981415981221434605 12322753493030992958037977)
            ·
              refine ⟨9242065119773244718528483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12322753493030992958037977 9242065119773244718528483)
              ·
                refine ⟨13863097679659867077792725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9242065119773244718528483 13863097679659867077792725)
                ·
                  refine ⟨324916351867028134635767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13863097679659867077792725 324916351867028134635767)
                  ·
                    rfl

theorem cell23_5694951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 7].length) (baseStart_5694951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694951 prefixEnd_5694951 := by exact prefixLift 5694951
  have htrace : WordTrace (prefixWord ++ tailWord_5694951) baseStart_5694951 baseEnd_5694951 := by
    simpa [prefixWord, tailWord_5694951, baseEnd_5694951] using wordTrace_append hprefix tailTrace_5694951
  have hstable : (prefixWord ++ tailWord_5694951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694951).length < 2 ^ (prefixWord ++ tailWord_5694951).sum := by decide
  have hdescent : baseEnd_5694951 < baseStart_5694951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694961 : List Nat := [1, 2, 2, 2, 3, 2, 2, 1, 2, 3, 3]
def baseStart_5694961 : Nat := 118140960795 + 5694961 * 2 ^ 59
def prefixEnd_5694961 : Nat := 4983230072969 + 3 ^ 40 * 5694961 * 2
def baseEnd_5694961 : Nat := 2924252301609798172596857

theorem tailTrace_5694961 : CollatzResearch.WordTrace tailWord_5694961 prefixEnd_5694961 2924252301609798172596857 := by
  unfold tailWord_5694961
  simp only [CollatzResearch.WordTrace]
  refine ⟨207712291921136393749524737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138474861280757595833016491 207712291921136393749524737)
  ·
    refine ⟨155784218940852295312143553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207712291921136393749524737 155784218940852295312143553)
    ·
      refine ⟨116838164205639221484107665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155784218940852295312143553 116838164205639221484107665)
      ·
        refine ⟨87628623154229416113080749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116838164205639221484107665 87628623154229416113080749)
        ·
          refine ⟨32860733682836031042405281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87628623154229416113080749 32860733682836031042405281)
          ·
            refine ⟨24645550262127023281803961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32860733682836031042405281 24645550262127023281803961)
            ·
              refine ⟨18484162696595267461352971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24645550262127023281803961 18484162696595267461352971)
              ·
                refine ⟨27726244044892901192029457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18484162696595267461352971 27726244044892901192029457)
                ·
                  refine ⟨20794683033669675894022093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27726244044892901192029457 20794683033669675894022093)
                  ·
                    refine ⟨7798006137626128460258285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20794683033669675894022093 7798006137626128460258285)
                    ·
                      refine ⟨2924252301609798172596857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7798006137626128460258285 2924252301609798172596857)
                      ·
                        rfl

theorem cell23_5694961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_5694961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694961 prefixEnd_5694961 := by exact prefixLift 5694961
  have htrace : WordTrace (prefixWord ++ tailWord_5694961) baseStart_5694961 baseEnd_5694961 := by
    simpa [prefixWord, tailWord_5694961, baseEnd_5694961] using wordTrace_append hprefix tailTrace_5694961
  have hstable : (prefixWord ++ tailWord_5694961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694961).length < 2 ^ (prefixWord ++ tailWord_5694961).sum := by decide
  have hdescent : baseEnd_5694961 < baseStart_5694961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5694982 : List Nat := [6, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_5694982 : Nat := 118140960795 + 5694982 * 2 ^ 59
def prefixEnd_5694982 : Nat := 4983230072969 + 3 ^ 40 * 5694982 * 2
def baseEnd_5694982 : Nat := 2924263084703542590434261

theorem tailTrace_5694982 : CollatzResearch.WordTrace tailWord_5694982 prefixEnd_5694982 2924263084703542590434261 := by
  unfold tailWord_5694982
  simp only [CollatzResearch.WordTrace]
  refine ⟨6491033057939384823001225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 138475371902706876224026133 6491033057939384823001225)
  ·
    refine ⟨4868274793454538617250919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6491033057939384823001225 4868274793454538617250919)
    ·
      refine ⟨7302412190181807925876379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4868274793454538617250919 7302412190181807925876379)
      ·
        refine ⟨10953618285272711888814569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7302412190181807925876379 10953618285272711888814569)
        ·
          refine ⟨8215213713954533916610927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10953618285272711888814569 8215213713954533916610927)
          ·
            refine ⟨12322820570931800874916391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8215213713954533916610927 12322820570931800874916391)
            ·
              refine ⟨18484230856397701312374587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12322820570931800874916391 18484230856397701312374587)
              ·
                refine ⟨27726346284596551968561881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18484230856397701312374587 27726346284596551968561881)
                ·
                  refine ⟨20794759713447413976421411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27726346284596551968561881 20794759713447413976421411)
                  ·
                    refine ⟨31192139570171120964632117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20794759713447413976421411 31192139570171120964632117)
                    ·
                      refine ⟨2924263084703542590434261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31192139570171120964632117 2924263084703542590434261)
                      ·
                        rfl

theorem cell23_5694982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_5694982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5694982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5694982 prefixEnd_5694982 := by exact prefixLift 5694982
  have htrace : WordTrace (prefixWord ++ tailWord_5694982) baseStart_5694982 baseEnd_5694982 := by
    simpa [prefixWord, tailWord_5694982, baseEnd_5694982] using wordTrace_append hprefix tailTrace_5694982
  have hstable : (prefixWord ++ tailWord_5694982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5694982).length < 2 ^ (prefixWord ++ tailWord_5694982).sum := by decide
  have hdescent : baseEnd_5694982 < baseStart_5694982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5694982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695018 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 1, 6, 2]
def baseStart_5695018 : Nat := 118140960795 + 5695018 * 2 ^ 59
def prefixEnd_5695018 : Nat := 4983230072969 + 3 ^ 40 * 5695018 * 2
def baseEnd_5695018 : Nat := 2924281570007104449584095

theorem tailTrace_5695018 : CollatzResearch.WordTrace tailWord_5695018 prefixEnd_5695018 2924281570007104449584095 := by
  unfold tailWord_5695018
  simp only [CollatzResearch.WordTrace]
  refine ⟨51928592720482473121087427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138476247254619928322899805 51928592720482473121087427)
  ·
    refine ⟨77892889080723709681631141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51928592720482473121087427 77892889080723709681631141)
    ·
      refine ⟨14604916702635695565305839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77892889080723709681631141 14604916702635695565305839)
      ·
        refine ⟨21907375053953543347958759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14604916702635695565305839 21907375053953543347958759)
        ·
          refine ⟨32861062580930315021938139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21907375053953543347958759 32861062580930315021938139)
          ·
            refine ⟨49291593871395472532907209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32861062580930315021938139 49291593871395472532907209)
            ·
              refine ⟨36968695403546604399680407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49291593871395472532907209 36968695403546604399680407)
              ·
                refine ⟨55453043105319906599520611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36968695403546604399680407 55453043105319906599520611)
                ·
                  refine ⟨83179564657979859899280917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55453043105319906599520611 83179564657979859899280917)
                  ·
                    refine ⟨3899042093342805932778793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83179564657979859899280917 3899042093342805932778793)
                    ·
                      refine ⟨2924281570007104449584095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3899042093342805932778793 2924281570007104449584095)
                      ·
                        rfl

theorem cell23_5695018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_5695018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695018 prefixEnd_5695018 := by exact prefixLift 5695018
  have htrace : WordTrace (prefixWord ++ tailWord_5695018) baseStart_5695018 baseEnd_5695018 := by
    simpa [prefixWord, tailWord_5695018, baseEnd_5695018] using wordTrace_append hprefix tailTrace_5695018
  have hstable : (prefixWord ++ tailWord_5695018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695018).length < 2 ^ (prefixWord ++ tailWord_5695018).sum := by decide
  have hdescent : baseEnd_5695018 < baseStart_5695018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695058 : List Nat := [3, 2, 2, 1, 2, 3, 2, 2, 6]
def baseStart_5695058 : Nat := 118140960795 + 5695058 * 2 ^ 59
def prefixEnd_5695058 : Nat := 4983230072969 + 3 ^ 40 * 5695058 * 2
def baseEnd_5695058 : Nat := 324922456581476032564879

theorem tailTrace_5695058 : CollatzResearch.WordTrace tailWord_5695058 prefixEnd_5695058 324922456581476032564879 := by
  unfold tailWord_5695058
  simp only [CollatzResearch.WordTrace]
  refine ⟨51928957450446244828951457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138477219867856652877203885 51928957450446244828951457)
  ·
    refine ⟨38946718087834683621713593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51928957450446244828951457 38946718087834683621713593)
    ·
      refine ⟨29210038565876012716285195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38946718087834683621713593 29210038565876012716285195)
      ·
        refine ⟨43815057848814019074427793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29210038565876012716285195 43815057848814019074427793)
        ·
          refine ⟨32861293386610514305820845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43815057848814019074427793 32861293386610514305820845)
          ·
            refine ⟨12322985019978942864682817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32861293386610514305820845 12322985019978942864682817)
            ·
              refine ⟨9242238764984207148512113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12322985019978942864682817 9242238764984207148512113)
              ·
                refine ⟨6931679073738155361384085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9242238764984207148512113 6931679073738155361384085)
                ·
                  refine ⟨324922456581476032564879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6931679073738155361384085 324922456581476032564879)
                  ·
                    rfl

theorem cell23_5695058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 6].length) (baseStart_5695058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695058 prefixEnd_5695058 := by exact prefixLift 5695058
  have htrace : WordTrace (prefixWord ++ tailWord_5695058) baseStart_5695058 baseEnd_5695058 := by
    simpa [prefixWord, tailWord_5695058, baseEnd_5695058] using wordTrace_append hprefix tailTrace_5695058
  have hstable : (prefixWord ++ tailWord_5695058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695058).length < 2 ^ (prefixWord ++ tailWord_5695058).sum := by decide
  have hdescent : baseEnd_5695058 < baseStart_5695058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695105 : List Nat := [1, 2, 4, 2, 1, 2, 4, 1, 1, 5]
def baseStart_5695105 : Nat := 118140960795 + 5695105 * 2 ^ 59
def prefixEnd_5695105 : Nat := 4983230072969 + 3 ^ 40 * 5695105 * 2
def baseEnd_5695105 : Nat := 974775414274681869732065

theorem tailTrace_5695105 : CollatzResearch.WordTrace tailWord_5695105 prefixEnd_5695105 974775414274681869732065 := by
  unfold tailWord_5695105
  simp only [CollatzResearch.WordTrace]
  refine ⟨207717544032614706342766769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138478362688409804228511179 207717544032614706342766769)
  ·
    refine ⟨155788158024461029757075077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207717544032614706342766769 155788158024461029757075077)
    ·
      refine ⟨29210279629586443079451577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155788158024461029757075077 29210279629586443079451577)
      ·
        refine ⟨21907709722189832309588683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29210279629586443079451577 21907709722189832309588683)
        ·
          refine ⟨32861564583284748464383025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21907709722189832309588683 32861564583284748464383025)
          ·
            refine ⟨24646173437463561348287269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32861564583284748464383025 24646173437463561348287269)
            ·
              refine ⟨4621157519524417752803863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24646173437463561348287269 4621157519524417752803863)
              ·
                refine ⟨6931736279286626629205795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4621157519524417752803863 6931736279286626629205795)
                ·
                  refine ⟨10397604418929939943808693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6931736279286626629205795 10397604418929939943808693)
                  ·
                    refine ⟨974775414274681869732065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10397604418929939943808693 974775414274681869732065)
                    ·
                      rfl

theorem cell23_5695105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_5695105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695105 prefixEnd_5695105 := by exact prefixLift 5695105
  have htrace : WordTrace (prefixWord ++ tailWord_5695105) baseStart_5695105 baseEnd_5695105 := by
    simpa [prefixWord, tailWord_5695105, baseEnd_5695105] using wordTrace_append hprefix tailTrace_5695105
  have hstable : (prefixWord ++ tailWord_5695105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695105).length < 2 ^ (prefixWord ++ tailWord_5695105).sum := by decide
  have hdescent : baseEnd_5695105 < baseStart_5695105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695128 : List Nat := [2, 1, 2, 4, 1, 3, 1, 2, 1, 1, 5]
def baseStart_5695128 : Nat := 118140960795 + 5695128 * 2 ^ 59
def prefixEnd_5695128 : Nat := 4983230072969 + 3 ^ 40 * 5695128 * 2
def baseEnd_5695128 : Nat := 2924338052879099019208589

theorem tailTrace_5695128 : CollatzResearch.WordTrace tailWord_5695128 prefixEnd_5695128 2924338052879099019208589 := by
  unfold tailWord_5695128
  simp only [CollatzResearch.WordTrace]
  refine ⟨103859191455765690635427019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138478921941020920847236025 103859191455765690635427019)
  ·
    refine ⟨155788787183648535953140529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103859191455765690635427019 155788787183648535953140529)
    ·
      refine ⟨116841590387736401964855397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155788787183648535953140529 116841590387736401964855397)
      ·
        refine ⟨21907798197700575368410387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116841590387736401964855397 21907798197700575368410387)
        ·
          refine ⟨32861697296550863052615581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21907798197700575368410387 32861697296550863052615581)
          ·
            refine ⟨12323136486206573644730843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32861697296550863052615581 12323136486206573644730843)
            ·
              refine ⟨18484704729309860467096265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12323136486206573644730843 18484704729309860467096265)
              ·
                refine ⟨13863528546982395350322199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18484704729309860467096265 13863528546982395350322199)
                ·
                  refine ⟨20795292820473593025483299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13863528546982395350322199 20795292820473593025483299)
                  ·
                    refine ⟨31192939230710389538224949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20795292820473593025483299 31192939230710389538224949)
                    ·
                      refine ⟨2924338052879099019208589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31192939230710389538224949 2924338052879099019208589)
                      ·
                        rfl

theorem cell23_5695128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_5695128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695128 prefixEnd_5695128 := by exact prefixLift 5695128
  have htrace : WordTrace (prefixWord ++ tailWord_5695128) baseStart_5695128 baseEnd_5695128 := by
    simpa [prefixWord, tailWord_5695128, baseEnd_5695128] using wordTrace_append hprefix tailTrace_5695128
  have hstable : (prefixWord ++ tailWord_5695128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695128).length < 2 ^ (prefixWord ++ tailWord_5695128).sum := by decide
  have hdescent : baseEnd_5695128 < baseStart_5695128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695159 : List Nat := [1, 1, 3, 1, 5, 1, 3, 3, 1, 2, 2]
def baseStart_5695159 : Nat := 118140960795 + 5695159 * 2 ^ 59
def prefixEnd_5695159 : Nat := 4983230072969 + 3 ^ 40 * 5695159 * 2
def baseEnd_5695159 : Nat := 2924353970779388397920947

theorem tailTrace_5695159 : CollatzResearch.WordTrace tailWord_5695159 prefixEnd_5695159 2924353970779388397920947 := by
  unfold tailWord_5695159
  simp only [CollatzResearch.WordTrace]
  refine ⟨207719513574419073565232531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138479675716279382376821687 207719513574419073565232531)
  ·
    refine ⟨311579270361628610347848797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207719513574419073565232531 311579270361628610347848797)
    ·
      refine ⟨116842226385610728880443299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 311579270361628610347848797 116842226385610728880443299)
      ·
        refine ⟨175263339578416093320664949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116842226385610728880443299 175263339578416093320664949)
        ·
          refine ⟨16430938085476508748812339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 175263339578416093320664949 16430938085476508748812339)
          ·
            refine ⟨24646407128214763123218509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16430938085476508748812339 24646407128214763123218509)
            ·
              refine ⟨9242402673080536171206941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24646407128214763123218509 9242402673080536171206941)
              ·
                refine ⟨3465901002405201064202603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9242402673080536171206941 3465901002405201064202603)
                ·
                  refine ⟨5198851503607801596303905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3465901002405201064202603 5198851503607801596303905)
                  ·
                    refine ⟨3899138627705851197227929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5198851503607801596303905 3899138627705851197227929)
                    ·
                      refine ⟨2924353970779388397920947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3899138627705851197227929 2924353970779388397920947)
                      ·
                        rfl

theorem cell23_5695159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3, 1, 2, 2].length) (baseStart_5695159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695159 prefixEnd_5695159 := by exact prefixLift 5695159
  have htrace : WordTrace (prefixWord ++ tailWord_5695159) baseStart_5695159 baseEnd_5695159 := by
    simpa [prefixWord, tailWord_5695159, baseEnd_5695159] using wordTrace_append hprefix tailTrace_5695159
  have hstable : (prefixWord ++ tailWord_5695159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695159).length < 2 ^ (prefixWord ++ tailWord_5695159).sum := by decide
  have hdescent : baseEnd_5695159 < baseStart_5695159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695170 : List Nat := [3, 5, 1, 2, 1, 1, 3, 2, 1, 1, 3]
def baseStart_5695170 : Nat := 118140960795 + 5695170 * 2 ^ 59
def prefixEnd_5695170 : Nat := 4983230072969 + 3 ^ 40 * 5695170 * 2
def baseEnd_5695170 : Nat := 2924359619066587854883397

theorem tailTrace_5695170 : CollatzResearch.WordTrace tailWord_5695170 prefixEnd_5695170 2924359619066587854883397 := by
  unfold tailWord_5695170
  simp only [CollatzResearch.WordTrace]
  refine ⟨51929978694344805610970741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138479943184919481629255309 51929978694344805610970741)
  ·
    refine ⟨4868435502594825526028507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51929978694344805610970741 4868435502594825526028507)
    ·
      refine ⟨7302653253892238289042761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4868435502594825526028507 7302653253892238289042761)
      ·
        refine ⟨5476989940419178716782071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7302653253892238289042761 5476989940419178716782071)
        ·
          refine ⟨8215484910628768075173107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5476989940419178716782071 8215484910628768075173107)
          ·
            refine ⟨12323227365943152112759661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8215484910628768075173107 12323227365943152112759661)
            ·
              refine ⟨4621210262228682042284873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12323227365943152112759661 4621210262228682042284873)
              ·
                refine ⟨3465907696671511531713655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4621210262228682042284873 3465907696671511531713655)
                ·
                  refine ⟨5198861545007267297570483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3465907696671511531713655 5198861545007267297570483)
                  ·
                    refine ⟨7798292317510900946355725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5198861545007267297570483 7798292317510900946355725)
                    ·
                      refine ⟨2924359619066587854883397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7798292317510900946355725 2924359619066587854883397)
                      ·
                        rfl

theorem cell23_5695170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_5695170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695170 prefixEnd_5695170 := by exact prefixLift 5695170
  have htrace : WordTrace (prefixWord ++ tailWord_5695170) baseStart_5695170 baseEnd_5695170 := by
    simpa [prefixWord, tailWord_5695170, baseEnd_5695170] using wordTrace_append hprefix tailTrace_5695170
  have hstable : (prefixWord ++ tailWord_5695170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695170).length < 2 ^ (prefixWord ++ tailWord_5695170).sum := by decide
  have hdescent : baseEnd_5695170 < baseStart_5695170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695175 : List Nat := [1, 1, 4, 1, 1, 1, 4, 4, 2, 1, 3]
def baseStart_5695175 : Nat := 118140960795 + 5695175 * 2 ^ 59
def prefixEnd_5695175 : Nat := 4983230072969 + 3 ^ 40 * 5695175 * 2
def baseEnd_5695175 : Nat := 2924362186469860335320873

theorem tailTrace_5695175 : CollatzResearch.WordTrace tailWord_5695175 prefixEnd_5695175 2924362186469860335320873 := by
  unfold tailWord_5695175
  simp only [CollatzResearch.WordTrace]
  refine ⟨207720097142361108297814979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138480064761574072198543319 207720097142361108297814979)
  ·
    refine ⟨311580145713541662446722469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207720097142361108297814979 311580145713541662446722469)
    ·
      refine ⟨58421277321289061708760463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 311580145713541662446722469 58421277321289061708760463)
      ·
        refine ⟨87631915981933592563140695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58421277321289061708760463 87631915981933592563140695)
        ·
          refine ⟨131447873972900388844711043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87631915981933592563140695 131447873972900388844711043)
          ·
            refine ⟨197171810959350583267066565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131447873972900388844711043 197171810959350583267066565)
            ·
              refine ⟨36969714554878234362574981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 197171810959350583267066565 36969714554878234362574981)
              ·
                refine ⟨6931821479039668942982809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36969714554878234362574981 6931821479039668942982809)
                ·
                  refine ⟨5198866109279751707237107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6931821479039668942982809 5198866109279751707237107)
                  ·
                    refine ⟨7798299163919627560855661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5198866109279751707237107 7798299163919627560855661)
                    ·
                      refine ⟨2924362186469860335320873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7798299163919627560855661 2924362186469860335320873)
                      ·
                        rfl

theorem cell23_5695175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_5695175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695175 prefixEnd_5695175 := by exact prefixLift 5695175
  have htrace : WordTrace (prefixWord ++ tailWord_5695175) baseStart_5695175 baseEnd_5695175 := by
    simpa [prefixWord, tailWord_5695175, baseEnd_5695175] using wordTrace_append hprefix tailTrace_5695175
  have hstable : (prefixWord ++ tailWord_5695175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695175).length < 2 ^ (prefixWord ++ tailWord_5695175).sum := by decide
  have hdescent : baseEnd_5695175 < baseStart_5695175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695191 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 1, 8]
def baseStart_5695191 : Nat := 118140960795 + 5695191 * 2 ^ 59
def prefixEnd_5695191 : Nat := 4983230072969 + 3 ^ 40 * 5695191 * 2
def baseEnd_5695191 : Nat := 974790134053444090906933

theorem tailTrace_5695191 : CollatzResearch.WordTrace tailWord_5695191 prefixEnd_5695191 974790134053444090906933 := by
  unfold tailWord_5695191
  simp only [CollatzResearch.WordTrace]
  refine ⟨207720680710303143030397427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138480453806868762020264951 207720680710303143030397427)
  ·
    refine ⟨311581021065454714545596141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207720680710303143030397427 311581021065454714545596141)
    ·
      refine ⟨116842882899545517954598553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 311581021065454714545596141 116842882899545517954598553)
      ·
        refine ⟨87632162174659138465948915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116842882899545517954598553 87632162174659138465948915)
        ·
          refine ⟨131448243261988707698923373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87632162174659138465948915 131448243261988707698923373)
          ·
            refine ⟨49293091223245765387096265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131448243261988707698923373 49293091223245765387096265)
            ·
              refine ⟨36969818417434324040322199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49293091223245765387096265 36969818417434324040322199)
              ·
                refine ⟨55454727626151486060483299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36969818417434324040322199 55454727626151486060483299)
                ·
                  refine ⟨83182091439227229090724949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55454727626151486060483299 83182091439227229090724949)
                  ·
                    refine ⟨974790134053444090906933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83182091439227229090724949 974790134053444090906933)
                    ·
                      rfl

theorem cell23_5695191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_5695191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695191 prefixEnd_5695191 := by exact prefixLift 5695191
  have htrace : WordTrace (prefixWord ++ tailWord_5695191) baseStart_5695191 baseEnd_5695191 := by
    simpa [prefixWord, tailWord_5695191, baseEnd_5695191] using wordTrace_append hprefix tailTrace_5695191
  have hstable : (prefixWord ++ tailWord_5695191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695191).length < 2 ^ (prefixWord ++ tailWord_5695191).sum := by decide
  have hdescent : baseEnd_5695191 < baseStart_5695191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695196 : List Nat := [2, 2, 5, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_5695196 : Nat := 118140960795 + 5695196 * 2 ^ 59
def prefixEnd_5695196 : Nat := 4983230072969 + 3 ^ 40 * 5695196 * 2
def baseEnd_5695196 : Nat := 2924372969563604753158277

theorem tailTrace_5695196 : CollatzResearch.WordTrace tailWord_5695196 prefixEnd_5695196 2924372969563604753158277 := by
  unfold tailWord_5695196
  simp only [CollatzResearch.WordTrace]
  refine ⟨103860431537642514442164721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138480575383523352589552961 103860431537642514442164721)
  ·
    refine ⟨77895323653231885831623541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103860431537642514442164721 77895323653231885831623541)
    ·
      refine ⟨7302686592490489296714707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77895323653231885831623541 7302686592490489296714707)
      ·
        refine ⟨10954029888735733945072061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7302686592490489296714707 10954029888735733945072061)
        ·
          refine ⟨4107761208275900229402023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10954029888735733945072061 4107761208275900229402023)
          ·
            refine ⟨6161641812413850344103035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4107761208275900229402023 6161641812413850344103035)
            ·
              refine ⟨9242462718620775516154553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6161641812413850344103035 9242462718620775516154553)
              ·
                refine ⟨6931847038965581637115915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9242462718620775516154553 6931847038965581637115915)
                ·
                  refine ⟨10397770558448372455673873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6931847038965581637115915 10397770558448372455673873)
                  ·
                    refine ⟨7798327918836279341755405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10397770558448372455673873 7798327918836279341755405)
                    ·
                      refine ⟨2924372969563604753158277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7798327918836279341755405 2924372969563604753158277)
                      ·
                        rfl

theorem cell23_5695196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_5695196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695196 prefixEnd_5695196 := by exact prefixLift 5695196
  have htrace : WordTrace (prefixWord ++ tailWord_5695196) baseStart_5695196 baseEnd_5695196 := by
    simpa [prefixWord, tailWord_5695196, baseEnd_5695196] using wordTrace_append hprefix tailTrace_5695196
  have hstable : (prefixWord ++ tailWord_5695196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695196).length < 2 ^ (prefixWord ++ tailWord_5695196).sum := by decide
  have hdescent : baseEnd_5695196 < baseStart_5695196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695215 : List Nat := [1, 1, 2, 1, 5, 1, 3, 2, 1, 4, 2]
def baseStart_5695215 : Nat := 118140960795 + 5695215 * 2 ^ 59
def prefixEnd_5695215 : Nat := 4983230072969 + 3 ^ 40 * 5695215 * 2
def baseEnd_5695215 : Nat := 2924382725696040178820689

theorem tailTrace_5695215 : CollatzResearch.WordTrace tailWord_5695215 prefixEnd_5695215 2924382725696040178820689 := by
  unfold tailWord_5695215
  simp only [CollatzResearch.WordTrace]
  refine ⟨207721556062216195129271099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138481037374810796752847399 207721556062216195129271099)
  ·
    refine ⟨311582334093324292693906649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207721556062216195129271099 311582334093324292693906649)
    ·
      refine ⟨233686750569993219520429987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311582334093324292693906649 233686750569993219520429987)
      ·
        refine ⟨350530125854989829280644981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233686750569993219520429987 350530125854989829280644981)
        ·
          refine ⟨32862199298905296495060467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 350530125854989829280644981 32862199298905296495060467)
          ·
            refine ⟨49293298948357944742590701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32862199298905296495060467 49293298948357944742590701)
            ·
              refine ⟨18484987105634229278471513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49293298948357944742590701 18484987105634229278471513)
              ·
                refine ⟨13863740329225671958853635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18484987105634229278471513 13863740329225671958853635)
                ·
                  refine ⟨20795610493838507938280453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13863740329225671958853635 20795610493838507938280453)
                  ·
                    refine ⟨3899176967594720238427585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20795610493838507938280453 3899176967594720238427585)
                    ·
                      refine ⟨2924382725696040178820689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3899176967594720238427585 2924382725696040178820689)
                      ·
                        rfl

theorem cell23_5695215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 4, 2].length) (baseStart_5695215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695215 prefixEnd_5695215 := by exact prefixLift 5695215
  have htrace : WordTrace (prefixWord ++ tailWord_5695215) baseStart_5695215 baseEnd_5695215 := by
    simpa [prefixWord, tailWord_5695215, baseEnd_5695215] using wordTrace_append hprefix tailTrace_5695215
  have hstable : (prefixWord ++ tailWord_5695215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695215).length < 2 ^ (prefixWord ++ tailWord_5695215).sum := by decide
  have hdescent : baseEnd_5695215 < baseStart_5695215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695218 : List Nat := [3, 2, 1, 3, 1, 1, 1, 3, 2, 1, 5]
def baseStart_5695218 : Nat := 118140960795 + 5695218 * 2 ^ 59
def prefixEnd_5695218 : Nat := 4983230072969 + 3 ^ 40 * 5695218 * 2
def baseEnd_5695218 : Nat := 2924384266138003667083175

theorem tailTrace_5695218 : CollatzResearch.WordTrace tailWord_5695218 prefixEnd_5695218 2924384266138003667083175 := by
  unfold tailWord_5695218
  simp only [CollatzResearch.WordTrace]
  refine ⟨51930416370301331660407577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138481110320803551094420205 51930416370301331660407577)
  ·
    refine ⟨38947812277725998745305683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51930416370301331660407577 38947812277725998745305683)
    ·
      refine ⟨58421718416588998117958525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38947812277725998745305683 58421718416588998117958525)
      ·
        refine ⟨21908144406220874294234447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58421718416588998117958525 21908144406220874294234447)
        ·
          refine ⟨32862216609331311441351671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21908144406220874294234447 32862216609331311441351671)
          ·
            refine ⟨49293324913996967162027507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32862216609331311441351671 49293324913996967162027507)
            ·
              refine ⟨73939987370995450743041261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49293324913996967162027507 73939987370995450743041261)
              ·
                refine ⟨27727495264123294028640473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73939987370995450743041261 27727495264123294028640473)
                ·
                  refine ⟨20795621448092470521480355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27727495264123294028640473 20795621448092470521480355)
                  ·
                    refine ⟨31193432172138705782220533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20795621448092470521480355 31193432172138705782220533)
                    ·
                      refine ⟨2924384266138003667083175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31193432172138705782220533 2924384266138003667083175)
                      ·
                        rfl

theorem cell23_5695218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_5695218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695218 prefixEnd_5695218 := by exact prefixLift 5695218
  have htrace : WordTrace (prefixWord ++ tailWord_5695218) baseStart_5695218 baseEnd_5695218 := by
    simpa [prefixWord, tailWord_5695218, baseEnd_5695218] using wordTrace_append hprefix tailTrace_5695218
  have hstable : (prefixWord ++ tailWord_5695218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695218).length < 2 ^ (prefixWord ++ tailWord_5695218).sum := by decide
  have hdescent : baseEnd_5695218 < baseStart_5695218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695228 : List Nat := [2, 2, 2, 1, 3, 1, 2, 2, 2, 2, 4]
def baseStart_5695228 : Nat := 118140960795 + 5695228 * 2 ^ 59
def prefixEnd_5695228 : Nat := 4983230072969 + 3 ^ 40 * 5695228 * 2
def baseEnd_5695228 : Nat := 2924389400944548627958129

theorem tailTrace_5695228 : CollatzResearch.WordTrace tailWord_5695228 prefixEnd_5695228 2924389400944548627958129 := by
  unfold tailWord_5695228
  simp only [CollatzResearch.WordTrace]
  refine ⟨103861015105584549174747169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138481353474112732232996225 103861015105584549174747169)
  ·
    refine ⟨77895761329188411881060377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103861015105584549174747169 77895761329188411881060377)
    ·
      refine ⟨58421820996891308910795283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77895761329188411881060377 58421820996891308910795283)
      ·
        refine ⟨87632731495336963366192925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58421820996891308910795283 87632731495336963366192925)
        ·
          refine ⟨32862274310751361262322347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87632731495336963366192925 32862274310751361262322347)
          ·
            refine ⟨49293411466127041893483521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32862274310751361262322347 49293411466127041893483521)
            ·
              refine ⟨36970058599595281420112641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49293411466127041893483521 36970058599595281420112641)
              ·
                refine ⟨27727543949696461065084481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36970058599595281420112641 27727543949696461065084481)
                ·
                  refine ⟨20795657962272345798813361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27727543949696461065084481 20795657962272345798813361)
                  ·
                    refine ⟨15596743471704259349110021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20795657962272345798813361 15596743471704259349110021)
                    ·
                      refine ⟨2924389400944548627958129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15596743471704259349110021 2924389400944548627958129)
                      ·
                        rfl

theorem cell23_5695228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_5695228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695228 prefixEnd_5695228 := by exact prefixLift 5695228
  have htrace : WordTrace (prefixWord ++ tailWord_5695228) baseStart_5695228 baseEnd_5695228 := by
    simpa [prefixWord, tailWord_5695228, baseEnd_5695228] using wordTrace_append hprefix tailTrace_5695228
  have hstable : (prefixWord ++ tailWord_5695228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695228).length < 2 ^ (prefixWord ++ tailWord_5695228).sum := by decide
  have hdescent : baseEnd_5695228 < baseStart_5695228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695231 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 7]
def baseStart_5695231 : Nat := 118140960795 + 5695231 * 2 ^ 59
def prefixEnd_5695231 : Nat := 4983230072969 + 3 ^ 40 * 5695231 * 2
def baseEnd_5695231 : Nat := 2924390941386512116220615

theorem tailTrace_5695231 : CollatzResearch.WordTrace tailWord_5695231 prefixEnd_5695231 2924390941386512116220615 := by
  unfold tailWord_5695231
  simp only [CollatzResearch.WordTrace]
  refine ⟨207722139630158229861853547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138481426420105486574569031 207722139630158229861853547)
  ·
    refine ⟨311583209445237344792780321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207722139630158229861853547 311583209445237344792780321)
    ·
      refine ⟨233687407083928008594585241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311583209445237344792780321 233687407083928008594585241)
      ·
        refine ⟨175265555312946006445938931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233687407083928008594585241 175265555312946006445938931)
        ·
          refine ⟨262898332969419009668908397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175265555312946006445938931 262898332969419009668908397)
          ·
            refine ⟨98586874863532128625840649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 262898332969419009668908397 98586874863532128625840649)
            ·
              refine ⟨73940156147649096469380487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98586874863532128625840649 73940156147649096469380487)
              ·
                refine ⟨110910234221473644704070731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73940156147649096469380487 110910234221473644704070731)
                ·
                  refine ⟨166365351332210467056106097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110910234221473644704070731 166365351332210467056106097)
                  ·
                    refine ⟨124774013499157850292079573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 166365351332210467056106097 124774013499157850292079573)
                    ·
                      refine ⟨2924390941386512116220615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124774013499157850292079573 2924390941386512116220615)
                      ·
                        rfl

theorem cell23_5695231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_5695231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695231 prefixEnd_5695231 := by exact prefixLift 5695231
  have htrace : WordTrace (prefixWord ++ tailWord_5695231) baseStart_5695231 baseEnd_5695231 := by
    simpa [prefixWord, tailWord_5695231, baseEnd_5695231] using wordTrace_append hprefix tailTrace_5695231
  have hstable : (prefixWord ++ tailWord_5695231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695231).length < 2 ^ (prefixWord ++ tailWord_5695231).sum := by decide
  have hdescent : baseEnd_5695231 < baseStart_5695231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695241 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 8]
def baseStart_5695241 : Nat := 118140960795 + 5695241 * 2 ^ 59
def prefixEnd_5695241 : Nat := 4983230072969 + 3 ^ 40 * 5695241 * 2
def baseEnd_5695241 : Nat := 2924396076193057077095569

theorem tailTrace_5695241 : CollatzResearch.WordTrace tailWord_5695241 prefixEnd_5695241 2924396076193057077095569 := by
  unfold tailWord_5695241
  simp only [CollatzResearch.WordTrace]
  refine ⟨207722504360122001569717577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138481669573414667713145051 207722504360122001569717577)
  ·
    refine ⟨155791878270091501177288183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207722504360122001569717577 155791878270091501177288183)
    ·
      refine ⟨233687817405137251765932275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155791878270091501177288183 233687817405137251765932275)
      ·
        refine ⟨350531726107705877648898413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233687817405137251765932275 350531726107705877648898413)
        ·
          refine ⟨131449397290389704118336905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 350531726107705877648898413 131449397290389704118336905)
          ·
            refine ⟨98587047967792278088752679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131449397290389704118336905 98587047967792278088752679)
            ·
              refine ⟨147880571951688417133129019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98587047967792278088752679 147880571951688417133129019)
              ·
                refine ⟨221820857927532625699693529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147880571951688417133129019 221820857927532625699693529)
                ·
                  refine ⟨166365643445649469274770147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221820857927532625699693529 166365643445649469274770147)
                  ·
                    refine ⟨249548465168474203912155221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 166365643445649469274770147 249548465168474203912155221)
                    ·
                      refine ⟨2924396076193057077095569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 249548465168474203912155221 2924396076193057077095569)
                      ·
                        rfl

theorem cell23_5695241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 1, 8].length) (baseStart_5695241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695241 prefixEnd_5695241 := by exact prefixLift 5695241
  have htrace : WordTrace (prefixWord ++ tailWord_5695241) baseStart_5695241 baseEnd_5695241 := by
    simpa [prefixWord, tailWord_5695241, baseEnd_5695241] using wordTrace_append hprefix tailTrace_5695241
  have hstable : (prefixWord ++ tailWord_5695241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695241).length < 2 ^ (prefixWord ++ tailWord_5695241).sum := by decide
  have hdescent : baseEnd_5695241 < baseStart_5695241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695272 : List Nat := [2, 1, 5, 1, 1, 3, 2, 3, 5]
def baseStart_5695272 : Nat := 118140960795 + 5695272 * 2 ^ 59
def prefixEnd_5695272 : Nat := 4983230072969 + 3 ^ 40 * 5695272 * 2
def baseEnd_5695272 : Nat := 324934666010371828423103

theorem tailTrace_5695272 : CollatzResearch.WordTrace tailWord_5695272 prefixEnd_5695272 324934666010371828423103 := by
  unfold tailWord_5695272
  simp only [CollatzResearch.WordTrace]
  refine ⟨103861817511504846932048035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138482423348673129242730713 103861817511504846932048035)
  ·
    refine ⟨155792726267257270398072053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103861817511504846932048035 155792726267257270398072053)
    ·
      refine ⟨14605568087555369099819255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 155792726267257270398072053 14605568087555369099819255)
      ·
        refine ⟨21908352131333053649728883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14605568087555369099819255 21908352131333053649728883)
        ·
          refine ⟨32862528196999580474593325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21908352131333053649728883 32862528196999580474593325)
          ·
            refine ⟨12323448073874842677972497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32862528196999580474593325 12323448073874842677972497)
            ·
              refine ⟨9242586055406132008479373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12323448073874842677972497 9242586055406132008479373)
              ·
                refine ⟨3465969770777299503179765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9242586055406132008479373 3465969770777299503179765)
                ·
                  refine ⟨324934666010371828423103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3465969770777299503179765 324934666010371828423103)
                  ·
                    rfl

theorem cell23_5695272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3, 5].length) (baseStart_5695272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695272 prefixEnd_5695272 := by exact prefixLift 5695272
  have htrace : WordTrace (prefixWord ++ tailWord_5695272) baseStart_5695272 baseEnd_5695272 := by
    simpa [prefixWord, tailWord_5695272, baseEnd_5695272] using wordTrace_append hprefix tailTrace_5695272
  have hstable : (prefixWord ++ tailWord_5695272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695272).length < 2 ^ (prefixWord ++ tailWord_5695272).sum := by decide
  have hdescent : baseEnd_5695272 < baseStart_5695272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695302 : List Nat := [6, 1, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_5695302 : Nat := 118140960795 + 5695302 * 2 ^ 59
def prefixEnd_5695302 : Nat := 4983230072969 + 3 ^ 40 * 5695302 * 2
def baseEnd_5695302 : Nat := 974809132837660446144263

theorem tailTrace_5695302 : CollatzResearch.WordTrace tailWord_5695302 prefixEnd_5695302 974809132837660446144263 := by
  unfold tailWord_5695302
  simp only [CollatzResearch.WordTrace]
  refine ⟨6491397787903156530865255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 138483152808600672658458773 6491397787903156530865255)
  ·
    refine ⟨9737096681854734796297883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6491397787903156530865255 9737096681854734796297883)
    ·
      refine ⟨14605645022782102194446825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9737096681854734796297883 14605645022782102194446825)
      ·
        refine ⟨10954233767086576645835119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14605645022782102194446825 10954233767086576645835119)
        ·
          refine ⟨16431350650629864968752679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10954233767086576645835119 16431350650629864968752679)
          ·
            refine ⟨24647025975944797453129019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16431350650629864968752679 24647025975944797453129019)
            ·
              refine ⟨36970538963917196179693529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24647025975944797453129019 36970538963917196179693529)
              ·
                refine ⟨27727904222937897134770147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36970538963917196179693529 27727904222937897134770147)
                ·
                  refine ⟨41591856334406845702155221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27727904222937897134770147 41591856334406845702155221)
                  ·
                    refine ⟨974809132837660446144263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41591856334406845702155221 974809132837660446144263)
                    ·
                      rfl

theorem cell23_5695302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_5695302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695302 prefixEnd_5695302 := by exact prefixLift 5695302
  have htrace : WordTrace (prefixWord ++ tailWord_5695302) baseStart_5695302 baseEnd_5695302 := by
    simpa [prefixWord, tailWord_5695302, baseEnd_5695302] using wordTrace_append hprefix tailTrace_5695302
  have hstable : (prefixWord ++ tailWord_5695302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695302).length < 2 ^ (prefixWord ++ tailWord_5695302).sum := by decide
  have hdescent : baseEnd_5695302 < baseStart_5695302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695305 : List Nat := [1, 2, 1, 1, 2, 4, 1, 3, 2, 4, 2]
def baseStart_5695305 : Nat := 118140960795 + 5695305 * 2 ^ 59
def prefixEnd_5695305 : Nat := 4983230072969 + 3 ^ 40 * 5695305 * 2
def baseEnd_5695305 : Nat := 2924428938954944826695275

theorem tailTrace_5695305 : CollatzResearch.WordTrace tailWord_5695305 prefixEnd_5695305 2924428938954944826695275 := by
  unfold tailWord_5695305
  simp only [CollatzResearch.WordTrace]
  refine ⟨207724838631890140500047369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138483225754593427000031579 207724838631890140500047369)
  ·
    refine ⟨155793628973917605375035527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207724838631890140500047369 155793628973917605375035527)
    ·
      refine ⟨233690443460876408062553291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155793628973917605375035527 233690443460876408062553291)
      ·
        refine ⟨350535665191314612093829937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233690443460876408062553291 350535665191314612093829937)
        ·
          refine ⟨262901748893485959070372453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350535665191314612093829937 262901748893485959070372453)
          ·
            refine ⟨49294077917528617325694835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 262901748893485959070372453 49294077917528617325694835)
            ·
              refine ⟨73941116876292925988542253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49294077917528617325694835 73941116876292925988542253)
              ·
                refine ⟨27727918828609847245703345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73941116876292925988542253 27727918828609847245703345)
                ·
                  refine ⟨20795939121457385434277509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27727918828609847245703345 20795939121457385434277509)
                  ·
                    refine ⟨3899238585273259768927033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20795939121457385434277509 3899238585273259768927033)
                    ·
                      refine ⟨2924428938954944826695275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3899238585273259768927033 2924428938954944826695275)
                      ·
                        rfl

theorem cell23_5695305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 4, 2].length) (baseStart_5695305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695305 prefixEnd_5695305 := by exact prefixLift 5695305
  have htrace : WordTrace (prefixWord ++ tailWord_5695305) baseStart_5695305 baseEnd_5695305 := by
    simpa [prefixWord, tailWord_5695305, baseEnd_5695305] using wordTrace_append hprefix tailTrace_5695305
  have hstable : (prefixWord ++ tailWord_5695305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695305).length < 2 ^ (prefixWord ++ tailWord_5695305).sum := by decide
  have hdescent : baseEnd_5695305 < baseStart_5695305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695328 : List Nat := [2, 1, 1, 3, 3, 2, 1, 2, 8]
def baseStart_5695328 : Nat := 118140960795 + 5695328 * 2 ^ 59
def prefixEnd_5695328 : Nat := 4983230072969 + 3 ^ 40 * 5695328 * 2
def baseEnd_5695328 : Nat := 324937861001110915189741

theorem tailTrace_5695328 : CollatzResearch.WordTrace tailWord_5695328 prefixEnd_5695328 324937861001110915189741 := by
  unfold tailWord_5695328
  simp only [CollatzResearch.WordTrace]
  refine ⟨103862838755403407714067319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138483785007204543618756425 103862838755403407714067319)
  ·
    refine ⟨155794258133105111571100979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103862838755403407714067319 155794258133105111571100979)
    ·
      refine ⟨233691387199657667356651469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155794258133105111571100979 233691387199657667356651469)
      ·
        refine ⟨87634270199871625258744301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233691387199657667356651469 87634270199871625258744301)
        ·
          refine ⟨32862851324951859472029113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87634270199871625258744301 32862851324951859472029113)
          ·
            refine ⟨24647138493713894604021835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32862851324951859472029113 24647138493713894604021835)
            ·
              refine ⟨36970707740570841906032753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24647138493713894604021835 36970707740570841906032753)
              ·
                refine ⟨27728030805428131429524565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36970707740570841906032753 27728030805428131429524565)
                ·
                  refine ⟨324937861001110915189741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27728030805428131429524565 324937861001110915189741)
                  ·
                    rfl

theorem cell23_5695328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 8].length) (baseStart_5695328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695328 prefixEnd_5695328 := by exact prefixLift 5695328
  have htrace : WordTrace (prefixWord ++ tailWord_5695328) baseStart_5695328 baseEnd_5695328 := by
    simpa [prefixWord, tailWord_5695328, baseEnd_5695328] using wordTrace_append hprefix tailTrace_5695328
  have hstable : (prefixWord ++ tailWord_5695328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695328).length < 2 ^ (prefixWord ++ tailWord_5695328).sum := by decide
  have hdescent : baseEnd_5695328 < baseStart_5695328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695342 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 4, 2, 3]
def baseStart_5695342 : Nat := 118140960795 + 5695342 * 2 ^ 59
def prefixEnd_5695342 : Nat := 4983230072969 + 3 ^ 40 * 5695342 * 2
def baseEnd_5695342 : Nat := 2924447937739161181932605

theorem tailTrace_5695342 : CollatzResearch.WordTrace tailWord_5695342 prefixEnd_5695342 2924447937739161181932605 := by
  unfold tailWord_5695342
  simp only [CollatzResearch.WordTrace]
  refine ⟨25965773516594511977393035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138484125421837397212762853 25965773516594511977393035)
  ·
    refine ⟨38948660274891767966089553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25965773516594511977393035 38948660274891767966089553)
    ·
      refine ⟨29211495206168825974567165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38948660274891767966089553 29211495206168825974567165)
      ·
        refine ⟨10954310702313309740462687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29211495206168825974567165 10954310702313309740462687)
        ·
          refine ⟨16431466053469964610694031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10954310702313309740462687 16431466053469964610694031)
          ·
            refine ⟨24647199080204946916041047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16431466053469964610694031 24647199080204946916041047)
            ·
              refine ⟨36970798620307420374061571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24647199080204946916041047 36970798620307420374061571)
              ·
                refine ⟨55456197930461130561092357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36970798620307420374061571 55456197930461130561092357)
                ·
                  refine ⟨10398037111961461980204817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55456197930461130561092357 10398037111961461980204817)
                  ·
                    refine ⟨7798527833971096485153613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10398037111961461980204817 7798527833971096485153613)
                    ·
                      refine ⟨2924447937739161181932605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7798527833971096485153613 2924447937739161181932605)
                      ·
                        rfl

theorem cell23_5695342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_5695342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695342 prefixEnd_5695342 := by exact prefixLift 5695342
  have htrace : WordTrace (prefixWord ++ tailWord_5695342) baseStart_5695342 baseEnd_5695342 := by
    simpa [prefixWord, tailWord_5695342, baseEnd_5695342] using wordTrace_append hprefix tailTrace_5695342
  have hstable : (prefixWord ++ tailWord_5695342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695342).length < 2 ^ (prefixWord ++ tailWord_5695342).sum := by decide
  have hdescent : baseEnd_5695342 < baseStart_5695342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695399 : List Nat := [1, 1, 6, 1, 2, 1, 2, 2, 2, 3, 2]
def baseStart_5695399 : Nat := 118140960795 + 5695399 * 2 ^ 59
def prefixEnd_5695399 : Nat := 4983230072969 + 3 ^ 40 * 5695399 * 2
def baseEnd_5695399 : Nat := 2924477206136467458919843

theorem tailTrace_5695399 : CollatzResearch.WordTrace tailWord_5695399 prefixEnd_5695399 2924477206136467458919843 := by
  unfold tailWord_5695399
  simp only [CollatzResearch.WordTrace]
  refine ⟨207728267093549594553969251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138485511395699729702646167 207728267093549594553969251)
  ·
    refine ⟨311592400640324391830953877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207728267093549594553969251 311592400640324391830953877)
    ·
      refine ⟨14605893780015205867075963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 311592400640324391830953877 14605893780015205867075963)
      ·
        refine ⟨21908840670022808800613945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14605893780015205867075963 21908840670022808800613945)
        ·
          refine ⟨16431630502517106600460459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21908840670022808800613945 16431630502517106600460459)
          ·
            refine ⟨24647445753775659900690689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16431630502517106600460459 24647445753775659900690689)
            ·
              refine ⟨18485584315331744925518017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24647445753775659900690689 18485584315331744925518017)
              ·
                refine ⟨13864188236498808694138513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18485584315331744925518017 13864188236498808694138513)
                ·
                  refine ⟨10398141177374106520603885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13864188236498808694138513 10398141177374106520603885)
                  ·
                    refine ⟨3899302941515289945226457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10398141177374106520603885 3899302941515289945226457)
                    ·
                      refine ⟨2924477206136467458919843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3899302941515289945226457 2924477206136467458919843)
                      ·
                        rfl

theorem cell23_5695399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_5695399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695399 prefixEnd_5695399 := by exact prefixLift 5695399
  have htrace : WordTrace (prefixWord ++ tailWord_5695399) baseStart_5695399 baseEnd_5695399 := by
    simpa [prefixWord, tailWord_5695399, baseEnd_5695399] using wordTrace_append hprefix tailTrace_5695399
  have hstable : (prefixWord ++ tailWord_5695399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695399).length < 2 ^ (prefixWord ++ tailWord_5695399).sum := by decide
  have hdescent : baseEnd_5695399 < baseStart_5695399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695400 : List Nat := [2, 1, 6, 2, 1, 2, 2, 2, 1, 4]
def baseStart_5695400 : Nat := 118140960795 + 5695400 * 2 ^ 59
def prefixEnd_5695400 : Nat := 4983230072969 + 3 ^ 40 * 5695400 * 2
def baseEnd_5695400 : Nat := 974825906539040651669113

theorem tailTrace_5695400 : CollatzResearch.WordTrace tailWord_5695400 prefixEnd_5695400 974825906539040651669113 := by
  unfold tailWord_5695400
  simp only [CollatzResearch.WordTrace]
  refine ⟨103864151783272985862377827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138485535711030647816503769 103864151783272985862377827)
  ·
    refine ⟨155796227674909478793566741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103864151783272985862377827 155796227674909478793566741)
    ·
      refine ⟨7302948172261381818448441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 155796227674909478793566741 7302948172261381818448441)
      ·
        refine ⟨5477211129196036363836331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7302948172261381818448441 5477211129196036363836331)
        ·
          refine ⟨8215816693794054545754497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5477211129196036363836331 8215816693794054545754497)
          ·
            refine ⟨6161862520345540909315873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8215816693794054545754497 6161862520345540909315873)
            ·
              refine ⟨4621396890259155681986905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6161862520345540909315873 4621396890259155681986905)
              ·
                refine ⟨3466047667694366761490179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4621396890259155681986905 3466047667694366761490179)
                ·
                  refine ⟨5199071501541550142235269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3466047667694366761490179 5199071501541550142235269)
                  ·
                    refine ⟨974825906539040651669113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5199071501541550142235269 974825906539040651669113)
                    ·
                      rfl

theorem cell23_5695400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_5695400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695400 prefixEnd_5695400 := by exact prefixLift 5695400
  have htrace : WordTrace (prefixWord ++ tailWord_5695400) baseStart_5695400 baseEnd_5695400 := by
    simpa [prefixWord, tailWord_5695400, baseEnd_5695400] using wordTrace_append hprefix tailTrace_5695400
  have hstable : (prefixWord ++ tailWord_5695400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695400).length < 2 ^ (prefixWord ++ tailWord_5695400).sum := by decide
  have hdescent : baseEnd_5695400 < baseStart_5695400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695418 : List Nat := [3, 1, 1, 1, 2, 1, 2, 12]
def baseStart_5695418 : Nat := 118140960795 + 5695418 * 2 ^ 59
def prefixEnd_5695418 : Nat := 4983230072969 + 3 ^ 40 * 5695418 * 2
def baseEnd_5695418 : Nat := 108314331935885292021565

theorem tailTrace_5695418 : CollatzResearch.WordTrace tailWord_5695418 prefixEnd_5695418 108314331935885292021565 := by
  unfold tailWord_5695418
  simp only [CollatzResearch.WordTrace]
  refine ⟨51932240020120190199727727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138485973386987173865940605 51932240020120190199727727)
  ·
    refine ⟨77898360030180285299591591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51932240020120190199727727 77898360030180285299591591)
    ·
      refine ⟨116847540045270427949387387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77898360030180285299591591 116847540045270427949387387)
      ·
        refine ⟨175271310067905641924081081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116847540045270427949387387 175271310067905641924081081)
        ·
          refine ⟨131453482550929231443060811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175271310067905641924081081 131453482550929231443060811)
          ·
            refine ⟨197180223826393847164591217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131453482550929231443060811 197180223826393847164591217)
            ·
              refine ⟨147885167869795385373443413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197180223826393847164591217 147885167869795385373443413)
              ·
                refine ⟨108314331935885292021565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 147885167869795385373443413 108314331935885292021565)
                ·
                  rfl

theorem cell23_5695418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 12].length) (baseStart_5695418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695418 prefixEnd_5695418 := by exact prefixLift 5695418
  have htrace : WordTrace (prefixWord ++ tailWord_5695418) baseStart_5695418 baseEnd_5695418 := by
    simpa [prefixWord, tailWord_5695418, baseEnd_5695418] using wordTrace_append hprefix tailTrace_5695418
  have hstable : (prefixWord ++ tailWord_5695418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695418).length < 2 ^ (prefixWord ++ tailWord_5695418).sum := by decide
  have hdescent : baseEnd_5695418 < baseStart_5695418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695422 : List Nat := [4, 2, 1, 1, 1, 4, 2, 1, 1, 6]
def baseStart_5695422 : Nat := 118140960795 + 5695422 * 2 ^ 59
def prefixEnd_5695422 : Nat := 4983230072969 + 3 ^ 40 * 5695422 * 2
def baseEnd_5695422 : Nat := 974829672063840289644079

theorem tailTrace_5695422 : CollatzResearch.WordTrace tailWord_5695422 prefixEnd_5695422 974829672063840289644079 := by
  unfold tailWord_5695422
  simp only [CollatzResearch.WordTrace]
  refine ⟨25966138246558283685257065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138486070648310846321371013 25966138246558283685257065)
  ·
    refine ⟨19474603684918712763942799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25966138246558283685257065 19474603684918712763942799)
    ·
      refine ⟨29211905527378069145914199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19474603684918712763942799 29211905527378069145914199)
      ·
        refine ⟨43817858291067103718871299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29211905527378069145914199 43817858291067103718871299)
        ·
          refine ⟨65726787436600655578306949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43817858291067103718871299 65726787436600655578306949)
          ·
            refine ⟨12323772644362622920932553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65726787436600655578306949 12323772644362622920932553)
            ·
              refine ⟨9242829483271967190699415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12323772644362622920932553 9242829483271967190699415)
              ·
                refine ⟨13864244224907950786049123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9242829483271967190699415 13864244224907950786049123)
                ·
                  refine ⟨20796366337361926179073685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13864244224907950786049123 20796366337361926179073685)
                  ·
                    refine ⟨974829672063840289644079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20796366337361926179073685 974829672063840289644079)
                    ·
                      rfl

theorem cell23_5695422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_5695422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695422 prefixEnd_5695422 := by exact prefixLift 5695422
  have htrace : WordTrace (prefixWord ++ tailWord_5695422) baseStart_5695422 baseEnd_5695422 := by
    simpa [prefixWord, tailWord_5695422, baseEnd_5695422] using wordTrace_append hprefix tailTrace_5695422
  have hstable : (prefixWord ++ tailWord_5695422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695422).length < 2 ^ (prefixWord ++ tailWord_5695422).sum := by decide
  have hdescent : baseEnd_5695422 < baseStart_5695422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695432 : List Nat := [2, 1, 3, 1, 4, 1, 2, 1, 3, 2, 3]
def baseStart_5695432 : Nat := 118140960795 + 5695432 * 2 ^ 59
def prefixEnd_5695432 : Nat := 4983230072969 + 3 ^ 40 * 5695432 * 2
def baseEnd_5695432 : Nat := 2924494150998065829807191

theorem tailTrace_5695432 : CollatzResearch.WordTrace tailWord_5695432 prefixEnd_5695432 2924494150998065829807191 := by
  unfold tailWord_5695432
  simp only [CollatzResearch.WordTrace]
  refine ⟨103864735351215020594960275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138486313801620027459947033 103864735351215020594960275)
  ·
    refine ⟨155797103026822530892440413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103864735351215020594960275 155797103026822530892440413)
    ·
      refine ⟨58423913635058449084665155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155797103026822530892440413 58423913635058449084665155)
      ·
        refine ⟨87635870452587673626997733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58423913635058449084665155 87635870452587673626997733)
        ·
          refine ⟨16431725709860188805062075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87635870452587673626997733 16431725709860188805062075)
          ·
            refine ⟨24647588564790283207593113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16431725709860188805062075 24647588564790283207593113)
            ·
              refine ⟨18485691423592712405694835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24647588564790283207593113 18485691423592712405694835)
              ·
                refine ⟨27728537135389068608542253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18485691423592712405694835 27728537135389068608542253)
                ·
                  refine ⟨10398201425770900728203345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27728537135389068608542253 10398201425770900728203345)
                  ·
                    refine ⟨7798651069328175546152509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10398201425770900728203345 7798651069328175546152509)
                    ·
                      refine ⟨2924494150998065829807191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7798651069328175546152509 2924494150998065829807191)
                      ·
                        rfl

theorem cell23_5695432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_5695432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695432 prefixEnd_5695432 := by exact prefixLift 5695432
  have htrace : WordTrace (prefixWord ++ tailWord_5695432) baseStart_5695432 baseEnd_5695432 := by
    simpa [prefixWord, tailWord_5695432, baseEnd_5695432] using wordTrace_append hprefix tailTrace_5695432
  have hstable : (prefixWord ++ tailWord_5695432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695432).length < 2 ^ (prefixWord ++ tailWord_5695432).sum := by decide
  have hdescent : baseEnd_5695432 < baseStart_5695432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695435 : List Nat := [1, 1, 1, 1, 3, 4, 5, 7]
def baseStart_5695435 : Nat := 118140960795 + 5695435 * 2 ^ 59
def prefixEnd_5695435 : Nat := 4983230072969 + 3 ^ 40 * 5695435 * 2
def baseEnd_5695435 : Nat := 108314655238519604372951

theorem tailTrace_5695435 : CollatzResearch.WordTrace tailWord_5695435 prefixEnd_5695435 108314655238519604372951 := by
  unfold tailWord_5695435
  simp only [CollatzResearch.WordTrace]
  refine ⟨207729580121419172702279759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138486386747612781801519839 207729580121419172702279759)
  ·
    refine ⟨311594370182128759053419639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207729580121419172702279759 311594370182128759053419639)
    ·
      refine ⟨467391555273193138580129459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311594370182128759053419639 467391555273193138580129459)
      ·
        refine ⟨701087332909789707870194189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467391555273193138580129459 701087332909789707870194189)
        ·
          refine ⟨262907749841171140451322821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 701087332909789707870194189 262907749841171140451322821)
          ·
            refine ⟨49295203095219588834623029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 262907749841171140451322821 49295203095219588834623029)
            ·
              refine ⟨4621425290176836453245909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49295203095219588834623029 4621425290176836453245909)
              ·
                refine ⟨108314655238519604372951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4621425290176836453245909 108314655238519604372951)
                ·
                  rfl

theorem cell23_5695435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 7].length) (baseStart_5695435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695435 prefixEnd_5695435 := by exact prefixLift 5695435
  have htrace : WordTrace (prefixWord ++ tailWord_5695435) baseStart_5695435 baseEnd_5695435 := by
    simpa [prefixWord, tailWord_5695435, baseEnd_5695435] using wordTrace_append hprefix tailTrace_5695435
  have hstable : (prefixWord ++ tailWord_5695435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695435).length < 2 ^ (prefixWord ++ tailWord_5695435).sum := by decide
  have hdescent : baseEnd_5695435 < baseStart_5695435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695446 : List Nat := [5, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_5695446 : Nat := 118140960795 + 5695446 * 2 ^ 59
def prefixEnd_5695446 : Nat := 4983230072969 + 3 ^ 40 * 5695446 * 2
def baseEnd_5695446 : Nat := 2924501339727228775032127

theorem tailTrace_5695446 : CollatzResearch.WordTrace tailWord_5695446 prefixEnd_5695446 2924501339727228775032127 := by
  unfold tailWord_5695446
  simp only [CollatzResearch.WordTrace]
  refine ⟨12983123832773707598808137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138486654216252881053953461 12983123832773707598808137)
  ·
    refine ⟨9737342874580280699106103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12983123832773707598808137 9737342874580280699106103)
    ·
      refine ⟨14606014311870421048659155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9737342874580280699106103 14606014311870421048659155)
      ·
        refine ⟨21909021467805631572988733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14606014311870421048659155 21909021467805631572988733)
        ·
          refine ⟨8215883050427111839870775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21909021467805631572988733 8215883050427111839870775)
          ·
            refine ⟨12323824575640667759806163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8215883050427111839870775 12323824575640667759806163)
            ·
              refine ⟨18485736863461001639709245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12323824575640667759806163 18485736863461001639709245)
              ·
                refine ⟨6932151323797875614890967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18485736863461001639709245 6932151323797875614890967)
                ·
                  refine ⟨10398226985696813422336451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6932151323797875614890967 10398226985696813422336451)
                  ·
                    refine ⟨15597340478545220133504677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10398226985696813422336451 15597340478545220133504677)
                    ·
                      refine ⟨2924501339727228775032127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15597340478545220133504677 2924501339727228775032127)
                      ·
                        rfl

theorem cell23_5695446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_5695446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695446 prefixEnd_5695446 := by exact prefixLift 5695446
  have htrace : WordTrace (prefixWord ++ tailWord_5695446) baseStart_5695446 baseEnd_5695446 := by
    simpa [prefixWord, tailWord_5695446, baseEnd_5695446] using wordTrace_append hprefix tailTrace_5695446
  have hstable : (prefixWord ++ tailWord_5695446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695446).length < 2 ^ (prefixWord ++ tailWord_5695446).sum := by decide
  have hdescent : baseEnd_5695446 < baseStart_5695446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695449 : List Nat := [1, 2, 1, 2, 6, 1, 1, 3, 1, 2, 3]
def baseStart_5695449 : Nat := 118140960795 + 5695449 * 2 ^ 59
def prefixEnd_5695449 : Nat := 4983230072969 + 3 ^ 40 * 5695449 * 2
def baseEnd_5695449 : Nat := 2924502880169192263294613

theorem tailTrace_5695449 : CollatzResearch.WordTrace tailWord_5695449 prefixEnd_5695449 2924502880169192263294613 := by
  unfold tailWord_5695449
  simp only [CollatzResearch.WordTrace]
  refine ⟨207730090743368453093289401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138486727162245635395526267 207730090743368453093289401)
  ·
    refine ⟨155797568057526339819967051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207730090743368453093289401 155797568057526339819967051)
    ·
      refine ⟨233696352086289509729950577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155797568057526339819967051 233696352086289509729950577)
      ·
        refine ⟨175272264064717132297462933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233696352086289509729950577 175272264064717132297462933)
        ·
          refine ⟨8215887378033615576443575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 175272264064717132297462933 8215887378033615576443575)
          ·
            refine ⟨12323831067050423364665363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8215887378033615576443575 12323831067050423364665363)
            ·
              refine ⟨18485746600575635046998045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12323831067050423364665363 18485746600575635046998045)
              ·
                refine ⟨6932154975215863142624267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18485746600575635046998045 6932154975215863142624267)
                ·
                  refine ⟨10398232462823794713936401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6932154975215863142624267 10398232462823794713936401)
                  ·
                    refine ⟨7798674347117846035452301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10398232462823794713936401 7798674347117846035452301)
                    ·
                      refine ⟨2924502880169192263294613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7798674347117846035452301 2924502880169192263294613)
                      ·
                        rfl

theorem cell23_5695449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 2, 3].length) (baseStart_5695449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695449 prefixEnd_5695449 := by exact prefixLift 5695449
  have htrace : WordTrace (prefixWord ++ tailWord_5695449) baseStart_5695449 baseEnd_5695449 := by
    simpa [prefixWord, tailWord_5695449, baseEnd_5695449] using wordTrace_append hprefix tailTrace_5695449
  have hstable : (prefixWord ++ tailWord_5695449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695449).length < 2 ^ (prefixWord ++ tailWord_5695449).sum := by decide
  have hdescent : baseEnd_5695449 < baseStart_5695449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695472 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 5, 3, 2]
def baseStart_5695472 : Nat := 118140960795 + 5695472 * 2 ^ 59
def prefixEnd_5695472 : Nat := 4983230072969 + 3 ^ 40 * 5695472 * 2
def baseEnd_5695472 : Nat := 2924514690224245673307007

theorem tailTrace_5695472 : CollatzResearch.WordTrace tailWord_5695472 prefixEnd_5695472 2924514690224245673307007 := by
  unfold tailWord_5695472
  simp only [CollatzResearch.WordTrace]
  refine ⟨103865464811142564010688335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138487286414856752014251113 103865464811142564010688335)
  ·
    refine ⟨155798197216713846016032503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103865464811142564010688335 155798197216713846016032503)
    ·
      refine ⟨233697295825070769024048755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155798197216713846016032503 233697295825070769024048755)
      ·
        refine ⟨350545943737606153536073133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233697295825070769024048755 350545943737606153536073133)
        ·
          refine ⟨131454728901602307576027425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 350545943737606153536073133 131454728901602307576027425)
          ·
            refine ⟨98591046676201730682020569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131454728901602307576027425 98591046676201730682020569)
            ·
              refine ⟨73943285007151298011515427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98591046676201730682020569 73943285007151298011515427)
              ·
                refine ⟨110914927510726947017273141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73943285007151298011515427 110914927510726947017273141)
                ·
                  refine ⟨10398274454130651282869357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110914927510726947017273141 10398274454130651282869357)
                  ·
                    refine ⟨3899352920298994231076009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10398274454130651282869357 3899352920298994231076009)
                    ·
                      refine ⟨2924514690224245673307007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3899352920298994231076009 2924514690224245673307007)
                      ·
                        rfl

theorem cell23_5695472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 5, 3, 2].length) (baseStart_5695472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695472 prefixEnd_5695472 := by exact prefixLift 5695472
  have htrace : WordTrace (prefixWord ++ tailWord_5695472) baseStart_5695472 baseEnd_5695472 := by
    simpa [prefixWord, tailWord_5695472, baseEnd_5695472] using wordTrace_append hprefix tailTrace_5695472
  have hstable : (prefixWord ++ tailWord_5695472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695472).length < 2 ^ (prefixWord ++ tailWord_5695472).sum := by decide
  have hdescent : baseEnd_5695472 < baseStart_5695472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695485 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 2, 3, 4]
def baseStart_5695485 : Nat := 118140960795 + 5695485 * 2 ^ 59
def prefixEnd_5695485 : Nat := 4983230072969 + 3 ^ 40 * 5695485 * 2
def baseEnd_5695485 : Nat := 2924521365472754122444447

theorem tailTrace_5695485 : CollatzResearch.WordTrace tailWord_5695485 prefixEnd_5695485 2924521365472754122444447 := by
  unfold tailWord_5695485
  simp only [CollatzResearch.WordTrace]
  refine ⟨207731403771238031241599909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138487602514158687494399939 207731403771238031241599909)
  ·
    refine ⟨38949638207107130857799983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207731403771238031241599909 38949638207107130857799983)
    ·
      refine ⟨58424457310660696286699975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38949638207107130857799983 58424457310660696286699975)
      ·
        refine ⟨87636685965991044430049963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58424457310660696286699975 87636685965991044430049963)
        ·
          refine ⟨131455028948986566645074945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87636685965991044430049963 131455028948986566645074945)
          ·
            refine ⟨98591271711739924983806209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131455028948986566645074945 98591271711739924983806209)
            ·
              refine ⟨73943453783804943737854657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98591271711739924983806209 73943453783804943737854657)
              ·
                refine ⟨55457590337853707803390993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73943453783804943737854657 55457590337853707803390993)
                ·
                  refine ⟨41593192753390280852543245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55457590337853707803390993 41593192753390280852543245)
                  ·
                    refine ⟨15597447282521355319703717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41593192753390280852543245 15597447282521355319703717)
                    ·
                      refine ⟨2924521365472754122444447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15597447282521355319703717 2924521365472754122444447)
                      ·
                        rfl

theorem cell23_5695485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_5695485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695485 prefixEnd_5695485 := by exact prefixLift 5695485
  have htrace : WordTrace (prefixWord ++ tailWord_5695485) baseStart_5695485 baseEnd_5695485 := by
    simpa [prefixWord, tailWord_5695485, baseEnd_5695485] using wordTrace_append hprefix tailTrace_5695485
  have hstable : (prefixWord ++ tailWord_5695485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695485).length < 2 ^ (prefixWord ++ tailWord_5695485).sum := by decide
  have hdescent : baseEnd_5695485 < baseStart_5695485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695505 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 3]
def baseStart_5695505 : Nat := 118140960795 + 5695505 * 2 ^ 59
def prefixEnd_5695505 : Nat := 4983230072969 + 3 ^ 40 * 5695505 * 2
def baseEnd_5695505 : Nat := 2924531635085844044194355

theorem tailTrace_5695505 : CollatzResearch.WordTrace tailWord_5695505 prefixEnd_5695505 2924531635085844044194355 := by
  unfold tailWord_5695505
  simp only [CollatzResearch.WordTrace]
  refine ⟨207732133231165574657327969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138488088820777049771551979 207732133231165574657327969)
  ·
    refine ⟨155799099923374180992995977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207732133231165574657327969 155799099923374180992995977)
    ·
      refine ⟨116849324942530635744746983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155799099923374180992995977 116849324942530635744746983)
      ·
        refine ⟨175273987413795953617120475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116849324942530635744746983 175273987413795953617120475)
        ·
          refine ⟨262910981120693930425680713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175273987413795953617120475 262910981120693930425680713)
          ·
            refine ⟨197183235840520447819260535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262910981120693930425680713 197183235840520447819260535)
            ·
              refine ⟨295774853760780671728890803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197183235840520447819260535 295774853760780671728890803)
              ·
                refine ⟨443662280641171007593336205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295774853760780671728890803 443662280641171007593336205)
                ·
                  refine ⟨166373355240439127847501077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 443662280641171007593336205 166373355240439127847501077)
                  ·
                    refine ⟨7798751026895584117851613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 166373355240439127847501077 7798751026895584117851613)
                    ·
                      refine ⟨2924531635085844044194355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7798751026895584117851613 2924531635085844044194355)
                      ·
                        rfl

theorem cell23_5695505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 3].length) (baseStart_5695505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695505 prefixEnd_5695505 := by exact prefixLift 5695505
  have htrace : WordTrace (prefixWord ++ tailWord_5695505) baseStart_5695505 baseEnd_5695505 := by
    simpa [prefixWord, tailWord_5695505, baseEnd_5695505] using wordTrace_append hprefix tailTrace_5695505
  have hstable : (prefixWord ++ tailWord_5695505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695505).length < 2 ^ (prefixWord ++ tailWord_5695505).sum := by decide
  have hdescent : baseEnd_5695505 < baseStart_5695505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695515 : List Nat := [1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 4]
def baseStart_5695515 : Nat := 118140960795 + 5695515 * 2 ^ 59
def prefixEnd_5695515 : Nat := 4983230072969 + 3 ^ 40 * 5695515 * 2
def baseEnd_5695515 : Nat := 2924536769892389005069309

theorem tailTrace_5695515 : CollatzResearch.WordTrace tailWord_5695515 prefixEnd_5695515 2924536769892389005069309 := by
  unfold tailWord_5695515
  simp only [CollatzResearch.WordTrace]
  refine ⟨207732497961129346365191999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138488331974086230910127999 207732497961129346365191999)
  ·
    refine ⟨311598746941694019547787999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207732497961129346365191999 311598746941694019547787999)
    ·
      refine ⟨467398120412541029321681999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311598746941694019547787999 467398120412541029321681999)
      ·
        refine ⟨701097180618811543982522999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467398120412541029321681999 701097180618811543982522999)
        ·
          refine ⟨1051645770928217315973784499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701097180618811543982522999 1051645770928217315973784499)
          ·
            refine ⟨1577468656392325973960676749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1051645770928217315973784499 1577468656392325973960676749)
            ·
              refine ⟨591550746147122240235253781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1577468656392325973960676749 591550746147122240235253781)
              ·
                refine ⟨27728941225646355011027521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 591550746147122240235253781 27728941225646355011027521)
                ·
                  refine ⟨20796705919234766258270641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27728941225646355011027521 20796705919234766258270641)
                  ·
                    refine ⟨15597529439426074693702981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20796705919234766258270641 15597529439426074693702981)
                    ·
                      refine ⟨2924536769892389005069309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15597529439426074693702981 2924536769892389005069309)
                      ·
                        rfl

theorem cell23_5695515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 2, 4].length) (baseStart_5695515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695515 prefixEnd_5695515 := by exact prefixLift 5695515
  have htrace : WordTrace (prefixWord ++ tailWord_5695515) baseStart_5695515 baseEnd_5695515 := by
    simpa [prefixWord, tailWord_5695515, baseEnd_5695515] using wordTrace_append hprefix tailTrace_5695515
  have hstable : (prefixWord ++ tailWord_5695515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695515).length < 2 ^ (prefixWord ++ tailWord_5695515).sum := by decide
  have hdescent : baseEnd_5695515 < baseStart_5695515 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695519 : List Nat := [1, 1, 2, 4, 1, 2, 1, 3, 4, 2, 2]
def baseStart_5695519 : Nat := 118140960795 + 5695519 * 2 ^ 59
def prefixEnd_5695519 : Nat := 4983230072969 + 3 ^ 40 * 5695519 * 2
def baseEnd_5695519 : Nat := 2924538823815006989419291

theorem tailTrace_5695519 : CollatzResearch.WordTrace tailWord_5695519 prefixEnd_5695519 2924538823815006989419291 := by
  unfold tailWord_5695519
  simp only [CollatzResearch.WordTrace]
  refine ⟨207732643853114855048337611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138488429235409903365558407 207732643853114855048337611)
  ·
    refine ⟨311598965779672282572506417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207732643853114855048337611 311598965779672282572506417)
    ·
      refine ⟨233699224334754211929379813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311598965779672282572506417 233699224334754211929379813)
      ·
        refine ⟨43818604562766414736758715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233699224334754211929379813 43818604562766414736758715)
        ·
          refine ⟨65727906844149622105138073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43818604562766414736758715 65727906844149622105138073)
          ·
            refine ⟨49295930133112216578853555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65727906844149622105138073 49295930133112216578853555)
            ·
              refine ⟨73943895199668324868280333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49295930133112216578853555 73943895199668324868280333)
              ·
                refine ⟨27728960699875621825605125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73943895199668324868280333 27728960699875621825605125)
                ·
                  refine ⟨5199180131226679092300961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27728960699875621825605125 5199180131226679092300961)
                  ·
                    refine ⟨3899385098420009319225721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5199180131226679092300961 3899385098420009319225721)
                    ·
                      refine ⟨2924538823815006989419291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3899385098420009319225721 2924538823815006989419291)
                      ·
                        rfl

theorem cell23_5695519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_5695519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695519 prefixEnd_5695519 := by exact prefixLift 5695519
  have htrace : WordTrace (prefixWord ++ tailWord_5695519) baseStart_5695519 baseEnd_5695519 := by
    simpa [prefixWord, tailWord_5695519, baseEnd_5695519] using wordTrace_append hprefix tailTrace_5695519
  have hstable : (prefixWord ++ tailWord_5695519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695519).length < 2 ^ (prefixWord ++ tailWord_5695519).sum := by decide
  have hdescent : baseEnd_5695519 < baseStart_5695519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695522 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 2, 4, 3]
def baseStart_5695522 : Nat := 118140960795 + 5695522 * 2 ^ 59
def prefixEnd_5695522 : Nat := 4983230072969 + 3 ^ 40 * 5695522 * 2
def baseEnd_5695522 : Nat := 2924540364256970477681777

theorem tailTrace_5695522 : CollatzResearch.WordTrace tailWord_5695522 prefixEnd_5695522 2924540364256970477681777 := by
  unfold tailWord_5695522
  simp only [CollatzResearch.WordTrace]
  refine ⟨51933188318025996640174205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138488502181402657707131213 51933188318025996640174205)
  ·
    refine ⟨19474945619259748740065327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51933188318025996640174205 19474945619259748740065327)
    ·
      refine ⟨29212418428889623110097991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19474945619259748740065327 29212418428889623110097991)
      ·
        refine ⟨43818627643334434665146987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29212418428889623110097991 43818627643334434665146987)
        ·
          refine ⟨65727941465001651997720481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43818627643334434665146987 65727941465001651997720481)
          ·
            refine ⟨49295956098751238998290361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65727941465001651997720481 49295956098751238998290361)
            ·
              refine ⟨36971967074063429248717771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49295956098751238998290361 36971967074063429248717771)
              ·
                refine ⟨55457950611095143873076657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36971967074063429248717771 55457950611095143873076657)
                ·
                  refine ⟨41593462958321357904807493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55457950611095143873076657 41593462958321357904807493)
                  ·
                    refine ⟨7798774304685254607151405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41593462958321357904807493 7798774304685254607151405)
                    ·
                      refine ⟨2924540364256970477681777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7798774304685254607151405 2924540364256970477681777)
                      ·
                        rfl

theorem cell23_5695522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_5695522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695522 prefixEnd_5695522 := by exact prefixLift 5695522
  have htrace : WordTrace (prefixWord ++ tailWord_5695522) baseStart_5695522 baseEnd_5695522 := by
    simpa [prefixWord, tailWord_5695522, baseEnd_5695522] using wordTrace_append hprefix tailTrace_5695522
  have hstable : (prefixWord ++ tailWord_5695522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695522).length < 2 ^ (prefixWord ++ tailWord_5695522).sum := by decide
  have hdescent : baseEnd_5695522 < baseStart_5695522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695536 : List Nat := [2, 1, 1, 1, 2, 6, 1, 3, 2, 2, 2]
def baseStart_5695536 : Nat := 118140960795 + 5695536 * 2 ^ 59
def prefixEnd_5695536 : Nat := 4983230072969 + 3 ^ 40 * 5695536 * 2
def baseEnd_5695536 : Nat := 2924547552986133422906713

theorem tailTrace_5695536 : CollatzResearch.WordTrace tailWord_5695536 prefixEnd_5695536 2924547552986133422906713 := by
  unfold tailWord_5695536
  simp only [CollatzResearch.WordTrace]
  refine ⟨103866631947026633475853231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138488842596035511301137641 103866631947026633475853231)
  ·
    refine ⟨155799947920539950213779847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103866631947026633475853231 155799947920539950213779847)
    ·
      refine ⟨233699921880809925320669771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155799947920539950213779847 233699921880809925320669771)
      ·
        refine ⟨350549882821214887981004657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233699921880809925320669771 350549882821214887981004657)
        ·
          refine ⟨262912412115911165985753493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350549882821214887981004657 262912412115911165985753493)
          ·
            refine ⟨12324019317933335905582195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 262912412115911165985753493 12324019317933335905582195)
            ·
              refine ⟨18486028976900003858373293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12324019317933335905582195 18486028976900003858373293)
              ·
                refine ⟨6932260866337501446889985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18486028976900003858373293 6932260866337501446889985)
                ·
                  refine ⟨5199195649753126085167489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6932260866337501446889985 5199195649753126085167489)
                  ·
                    refine ⟨3899396737314844563875617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5199195649753126085167489 3899396737314844563875617)
                    ·
                      refine ⟨2924547552986133422906713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3899396737314844563875617 2924547552986133422906713)
                      ·
                        rfl

theorem cell23_5695536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 2, 2, 2].length) (baseStart_5695536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695536 prefixEnd_5695536 := by exact prefixLift 5695536
  have htrace : WordTrace (prefixWord ++ tailWord_5695536) baseStart_5695536 baseEnd_5695536 := by
    simpa [prefixWord, tailWord_5695536, baseEnd_5695536] using wordTrace_append hprefix tailTrace_5695536
  have hstable : (prefixWord ++ tailWord_5695536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695536).length < 2 ^ (prefixWord ++ tailWord_5695536).sum := by decide
  have hdescent : baseEnd_5695536 < baseStart_5695536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695540 : List Nat := [2, 5, 1, 2, 2, 2, 1, 2, 1, 3, 2]
def baseStart_5695540 : Nat := 118140960795 + 5695540 * 2 ^ 59
def prefixEnd_5695540 : Nat := 4983230072969 + 3 ^ 40 * 5695540 * 2
def baseEnd_5695540 : Nat := 2924549606908751407256695

theorem tailTrace_5695540 : CollatzResearch.WordTrace tailWord_5695540 prefixEnd_5695540 2924549606908751407256695 := by
  unfold tailWord_5695540
  simp only [CollatzResearch.WordTrace]
  refine ⟨103866704893019387817426037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138488939857359183756568049 103866704893019387817426037)
  ·
    refine ⟨9737503583720567607883691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103866704893019387817426037 9737503583720567607883691)
    ·
      refine ⟨14606255375580851411825537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9737503583720567607883691 14606255375580851411825537)
      ·
        refine ⟨10954691531685638558869153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14606255375580851411825537 10954691531685638558869153)
        ·
          refine ⟨8216018648764228919151865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10954691531685638558869153 8216018648764228919151865)
          ·
            refine ⟨6162013986573171689363899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8216018648764228919151865 6162013986573171689363899)
            ·
              refine ⟨9243020979859757534045849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6162013986573171689363899 9243020979859757534045849)
              ·
                refine ⟨6932265734894818150534387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9243020979859757534045849 6932265734894818150534387)
                ·
                  refine ⟨10398398602342227225801581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6932265734894818150534387 10398398602342227225801581)
                  ·
                    refine ⟨3899399475878335209675593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10398398602342227225801581 3899399475878335209675593)
                    ·
                      refine ⟨2924549606908751407256695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3899399475878335209675593 2924549606908751407256695)
                      ·
                        rfl

theorem cell23_5695540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_5695540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695540 prefixEnd_5695540 := by exact prefixLift 5695540
  have htrace : WordTrace (prefixWord ++ tailWord_5695540) baseStart_5695540 baseEnd_5695540 := by
    simpa [prefixWord, tailWord_5695540, baseEnd_5695540] using wordTrace_append hprefix tailTrace_5695540
  have hstable : (prefixWord ++ tailWord_5695540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695540).length < 2 ^ (prefixWord ++ tailWord_5695540).sum := by decide
  have hdescent : baseEnd_5695540 < baseStart_5695540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695542 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 9]
def baseStart_5695542 : Nat := 118140960795 + 5695542 * 2 ^ 59
def prefixEnd_5695542 : Nat := 4983230072969 + 3 ^ 40 * 5695542 * 2
def baseEnd_5695542 : Nat := 324950070430006711047965

theorem tailTrace_5695542 : CollatzResearch.WordTrace tailWord_5695542 prefixEnd_5695542 324950070430006711047965 := by
  unfold tailWord_5695542
  simp only [CollatzResearch.WordTrace]
  refine ⟨12983342670751970623526555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138488988488021019984283253 12983342670751970623526555)
  ·
    refine ⟨19475014006127955935289833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12983342670751970623526555 19475014006127955935289833)
    ·
      refine ⟨14606260504595966951467375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19475014006127955935289833 14606260504595966951467375)
      ·
        refine ⟨21909390756893950427201063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14606260504595966951467375 21909390756893950427201063)
        ·
          refine ⟨32864086135340925640801595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21909390756893950427201063 32864086135340925640801595)
          ·
            refine ⟨49296129203011388461202393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32864086135340925640801595 49296129203011388461202393)
            ·
              refine ⟨36972096902258541345901795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49296129203011388461202393 36972096902258541345901795)
              ·
                refine ⟨55458145353387812018852693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36972096902258541345901795 55458145353387812018852693)
                ·
                  refine ⟨324950070430006711047965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55458145353387812018852693 324950070430006711047965)
                  ·
                    rfl

theorem cell23_5695542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_5695542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695542 prefixEnd_5695542 := by exact prefixLift 5695542
  have htrace : WordTrace (prefixWord ++ tailWord_5695542) baseStart_5695542 baseEnd_5695542 := by
    simpa [prefixWord, tailWord_5695542, baseEnd_5695542] using wordTrace_append hprefix tailTrace_5695542
  have hstable : (prefixWord ++ tailWord_5695542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695542).length < 2 ^ (prefixWord ++ tailWord_5695542).sum := by decide
  have hdescent : baseEnd_5695542 < baseStart_5695542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695576 : List Nat := [2, 1, 2, 2, 1, 6, 2, 2, 5]
def baseStart_5695576 : Nat := 118140960795 + 5695576 * 2 ^ 59
def prefixEnd_5695576 : Nat := 4983230072969 + 3 ^ 40 * 5695576 * 2
def baseEnd_5695576 : Nat := 324952010245812585156281

theorem tailTrace_5695576 : CollatzResearch.WordTrace tailWord_5695576 prefixEnd_5695576 324952010245812585156281 := by
  unfold tailWord_5695576
  simp only [CollatzResearch.WordTrace]
  refine ⟨103867361406954176891581291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138489815209272235855441721 103867361406954176891581291)
  ·
    refine ⟨155801042110431265337371937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103867361406954176891581291 155801042110431265337371937)
    ·
      refine ⟨116850781582823449003028953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155801042110431265337371937 116850781582823449003028953)
      ·
        refine ⟨87638086187117586752271715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116850781582823449003028953 87638086187117586752271715)
        ·
          refine ⟨131457129280676380128407573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87638086187117586752271715 131457129280676380128407573)
          ·
            refine ⟨6162052935031705318519105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 131457129280676380128407573 6162052935031705318519105)
            ·
              refine ⟨4621539701273778988889329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6162052935031705318519105 4621539701273778988889329)
              ·
                refine ⟨3466154775955334241666997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4621539701273778988889329 3466154775955334241666997)
                ·
                  refine ⟨324952010245812585156281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3466154775955334241666997 324952010245812585156281)
                  ·
                    rfl

theorem cell23_5695576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2, 5].length) (baseStart_5695576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695576 prefixEnd_5695576 := by exact prefixLift 5695576
  have htrace : WordTrace (prefixWord ++ tailWord_5695576) baseStart_5695576 baseEnd_5695576 := by
    simpa [prefixWord, tailWord_5695576, baseEnd_5695576] using wordTrace_append hprefix tailTrace_5695576
  have hstable : (prefixWord ++ tailWord_5695576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695576).length < 2 ^ (prefixWord ++ tailWord_5695576).sum := by decide
  have hdescent : baseEnd_5695576 < baseStart_5695576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695585 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 2, 8]
def baseStart_5695585 : Nat := 118140960795 + 5695585 * 2 ^ 59
def prefixEnd_5695585 : Nat := 4983230072969 + 3 ^ 40 * 5695585 * 2
def baseEnd_5695585 : Nat := 974857571179401243731329

theorem tailTrace_5695585 : CollatzResearch.WordTrace tailWord_5695585 prefixEnd_5695585 974857571179401243731329 := by
  unfold tailWord_5695585
  simp only [CollatzResearch.WordTrace]
  refine ⟨207735051070875748320240209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138490034047250498880160139 207735051070875748320240209)
  ·
    refine ⟨155801288303156811240180157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207735051070875748320240209 155801288303156811240180157)
    ·
      refine ⟨58425483113683804215067559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155801288303156811240180157 58425483113683804215067559)
      ·
        refine ⟨87638224670525706322601339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58425483113683804215067559 87638224670525706322601339)
        ·
          refine ⟨131457337005788559483902009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87638224670525706322601339 131457337005788559483902009)
          ·
            refine ⟨98593002754341419612926507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131457337005788559483902009 98593002754341419612926507)
            ·
              refine ⟨147889504131512129419389761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98593002754341419612926507 147889504131512129419389761)
              ·
                refine ⟨110917128098634097064542321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147889504131512129419389761 110917128098634097064542321)
                ·
                  refine ⟨83187846073975572798406741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110917128098634097064542321 83187846073975572798406741)
                  ·
                    refine ⟨974857571179401243731329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83187846073975572798406741 974857571179401243731329)
                    ·
                      rfl

theorem cell23_5695585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_5695585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695585 prefixEnd_5695585 := by exact prefixLift 5695585
  have htrace : WordTrace (prefixWord ++ tailWord_5695585) baseStart_5695585 baseEnd_5695585 := by
    simpa [prefixWord, tailWord_5695585, baseEnd_5695585] using wordTrace_append hprefix tailTrace_5695585
  have hstable : (prefixWord ++ tailWord_5695585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695585).length < 2 ^ (prefixWord ++ tailWord_5695585).sum := by decide
  have hdescent : baseEnd_5695585 < baseStart_5695585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695586 : List Nat := [3, 3, 2, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_5695586 : Nat := 118140960795 + 5695586 * 2 ^ 59
def prefixEnd_5695586 : Nat := 4983230072969 + 3 ^ 40 * 5695586 * 2
def baseEnd_5695586 : Nat := 2924573227018858227281483

theorem tailTrace_5695586 : CollatzResearch.WordTrace tailWord_5695586 prefixEnd_5695586 2924573227018858227281483 := by
  unfold tailWord_5695586
  simp only [CollatzResearch.WordTrace]
  refine ⟨51933771885968031372756653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138490058362581416994017741 51933771885968031372756653)
  ·
    refine ⟨19475164457238011764783745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51933771885968031372756653 19475164457238011764783745)
    ·
      refine ⟨14606373342928508823587809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19475164457238011764783745 14606373342928508823587809)
      ·
        refine ⟨10954780007196381617690857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14606373342928508823587809 10954780007196381617690857)
        ·
          refine ⟨8216085005397286213268143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10954780007196381617690857 8216085005397286213268143)
          ·
            refine ⟨12324127508095929319902215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8216085005397286213268143 12324127508095929319902215)
            ·
              refine ⟨18486191262143893979853323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12324127508095929319902215 18486191262143893979853323)
              ·
                refine ⟨27729286893215840969779985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18486191262143893979853323 27729286893215840969779985)
                ·
                  refine ⟨20796965169911880727334989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27729286893215840969779985 20796965169911880727334989)
                  ·
                    refine ⟨7798861938716955272750621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20796965169911880727334989 7798861938716955272750621)
                    ·
                      refine ⟨2924573227018858227281483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7798861938716955272750621 2924573227018858227281483)
                      ·
                        rfl

theorem cell23_5695586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_5695586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695586 prefixEnd_5695586 := by exact prefixLift 5695586
  have htrace : WordTrace (prefixWord ++ tailWord_5695586) baseStart_5695586 baseEnd_5695586 := by
    simpa [prefixWord, tailWord_5695586, baseEnd_5695586] using wordTrace_append hprefix tailTrace_5695586
  have hstable : (prefixWord ++ tailWord_5695586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695586).length < 2 ^ (prefixWord ++ tailWord_5695586).sum := by decide
  have hdescent : baseEnd_5695586 < baseStart_5695586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695606 : List Nat := [5, 1, 1, 2, 1, 4, 1, 1, 2, 5]
def baseStart_5695606 : Nat := 118140960795 + 5695606 * 2 ^ 59
def prefixEnd_5695606 : Nat := 4983230072969 + 3 ^ 40 * 5695606 * 2
def baseEnd_5695606 : Nat := 974861165543982716343797

theorem tailTrace_5695606 : CollatzResearch.WordTrace tailWord_5695606 prefixEnd_5695606 974861165543982716343797 := by
  unfold tailWord_5695606
  simp only [CollatzResearch.WordTrace]
  refine ⟨12983488562737479306672167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138490544669199779271169781 12983488562737479306672167)
  ·
    refine ⟨19475232844106218960008251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12983488562737479306672167 19475232844106218960008251)
    ·
      refine ⟨29212849266159328440012377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19475232844106218960008251 29212849266159328440012377)
      ·
        refine ⟨21909636949619496330009283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29212849266159328440012377 21909636949619496330009283)
        ·
          refine ⟨32864455424429244495013925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21909636949619496330009283 32864455424429244495013925)
          ·
            refine ⟨6162085392080483342815111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32864455424429244495013925 6162085392080483342815111)
            ·
              refine ⟨9243128088120725014222667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6162085392080483342815111 9243128088120725014222667)
              ·
                refine ⟨13864692132181087521334001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9243128088120725014222667 13864692132181087521334001)
                ·
                  refine ⟨10398519099135815641000501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13864692132181087521334001 10398519099135815641000501)
                  ·
                    refine ⟨974861165543982716343797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10398519099135815641000501 974861165543982716343797)
                    ·
                      rfl

theorem cell23_5695606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_5695606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695606 prefixEnd_5695606 := by exact prefixLift 5695606
  have htrace : WordTrace (prefixWord ++ tailWord_5695606) baseStart_5695606 baseEnd_5695606 := by
    simpa [prefixWord, tailWord_5695606, baseEnd_5695606] using wordTrace_append hprefix tailTrace_5695606
  have hstable : (prefixWord ++ tailWord_5695606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695606).length < 2 ^ (prefixWord ++ tailWord_5695606).sum := by decide
  have hdescent : baseEnd_5695606 < baseStart_5695606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695609 : List Nat := [1, 2, 1, 3, 4, 1, 3, 1, 2, 1, 4]
def baseStart_5695609 : Nat := 118140960795 + 5695609 * 2 ^ 59
def prefixEnd_5695609 : Nat := 4983230072969 + 3 ^ 40 * 5695609 * 2
def baseEnd_5695609 : Nat := 2924585037073911637293877

theorem tailTrace_5695609 : CollatzResearch.WordTrace tailWord_5695609 prefixEnd_5695609 2924585037073911637293877 := by
  unfold tailWord_5695609
  simp only [CollatzResearch.WordTrace]
  refine ⟨207735926422788800419113881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138490617615192533612742587 207735926422788800419113881)
  ·
    refine ⟨155801944817091600314335411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207735926422788800419113881 155801944817091600314335411)
    ·
      refine ⟨233702917225637400471503117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155801944817091600314335411 233702917225637400471503117)
      ·
        refine ⟨87638593959614025176813669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233702917225637400471503117 87638593959614025176813669)
        ·
          refine ⟨16432236367427629720652563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87638593959614025176813669 16432236367427629720652563)
          ·
            refine ⟨24648354551141444580978845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16432236367427629720652563 24648354551141444580978845)
            ·
              refine ⟨9243132956678041717867067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24648354551141444580978845 9243132956678041717867067)
              ·
                refine ⟨13864699435017062576800601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9243132956678041717867067 13864699435017062576800601)
                ·
                  refine ⟨10398524576262796932600451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13864699435017062576800601 10398524576262796932600451)
                  ·
                    refine ⟨15597786864394195398900677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10398524576262796932600451 15597786864394195398900677)
                    ·
                      refine ⟨2924585037073911637293877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15597786864394195398900677 2924585037073911637293877)
                      ·
                        rfl

theorem cell23_5695609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_5695609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695609 prefixEnd_5695609 := by exact prefixLift 5695609
  have htrace : WordTrace (prefixWord ++ tailWord_5695609) baseStart_5695609 baseEnd_5695609 := by
    simpa [prefixWord, tailWord_5695609, baseEnd_5695609] using wordTrace_append hprefix tailTrace_5695609
  have hstable : (prefixWord ++ tailWord_5695609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695609).length < 2 ^ (prefixWord ++ tailWord_5695609).sum := by decide
  have hdescent : baseEnd_5695609 < baseStart_5695609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695712 : List Nat := [2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 6]
def baseStart_5695712 : Nat := 118140960795 + 5695712 * 2 ^ 59
def prefixEnd_5695712 : Nat := 4983230072969 + 3 ^ 40 * 5695712 * 2
def baseEnd_5695712 : Nat := 2924637925581324734305903

theorem tailTrace_5695712 : CollatzResearch.WordTrace tailWord_5695712 prefixEnd_5695712 2924637925581324734305903 := by
  unfold tailWord_5695712
  simp only [CollatzResearch.WordTrace]
  refine ⟨103869841570707824505056695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138493122094277099340075593 103869841570707824505056695)
  ·
    refine ⟨155804762356061736757585043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103869841570707824505056695 155804762356061736757585043)
    ·
      refine ⟨233707143534092605136377565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155804762356061736757585043 233707143534092605136377565)
      ·
        refine ⟨87640178825284726926141587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233707143534092605136377565 87640178825284726926141587)
        ·
          refine ⟨131460268237927090389212381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87640178825284726926141587 131460268237927090389212381)
          ·
            refine ⟨49297600589222658895954643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131460268237927090389212381 49297600589222658895954643)
            ·
              refine ⟨73946400883833988343931965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49297600589222658895954643 73946400883833988343931965)
              ·
                refine ⟨27729900331437745628974487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73946400883833988343931965 27729900331437745628974487)
                ·
                  refine ⟨41594850497156618443461731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27729900331437745628974487 41594850497156618443461731)
                  ·
                    refine ⟨62392275745734927665192597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41594850497156618443461731 62392275745734927665192597)
                    ·
                      refine ⟨2924637925581324734305903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62392275745734927665192597 2924637925581324734305903)
                      ·
                        rfl

theorem cell23_5695712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_5695712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695712 prefixEnd_5695712 := by exact prefixLift 5695712
  have htrace : WordTrace (prefixWord ++ tailWord_5695712) baseStart_5695712 baseEnd_5695712 := by
    simpa [prefixWord, tailWord_5695712, baseEnd_5695712] using wordTrace_append hprefix tailTrace_5695712
  have hstable : (prefixWord ++ tailWord_5695712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695712).length < 2 ^ (prefixWord ++ tailWord_5695712).sum := by decide
  have hdescent : baseEnd_5695712 < baseStart_5695712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695716 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 5, 2, 2]
def baseStart_5695716 : Nat := 118140960795 + 5695716 * 2 ^ 59
def prefixEnd_5695716 : Nat := 4983230072969 + 3 ^ 40 * 5695716 * 2
def baseEnd_5695716 : Nat := 2924639979503942718655885

theorem tailTrace_5695716 : CollatzResearch.WordTrace tailWord_5695716 prefixEnd_5695716 2924639979503942718655885 := by
  unfold tailWord_5695716
  simp only [CollatzResearch.WordTrace]
  refine ⟨103869914516700578846629501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138493219355600771795506001 103869914516700578846629501)
  ·
    refine ⟨38951217943762717067486063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103869914516700578846629501 38951217943762717067486063)
    ·
      refine ⟨58426826915644075601229095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38951217943762717067486063 58426826915644075601229095)
      ·
        refine ⟨87640240373466113401843643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58426826915644075601229095 87640240373466113401843643)
        ·
          refine ⟨131460360560199170102765465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87640240373466113401843643 131460360560199170102765465)
          ·
            refine ⟨98595270420149377577074099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131460360560199170102765465 98595270420149377577074099)
            ·
              refine ⟨147892905630224066365611149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98595270420149377577074099 147892905630224066365611149)
              ·
                refine ⟨55459839611334024887104181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147892905630224066365611149 55459839611334024887104181)
                ·
                  refine ⟨5199359963562564833166017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55459839611334024887104181 5199359963562564833166017)
                  ·
                    refine ⟨3899519972671923624874513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5199359963562564833166017 3899519972671923624874513)
                    ·
                      refine ⟨2924639979503942718655885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3899519972671923624874513 2924639979503942718655885)
                      ·
                        rfl

theorem cell23_5695716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 5, 2, 2].length) (baseStart_5695716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695716 prefixEnd_5695716 := by exact prefixLift 5695716
  have htrace : WordTrace (prefixWord ++ tailWord_5695716) baseStart_5695716 baseEnd_5695716 := by
    simpa [prefixWord, tailWord_5695716, baseEnd_5695716] using wordTrace_append hprefix tailTrace_5695716
  have hstable : (prefixWord ++ tailWord_5695716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695716).length < 2 ^ (prefixWord ++ tailWord_5695716).sum := by decide
  have hdescent : baseEnd_5695716 < baseStart_5695716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5695722 : List Nat := [3, 1, 3, 1, 1, 2, 1, 11]
def baseStart_5695722 : Nat := 118140960795 + 5695722 * 2 ^ 59
def prefixEnd_5695722 : Nat := 4983230072969 + 3 ^ 40 * 5695722 * 2
def baseEnd_5695722 : Nat := 108320113347698877599291

theorem tailTrace_5695722 : CollatzResearch.WordTrace tailWord_5695722 prefixEnd_5695722 108320113347698877599291 := by
  unfold tailWord_5695722
  simp only [CollatzResearch.WordTrace]
  refine ⟨51935011967844855179494355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138493365247586280478651613 51935011967844855179494355)
  ·
    refine ⟨77902517951767282769241533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51935011967844855179494355 77902517951767282769241533)
    ·
      refine ⟨29213444231912731038465575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77902517951767282769241533 29213444231912731038465575)
      ·
        refine ⟨43820166347869096557698363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29213444231912731038465575 43820166347869096557698363)
        ·
          refine ⟨65730249521803644836547545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43820166347869096557698363 65730249521803644836547545)
          ·
            refine ⟨49297687141352733627410659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65730249521803644836547545 49297687141352733627410659)
            ·
              refine ⟨73946530712029100441115989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49297687141352733627410659 73946530712029100441115989)
              ·
                refine ⟨108320113347698877599291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 73946530712029100441115989 108320113347698877599291)
                ·
                  rfl

theorem cell23_5695722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 11].length) (baseStart_5695722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5695722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5695722 prefixEnd_5695722 := by exact prefixLift 5695722
  have htrace : WordTrace (prefixWord ++ tailWord_5695722) baseStart_5695722 baseEnd_5695722 := by
    simpa [prefixWord, tailWord_5695722, baseEnd_5695722] using wordTrace_append hprefix tailTrace_5695722
  have hstable : (prefixWord ++ tailWord_5695722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5695722).length < 2 ^ (prefixWord ++ tailWord_5695722).sum := by decide
  have hdescent : baseEnd_5695722 < baseStart_5695722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5695722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
