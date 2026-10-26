import V185TrunkScan23Chunk1182

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7009008 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 5, 2, 2]
def baseStart_7009008 : Nat := 118140960795 + 7009008 * 2 ^ 59
def prefixEnd_7009008 : Nat := 4983230072969 + 3 ^ 40 * 7009008 * 2
def baseEnd_7009008 : Nat := 3598990015208418457666165

theorem tailTrace_7009008 : CollatzResearch.WordTrace tailWord_7009008 prefixEnd_7009008 3598990015208418457666165 := by
  unfold tailWord_7009008
  simp only [CollatzResearch.WordTrace]
  refine ⟨127819761695784267055013839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170426348927712356073351785 127819761695784267055013839)
  ·
    refine ⟨191729642543676400582520759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127819761695784267055013839 191729642543676400582520759)
    ·
      refine ⟨287594463815514600873781139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191729642543676400582520759 287594463815514600873781139)
      ·
        refine ⟨431391695723271901310671709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287594463815514600873781139 431391695723271901310671709)
        ·
          refine ⟨161771885896226962991501891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 431391695723271901310671709 161771885896226962991501891)
          ·
            refine ⟨242657828844340444487252837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161771885896226962991501891 242657828844340444487252837)
            ·
              refine ⟨45498342908313833341359907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 242657828844340444487252837 45498342908313833341359907)
              ·
                refine ⟨68247514362470750012039861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45498342908313833341359907 68247514362470750012039861)
                ·
                  refine ⟨6398204471481632813628737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68247514362470750012039861 6398204471481632813628737)
                  ·
                    refine ⟨4798653353611224610221553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6398204471481632813628737 4798653353611224610221553)
                    ·
                      refine ⟨3598990015208418457666165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4798653353611224610221553 3598990015208418457666165)
                      ·
                        rfl

theorem cell23_7009008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 5, 2, 2].length) (baseStart_7009008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009008 prefixEnd_7009008 := by exact prefixLift 7009008
  have htrace : WordTrace (prefixWord ++ tailWord_7009008) baseStart_7009008 baseEnd_7009008 := by
    simpa [prefixWord, tailWord_7009008, baseEnd_7009008] using wordTrace_append hprefix tailTrace_7009008
  have hstable : (prefixWord ++ tailWord_7009008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009008).length < 2 ^ (prefixWord ++ tailWord_7009008).sum := by decide
  have hdescent : baseEnd_7009008 < baseStart_7009008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009021 : List Nat := [1, 4, 1, 1, 1, 1, 5, 2, 1, 2, 4]
def baseStart_7009021 : Nat := 118140960795 + 7009021 * 2 ^ 59
def prefixEnd_7009021 : Nat := 4983230072969 + 3 ^ 40 * 7009021 * 2
def baseEnd_7009021 : Nat := 3598996690456926906803605

theorem tailTrace_7009021 : CollatzResearch.WordTrace tailWord_7009021 prefixEnd_7009021 3598996690456926906803605 := by
  unfold tailWord_7009021
  simp only [CollatzResearch.WordTrace]
  refine ⟨255639997540521437330250917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170426665027014291553500611 255639997540521437330250917)
  ·
    refine ⟨47932499538847769499422047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255639997540521437330250917 47932499538847769499422047)
    ·
      refine ⟨71898749308271654249133071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47932499538847769499422047 71898749308271654249133071)
      ·
        refine ⟨107848123962407481373699607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71898749308271654249133071 107848123962407481373699607)
        ·
          refine ⟨161772185943611222060549411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107848123962407481373699607 161772185943611222060549411)
          ·
            refine ⟨242658278915416833090824117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161772185943611222060549411 242658278915416833090824117)
            ·
              refine ⟨22749213648320328102264761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 242658278915416833090824117 22749213648320328102264761)
              ·
                refine ⟨17061910236240246076698571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22749213648320328102264761 17061910236240246076698571)
                ·
                  refine ⟨25592865354360369115047857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17061910236240246076698571 25592865354360369115047857)
                  ·
                    refine ⟨19194649015770276836285893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25592865354360369115047857 19194649015770276836285893)
                    ·
                      refine ⟨3598996690456926906803605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19194649015770276836285893 3598996690456926906803605)
                      ·
                        rfl

theorem cell23_7009021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_7009021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009021 prefixEnd_7009021 := by exact prefixLift 7009021
  have htrace : WordTrace (prefixWord ++ tailWord_7009021) baseStart_7009021 baseEnd_7009021 := by
    simpa [prefixWord, tailWord_7009021, baseEnd_7009021] using wordTrace_append hprefix tailTrace_7009021
  have hstable : (prefixWord ++ tailWord_7009021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009021).length < 2 ^ (prefixWord ++ tailWord_7009021).sum := by decide
  have hdescent : baseEnd_7009021 < baseStart_7009021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009051 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 1, 9, 2]
def baseStart_7009051 : Nat := 118140960795 + 7009051 * 2 ^ 59
def prefixEnd_7009051 : Nat := 4983230072969 + 3 ^ 40 * 7009051 * 2
def baseEnd_7009051 : Nat := 3599012094876561789428467

theorem tailTrace_7009051 : CollatzResearch.WordTrace tailWord_7009051 prefixEnd_7009051 3599012094876561789428467 := by
  unfold tailWord_7009051
  simp only [CollatzResearch.WordTrace]
  refine ⟨255641091730412752453843007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170427394486941834969228671 255641091730412752453843007)
  ·
    refine ⟨383461637595619128680764511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255641091730412752453843007 383461637595619128680764511)
    ·
      refine ⟨575192456393428693021146767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383461637595619128680764511 575192456393428693021146767)
      ·
        refine ⟨862788684590143039531720151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575192456393428693021146767 862788684590143039531720151)
        ·
          refine ⟨1294183026885214559297580227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 862788684590143039531720151 1294183026885214559297580227)
          ·
            refine ⟨1941274540327821838946370341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1294183026885214559297580227 1941274540327821838946370341)
            ·
              refine ⟨363988976311466594802444439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1941274540327821838946370341 363988976311466594802444439)
              ·
                refine ⟨545983464467199892203666659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363988976311466594802444439 545983464467199892203666659)
                ·
                  refine ⟨818975196700799838305499989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 545983464467199892203666659 818975196700799838305499989)
                  ·
                    refine ⟨4798682793168749052571289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 818975196700799838305499989 4798682793168749052571289)
                    ·
                      refine ⟨3599012094876561789428467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4798682793168749052571289 3599012094876561789428467)
                      ·
                        rfl

theorem cell23_7009051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 9, 2].length) (baseStart_7009051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009051 prefixEnd_7009051 := by exact prefixLift 7009051
  have htrace : WordTrace (prefixWord ++ tailWord_7009051) baseStart_7009051 baseEnd_7009051 := by
    simpa [prefixWord, tailWord_7009051, baseEnd_7009051] using wordTrace_append hprefix tailTrace_7009051
  have hstable : (prefixWord ++ tailWord_7009051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009051).length < 2 ^ (prefixWord ++ tailWord_7009051).sum := by decide
  have hdescent : baseEnd_7009051 < baseStart_7009051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009058 : List Nat := [3, 3, 1, 1, 2, 2, 1, 3, 1, 3, 3]
def baseStart_7009058 : Nat := 118140960795 + 7009058 * 2 ^ 59
def prefixEnd_7009058 : Nat := 4983230072969 + 3 ^ 40 * 7009058 * 2
def baseEnd_7009058 : Nat := 3599015689241143262040935

theorem tailTrace_7009058 : CollatzResearch.WordTrace tailWord_7009058 prefixEnd_7009058 3599015689241143262040935 := by
  unfold tailWord_7009058
  simp only [CollatzResearch.WordTrace]
  refine ⟨63910336760346848162336957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170427564694258261766231885 63910336760346848162336957)
  ·
    refine ⟨23966376285130068060876359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63910336760346848162336957 23966376285130068060876359)
    ·
      refine ⟨35949564427695102091314539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23966376285130068060876359 35949564427695102091314539)
      ·
        refine ⟨53924346641542653136971809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35949564427695102091314539 53924346641542653136971809)
        ·
          refine ⟨40443259981156989852728857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53924346641542653136971809 40443259981156989852728857)
          ·
            refine ⟨30332444985867742389546643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40443259981156989852728857 30332444985867742389546643)
            ·
              refine ⟨45498667478801613584319965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30332444985867742389546643 45498667478801613584319965)
              ·
                refine ⟨17062000304550605094119987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45498667478801613584319965 17062000304550605094119987)
                ·
                  refine ⟨25593000456825907641179981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17062000304550605094119987 25593000456825907641179981)
                  ·
                    refine ⟨9597375171309715365442493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25593000456825907641179981 9597375171309715365442493)
                    ·
                      refine ⟨3599015689241143262040935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9597375171309715365442493 3599015689241143262040935)
                      ·
                        rfl

theorem cell23_7009058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_7009058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009058 prefixEnd_7009058 := by exact prefixLift 7009058
  have htrace : WordTrace (prefixWord ++ tailWord_7009058) baseStart_7009058 baseEnd_7009058 := by
    simpa [prefixWord, tailWord_7009058, baseEnd_7009058] using wordTrace_append hprefix tailTrace_7009058
  have hstable : (prefixWord ++ tailWord_7009058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009058).length < 2 ^ (prefixWord ++ tailWord_7009058).sum := by decide
  have hdescent : baseEnd_7009058 < baseStart_7009058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009068 : List Nat := [2, 2, 1, 1, 1, 4, 1, 3, 3, 3, 2]
def baseStart_7009068 : Nat := 118140960795 + 7009068 * 2 ^ 59
def prefixEnd_7009068 : Nat := 4983230072969 + 3 ^ 40 * 7009068 * 2
def baseEnd_7009068 : Nat := 3599020824047688222915889

theorem tailTrace_7009068 : CollatzResearch.WordTrace tailWord_7009068 prefixEnd_7009068 3599020824047688222915889 := by
  unfold tailWord_7009068
  simp only [CollatzResearch.WordTrace]
  refine ⟨127820855885675582178605929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170427807847567442904807905 127820855885675582178605929)
  ·
    refine ⟨95865641914256686633954447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127820855885675582178605929 95865641914256686633954447)
    ·
      refine ⟨143798462871385029950931671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95865641914256686633954447 143798462871385029950931671)
      ·
        refine ⟨215697694307077544926397507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143798462871385029950931671 215697694307077544926397507)
        ·
          refine ⟨323546541460616317389596261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215697694307077544926397507 323546541460616317389596261)
          ·
            refine ⟨60664976523865559510549299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 323546541460616317389596261 60664976523865559510549299)
            ·
              refine ⟨90997464785798339265823949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60664976523865559510549299 90997464785798339265823949)
              ·
                refine ⟨34124049294674377224683981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90997464785798339265823949 34124049294674377224683981)
                ·
                  refine ⟨12796518485502891459256493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34124049294674377224683981 12796518485502891459256493)
                  ·
                    refine ⟨4798694432063584297221185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12796518485502891459256493 4798694432063584297221185)
                    ·
                      refine ⟨3599020824047688222915889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4798694432063584297221185 3599020824047688222915889)
                      ·
                        rfl

theorem cell23_7009068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 3, 2].length) (baseStart_7009068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009068 prefixEnd_7009068 := by exact prefixLift 7009068
  have htrace : WordTrace (prefixWord ++ tailWord_7009068) baseStart_7009068 baseEnd_7009068 := by
    simpa [prefixWord, tailWord_7009068, baseEnd_7009068] using wordTrace_append hprefix tailTrace_7009068
  have hstable : (prefixWord ++ tailWord_7009068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009068).length < 2 ^ (prefixWord ++ tailWord_7009068).sum := by decide
  have hdescent : baseEnd_7009068 < baseStart_7009068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009076 : List Nat := [2, 5, 1, 1, 3, 1, 2, 3, 1, 2, 2]
def baseStart_7009076 : Nat := 118140960795 + 7009076 * 2 ^ 59
def prefixEnd_7009076 : Nat := 4983230072969 + 3 ^ 40 * 7009076 * 2
def baseEnd_7009076 : Nat := 3599024931892924191615853

theorem tailTrace_7009076 : CollatzResearch.WordTrace tailWord_7009076 prefixEnd_7009076 3599024931892924191615853 := by
  unfold tailWord_7009076
  simp only [CollatzResearch.WordTrace]
  refine ⟨127821001777661090861751541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170428002370214787815668721 127821001777661090861751541)
  ·
    refine ⟨11983218916655727268289207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127821001777661090861751541 11983218916655727268289207)
    ·
      refine ⟨17974828374983590902433811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11983218916655727268289207 17974828374983590902433811)
      ·
        refine ⟨26962242562475386353650717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17974828374983590902433811 26962242562475386353650717)
        ·
          refine ⟨10110840960928269882619019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26962242562475386353650717 10110840960928269882619019)
          ·
            refine ⟨15166261441392404823928529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10110840960928269882619019 15166261441392404823928529)
            ·
              refine ⟨11374696081044303617946397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15166261441392404823928529 11374696081044303617946397)
              ·
                refine ⟨4265511030391613856729899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11374696081044303617946397 4265511030391613856729899)
                ·
                  refine ⟨6398266545587420785094849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4265511030391613856729899 6398266545587420785094849)
                  ·
                    refine ⟨4798699909190565588821137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6398266545587420785094849 4798699909190565588821137)
                    ·
                      refine ⟨3599024931892924191615853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4798699909190565588821137 3599024931892924191615853)
                      ·
                        rfl

theorem cell23_7009076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_7009076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009076 prefixEnd_7009076 := by exact prefixLift 7009076
  have htrace : WordTrace (prefixWord ++ tailWord_7009076) baseStart_7009076 baseEnd_7009076 := by
    simpa [prefixWord, tailWord_7009076, baseEnd_7009076] using wordTrace_append hprefix tailTrace_7009076
  have hstable : (prefixWord ++ tailWord_7009076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009076).length < 2 ^ (prefixWord ++ tailWord_7009076).sum := by decide
  have hdescent : baseEnd_7009076 < baseStart_7009076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009131 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 1, 5, 3]
def baseStart_7009131 : Nat := 118140960795 + 7009131 * 2 ^ 59
def prefixEnd_7009131 : Nat := 4983230072969 + 3 ^ 40 * 7009131 * 2
def baseEnd_7009131 : Nat := 3599053173328921476428099

theorem tailTrace_7009131 : CollatzResearch.WordTrace tailWord_7009131 prefixEnd_7009131 3599053173328921476428099 := by
  unfold tailWord_7009131
  simp only [CollatzResearch.WordTrace]
  refine ⟨255644009570122926116755247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170429339713415284077836831 255644009570122926116755247)
  ·
    refine ⟨383466014355184389175132871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255644009570122926116755247 383466014355184389175132871)
    ·
      refine ⟨575199021532776583762699307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383466014355184389175132871 575199021532776583762699307)
      ·
        refine ⟨862798532299164875644048961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575199021532776583762699307 862798532299164875644048961)
        ·
          refine ⟨647098899224373656733036721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 862798532299164875644048961 647098899224373656733036721)
          ·
            refine ⟨485324174418280242549777541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 647098899224373656733036721 485324174418280242549777541)
            ·
              refine ⟨90998282703427545478083289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 485324174418280242549777541 90998282703427545478083289)
              ·
                refine ⟨68248712027570659108562467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90998282703427545478083289 68248712027570659108562467)
                ·
                  refine ⟨102373068041355988662843701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68248712027570659108562467 102373068041355988662843701)
                  ·
                    refine ⟨9597475128877123937141597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102373068041355988662843701 9597475128877123937141597)
                    ·
                      refine ⟨3599053173328921476428099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9597475128877123937141597 3599053173328921476428099)
                      ·
                        rfl

theorem cell23_7009131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 5, 3].length) (baseStart_7009131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009131 prefixEnd_7009131 := by exact prefixLift 7009131
  have htrace : WordTrace (prefixWord ++ tailWord_7009131) baseStart_7009131 baseEnd_7009131 := by
    simpa [prefixWord, tailWord_7009131, baseEnd_7009131] using wordTrace_append hprefix tailTrace_7009131
  have hstable : (prefixWord ++ tailWord_7009131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009131).length < 2 ^ (prefixWord ++ tailWord_7009131).sum := by decide
  have hdescent : baseEnd_7009131 < baseStart_7009131 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009151 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 4, 5]
def baseStart_7009151 : Nat := 118140960795 + 7009151 * 2 ^ 59
def prefixEnd_7009151 : Nat := 4983230072969 + 3 ^ 40 * 7009151 * 2
def baseEnd_7009151 : Nat := 1199687814314003799392669

theorem tailTrace_7009151 : CollatzResearch.WordTrace tailWord_7009151 prefixEnd_7009151 1199687814314003799392669 := by
  unfold tailWord_7009151
  simp only [CollatzResearch.WordTrace]
  refine ⟨255644739030050469532483307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170429826020033646354988871 255644739030050469532483307)
  ·
    refine ⟨383467108545075704298724961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255644739030050469532483307 383467108545075704298724961)
    ·
      refine ⟨287600331408806778224043721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383467108545075704298724961 287600331408806778224043721)
      ·
        refine ⟨215700248556605083668032791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287600331408806778224043721 215700248556605083668032791)
        ·
          refine ⟨323550372834907625502049187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215700248556605083668032791 323550372834907625502049187)
          ·
            refine ⟨485325559252361438253073781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323550372834907625502049187 485325559252361438253073781)
            ·
              refine ⟨45499271179908884836225667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 485325559252361438253073781 45499271179908884836225667)
              ·
                refine ⟨68248906769863327254338501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45499271179908884836225667 68248906769863327254338501)
                ·
                  refine ⟨12796670019349373860188469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68248906769863327254338501 12796670019349373860188469)
                  ·
                    refine ⟨1199687814314003799392669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12796670019349373860188469 1199687814314003799392669)
                    ·
                      rfl

theorem cell23_7009151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 5].length) (baseStart_7009151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009151 prefixEnd_7009151 := by exact prefixLift 7009151
  have htrace : WordTrace (prefixWord ++ tailWord_7009151) baseStart_7009151 baseEnd_7009151 := by
    simpa [prefixWord, tailWord_7009151, baseEnd_7009151] using wordTrace_append hprefix tailTrace_7009151
  have hstable : (prefixWord ++ tailWord_7009151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009151).length < 2 ^ (prefixWord ++ tailWord_7009151).sum := by decide
  have hdescent : baseEnd_7009151 < baseStart_7009151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009155 : List Nat := [1, 1, 1, 3, 4, 1, 5, 2, 5]
def baseStart_7009155 : Nat := 118140960795 + 7009155 * 2 ^ 59
def prefixEnd_7009155 : Nat := 4983230072969 + 3 ^ 40 * 7009155 * 2
def baseEnd_7009155 : Nat := 399896166318292153614221

theorem tailTrace_7009155 : CollatzResearch.WordTrace tailWord_7009155 prefixEnd_7009155 399896166318292153614221 := by
  unfold tailWord_7009155
  simp only [CollatzResearch.WordTrace]
  refine ⟨255644884922035978215628919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170429923281357318810419279 255644884922035978215628919)
  ·
    refine ⟨383467327383053967323443379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255644884922035978215628919 383467327383053967323443379)
    ·
      refine ⟨575200991074580950985165069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383467327383053967323443379 575200991074580950985165069)
      ·
        refine ⟨215700371652967856619436901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 575200991074580950985165069 215700371652967856619436901)
        ·
          refine ⟨40443819684931473116144419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215700371652967856619436901 40443819684931473116144419)
          ·
            refine ⟨60665729527397209674216629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40443819684931473116144419 60665729527397209674216629)
            ·
              refine ⟨5687412143193488406957809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60665729527397209674216629 5687412143193488406957809)
              ·
                refine ⟨4265559107395116305218357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5687412143193488406957809 4265559107395116305218357)
                ·
                  refine ⟨399896166318292153614221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4265559107395116305218357 399896166318292153614221)
                  ·
                    rfl

theorem cell23_7009155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2, 5].length) (baseStart_7009155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009155 prefixEnd_7009155 := by exact prefixLift 7009155
  have htrace : WordTrace (prefixWord ++ tailWord_7009155) baseStart_7009155 baseEnd_7009155 := by
    simpa [prefixWord, tailWord_7009155, baseEnd_7009155] using wordTrace_append hprefix tailTrace_7009155
  have hstable : (prefixWord ++ tailWord_7009155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009155).length < 2 ^ (prefixWord ++ tailWord_7009155).sum := by decide
  have hdescent : baseEnd_7009155 < baseStart_7009155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009161 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 1, 1, 7]
def baseStart_7009161 : Nat := 118140960795 + 7009161 * 2 ^ 59
def prefixEnd_7009161 : Nat := 4983230072969 + 3 ^ 40 * 7009161 * 2
def baseEnd_7009161 : Nat := 3599068577748556359052961

theorem tailTrace_7009161 : CollatzResearch.WordTrace tailWord_7009161 prefixEnd_7009161 3599068577748556359052961 := by
  unfold tailWord_7009161
  simp only [CollatzResearch.WordTrace]
  refine ⟨255645103760014241240347337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170430069173342827493564891 255645103760014241240347337)
  ·
    refine ⟨191733827820010680930260503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255645103760014241240347337 191733827820010680930260503)
    ·
      refine ⟨287600741730016021395390755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191733827820010680930260503 287600741730016021395390755)
      ·
        refine ⟨431401112595024032093086133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287600741730016021395390755 431401112595024032093086133)
        ·
          refine ⟨40443854305783503008726825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 431401112595024032093086133 40443854305783503008726825)
          ·
            refine ⟨30332890729337627256545119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40443854305783503008726825 30332890729337627256545119)
            ·
              refine ⟨45499336094006440884817679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30332890729337627256545119 45499336094006440884817679)
              ·
                refine ⟨68249004141009661327226519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45499336094006440884817679 68249004141009661327226519)
                ·
                  refine ⟨102373506211514491990839779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68249004141009661327226519 102373506211514491990839779)
                  ·
                    refine ⟨153560259317271737986259669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102373506211514491990839779 153560259317271737986259669)
                    ·
                      refine ⟨3599068577748556359052961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 153560259317271737986259669 3599068577748556359052961)
                      ·
                        rfl

theorem cell23_7009161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 1, 7].length) (baseStart_7009161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009161 prefixEnd_7009161 := by exact prefixLift 7009161
  have htrace : WordTrace (prefixWord ++ tailWord_7009161) baseStart_7009161 baseEnd_7009161 := by
    simpa [prefixWord, tailWord_7009161, baseEnd_7009161] using wordTrace_append hprefix tailTrace_7009161
  have hstable : (prefixWord ++ tailWord_7009161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009161).length < 2 ^ (prefixWord ++ tailWord_7009161).sum := by decide
  have hdescent : baseEnd_7009161 < baseStart_7009161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009171 : List Nat := [1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 4]
def baseStart_7009171 : Nat := 118140960795 + 7009171 * 2 ^ 59
def prefixEnd_7009171 : Nat := 4983230072969 + 3 ^ 40 * 7009171 * 2
def baseEnd_7009171 : Nat := 3599073712555101319927915

theorem tailTrace_7009171 : CollatzResearch.WordTrace tailWord_7009171 prefixEnd_7009171 3599073712555101319927915 := by
  unfold tailWord_7009171
  simp only [CollatzResearch.WordTrace]
  refine ⟨255645468489978012948211367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170430312326652008632140911 255645468489978012948211367)
  ·
    refine ⟨383468202734967019422317051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255645468489978012948211367 383468202734967019422317051)
    ·
      refine ⟨575202304102450529133475577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383468202734967019422317051 575202304102450529133475577)
      ·
        refine ⟨431401728076837896850106683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 575202304102450529133475577 431401728076837896850106683)
        ·
          refine ⟨647102592115256845275160025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431401728076837896850106683 647102592115256845275160025)
          ·
            refine ⟨485326944086442633956370019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 647102592115256845275160025 485326944086442633956370019)
            ·
              refine ⟨727990416129663950934555029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485326944086442633956370019 727990416129663950934555029)
              ·
                refine ⟨34124550756077997700057267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 727990416129663950934555029 34124550756077997700057267)
                ·
                  refine ⟨51186826134116996550085901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34124550756077997700057267 51186826134116996550085901)
                  ·
                    refine ⟨19195059800293873706282213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51186826134116996550085901 19195059800293873706282213)
                    ·
                      refine ⟨3599073712555101319927915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19195059800293873706282213 3599073712555101319927915)
                      ·
                        rfl

theorem cell23_7009171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 4].length) (baseStart_7009171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009171 prefixEnd_7009171 := by exact prefixLift 7009171
  have htrace : WordTrace (prefixWord ++ tailWord_7009171) baseStart_7009171 baseEnd_7009171 := by
    simpa [prefixWord, tailWord_7009171, baseEnd_7009171] using wordTrace_append hprefix tailTrace_7009171
  have hstable : (prefixWord ++ tailWord_7009171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009171).length < 2 ^ (prefixWord ++ tailWord_7009171).sum := by decide
  have hdescent : baseEnd_7009171 < baseStart_7009171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009185 : List Nat := [1, 2, 3, 4, 1, 2, 2, 1, 2, 5]
def baseStart_7009185 : Nat := 118140960795 + 7009185 * 2 ^ 59
def prefixEnd_7009185 : Nat := 4983230072969 + 3 ^ 40 * 7009185 * 2
def baseEnd_7009185 : Nat := 1199693633761421421717617

theorem tailTrace_7009185 : CollatzResearch.WordTrace tailWord_7009185 prefixEnd_7009185 1199693633761421421717617 := by
  unfold tailWord_7009185
  simp only [CollatzResearch.WordTrace]
  refine ⟨255645979111927293339221009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170430652741284862226147339 255645979111927293339221009)
  ·
    refine ⟨191734484333945470004415757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255645979111927293339221009 191734484333945470004415757)
    ·
      refine ⟨71900431625229551251655909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191734484333945470004415757 71900431625229551251655909)
      ·
        refine ⟨13481330929730540859685483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71900431625229551251655909 13481330929730540859685483)
        ·
          refine ⟨20221996394595811289528225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13481330929730540859685483 20221996394595811289528225)
          ·
            refine ⟨15166497295946858467146169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20221996394595811289528225 15166497295946858467146169)
            ·
              refine ⟨11374872971960143850359627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15166497295946858467146169 11374872971960143850359627)
              ·
                refine ⟨17062309457940215775539441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11374872971960143850359627 17062309457940215775539441)
                ·
                  refine ⟨12796732093455161831654581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17062309457940215775539441 12796732093455161831654581)
                  ·
                    refine ⟨1199693633761421421717617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12796732093455161831654581 1199693633761421421717617)
                    ·
                      rfl

theorem cell23_7009185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_7009185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009185 prefixEnd_7009185 := by exact prefixLift 7009185
  have htrace : WordTrace (prefixWord ++ tailWord_7009185) baseStart_7009185 baseEnd_7009185 := by
    simpa [prefixWord, tailWord_7009185, baseEnd_7009185] using wordTrace_append hprefix tailTrace_7009185
  have hstable : (prefixWord ++ tailWord_7009185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009185).length < 2 ^ (prefixWord ++ tailWord_7009185).sum := by decide
  have hdescent : baseEnd_7009185 < baseStart_7009185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009205 : List Nat := [1, 3, 3, 2, 1, 1, 2, 2, 2, 4, 2]
def baseStart_7009205 : Nat := 118140960795 + 7009205 * 2 ^ 59
def prefixEnd_7009205 : Nat := 4983230072969 + 3 ^ 40 * 7009205 * 2
def baseEnd_7009205 : Nat := 3599091170897354186902759

theorem tailTrace_7009205 : CollatzResearch.WordTrace tailWord_7009205 prefixEnd_7009205 3599091170897354186902759 := by
  unfold tailWord_7009205
  simp only [CollatzResearch.WordTrace]
  refine ⟨255646708571854836754949069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170431139047903224503299379 255646708571854836754949069)
  ·
    refine ⟨95867515714445563783105901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255646708571854836754949069 95867515714445563783105901)
    ·
      refine ⟨35950318392917086418664713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95867515714445563783105901 35950318392917086418664713)
      ·
        refine ⟨26962738794687814813998535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35950318392917086418664713 26962738794687814813998535)
        ·
          refine ⟨40444108192031722220997803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26962738794687814813998535 40444108192031722220997803)
          ·
            refine ⟨60666162288047583331496705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40444108192031722220997803 60666162288047583331496705)
            ·
              refine ⟨45499621716035687498622529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60666162288047583331496705 45499621716035687498622529)
              ·
                refine ⟨34124716287026765623966897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45499621716035687498622529 34124716287026765623966897)
                ·
                  refine ⟨25593537215270074217975173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34124716287026765623966897 25593537215270074217975173)
                  ·
                    refine ⟨4798788227863138915870345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25593537215270074217975173 4798788227863138915870345)
                    ·
                      refine ⟨3599091170897354186902759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4798788227863138915870345 3599091170897354186902759)
                      ·
                        rfl

theorem cell23_7009205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_7009205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009205 prefixEnd_7009205 := by exact prefixLift 7009205
  have htrace : WordTrace (prefixWord ++ tailWord_7009205) baseStart_7009205 baseEnd_7009205 := by
    simpa [prefixWord, tailWord_7009205, baseEnd_7009205] using wordTrace_append hprefix tailTrace_7009205
  have hstable : (prefixWord ++ tailWord_7009205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009205).length < 2 ^ (prefixWord ++ tailWord_7009205).sum := by decide
  have hdescent : baseEnd_7009205 < baseStart_7009205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009206 : List Nat := [5, 1, 4, 1, 1, 1, 1, 4, 5]
def baseStart_7009206 : Nat := 118140960795 + 7009206 * 2 ^ 59
def prefixEnd_7009206 : Nat := 4983230072969 + 3 ^ 40 * 7009206 * 2
def baseEnd_7009206 : Nat := 399899076042000964776695

theorem tailTrace_7009206 : CollatzResearch.WordTrace tailWord_7009206 prefixEnd_7009206 399899076042000964776695 := by
  unfold tailWord_7009206
  simp only [CollatzResearch.WordTrace]
  refine ⟨15977921565303200870358467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170431163363234142617156981 15977921565303200870358467)
  ·
    refine ⟨23966882347954801305537701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15977921565303200870358467 23966882347954801305537701)
    ·
      refine ⟨4493790440241525244788319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23966882347954801305537701 4493790440241525244788319)
      ·
        refine ⟨6740685660362287867182479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4493790440241525244788319 6740685660362287867182479)
        ·
          refine ⟨10111028490543431800773719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6740685660362287867182479 10111028490543431800773719)
          ·
            refine ⟨15166542735815147701160579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10111028490543431800773719 15166542735815147701160579)
            ·
              refine ⟨22749814103722721551740869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15166542735815147701160579 22749814103722721551740869)
              ·
                refine ⟨4265590144448010290951413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22749814103722721551740869 4265590144448010290951413)
                ·
                  refine ⟨399899076042000964776695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4265590144448010290951413 399899076042000964776695)
                  ·
                    rfl

theorem cell23_7009206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_7009206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009206 prefixEnd_7009206 := by exact prefixLift 7009206
  have htrace : WordTrace (prefixWord ++ tailWord_7009206) baseStart_7009206 baseEnd_7009206 := by
    simpa [prefixWord, tailWord_7009206, baseEnd_7009206] using wordTrace_append hprefix tailTrace_7009206
  have hstable : (prefixWord ++ tailWord_7009206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009206).length < 2 ^ (prefixWord ++ tailWord_7009206).sum := by decide
  have hdescent : baseEnd_7009206 < baseStart_7009206 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009228 : List Nat := [2, 2, 1, 4, 1, 1, 1, 5, 6]
def baseStart_7009228 : Nat := 118140960795 + 7009228 * 2 ^ 59
def prefixEnd_7009228 : Nat := 4983230072969 + 3 ^ 40 * 7009228 * 2
def baseEnd_7009228 : Nat := 399900331216934177435017

theorem tailTrace_7009228 : CollatzResearch.WordTrace tailWord_7009228 prefixEnd_7009228 399900331216934177435017 := by
  unfold tailWord_7009228
  simp only [CollatzResearch.WordTrace]
  refine ⟨127823773725385755841518169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170431698300514341122024225 127823773725385755841518169)
  ·
    refine ⟨95867830294039316881138627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127823773725385755841518169 95867830294039316881138627)
    ·
      refine ⟨143801745441058975321707941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95867830294039316881138627 143801745441058975321707941)
      ·
        refine ⟨26962827270198557872820239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143801745441058975321707941 26962827270198557872820239)
        ·
          refine ⟨40444240905297836809230359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26962827270198557872820239 40444240905297836809230359)
          ·
            refine ⟨60666361357946755213845539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40444240905297836809230359 60666361357946755213845539)
            ·
              refine ⟨90999542036920132820768309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60666361357946755213845539 90999542036920132820768309)
              ·
                refine ⟨8531207065961262451947029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90999542036920132820768309 8531207065961262451947029)
                ·
                  refine ⟨399900331216934177435017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8531207065961262451947029 399900331216934177435017)
                  ·
                    rfl

theorem cell23_7009228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 6].length) (baseStart_7009228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009228 prefixEnd_7009228 := by exact prefixLift 7009228
  have htrace : WordTrace (prefixWord ++ tailWord_7009228) baseStart_7009228 baseEnd_7009228 := by
    simpa [prefixWord, tailWord_7009228, baseEnd_7009228] using wordTrace_append hprefix tailTrace_7009228
  have hstable : (prefixWord ++ tailWord_7009228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009228).length < 2 ^ (prefixWord ++ tailWord_7009228).sum := by decide
  have hdescent : baseEnd_7009228 < baseStart_7009228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009242 : List Nat := [3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3]
def baseStart_7009242 : Nat := 118140960795 + 7009242 * 2 ^ 59
def prefixEnd_7009242 : Nat := 4983230072969 + 3 ^ 40 * 7009242 * 2
def baseEnd_7009242 : Nat := 3599110169681570542140089

theorem tailTrace_7009242 : CollatzResearch.WordTrace tailWord_7009242 prefixEnd_7009242 3599110169681570542140089 := by
  unfold tailWord_7009242
  simp only [CollatzResearch.WordTrace]
  refine ⟨63912014518180198018511495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170432038715147194716030653 63912014518180198018511495)
  ·
    refine ⟨95868021777270297027767243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63912014518180198018511495 95868021777270297027767243)
    ·
      refine ⟨143802032665905445541650865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95868021777270297027767243 143802032665905445541650865)
      ·
        refine ⟨107851524499429084156238149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143802032665905445541650865 107851524499429084156238149)
        ·
          refine ⟨20222160843642953279294653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107851524499429084156238149 20222160843642953279294653)
          ·
            refine ⟨7583310316366107479735495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20222160843642953279294653 7583310316366107479735495)
            ·
              refine ⟨11374965474549161219603243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7583310316366107479735495 11374965474549161219603243)
              ·
                refine ⟨17062448211823741829404865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11374965474549161219603243 17062448211823741829404865)
                ·
                  refine ⟨12796836158867806372053649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17062448211823741829404865 12796836158867806372053649)
                  ·
                    refine ⟨9597627119150854779040237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12796836158867806372053649 9597627119150854779040237)
                    ·
                      refine ⟨3599110169681570542140089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9597627119150854779040237 3599110169681570542140089)
                      ·
                        rfl

theorem cell23_7009242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_7009242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009242 prefixEnd_7009242 := by exact prefixLift 7009242
  have htrace : WordTrace (prefixWord ++ tailWord_7009242) baseStart_7009242 baseEnd_7009242 := by
    simpa [prefixWord, tailWord_7009242, baseEnd_7009242] using wordTrace_append hprefix tailTrace_7009242
  have hstable : (prefixWord ++ tailWord_7009242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009242).length < 2 ^ (prefixWord ++ tailWord_7009242).sum := by decide
  have hdescent : baseEnd_7009242 < baseStart_7009242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009262 : List Nat := [4, 1, 2, 1, 4, 2, 1, 2, 6]
def baseStart_7009262 : Nat := 118140960795 + 7009262 * 2 ^ 59
def prefixEnd_7009262 : Nat := 4983230072969 + 3 ^ 40 * 7009262 * 2
def baseEnd_7009262 : Nat := 399902271032740051543333

theorem tailTrace_7009262 : CollatzResearch.WordTrace tailWord_7009262 prefixEnd_7009262 399902271032740051543333 := by
  unfold tailWord_7009262
  simp only [CollatzResearch.WordTrace]
  refine ⟨31956098441581041936221755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170432525021765556993182693 31956098441581041936221755)
  ·
    refine ⟨47934147662371562904332633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31956098441581041936221755 47934147662371562904332633)
    ·
      refine ⟨35950610746778672178249475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47934147662371562904332633 35950610746778672178249475)
      ·
        refine ⟨53925916120168008267374213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35950610746778672178249475 53925916120168008267374213)
        ·
          refine ⟨10111109272531501550132665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53925916120168008267374213 10111109272531501550132665)
          ·
            refine ⟨7583331954398626162599499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10111109272531501550132665 7583331954398626162599499)
            ·
              refine ⟨11374997931597939243899249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7583331954398626162599499 11374997931597939243899249)
              ·
                refine ⟨8531248448698454432924437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11374997931597939243899249 8531248448698454432924437)
                ·
                  refine ⟨399902271032740051543333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8531248448698454432924437 399902271032740051543333)
                  ·
                    rfl

theorem cell23_7009262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 6].length) (baseStart_7009262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009262 prefixEnd_7009262 := by exact prefixLift 7009262
  have htrace : WordTrace (prefixWord ++ tailWord_7009262) baseStart_7009262 baseEnd_7009262 := by
    simpa [prefixWord, tailWord_7009262, baseEnd_7009262] using wordTrace_append hprefix tailTrace_7009262
  have hstable : (prefixWord ++ tailWord_7009262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009262).length < 2 ^ (prefixWord ++ tailWord_7009262).sum := by decide
  have hdescent : baseEnd_7009262 < baseStart_7009262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009271 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 1, 12]
def baseStart_7009271 : Nat := 118140960795 + 7009271 * 2 ^ 59
def prefixEnd_7009271 : Nat := 4983230072969 + 3 ^ 40 * 7009271 * 2
def baseEnd_7009271 : Nat := 1199708353540183642892485

theorem tailTrace_7009271 : CollatzResearch.WordTrace tailWord_7009271 prefixEnd_7009271 1199708353540183642892485 := by
  unfold tailWord_7009271
  simp only [CollatzResearch.WordTrace]
  refine ⟨255649115789615730026851667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170432743859743820017901111 255649115789615730026851667)
  ·
    refine ⟨383473673684423595040277501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255649115789615730026851667 383473673684423595040277501)
    ·
      refine ⟨143802627631658848140104063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383473673684423595040277501 143802627631658848140104063)
      ·
        refine ⟨215703941447488272210156095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143802627631658848140104063 215703941447488272210156095)
        ·
          refine ⟨323555912171232408315234143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215703941447488272210156095 323555912171232408315234143)
          ·
            refine ⟨485333868256848612472851215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323555912171232408315234143 485333868256848612472851215)
            ·
              refine ⟨728000802385272918709276823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485333868256848612472851215 728000802385272918709276823)
              ·
                refine ⟨1092001203577909378063915235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728000802385272918709276823 1092001203577909378063915235)
                ·
                  refine ⟨1638001805366864067095872853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1092001203577909378063915235 1638001805366864067095872853)
                  ·
                    refine ⟨1199708353540183642892485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1638001805366864067095872853 1199708353540183642892485)
                    ·
                      rfl

theorem cell23_7009271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_7009271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009271 prefixEnd_7009271 := by exact prefixLift 7009271
  have htrace : WordTrace (prefixWord ++ tailWord_7009271) baseStart_7009271 baseEnd_7009271 := by
    simpa [prefixWord, tailWord_7009271, baseEnd_7009271] using wordTrace_append hprefix tailTrace_7009271
  have hstable : (prefixWord ++ tailWord_7009271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009271).length < 2 ^ (prefixWord ++ tailWord_7009271).sum := by decide
  have hdescent : baseEnd_7009271 < baseStart_7009271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009315 : List Nat := [1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 5]
def baseStart_7009315 : Nat := 118140960795 + 7009315 * 2 ^ 59
def prefixEnd_7009315 : Nat := 4983230072969 + 3 ^ 40 * 7009315 * 2
def baseEnd_7009315 : Nat := 3599147653769348756527253

theorem tailTrace_7009315 : CollatzResearch.WordTrace tailWord_7009315 prefixEnd_7009315 3599147653769348756527253 := by
  unfold tailWord_7009315
  simp only [CollatzResearch.WordTrace]
  refine ⟨255650720601456325541453399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170433813734304217027635599 255650720601456325541453399)
  ·
    refine ⟨383476080902184488312180099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255650720601456325541453399 383476080902184488312180099)
    ·
      refine ⟨575214121353276732468270149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383476080902184488312180099 575214121353276732468270149)
      ·
        refine ⟨107852647753739387337800653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 575214121353276732468270149 107852647753739387337800653)
        ·
          refine ⟨40444742907652270251675245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107852647753739387337800653 40444742907652270251675245)
          ·
            refine ⟨15166778590369601344378217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40444742907652270251675245 15166778590369601344378217)
            ·
              refine ⟨11375083942777201008283663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15166778590369601344378217 11375083942777201008283663)
              ·
                refine ⟨17062625914165801512425495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11375083942777201008283663 17062625914165801512425495)
                ·
                  refine ⟨25593938871248702268638243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17062625914165801512425495 25593938871248702268638243)
                  ·
                    refine ⟨38390908306873053402957365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25593938871248702268638243 38390908306873053402957365)
                    ·
                      refine ⟨3599147653769348756527253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38390908306873053402957365 3599147653769348756527253)
                      ·
                        rfl

theorem cell23_7009315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_7009315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009315 prefixEnd_7009315 := by exact prefixLift 7009315
  have htrace : WordTrace (prefixWord ++ tailWord_7009315) baseStart_7009315 baseEnd_7009315 := by
    simpa [prefixWord, tailWord_7009315, baseEnd_7009315] using wordTrace_append hprefix tailTrace_7009315
  have hstable : (prefixWord ++ tailWord_7009315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009315).length < 2 ^ (prefixWord ++ tailWord_7009315).sum := by decide
  have hdescent : baseEnd_7009315 < baseStart_7009315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009332 : List Nat := [2, 5, 1, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_7009332 : Nat := 118140960795 + 7009332 * 2 ^ 59
def prefixEnd_7009332 : Nat := 4983230072969 + 3 ^ 40 * 7009332 * 2
def baseEnd_7009332 : Nat := 3599156382940475190014675

theorem tailTrace_7009332 : CollatzResearch.WordTrace tailWord_7009332 prefixEnd_7009332 3599156382940475190014675 := by
  unfold tailWord_7009332
  simp only [CollatzResearch.WordTrace]
  refine ⟨127825670321197368722411125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170434227094929824963214833 127825670321197368722411125)
  ·
    refine ⟨11983656592612253317726043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127825670321197368722411125 11983656592612253317726043)
    ·
      refine ⟨17975484888918379976589065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11983656592612253317726043 17975484888918379976589065)
      ·
        refine ⟨13481613666688784982441799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17975484888918379976589065 13481613666688784982441799)
        ·
          refine ⟨20222420500033177473662699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13481613666688784982441799 20222420500033177473662699)
          ·
            refine ⟨30333630750049766210494049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20222420500033177473662699 30333630750049766210494049)
            ·
              refine ⟨22750223062537324657870537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30333630750049766210494049 22750223062537324657870537)
              ·
                refine ⟨17062667296902993493402903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22750223062537324657870537 17062667296902993493402903)
                ·
                  refine ⟨25594000945354490240104355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17062667296902993493402903 25594000945354490240104355)
                  ·
                    refine ⟨38391001418031735360156533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25594000945354490240104355 38391001418031735360156533)
                    ·
                      refine ⟨3599156382940475190014675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38391001418031735360156533 3599156382940475190014675)
                      ·
                        rfl

theorem cell23_7009332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_7009332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009332 prefixEnd_7009332 := by exact prefixLift 7009332
  have htrace : WordTrace (prefixWord ++ tailWord_7009332) baseStart_7009332 baseEnd_7009332 := by
    simpa [prefixWord, tailWord_7009332, baseEnd_7009332] using wordTrace_append hprefix tailTrace_7009332
  have hstable : (prefixWord ++ tailWord_7009332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009332).length < 2 ^ (prefixWord ++ tailWord_7009332).sum := by decide
  have hdescent : baseEnd_7009332 < baseStart_7009332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009362 : List Nat := [3, 2, 2, 1, 3, 2, 1, 2, 1, 3, 3]
def baseStart_7009362 : Nat := 118140960795 + 7009362 * 2 ^ 59
def prefixEnd_7009362 : Nat := 4983230072969 + 3 ^ 40 * 7009362 * 2
def baseEnd_7009362 : Nat := 3599171787360110072639537

theorem tailTrace_7009362 : CollatzResearch.WordTrace tailWord_7009362 prefixEnd_7009362 3599171787360110072639537 := by
  unfold tailWord_7009362
  simp only [CollatzResearch.WordTrace]
  refine ⟨63913108708071513142103585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170434956554857368378942893 63913108708071513142103585)
  ·
    refine ⟨47934831531053634856577689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63913108708071513142103585 47934831531053634856577689)
    ·
      refine ⟨35951123648290226142433267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47934831531053634856577689 35951123648290226142433267)
      ·
        refine ⟨53926685472435339213649901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35951123648290226142433267 53926685472435339213649901)
        ·
          refine ⟨20222507052163252205118713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53926685472435339213649901 20222507052163252205118713)
          ·
            refine ⟨15166880289122439153839035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20222507052163252205118713 15166880289122439153839035)
            ·
              refine ⟨22750320433683658730758553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15166880289122439153839035 22750320433683658730758553)
              ·
                refine ⟨17062740325262744048068915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22750320433683658730758553 17062740325262744048068915)
                ·
                  refine ⟨25594110487894116072103373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17062740325262744048068915 25594110487894116072103373)
                  ·
                    refine ⟨9597791432960293527038765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25594110487894116072103373 9597791432960293527038765)
                    ·
                      refine ⟨3599171787360110072639537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9597791432960293527038765 3599171787360110072639537)
                      ·
                        rfl

theorem cell23_7009362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_7009362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009362 prefixEnd_7009362 := by exact prefixLift 7009362
  have htrace : WordTrace (prefixWord ++ tailWord_7009362) baseStart_7009362 baseEnd_7009362 := by
    simpa [prefixWord, tailWord_7009362, baseEnd_7009362] using wordTrace_append hprefix tailTrace_7009362
  have hstable : (prefixWord ++ tailWord_7009362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009362).length < 2 ^ (prefixWord ++ tailWord_7009362).sum := by decide
  have hdescent : baseEnd_7009362 < baseStart_7009362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009366 : List Nat := [5, 2, 2, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_7009366 : Nat := 118140960795 + 7009366 * 2 ^ 59
def prefixEnd_7009366 : Nat := 4983230072969 + 3 ^ 40 * 7009366 * 2
def baseEnd_7009366 : Nat := 3599173841282728056989519

theorem tailTrace_7009366 : CollatzResearch.WordTrace tailWord_7009366 prefixEnd_7009366 3599173841282728056989519 := by
  unfold tailWord_7009366
  simp only [CollatzResearch.WordTrace]
  refine ⟨15978286295266972578222497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170435053816181040834373301 15978286295266972578222497)
  ·
    refine ⟨11983714721450229433666873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15978286295266972578222497 11983714721450229433666873)
    ·
      refine ⟨8987786041087672075250155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11983714721450229433666873 8987786041087672075250155)
      ·
        refine ⟨13481679061631508112875233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8987786041087672075250155 13481679061631508112875233)
        ·
          refine ⟨10111259296223631084656425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13481679061631508112875233 10111259296223631084656425)
          ·
            refine ⟨7583444472167723313492319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10111259296223631084656425 7583444472167723313492319)
            ·
              refine ⟨11375166708251584970238479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7583444472167723313492319 11375166708251584970238479)
              ·
                refine ⟨17062750062377377455357719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11375166708251584970238479 17062750062377377455357719)
                ·
                  refine ⟨25594125093566066183036579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17062750062377377455357719 25594125093566066183036579)
                  ·
                    refine ⟨38391187640349099274554869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25594125093566066183036579 38391187640349099274554869)
                    ·
                      refine ⟨3599173841282728056989519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38391187640349099274554869 3599173841282728056989519)
                      ·
                        rfl

theorem cell23_7009366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_7009366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009366 prefixEnd_7009366 := by exact prefixLift 7009366
  have htrace : WordTrace (prefixWord ++ tailWord_7009366) baseStart_7009366 baseEnd_7009366 := by
    simpa [prefixWord, tailWord_7009366, baseEnd_7009366] using wordTrace_append hprefix tailTrace_7009366
  have hstable : (prefixWord ++ tailWord_7009366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009366).length < 2 ^ (prefixWord ++ tailWord_7009366).sum := by decide
  have hdescent : baseEnd_7009366 < baseStart_7009366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009405 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 2, 4, 3]
def baseStart_7009405 : Nat := 118140960795 + 7009405 * 2 ^ 59
def prefixEnd_7009405 : Nat := 4983230072969 + 3 ^ 40 * 7009405 * 2
def baseEnd_7009405 : Nat := 3599193867028253404401839

theorem tailTrace_7009405 : CollatzResearch.WordTrace tailWord_7009405 prefixEnd_7009405 3599193867028253404401839 := by
  unfold tailWord_7009405
  simp only [CollatzResearch.WordTrace]
  refine ⟨255654003171130270912229669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170436002114086847274819779 255654003171130270912229669)
  ·
    refine ⟨47935125594586925796043063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255654003171130270912229669 47935125594586925796043063)
    ·
      refine ⟨71902688391880388694064595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47935125594586925796043063 71902688391880388694064595)
      ·
        refine ⟨107854032587820583041096893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71902688391880388694064595 107854032587820583041096893)
        ·
          refine ⟨40445262220432718640411335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107854032587820583041096893 40445262220432718640411335)
          ·
            refine ⟨60667893330649077960617003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40445262220432718640411335 60667893330649077960617003)
            ·
              refine ⟨91001839995973616940925505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60667893330649077960617003 91001839995973616940925505)
              ·
                refine ⟨68251379996980212705694129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91001839995973616940925505 68251379996980212705694129)
                ·
                  refine ⟨51188534997735159529270597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68251379996980212705694129 51188534997735159529270597)
                  ·
                    refine ⟨9597850312075342411738237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51188534997735159529270597 9597850312075342411738237)
                    ·
                      refine ⟨3599193867028253404401839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9597850312075342411738237 3599193867028253404401839)
                      ·
                        rfl

theorem cell23_7009405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_7009405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009405 prefixEnd_7009405 := by exact prefixLift 7009405
  have htrace : WordTrace (prefixWord ++ tailWord_7009405) baseStart_7009405 baseEnd_7009405 := by
    simpa [prefixWord, tailWord_7009405, baseEnd_7009405] using wordTrace_append hprefix tailTrace_7009405
  have hstable : (prefixWord ++ tailWord_7009405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009405).length < 2 ^ (prefixWord ++ tailWord_7009405).sum := by decide
  have hdescent : baseEnd_7009405 < baseStart_7009405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009408 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 9]
def baseStart_7009408 : Nat := 118140960795 + 7009408 * 2 ^ 59
def prefixEnd_7009408 : Nat := 4983230072969 + 3 ^ 40 * 7009408 * 2
def baseEnd_7009408 : Nat := 399910600830024099184925

theorem tailTrace_7009408 : CollatzResearch.WordTrace tailWord_7009408 prefixEnd_7009408 399910600830024099184925 := by
  unfold tailWord_7009408
  simp only [CollatzResearch.WordTrace]
  refine ⟨127827056295059701212294439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170436075060079601616392585 127827056295059701212294439)
  ·
    refine ⟨191740584442589551818441659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127827056295059701212294439 191740584442589551818441659)
    ·
      refine ⟨287610876663884327727662489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191740584442589551818441659 287610876663884327727662489)
      ·
        refine ⟨215708157497913245795746867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287610876663884327727662489 215708157497913245795746867)
        ·
          refine ⟨323562236246869868693620301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215708157497913245795746867 323562236246869868693620301)
          ·
            refine ⟨121335838592576200760107613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323562236246869868693620301 121335838592576200760107613)
            ·
              refine ⟨45500939472216075285040355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121335838592576200760107613 45500939472216075285040355)
              ·
                refine ⟨68251409208324112927560533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45500939472216075285040355 68251409208324112927560533)
                ·
                  refine ⟨399910600830024099184925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68251409208324112927560533 399910600830024099184925)
                  ·
                    rfl

theorem cell23_7009408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 9].length) (baseStart_7009408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009408 prefixEnd_7009408 := by exact prefixLift 7009408
  have htrace : WordTrace (prefixWord ++ tailWord_7009408) baseStart_7009408 baseEnd_7009408 := by
    simpa [prefixWord, tailWord_7009408, baseEnd_7009408] using wordTrace_append hprefix tailTrace_7009408
  have hstable : (prefixWord ++ tailWord_7009408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009408).length < 2 ^ (prefixWord ++ tailWord_7009408).sum := by decide
  have hdescent : baseEnd_7009408 < baseStart_7009408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009436 : List Nat := [2, 2, 3, 2, 1, 2, 3, 2, 2, 2, 2]
def baseStart_7009436 : Nat := 118140960795 + 7009436 * 2 ^ 59
def prefixEnd_7009436 : Nat := 4983230072969 + 3 ^ 40 * 7009436 * 2
def baseEnd_7009436 : Nat := 3599209784928542783114197

theorem tailTrace_7009436 : CollatzResearch.WordTrace tailWord_7009436 prefixEnd_7009436 3599209784928542783114197 := by
  unfold tailWord_7009436
  simp only [CollatzResearch.WordTrace]
  refine ⟨127827566917008981603304081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170436755889345308804405441 127827566917008981603304081)
  ·
    refine ⟨95870675187756736202478061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127827566917008981603304081 95870675187756736202478061)
    ·
      refine ⟨35951503195408776075929273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95870675187756736202478061 35951503195408776075929273)
      ·
        refine ⟨26963627396556582056946955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35951503195408776075929273 26963627396556582056946955)
        ·
          refine ⟨40445441094834873085420433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26963627396556582056946955 40445441094834873085420433)
          ·
            refine ⟨30334080821126154814065325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40445441094834873085420433 30334080821126154814065325)
            ·
              refine ⟨11375280307922308055274497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30334080821126154814065325 11375280307922308055274497)
              ·
                refine ⟨8531460230941731041455873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11375280307922308055274497 8531460230941731041455873)
                ·
                  refine ⟨6398595173206298281091905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8531460230941731041455873 6398595173206298281091905)
                  ·
                    refine ⟨4798946379904723710818929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6398595173206298281091905 4798946379904723710818929)
                    ·
                      refine ⟨3599209784928542783114197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4798946379904723710818929 3599209784928542783114197)
                      ·
                        rfl

theorem cell23_7009436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_7009436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009436 prefixEnd_7009436 := by exact prefixLift 7009436
  have htrace : WordTrace (prefixWord ++ tailWord_7009436) baseStart_7009436 baseEnd_7009436 := by
    simpa [prefixWord, tailWord_7009436, baseEnd_7009436] using wordTrace_append hprefix tailTrace_7009436
  have hstable : (prefixWord ++ tailWord_7009436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009436).length < 2 ^ (prefixWord ++ tailWord_7009436).sum := by decide
  have hdescent : baseEnd_7009436 < baseStart_7009436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009453 : List Nat := [1, 5, 2, 1, 4, 1, 1, 1, 1, 4, 2]
def baseStart_7009453 : Nat := 118140960795 + 7009453 * 2 ^ 59
def prefixEnd_7009453 : Nat := 4983230072969 + 3 ^ 40 * 7009453 * 2
def baseEnd_7009453 : Nat := 3599218514099669216601619

theorem tailTrace_7009453 : CollatzResearch.WordTrace tailWord_7009453 prefixEnd_7009453 3599218514099669216601619 := by
  unfold tailWord_7009453
  simp only [CollatzResearch.WordTrace]
  refine ⟨255655753874956375109977013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170437169249970916739984675 255655753874956375109977013)
  ·
    refine ⟨23967726925777160166560345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 255655753874956375109977013 23967726925777160166560345)
    ·
      refine ⟨17975795194332870124920259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23967726925777160166560345 17975795194332870124920259)
      ·
        refine ⟨26963692791499305187380389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17975795194332870124920259 26963692791499305187380389)
        ·
          refine ⟨5055692398406119722633823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26963692791499305187380389 5055692398406119722633823)
          ·
            refine ⟨7583538597609179583950735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5055692398406119722633823 7583538597609179583950735)
            ·
              refine ⟨11375307896413769375926103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7583538597609179583950735 11375307896413769375926103)
              ·
                refine ⟨17062961844620654063889155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11375307896413769375926103 17062961844620654063889155)
                ·
                  refine ⟨25594442766930981095833733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17062961844620654063889155 25594442766930981095833733)
                  ·
                    refine ⟨4798958018799558955468825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25594442766930981095833733 4798958018799558955468825)
                    ·
                      refine ⟨3599218514099669216601619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4798958018799558955468825 3599218514099669216601619)
                      ·
                        rfl

theorem cell23_7009453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_7009453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009453 prefixEnd_7009453 := by exact prefixLift 7009453
  have htrace : WordTrace (prefixWord ++ tailWord_7009453) baseStart_7009453 baseEnd_7009453 := by
    simpa [prefixWord, tailWord_7009453, baseEnd_7009453] using wordTrace_append hprefix tailTrace_7009453
  have hstable : (prefixWord ++ tailWord_7009453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009453).length < 2 ^ (prefixWord ++ tailWord_7009453).sum := by decide
  have hdescent : baseEnd_7009453 < baseStart_7009453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009476 : List Nat := [2, 3, 3, 1, 3, 2, 1, 3, 5]
def baseStart_7009476 : Nat := 118140960795 + 7009476 * 2 ^ 59
def prefixEnd_7009476 : Nat := 4983230072969 + 3 ^ 40 * 7009476 * 2
def baseEnd_7009476 : Nat := 399914480461635847401557

theorem tailTrace_7009476 : CollatzResearch.WordTrace tailWord_7009476 prefixEnd_7009476 399914480461635847401557 := by
  unfold tailWord_7009476
  simp only [CollatzResearch.WordTrace]
  refine ⟨127828296376936525019032141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170437728502582033358709521 127828296376936525019032141)
  ·
    refine ⟨47935611141351196882137053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127828296376936525019032141 47935611141351196882137053)
    ·
      refine ⟨17975854178006698830801395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47935611141351196882137053 17975854178006698830801395)
      ·
        refine ⟨26963781267010048246202093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17975854178006698830801395 26963781267010048246202093)
        ·
          refine ⟨10111417975128768092325785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26963781267010048246202093 10111417975128768092325785)
          ·
            refine ⟨7583563481346576069244339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10111417975128768092325785 7583563481346576069244339)
            ·
              refine ⟨11375345222019864103866509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7583563481346576069244339 11375345222019864103866509)
              ·
                refine ⟨4265754458257449038949941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11375345222019864103866509 4265754458257449038949941)
                ·
                  refine ⟨399914480461635847401557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4265754458257449038949941 399914480461635847401557)
                  ·
                    rfl

theorem cell23_7009476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3, 5].length) (baseStart_7009476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009476 prefixEnd_7009476 := by exact prefixLift 7009476
  have htrace : WordTrace (prefixWord ++ tailWord_7009476) baseStart_7009476 baseEnd_7009476 := by
    simpa [prefixWord, tailWord_7009476, baseEnd_7009476] using wordTrace_append hprefix tailTrace_7009476
  have hstable : (prefixWord ++ tailWord_7009476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009476).length < 2 ^ (prefixWord ++ tailWord_7009476).sum := by decide
  have hdescent : baseEnd_7009476 < baseStart_7009476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009512 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 4, 2, 3]
def baseStart_7009512 : Nat := 118140960795 + 7009512 * 2 ^ 59
def prefixEnd_7009512 : Nat := 4983230072969 + 3 ^ 40 * 7009512 * 2
def baseEnd_7009512 : Nat := 3599248809458284485763847

theorem tailTrace_7009512 : CollatzResearch.WordTrace tailWord_7009512 prefixEnd_7009512 3599248809458284485763847 := by
  unfold tailWord_7009512
  simp only [CollatzResearch.WordTrace]
  refine ⟨127828952890871314093187395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170438603854495085457583193 127828952890871314093187395)
  ·
    refine ⟨191743429336306971139781093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127828952890871314093187395 191743429336306971139781093)
    ·
      refine ⟨35951893000557557088708955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191743429336306971139781093 35951893000557557088708955)
      ·
        refine ⟨53927839500836335633063433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35951893000557557088708955 53927839500836335633063433)
        ·
          refine ⟨40445879625627251724797575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53927839500836335633063433 40445879625627251724797575)
          ·
            refine ⟨60668819438440877587196363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40445879625627251724797575 60668819438440877587196363)
            ·
              refine ⟨91003229157661316380794545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60668819438440877587196363 91003229157661316380794545)
              ·
                refine ⟨68252421868245987285595909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91003229157661316380794545 68252421868245987285595909)
                ·
                  refine ⟨12797329100296122616049233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68252421868245987285595909 12797329100296122616049233)
                  ·
                    refine ⟨9597996825222091962036925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12797329100296122616049233 9597996825222091962036925)
                    ·
                      refine ⟨3599248809458284485763847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9597996825222091962036925 3599248809458284485763847)
                      ·
                        rfl

theorem cell23_7009512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_7009512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009512 prefixEnd_7009512 := by exact prefixLift 7009512
  have htrace : WordTrace (prefixWord ++ tailWord_7009512) baseStart_7009512 baseEnd_7009512 := by
    simpa [prefixWord, tailWord_7009512, baseEnd_7009512] using wordTrace_append hprefix tailTrace_7009512
  have hstable : (prefixWord ++ tailWord_7009512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009512).length < 2 ^ (prefixWord ++ tailWord_7009512).sum := by decide
  have hdescent : baseEnd_7009512 < baseStart_7009512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009559 : List Nat := [1, 1, 3, 4, 1, 1, 2, 3, 3, 1, 3]
def baseStart_7009559 : Nat := 118140960795 + 7009559 * 2 ^ 59
def prefixEnd_7009559 : Nat := 4983230072969 + 3 ^ 40 * 7009559 * 2
def baseEnd_7009559 : Nat := 3599272943049045801876131

theorem tailTrace_7009559 : CollatzResearch.WordTrace tailWord_7009559 prefixEnd_7009559 3599272943049045801876131 := by
  unfold tailWord_7009559
  simp only [CollatzResearch.WordTrace]
  refine ⟨255659620012572355213335731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170439746675048236808890487 255659620012572355213335731)
  ·
    refine ⟨383489430018858532820003597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255659620012572355213335731 383489430018858532820003597)
    ·
      refine ⟨143808536257071949807501349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383489430018858532820003597 143808536257071949807501349)
      ·
        refine ⟨26964100548200990588906503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143808536257071949807501349 26964100548200990588906503)
        ·
          refine ⟨40446150822301485883359755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26964100548200990588906503 40446150822301485883359755)
          ·
            refine ⟨60669226233452228825039633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40446150822301485883359755 60669226233452228825039633)
            ·
              refine ⟨45501919675089171618779725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60669226233452228825039633 45501919675089171618779725)
              ·
                refine ⟨17063219878158439357042397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45501919675089171618779725 17063219878158439357042397)
                ·
                  refine ⟨6398707454309414758890899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17063219878158439357042397 6398707454309414758890899)
                  ·
                    refine ⟨9598061181464122138336349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6398707454309414758890899 9598061181464122138336349)
                    ·
                      refine ⟨3599272943049045801876131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9598061181464122138336349 3599272943049045801876131)
                      ·
                        rfl

theorem cell23_7009559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_7009559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009559 prefixEnd_7009559 := by exact prefixLift 7009559
  have htrace : WordTrace (prefixWord ++ tailWord_7009559) baseStart_7009559 baseEnd_7009559 := by
    simpa [prefixWord, tailWord_7009559, baseEnd_7009559] using wordTrace_append hprefix tailTrace_7009559
  have hstable : (prefixWord ++ tailWord_7009559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009559).length < 2 ^ (prefixWord ++ tailWord_7009559).sum := by decide
  have hdescent : baseEnd_7009559 < baseStart_7009559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009562 : List Nat := [3, 1, 1, 3, 3, 1, 1, 2, 3, 5]
def baseStart_7009562 : Nat := 118140960795 + 7009562 * 2 ^ 59
def prefixEnd_7009562 : Nat := 4983230072969 + 3 ^ 40 * 7009562 * 2
def baseEnd_7009562 : Nat := 1199758161163669763379539

theorem tailTrace_7009562 : CollatzResearch.WordTrace tailWord_7009562 prefixEnd_7009562 1199758161163669763379539 := by
  unfold tailWord_7009562
  simp only [CollatzResearch.WordTrace]
  refine ⟨63914932357890371681423735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170439819621040991150463293 63914932357890371681423735)
  ·
    refine ⟨95872398536835557522135603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63914932357890371681423735 95872398536835557522135603)
    ·
      refine ⟨143808597805253336283203405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95872398536835557522135603 143808597805253336283203405)
      ·
        refine ⟨53928224176970001106201277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143808597805253336283203405 53928224176970001106201277)
        ·
          refine ⟨20223084066363750414825479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53928224176970001106201277 20223084066363750414825479)
          ·
            refine ⟨30334626099545625622238219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20223084066363750414825479 30334626099545625622238219)
            ·
              refine ⟨45501939149318438433357329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30334626099545625622238219 45501939149318438433357329)
              ·
                refine ⟨34126454361988828825017997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45501939149318438433357329 34126454361988828825017997)
                ·
                  refine ⟨12797420385745810809381749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34126454361988828825017997 12797420385745810809381749)
                  ·
                    refine ⟨1199758161163669763379539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12797420385745810809381749 1199758161163669763379539)
                    ·
                      rfl

theorem cell23_7009562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 3, 5].length) (baseStart_7009562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009562 prefixEnd_7009562 := by exact prefixLift 7009562
  have htrace : WordTrace (prefixWord ++ tailWord_7009562) baseStart_7009562 baseEnd_7009562 := by
    simpa [prefixWord, tailWord_7009562, baseEnd_7009562] using wordTrace_append hprefix tailTrace_7009562
  have hstable : (prefixWord ++ tailWord_7009562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009562).length < 2 ^ (prefixWord ++ tailWord_7009562).sum := by decide
  have hdescent : baseEnd_7009562 < baseStart_7009562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009576 : List Nat := [2, 1, 5, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_7009576 : Nat := 118140960795 + 7009576 * 2 ^ 59
def prefixEnd_7009576 : Nat := 4983230072969 + 3 ^ 40 * 7009576 * 2
def baseEnd_7009576 : Nat := 3599281672220172235363553

theorem tailTrace_7009576 : CollatzResearch.WordTrace tailWord_7009576 prefixEnd_7009576 3599281672220172235363553 := by
  unfold tailWord_7009576
  simp only [CollatzResearch.WordTrace]
  refine ⟨127830120026755383558352291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170440160035673844744469721 127830120026755383558352291)
  ·
    refine ⟨191745180040133075337528437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127830120026755383558352291 191745180040133075337528437)
    ·
      refine ⟨17976110628762475812893291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 191745180040133075337528437 17976110628762475812893291)
      ·
        refine ⟨26964165943143713719339937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17976110628762475812893291 26964165943143713719339937)
        ·
          refine ⟨20223124457357785289504953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26964165943143713719339937 20223124457357785289504953)
          ·
            refine ⟨15167343343018338967128715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20223124457357785289504953 15167343343018338967128715)
            ·
              refine ⟨22751015014527508450693073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15167343343018338967128715 22751015014527508450693073)
              ·
                refine ⟨17063261260895631338019805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22751015014527508450693073 17063261260895631338019805)
                ·
                  refine ⟨6398722972835861751757427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17063261260895631338019805 6398722972835861751757427)
                  ·
                    refine ⟨9598084459253792627636141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6398722972835861751757427 9598084459253792627636141)
                    ·
                      refine ⟨3599281672220172235363553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9598084459253792627636141 3599281672220172235363553)
                      ·
                        rfl

theorem cell23_7009576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_7009576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009576 prefixEnd_7009576 := by exact prefixLift 7009576
  have htrace : WordTrace (prefixWord ++ tailWord_7009576) baseStart_7009576 baseEnd_7009576 := by
    simpa [prefixWord, tailWord_7009576, baseEnd_7009576] using wordTrace_append hprefix tailTrace_7009576
  have hstable : (prefixWord ++ tailWord_7009576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009576).length < 2 ^ (prefixWord ++ tailWord_7009576).sum := by decide
  have hdescent : baseEnd_7009576 < baseStart_7009576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009586 : List Nat := [3, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2]
def baseStart_7009586 : Nat := 118140960795 + 7009586 * 2 ^ 59
def prefixEnd_7009586 : Nat := 4983230072969 + 3 ^ 40 * 7009586 * 2
def baseEnd_7009586 : Nat := 3599286807026717196238507

theorem tailTrace_7009586 : CollatzResearch.WordTrace tailWord_7009586 prefixEnd_7009586 3599286807026717196238507 := by
  unfold tailWord_7009586
  simp only [CollatzResearch.WordTrace]
  refine ⟨63915151195868634706142153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170440403188983025883045741 63915151195868634706142153)
  ·
    refine ⟨47936363396901476029606615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63915151195868634706142153 47936363396901476029606615)
    ·
      refine ⟨71904545095352214044409923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47936363396901476029606615 71904545095352214044409923)
      ·
        refine ⟨107856817643028321066614885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71904545095352214044409923 107856817643028321066614885)
        ·
          refine ⟨20223153308067810199990291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107856817643028321066614885 20223153308067810199990291)
          ·
            refine ⟨30334729962101715299985437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20223153308067810199990291 30334729962101715299985437)
            ·
              refine ⟨11375523735788143237494539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30334729962101715299985437 11375523735788143237494539)
              ·
                refine ⟨17063285603682214856241809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11375523735788143237494539 17063285603682214856241809)
                ·
                  refine ⟨12797464202761661142181357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17063285603682214856241809 12797464202761661142181357)
                  ·
                    refine ⟨4799049076035622928318009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12797464202761661142181357 4799049076035622928318009)
                    ·
                      refine ⟨3599286807026717196238507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4799049076035622928318009 3599286807026717196238507)
                      ·
                        rfl

theorem cell23_7009586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2].length) (baseStart_7009586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009586 prefixEnd_7009586 := by exact prefixLift 7009586
  have htrace : WordTrace (prefixWord ++ tailWord_7009586) baseStart_7009586 baseEnd_7009586 := by
    simpa [prefixWord, tailWord_7009586, baseEnd_7009586] using wordTrace_append hprefix tailTrace_7009586
  have hstable : (prefixWord ++ tailWord_7009586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009586).length < 2 ^ (prefixWord ++ tailWord_7009586).sum := by decide
  have hdescent : baseEnd_7009586 < baseStart_7009586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009592 : List Nat := [2, 1, 2, 1, 3, 1, 1, 4, 4, 4]
def baseStart_7009592 : Nat := 118140960795 + 7009592 * 2 ^ 59
def prefixEnd_7009592 : Nat := 4983230072969 + 3 ^ 40 * 7009592 * 2
def baseEnd_7009592 : Nat := 1199763295970214724254493

theorem tailTrace_7009592 : CollatzResearch.WordTrace tailWord_7009592 prefixEnd_7009592 1199763295970214724254493 := by
  unfold tailWord_7009592
  simp only [CollatzResearch.WordTrace]
  refine ⟨127830411810726400924643515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170440549080968534566191353 127830411810726400924643515)
  ·
    refine ⟨191745617716089601386965273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127830411810726400924643515 191745617716089601386965273)
    ·
      refine ⟨143809213287067201040223955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191745617716089601386965273 143809213287067201040223955)
      ·
        refine ⟨215713819930600801560335933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143809213287067201040223955 215713819930600801560335933)
        ·
          refine ⟨80892682473975300585125975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215713819930600801560335933 80892682473975300585125975)
          ·
            refine ⟨121339023710962950877688963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80892682473975300585125975 121339023710962950877688963)
            ·
              refine ⟨182008535566444426316533445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121339023710962950877688963 182008535566444426316533445)
              ·
                refine ⟨34126600418708329934350021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182008535566444426316533445 34126600418708329934350021)
                ·
                  refine ⟨6398737578507811862690629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34126600418708329934350021 6398737578507811862690629)
                  ·
                    refine ⟨1199763295970214724254493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6398737578507811862690629 1199763295970214724254493)
                    ·
                      rfl

theorem cell23_7009592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 4, 4].length) (baseStart_7009592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009592 prefixEnd_7009592 := by exact prefixLift 7009592
  have htrace : WordTrace (prefixWord ++ tailWord_7009592) baseStart_7009592 baseEnd_7009592 := by
    simpa [prefixWord, tailWord_7009592, baseEnd_7009592] using wordTrace_append hprefix tailTrace_7009592
  have hstable : (prefixWord ++ tailWord_7009592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009592).length < 2 ^ (prefixWord ++ tailWord_7009592).sum := by decide
  have hdescent : baseEnd_7009592 < baseStart_7009592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009595 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 4]
def baseStart_7009595 : Nat := 118140960795 + 7009595 * 2 ^ 59
def prefixEnd_7009595 : Nat := 4983230072969 + 3 ^ 40 * 7009595 * 2
def baseEnd_7009595 : Nat := 3599291428352607661025965

theorem tailTrace_7009595 : CollatzResearch.WordTrace tailWord_7009595 prefixEnd_7009595 3599291428352607661025965 := by
  unfold tailWord_7009595
  simp only [CollatzResearch.WordTrace]
  refine ⟨255660933040441933361646239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170440622026961288907764159 255660933040441933361646239)
  ·
    refine ⟨383491399560662900042469359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255660933040441933361646239 383491399560662900042469359)
    ·
      refine ⟨575237099340994350063704039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383491399560662900042469359 575237099340994350063704039)
      ·
        refine ⟨862855649011491525095556059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575237099340994350063704039 862855649011491525095556059)
        ·
          refine ⟨1294283473517237287643334089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 862855649011491525095556059 1294283473517237287643334089)
          ·
            refine ⟨970712605137927965732500567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1294283473517237287643334089 970712605137927965732500567)
            ·
              refine ⟨1456068907706891948598750851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 970712605137927965732500567 1456068907706891948598750851)
              ·
                refine ⟨2184103361560337922898126277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1456068907706891948598750851 2184103361560337922898126277)
                ·
                  refine ⟨409519380292563360543398677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2184103361560337922898126277 409519380292563360543398677)
                  ·
                    refine ⟨19196220951213907525471813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 409519380292563360543398677 19196220951213907525471813)
                    ·
                      refine ⟨3599291428352607661025965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19196220951213907525471813 3599291428352607661025965)
                      ·
                        rfl

theorem cell23_7009595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 4].length) (baseStart_7009595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009595 prefixEnd_7009595 := by exact prefixLift 7009595
  have htrace : WordTrace (prefixWord ++ tailWord_7009595) baseStart_7009595 baseEnd_7009595 := by
    simpa [prefixWord, tailWord_7009595, baseEnd_7009595] using wordTrace_append hprefix tailTrace_7009595
  have hstable : (prefixWord ++ tailWord_7009595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009595).length < 2 ^ (prefixWord ++ tailWord_7009595).sum := by decide
  have hdescent : baseEnd_7009595 < baseStart_7009595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009596 : List Nat := [2, 2, 2, 2, 1, 5, 2, 1, 1, 5]
def baseStart_7009596 : Nat := 118140960795 + 7009596 * 2 ^ 59
def prefixEnd_7009596 : Nat := 4983230072969 + 3 ^ 40 * 7009596 * 2
def baseEnd_7009596 : Nat := 1199763980611087385704487

theorem tailTrace_7009596 : CollatzResearch.WordTrace tailWord_7009596 prefixEnd_7009596 1199763980611087385704487 := by
  unfold tailWord_7009596
  simp only [CollatzResearch.WordTrace]
  refine ⟨127830484756719155266216321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170440646342292207021621761 127830484756719155266216321)
  ·
    refine ⟨95872863567539366449662241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127830484756719155266216321 95872863567539366449662241)
    ·
      refine ⟨71904647675654524837246681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95872863567539366449662241 71904647675654524837246681)
      ·
        refine ⟨53928485756740893627935011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71904647675654524837246681 53928485756740893627935011)
        ·
          refine ⟨80892728635111340441902517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53928485756740893627935011 80892728635111340441902517)
          ·
            refine ⟨7583693309541688166428361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80892728635111340441902517 7583693309541688166428361)
            ·
              refine ⟨5687769982156266124821271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7583693309541688166428361 5687769982156266124821271)
              ·
                refine ⟨8531654973234399187231907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5687769982156266124821271 8531654973234399187231907)
                ·
                  refine ⟨12797482459851598780847861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8531654973234399187231907 12797482459851598780847861)
                  ·
                    refine ⟨1199763980611087385704487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12797482459851598780847861 1199763980611087385704487)
                    ·
                      rfl

theorem cell23_7009596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_7009596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009596 prefixEnd_7009596 := by exact prefixLift 7009596
  have htrace : WordTrace (prefixWord ++ tailWord_7009596) baseStart_7009596 baseEnd_7009596 := by
    simpa [prefixWord, tailWord_7009596, baseEnd_7009596] using wordTrace_append hprefix tailTrace_7009596
  have hstable : (prefixWord ++ tailWord_7009596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009596).length < 2 ^ (prefixWord ++ tailWord_7009596).sum := by decide
  have hdescent : baseEnd_7009596 < baseStart_7009596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009599 : List Nat := [1, 1, 2, 2, 4, 3, 1, 3, 1, 1, 4]
def baseStart_7009599 : Nat := 118140960795 + 7009599 * 2 ^ 59
def prefixEnd_7009599 : Nat := 4983230072969 + 3 ^ 40 * 7009599 * 2
def baseEnd_7009599 : Nat := 3599293482275225645375947

theorem tailTrace_7009599 : CollatzResearch.WordTrace tailWord_7009599 prefixEnd_7009599 3599293482275225645375947 := by
  unfold tailWord_7009599
  simp only [CollatzResearch.WordTrace]
  refine ⟨255661078932427442044791851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170440719288284961363194567 255661078932427442044791851)
  ·
    refine ⟨383491618398641163067187777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255661078932427442044791851 383491618398641163067187777)
    ·
      refine ⟨287618713798980872300390833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383491618398641163067187777 287618713798980872300390833)
      ·
        refine ⟨215714035349235654225293125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287618713798980872300390833 215714035349235654225293125)
        ·
          refine ⟨40446381627981685167242461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215714035349235654225293125 40446381627981685167242461)
          ·
            refine ⟨15167393110493131937715923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40446381627981685167242461 15167393110493131937715923)
            ·
              refine ⟨22751089665739697906573885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15167393110493131937715923 22751089665739697906573885)
              ·
                refine ⟨8531658624652386714965207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22751089665739697906573885 8531658624652386714965207)
                ·
                  refine ⟨12797487936978580072447811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8531658624652386714965207 12797487936978580072447811)
                  ·
                    refine ⟨19196231905467870108671717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12797487936978580072447811 19196231905467870108671717)
                    ·
                      refine ⟨3599293482275225645375947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19196231905467870108671717 3599293482275225645375947)
                      ·
                        rfl

theorem cell23_7009599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 1, 4].length) (baseStart_7009599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009599 prefixEnd_7009599 := by exact prefixLift 7009599
  have htrace : WordTrace (prefixWord ++ tailWord_7009599) baseStart_7009599 baseEnd_7009599 := by
    simpa [prefixWord, tailWord_7009599, baseEnd_7009599] using wordTrace_append hprefix tailTrace_7009599
  have hstable : (prefixWord ++ tailWord_7009599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009599).length < 2 ^ (prefixWord ++ tailWord_7009599).sum := by decide
  have hdescent : baseEnd_7009599 < baseStart_7009599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009609 : List Nat := [1, 2, 1, 1, 2, 3, 5, 2, 2, 4]
def baseStart_7009609 : Nat := 118140960795 + 7009609 * 2 ^ 59
def prefixEnd_7009609 : Nat := 4983230072969 + 3 ^ 40 * 7009609 * 2
def baseEnd_7009609 : Nat := 1199766205693923535416967

theorem tailTrace_7009609 : CollatzResearch.WordTrace tailWord_7009609 prefixEnd_7009609 1199766205693923535416967 := by
  unfold tailWord_7009609
  simp only [CollatzResearch.WordTrace]
  refine ⟨255661443662391213752655881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170440962441594142501770587 255661443662391213752655881)
  ·
    refine ⟨191746082746793410314491911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255661443662391213752655881 191746082746793410314491911)
    ·
      refine ⟨287619124120190115471737867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191746082746793410314491911 287619124120190115471737867)
      ·
        refine ⟨431428686180285173207606801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287619124120190115471737867 431428686180285173207606801)
        ·
          refine ⟨323571514635213879905705101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431428686180285173207606801 323571514635213879905705101)
          ·
            refine ⟨121339317988205204964639413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323571514635213879905705101 121339317988205204964639413)
            ·
              refine ⟨11375561061394237965434945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121339317988205204964639413 11375561061394237965434945)
              ·
                refine ⟨8531670796045678474076209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11375561061394237965434945 8531670796045678474076209)
                ·
                  refine ⟨6398753097034258855557157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8531670796045678474076209 6398753097034258855557157)
                  ·
                    refine ⟨1199766205693923535416967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6398753097034258855557157 1199766205693923535416967)
                    ·
                      rfl

theorem cell23_7009609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2, 4].length) (baseStart_7009609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009609 prefixEnd_7009609 := by exact prefixLift 7009609
  have htrace : WordTrace (prefixWord ++ tailWord_7009609) baseStart_7009609 baseEnd_7009609 := by
    simpa [prefixWord, tailWord_7009609, baseEnd_7009609] using wordTrace_append hprefix tailTrace_7009609
  have hstable : (prefixWord ++ tailWord_7009609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009609).length < 2 ^ (prefixWord ++ tailWord_7009609).sum := by decide
  have hdescent : baseEnd_7009609 < baseStart_7009609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009616 : List Nat := [2, 1, 1, 1, 1, 5, 4, 1, 3, 2, 2]
def baseStart_7009616 : Nat := 118140960795 + 7009616 * 2 ^ 59
def prefixEnd_7009616 : Nat := 4983230072969 + 3 ^ 40 * 7009616 * 2
def baseEnd_7009616 : Nat := 3599302211446352078863369

theorem tailTrace_7009616 : CollatzResearch.WordTrace tailWord_7009616 prefixEnd_7009616 3599302211446352078863369 := by
  unfold tailWord_7009616
  simp only [CollatzResearch.WordTrace]
  refine ⟨127830849486682926974080351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170441132648910569298773801 127830849486682926974080351)
  ·
    refine ⟨191746274230024390461120527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127830849486682926974080351 191746274230024390461120527)
    ·
      refine ⟨287619411345036585691680791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191746274230024390461120527 287619411345036585691680791)
      ·
        refine ⟨431429117017554878537521187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287619411345036585691680791 431429117017554878537521187)
        ·
          refine ⟨647143675526332317806281781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431429117017554878537521187 647143675526332317806281781)
          ·
            refine ⟨60669719580593654794338917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 647143675526332317806281781 60669719580593654794338917)
            ·
              refine ⟨11375572421361310273938547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60669719580593654794338917 11375572421361310273938547)
              ·
                refine ⟨17063358632041965410907821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11375572421361310273938547 17063358632041965410907821)
                ·
                  refine ⟨6398759487015737029090433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17063358632041965410907821 6398759487015737029090433)
                  ·
                    refine ⟨4799069615261802771817825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6398759487015737029090433 4799069615261802771817825)
                    ·
                      refine ⟨3599302211446352078863369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4799069615261802771817825 3599302211446352078863369)
                      ·
                        rfl

theorem cell23_7009616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 3, 2, 2].length) (baseStart_7009616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009616 prefixEnd_7009616 := by exact prefixLift 7009616
  have htrace : WordTrace (prefixWord ++ tailWord_7009616) baseStart_7009616 baseEnd_7009616 := by
    simpa [prefixWord, tailWord_7009616, baseEnd_7009616] using wordTrace_append hprefix tailTrace_7009616
  have hstable : (prefixWord ++ tailWord_7009616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009616).length < 2 ^ (prefixWord ++ tailWord_7009616).sum := by decide
  have hdescent : baseEnd_7009616 < baseStart_7009616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009636 : List Nat := [2, 3, 1, 1, 3, 3, 2, 2, 1, 2, 3]
def baseStart_7009636 : Nat := 118140960795 + 7009636 * 2 ^ 59
def prefixEnd_7009636 : Nat := 4983230072969 + 3 ^ 40 * 7009636 * 2
def baseEnd_7009636 : Nat := 3599312481059442000613277

theorem tailTrace_7009636 : CollatzResearch.WordTrace tailWord_7009636 prefixEnd_7009636 3599312481059442000613277 := by
  unfold tailWord_7009636
  simp only [CollatzResearch.WordTrace]
  refine ⟨127831214216646698681944381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170441618955528931575925841 127831214216646698681944381)
  ·
    refine ⟨47936705331242512005729143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127831214216646698681944381 47936705331242512005729143)
    ·
      refine ⟨71905057996863768008593715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47936705331242512005729143 71905057996863768008593715)
      ·
        refine ⟨107857586995295652012890573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71905057996863768008593715 107857586995295652012890573)
        ·
          refine ⟨40446595123235869504833965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107857586995295652012890573 40446595123235869504833965)
          ·
            refine ⟨15167473171213451064312737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40446595123235869504833965 15167473171213451064312737)
            ·
              refine ⟨11375604878410088298234553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15167473171213451064312737 11375604878410088298234553)
              ·
                refine ⟨8531703658807566223675915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11375604878410088298234553 8531703658807566223675915)
                ·
                  refine ⟨12797555488211349335513873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8531703658807566223675915 12797555488211349335513873)
                  ·
                    refine ⟨9598166616158512001635405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12797555488211349335513873 9598166616158512001635405)
                    ·
                      refine ⟨3599312481059442000613277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9598166616158512001635405 3599312481059442000613277)
                      ·
                        rfl

theorem cell23_7009636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_7009636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009636 prefixEnd_7009636 := by exact prefixLift 7009636
  have htrace : WordTrace (prefixWord ++ tailWord_7009636) baseStart_7009636 baseEnd_7009636 := by
    simpa [prefixWord, tailWord_7009636, baseEnd_7009636] using wordTrace_append hprefix tailTrace_7009636
  have hstable : (prefixWord ++ tailWord_7009636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009636).length < 2 ^ (prefixWord ++ tailWord_7009636).sum := by decide
  have hdescent : baseEnd_7009636 < baseStart_7009636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009649 : List Nat := [1, 2, 2, 2, 1, 2, 3, 2, 4, 1, 3]
def baseStart_7009649 : Nat := 118140960795 + 7009649 * 2 ^ 59
def prefixEnd_7009649 : Nat := 4983230072969 + 3 ^ 40 * 7009649 * 2
def baseEnd_7009649 : Nat := 3599319156307950449750717

theorem tailTrace_7009649 : CollatzResearch.WordTrace tailWord_7009649 prefixEnd_7009649 3599319156307950449750717 := by
  unfold tailWord_7009649
  simp only [CollatzResearch.WordTrace]
  refine ⟨255662902582246300584112001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170441935054830867056074667 255662902582246300584112001)
  ·
    refine ⟨191747176936684725438084001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255662902582246300584112001 191747176936684725438084001)
    ·
      refine ⟨143810382702513544078563001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191747176936684725438084001 143810382702513544078563001)
      ·
        refine ⟨107857787026885158058922251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143810382702513544078563001 107857787026885158058922251)
        ·
          refine ⟨161786680540327737088383377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107857787026885158058922251 161786680540327737088383377)
          ·
            refine ⟨121340010405245802816287533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161786680540327737088383377 121340010405245802816287533)
            ·
              refine ⟨45502503901967176056107825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121340010405245802816287533 45502503901967176056107825)
              ·
                refine ⟨34126877926475382042080869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45502503901967176056107825 34126877926475382042080869)
                ·
                  refine ⟨6398789611214134132890163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34126877926475382042080869 6398789611214134132890163)
                  ·
                    refine ⟨9598184416821201199335245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6398789611214134132890163 9598184416821201199335245)
                    ·
                      refine ⟨3599319156307950449750717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9598184416821201199335245 3599319156307950449750717)
                      ·
                        rfl

theorem cell23_7009649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_7009649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009649 prefixEnd_7009649 := by exact prefixLift 7009649
  have htrace : WordTrace (prefixWord ++ tailWord_7009649) baseStart_7009649 baseEnd_7009649 := by
    simpa [prefixWord, tailWord_7009649, baseEnd_7009649] using wordTrace_append hprefix tailTrace_7009649
  have hstable : (prefixWord ++ tailWord_7009649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009649).length < 2 ^ (prefixWord ++ tailWord_7009649).sum := by decide
  have hdescent : baseEnd_7009649 < baseStart_7009649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009693 : List Nat := [1, 4, 2, 1, 3, 1, 3, 2, 1, 3, 2]
def baseStart_7009693 : Nat := 118140960795 + 7009693 * 2 ^ 59
def prefixEnd_7009693 : Nat := 4983230072969 + 3 ^ 40 * 7009693 * 2
def baseEnd_7009693 : Nat := 3599341749456748277600515

theorem tailTrace_7009693 : CollatzResearch.WordTrace tailWord_7009693 prefixEnd_7009693 3599341749456748277600515 := by
  unfold tailWord_7009693
  simp only [CollatzResearch.WordTrace]
  refine ⟨255664507394086896098713733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170443004929391264065809155 255664507394086896098713733)
  ·
    refine ⟨47937095136391293018508825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255664507394086896098713733 47937095136391293018508825)
    ·
      refine ⟨35952821352293469763881619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47937095136391293018508825 35952821352293469763881619)
      ·
        refine ⟨53929232028440204645822429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35952821352293469763881619 53929232028440204645822429)
        ·
          refine ⟨20223462010665076742183411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53929232028440204645822429 20223462010665076742183411)
          ·
            refine ⟨30335193015997615113275117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20223462010665076742183411 30335193015997615113275117)
            ·
              refine ⟨11375697380999105667478169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30335193015997615113275117 11375697380999105667478169)
              ·
                refine ⟨8531773035749329250608627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11375697380999105667478169 8531773035749329250608627)
                ·
                  refine ⟨12797659553623993875912941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8531773035749329250608627 12797659553623993875912941)
                  ·
                    refine ⟨4799122332608997703467353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12797659553623993875912941 4799122332608997703467353)
                    ·
                      refine ⟨3599341749456748277600515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4799122332608997703467353 3599341749456748277600515)
                      ·
                        rfl

theorem cell23_7009693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_7009693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009693 prefixEnd_7009693 := by exact prefixLift 7009693
  have htrace : WordTrace (prefixWord ++ tailWord_7009693) baseStart_7009693 baseEnd_7009693 := by
    simpa [prefixWord, tailWord_7009693, baseEnd_7009693] using wordTrace_append hprefix tailTrace_7009693
  have hstable : (prefixWord ++ tailWord_7009693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009693).length < 2 ^ (prefixWord ++ tailWord_7009693).sum := by decide
  have hdescent : baseEnd_7009693 < baseStart_7009693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009752 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 1, 1, 7]
def baseStart_7009752 : Nat := 118140960795 + 7009752 * 2 ^ 59
def prefixEnd_7009752 : Nat := 4983230072969 + 3 ^ 40 * 7009752 * 2
def baseEnd_7009752 : Nat := 3599372044815363546762743

theorem tailTrace_7009752 : CollatzResearch.WordTrace tailWord_7009752 prefixEnd_7009752 3599372044815363546762743 := by
  unfold tailWord_7009752
  simp only [CollatzResearch.WordTrace]
  refine ⟨127833329650436574587555755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170444439533915432783407673 127833329650436574587555755)
  ·
    refine ⟨191749994475654861881333633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127833329650436574587555755 191749994475654861881333633)
    ·
      refine ⟨143812495856741146411000225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191749994475654861881333633 143812495856741146411000225)
      ·
        refine ⟨107859371892555859808250169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143812495856741146411000225 107859371892555859808250169)
        ·
          refine ⟨80894528919416894856187627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107859371892555859808250169 80894528919416894856187627)
          ·
            refine ⟨121341793379125342284281441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80894528919416894856187627 121341793379125342284281441)
            ·
              refine ⟨91006345034344006713211081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121341793379125342284281441 91006345034344006713211081)
              ·
                refine ⟨68254758775758005034908311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91006345034344006713211081 68254758775758005034908311)
                ·
                  refine ⟨102382138163637007552362467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68254758775758005034908311 102382138163637007552362467)
                  ·
                    refine ⟨153573207245455511328543701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102382138163637007552362467 153573207245455511328543701)
                    ·
                      refine ⟨3599372044815363546762743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 153573207245455511328543701 3599372044815363546762743)
                      ·
                        rfl

theorem cell23_7009752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_7009752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009752 prefixEnd_7009752 := by exact prefixLift 7009752
  have htrace : WordTrace (prefixWord ++ tailWord_7009752) baseStart_7009752 baseEnd_7009752 := by
    simpa [prefixWord, tailWord_7009752, baseEnd_7009752] using wordTrace_append hprefix tailTrace_7009752
  have hstable : (prefixWord ++ tailWord_7009752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009752).length < 2 ^ (prefixWord ++ tailWord_7009752).sum := by decide
  have hdescent : baseEnd_7009752 < baseStart_7009752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009823 : List Nat := [1, 1, 2, 4, 1, 1, 5, 3, 1, 4]
def baseStart_7009823 : Nat := 118140960795 + 7009823 * 2 ^ 59
def prefixEnd_7009823 : Nat := 4983230072969 + 3 ^ 40 * 7009823 * 2
def baseEnd_7009823 : Nat := 1199802833980610922991639

theorem tailTrace_7009823 : CollatzResearch.WordTrace tailWord_7009823 prefixEnd_7009823 1199802833980610922991639 := by
  unfold tailWord_7009823
  simp only [CollatzResearch.WordTrace]
  refine ⟨255669248883615928300946123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170446165922410618867297415 255669248883615928300946123)
  ·
    refine ⟨383503873325423892451419185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255669248883615928300946123 383503873325423892451419185)
    ·
      refine ⟨287627904994067919338564389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383503873325423892451419185 287627904994067919338564389)
      ·
        refine ⟨53930232186387734875980823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 287627904994067919338564389 53930232186387734875980823)
        ·
          refine ⟨80895348279581602313971235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53930232186387734875980823 80895348279581602313971235)
          ·
            refine ⟨121343022419372403470956853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80895348279581602313971235 121343022419372403470956853)
            ·
              refine ⟨11375908351816162825402205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121343022419372403470956853 11375908351816162825402205)
              ·
                refine ⟨4265965631931061059525827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11375908351816162825402205 4265965631931061059525827)
                ·
                  refine ⟨6398948447896591589288741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4265965631931061059525827 6398948447896591589288741)
                  ·
                    refine ⟨1199802833980610922991639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6398948447896591589288741 1199802833980610922991639)
                    ·
                      rfl

theorem cell23_7009823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3, 1, 4].length) (baseStart_7009823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009823 prefixEnd_7009823 := by exact prefixLift 7009823
  have htrace : WordTrace (prefixWord ++ tailWord_7009823) baseStart_7009823 baseEnd_7009823 := by
    simpa [prefixWord, tailWord_7009823, baseEnd_7009823] using wordTrace_append hprefix tailTrace_7009823
  have hstable : (prefixWord ++ tailWord_7009823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009823).length < 2 ^ (prefixWord ++ tailWord_7009823).sum := by decide
  have hdescent : baseEnd_7009823 < baseStart_7009823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009856 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 6, 3, 2]
def baseStart_7009856 : Nat := 118140960795 + 7009856 * 2 ^ 59
def prefixEnd_7009856 : Nat := 4983230072969 + 3 ^ 40 * 7009856 * 2
def baseEnd_7009856 : Nat := 3599425446803431139862265

theorem tailTrace_7009856 : CollatzResearch.WordTrace tailWord_7009856 prefixEnd_7009856 3599425446803431139862265 := by
  unfold tailWord_7009856
  simp only [CollatzResearch.WordTrace]
  refine ⟨127835226246248187468448711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170446968328330916624598281 127835226246248187468448711)
  ·
    refine ⟨191752839369372281202673067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127835226246248187468448711 191752839369372281202673067)
    ·
      refine ⟨287629259054058421804009601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191752839369372281202673067 287629259054058421804009601)
      ·
        refine ⟨215721944290543816353007201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287629259054058421804009601 215721944290543816353007201)
        ·
          refine ⟨161791458217907862264755401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215721944290543816353007201 161791458217907862264755401)
          ·
            refine ⟨121343593663430896698566551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161791458217907862264755401 121343593663430896698566551)
            ·
              refine ⟨182015390495146345047849827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121343593663430896698566551 182015390495146345047849827)
              ·
                refine ⟨273023085742719517571774741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182015390495146345047849827 273023085742719517571774741)
                ·
                  refine ⟨12797957144189977386176941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 273023085742719517571774741 12797957144189977386176941)
                  ·
                    refine ⟨4799233929071241519816353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12797957144189977386176941 4799233929071241519816353)
                    ·
                      refine ⟨3599425446803431139862265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4799233929071241519816353 3599425446803431139862265)
                      ·
                        rfl

theorem cell23_7009856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 6, 3, 2].length) (baseStart_7009856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009856 prefixEnd_7009856 := by exact prefixLift 7009856
  have htrace : WordTrace (prefixWord ++ tailWord_7009856) baseStart_7009856 baseEnd_7009856 := by
    simpa [prefixWord, tailWord_7009856, baseEnd_7009856] using wordTrace_append hprefix tailTrace_7009856
  have hstable : (prefixWord ++ tailWord_7009856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009856).length < 2 ^ (prefixWord ++ tailWord_7009856).sum := by decide
  have hdescent : baseEnd_7009856 < baseStart_7009856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009873 : List Nat := [1, 2, 2, 1, 3, 2, 4, 1, 2, 3, 2]
def baseStart_7009873 : Nat := 118140960795 + 7009873 * 2 ^ 59
def prefixEnd_7009873 : Nat := 4983230072969 + 3 ^ 40 * 7009873 * 2
def baseEnd_7009873 : Nat := 3599434175974557573349687

theorem tailTrace_7009873 : CollatzResearch.WordTrace tailWord_7009873 prefixEnd_7009873 3599434175974557573349687 := by
  unfold tailWord_7009873
  simp only [CollatzResearch.WordTrace]
  refine ⟨255671072533434786840266273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170447381688956524560177515 255671072533434786840266273)
  ·
    refine ⟨191753304400076090130199705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255671072533434786840266273 191753304400076090130199705)
    ·
      refine ⟨143814978300057067597649779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191753304400076090130199705 143814978300057067597649779)
      ·
        refine ⟨215722467450085601396474669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143814978300057067597649779 215722467450085601396474669)
        ·
          refine ⟨80895925293782100523678001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215722467450085601396474669 80895925293782100523678001)
          ·
            refine ⟨60671943970336575392758501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80895925293782100523678001 60671943970336575392758501)
            ·
              refine ⟨11375989494438107886142219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60671943970336575392758501 11375989494438107886142219)
              ·
                refine ⟨17063984241657161829213329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11375989494438107886142219 17063984241657161829213329)
                ·
                  refine ⟨12797988181242871371909997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17063984241657161829213329 12797988181242871371909997)
                  ·
                    refine ⟨4799245567966076764466249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12797988181242871371909997 4799245567966076764466249)
                    ·
                      refine ⟨3599434175974557573349687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4799245567966076764466249 3599434175974557573349687)
                      ·
                        rfl

theorem cell23_7009873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 3, 2].length) (baseStart_7009873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009873 prefixEnd_7009873 := by exact prefixLift 7009873
  have htrace : WordTrace (prefixWord ++ tailWord_7009873) baseStart_7009873 baseEnd_7009873 := by
    simpa [prefixWord, tailWord_7009873, baseEnd_7009873] using wordTrace_append hprefix tailTrace_7009873
  have hstable : (prefixWord ++ tailWord_7009873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009873).length < 2 ^ (prefixWord ++ tailWord_7009873).sum := by decide
  have hdescent : baseEnd_7009873 < baseStart_7009873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009879 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 3, 6]
def baseStart_7009879 : Nat := 118140960795 + 7009879 * 2 ^ 59
def prefixEnd_7009879 : Nat := 4983230072969 + 3 ^ 40 * 7009879 * 2
def baseEnd_7009879 : Nat := 1199812418952828183291553

theorem tailTrace_7009879 : CollatzResearch.WordTrace tailWord_7009879 prefixEnd_7009879 1199812418952828183291553 := by
  unfold tailWord_7009879
  simp only [CollatzResearch.WordTrace]
  refine ⟨255671291371413049864984691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170447527580942033243323127 255671291371413049864984691)
  ·
    refine ⟨383506937057119574797477037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255671291371413049864984691 383506937057119574797477037)
    ·
      refine ⟨143815101396419840549053889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383506937057119574797477037 143815101396419840549053889)
      ·
        refine ⟨107861326047314880411790417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143815101396419840549053889 107861326047314880411790417)
        ·
          refine ⟨80895994535486160308842813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107861326047314880411790417 80895994535486160308842813)
          ·
            refine ⟨30335997950807310115816055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80895994535486160308842813 30335997950807310115816055)
            ·
              refine ⟨45503996926210965173724083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30335997950807310115816055 45503996926210965173724083)
              ·
                refine ⟨68255995389316447760586125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45503996926210965173724083 68255995389316447760586125)
                ·
                  refine ⟨25595998270993667910219797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68255995389316447760586125 25595998270993667910219797)
                  ·
                    refine ⟨1199812418952828183291553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25595998270993667910219797 1199812418952828183291553)
                    ·
                      rfl

theorem cell23_7009879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 6].length) (baseStart_7009879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009879 prefixEnd_7009879 := by exact prefixLift 7009879
  have htrace : WordTrace (prefixWord ++ tailWord_7009879) baseStart_7009879 baseEnd_7009879 := by
    simpa [prefixWord, tailWord_7009879, baseEnd_7009879] using wordTrace_append hprefix tailTrace_7009879
  have hstable : (prefixWord ++ tailWord_7009879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009879).length < 2 ^ (prefixWord ++ tailWord_7009879).sum := by decide
  have hdescent : baseEnd_7009879 < baseStart_7009879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009903 : List Nat := [1, 1, 2, 1, 3, 2, 1, 5, 3, 2, 2]
def baseStart_7009903 : Nat := 118140960795 + 7009903 * 2 ^ 59
def prefixEnd_7009903 : Nat := 4983230072969 + 3 ^ 40 * 7009903 * 2
def baseEnd_7009903 : Nat := 3599449580394192455974549

theorem tailTrace_7009903 : CollatzResearch.WordTrace tailWord_7009903 prefixEnd_7009903 3599449580394192455974549 := by
  unfold tailWord_7009903
  simp only [CollatzResearch.WordTrace]
  refine ⟨255672166723326101963858363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170448111148884067975905575 255672166723326101963858363)
  ·
    refine ⟨383508250084989152945787545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255672166723326101963858363 383508250084989152945787545)
    ·
      refine ⟨287631187563741864709340659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383508250084989152945787545 287631187563741864709340659)
      ·
        refine ⟨431446781345612797064010989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287631187563741864709340659 431446781345612797064010989)
        ·
          refine ⟨161792543004604798899004121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 431446781345612797064010989 161792543004604798899004121)
          ·
            refine ⟨121344407253453599174253091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161792543004604798899004121 121344407253453599174253091)
            ·
              refine ⟨182016610880180398761379637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121344407253453599174253091 182016610880180398761379637)
              ·
                refine ⟨17064057270016912383879341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 182016610880180398761379637 17064057270016912383879341)
                ·
                  refine ⟨6399021476256342143954753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17064057270016912383879341 6399021476256342143954753)
                  ·
                    refine ⟨4799266107192256607966065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6399021476256342143954753 4799266107192256607966065)
                    ·
                      refine ⟨3599449580394192455974549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4799266107192256607966065 3599449580394192455974549)
                      ·
                        rfl

theorem cell23_7009903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3, 2, 2].length) (baseStart_7009903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009903 prefixEnd_7009903 := by exact prefixLift 7009903
  have htrace : WordTrace (prefixWord ++ tailWord_7009903) baseStart_7009903 baseEnd_7009903 := by
    simpa [prefixWord, tailWord_7009903, baseEnd_7009903] using wordTrace_append hprefix tailTrace_7009903
  have hstable : (prefixWord ++ tailWord_7009903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009903).length < 2 ^ (prefixWord ++ tailWord_7009903).sum := by decide
  have hdescent : baseEnd_7009903 < baseStart_7009903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009954 : List Nat := [3, 3, 1, 4, 1, 1, 2, 1, 3, 2, 2]
def baseStart_7009954 : Nat := 118140960795 + 7009954 * 2 ^ 59
def prefixEnd_7009954 : Nat := 4983230072969 + 3 ^ 40 * 7009954 * 2
def baseEnd_7009954 : Nat := 3599475767907571756436815

theorem tailTrace_7009954 : CollatzResearch.WordTrace tailWord_7009954 prefixEnd_7009954 3599475767907571756436815 := by
  unfold tailWord_7009954
  simp only [CollatzResearch.WordTrace]
  refine ⟨63918506711535334418491229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170449351230760891782643277 63918506711535334418491229)
  ·
    refine ⟨23969440016825750406934211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63918506711535334418491229 23969440016825750406934211)
    ·
      refine ⟨35954160025238625610401317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23969440016825750406934211 35954160025238625610401317)
      ·
        refine ⟨6741405004732242301950247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35954160025238625610401317 6741405004732242301950247)
        ·
          refine ⟨10112107507098363452925371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6741405004732242301950247 10112107507098363452925371)
          ·
            refine ⟨15168161260647545179388057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10112107507098363452925371 15168161260647545179388057)
            ·
              refine ⟨11376120945485658884541043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15168161260647545179388057 11376120945485658884541043)
              ·
                refine ⟨17064181418228488326811565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11376120945485658884541043 17064181418228488326811565)
                ·
                  refine ⟨6399068031835683122554337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17064181418228488326811565 6399068031835683122554337)
                  ·
                    refine ⟨4799301023876762341915753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6399068031835683122554337 4799301023876762341915753)
                    ·
                      refine ⟨3599475767907571756436815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4799301023876762341915753 3599475767907571756436815)
                      ·
                        rfl

theorem cell23_7009954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_7009954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009954 prefixEnd_7009954 := by exact prefixLift 7009954
  have htrace : WordTrace (prefixWord ++ tailWord_7009954) baseStart_7009954 baseEnd_7009954 := by
    simpa [prefixWord, tailWord_7009954, baseEnd_7009954] using wordTrace_append hprefix tailTrace_7009954
  have hstable : (prefixWord ++ tailWord_7009954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009954).length < 2 ^ (prefixWord ++ tailWord_7009954).sum := by decide
  have hdescent : baseEnd_7009954 < baseStart_7009954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009979 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 5]
def baseStart_7009979 : Nat := 118140960795 + 7009979 * 2 ^ 59
def prefixEnd_7009979 : Nat := 4983230072969 + 3 ^ 40 * 7009979 * 2
def baseEnd_7009979 : Nat := 3599488604923934158624199

theorem tailTrace_7009979 : CollatzResearch.WordTrace tailWord_7009979 prefixEnd_7009979 3599488604923934158624199 := by
  unfold tailWord_7009979
  simp only [CollatzResearch.WordTrace]
  refine ⟨255674938671050766943624991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170449959114033844629083327 255674938671050766943624991)
  ·
    refine ⟨383512408006576150415437487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255674938671050766943624991 383512408006576150415437487)
    ·
      refine ⟨575268612009864225623156231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383512408006576150415437487 575268612009864225623156231)
      ·
        refine ⟨862902918014796338434734347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575268612009864225623156231 862902918014796338434734347)
        ·
          refine ⟨1294354377022194507652101521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 862902918014796338434734347 1294354377022194507652101521)
          ·
            refine ⟨970765782766645880739076141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1294354377022194507652101521 970765782766645880739076141)
            ·
              refine ⟨364037168537492205277153553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 970765782766645880739076141 364037168537492205277153553)
              ·
                refine ⟨273027876403119153957865165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 364037168537492205277153553 273027876403119153957865165)
                ·
                  refine ⟨102385453651169682734199437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 273027876403119153957865165 102385453651169682734199437)
                  ·
                    refine ⟨38394545119188631025324789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 102385453651169682734199437 38394545119188631025324789)
                    ·
                      refine ⟨3599488604923934158624199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38394545119188631025324789 3599488604923934158624199)
                      ·
                        rfl

theorem cell23_7009979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 5].length) (baseStart_7009979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009979 prefixEnd_7009979 := by exact prefixLift 7009979
  have htrace : WordTrace (prefixWord ++ tailWord_7009979) baseStart_7009979 baseEnd_7009979 := by
    simpa [prefixWord, tailWord_7009979, baseEnd_7009979] using wordTrace_append hprefix tailTrace_7009979
  have hstable : (prefixWord ++ tailWord_7009979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009979).length < 2 ^ (prefixWord ++ tailWord_7009979).sum := by decide
  have hdescent : baseEnd_7009979 < baseStart_7009979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009980 : List Nat := [2, 2, 2, 3, 1, 2, 1, 4, 1, 3, 2]
def baseStart_7009980 : Nat := 118140960795 + 7009980 * 2 ^ 59
def prefixEnd_7009980 : Nat := 4983230072969 + 3 ^ 40 * 7009980 * 2
def baseEnd_7009980 : Nat := 3599489118404588654711695

theorem tailTrace_7009980 : CollatzResearch.WordTrace tailWord_7009980 prefixEnd_7009980 3599489118404588654711695 := by
  unfold tailWord_7009980
  simp only [CollatzResearch.WordTrace]
  refine ⟨127837487572023572057205697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170449983429364762742940929 127837487572023572057205697)
  ·
    refine ⟨95878115679017679042904273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127837487572023572057205697 95878115679017679042904273)
    ·
      refine ⟨71908586759263259282178205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95878115679017679042904273 71908586759263259282178205)
      ·
        refine ⟨26965720034723722230816827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71908586759263259282178205 26965720034723722230816827)
        ·
          refine ⟨40448580052085583346225241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26965720034723722230816827 40448580052085583346225241)
          ·
            refine ⟨30336435039064187509668931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40448580052085583346225241 30336435039064187509668931)
            ·
              refine ⟨45504652558596281264503397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30336435039064187509668931 45504652558596281264503397)
              ·
                refine ⟨8532122354736802737094387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45504652558596281264503397 8532122354736802737094387)
                ·
                  refine ⟨12798183532105204105641581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8532122354736802737094387 12798183532105204105641581)
                  ·
                    refine ⟨4799318824539451539615593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12798183532105204105641581 4799318824539451539615593)
                    ·
                      refine ⟨3599489118404588654711695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4799318824539451539615593 3599489118404588654711695)
                      ·
                        rfl

theorem cell23_7009980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_7009980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009980 prefixEnd_7009980 := by exact prefixLift 7009980
  have htrace : WordTrace (prefixWord ++ tailWord_7009980) baseStart_7009980 baseEnd_7009980 := by
    simpa [prefixWord, tailWord_7009980, baseEnd_7009980] using wordTrace_append hprefix tailTrace_7009980
  have hstable : (prefixWord ++ tailWord_7009980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009980).length < 2 ^ (prefixWord ++ tailWord_7009980).sum := by decide
  have hdescent : baseEnd_7009980 < baseStart_7009980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7009999 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 9]
def baseStart_7009999 : Nat := 118140960795 + 7009999 * 2 ^ 59
def prefixEnd_7009999 : Nat := 4983230072969 + 3 ^ 40 * 7009999 * 2
def baseEnd_7009999 : Nat := 399944319393002675597123

theorem tailTrace_7009999 : CollatzResearch.WordTrace tailWord_7009999 prefixEnd_7009999 399944319393002675597123 := by
  unfold tailWord_7009999
  simp only [CollatzResearch.WordTrace]
  refine ⟨255675668130978310359353051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170450445420652206906235367 255675668130978310359353051)
  ·
    refine ⟨383513502196467465539029577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255675668130978310359353051 383513502196467465539029577)
    ·
      refine ⟨287635126647350599154272183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383513502196467465539029577 287635126647350599154272183)
      ·
        refine ⟨431452689971025898731408275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287635126647350599154272183 431452689971025898731408275)
        ·
          refine ⟨647179034956538848097112413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431452689971025898731408275 647179034956538848097112413)
          ·
            refine ⟨242692138108702068036417155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 647179034956538848097112413 242692138108702068036417155)
            ·
              refine ⟨364038207163053102054625733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242692138108702068036417155 364038207163053102054625733)
              ·
                refine ⟨68257163843072456635242325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 364038207163053102054625733 68257163843072456635242325)
                ·
                  refine ⟨399944319393002675597123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68257163843072456635242325 399944319393002675597123)
                  ·
                    rfl

theorem cell23_7009999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 9].length) (baseStart_7009999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7009999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7009999 prefixEnd_7009999 := by exact prefixLift 7009999
  have htrace : WordTrace (prefixWord ++ tailWord_7009999) baseStart_7009999 baseEnd_7009999 := by
    simpa [prefixWord, tailWord_7009999, baseEnd_7009999] using wordTrace_append hprefix tailTrace_7009999
  have hstable : (prefixWord ++ tailWord_7009999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7009999).length < 2 ^ (prefixWord ++ tailWord_7009999).sum := by decide
  have hdescent : baseEnd_7009999 < baseStart_7009999 := by decide
  rcases family_descends (prefixWord ++ tailWord_7009999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010010 : List Nat := [3, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2]
def baseStart_7010010 : Nat := 118140960795 + 7010010 * 2 ^ 59
def prefixEnd_7010010 : Nat := 4983230072969 + 3 ^ 40 * 7010010 * 2
def baseEnd_7010010 : Nat := 3599504522824223537336557

theorem tailTrace_7010010 : CollatzResearch.WordTrace tailWord_7010010 prefixEnd_7010010 3599504522824223537336557 := by
  unfold tailWord_7010010
  simp only [CollatzResearch.WordTrace]
  refine ⟨63919017333484614809500871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170450712889292306158668989 63919017333484614809500871)
  ·
    refine ⟨95878526000226922214251307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63919017333484614809500871 95878526000226922214251307)
    ·
      refine ⟨143817789000340383321376961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95878526000226922214251307 143817789000340383321376961)
      ·
        refine ⟨107863341750255287491032721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143817789000340383321376961 107863341750255287491032721)
        ·
          refine ⟨80897506312691465618274541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107863341750255287491032721 80897506312691465618274541)
          ·
            refine ⟨30336564867259299606852953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80897506312691465618274541 30336564867259299606852953)
            ·
              refine ⟨22752423650444474705139715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30336564867259299606852953 22752423650444474705139715)
              ·
                refine ⟨34128635475666712057709573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22752423650444474705139715 34128635475666712057709573)
                ·
                  refine ⟨6399119151687508510820545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34128635475666712057709573 6399119151687508510820545)
                  ·
                    refine ⟨4799339363765631383115409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6399119151687508510820545 4799339363765631383115409)
                    ·
                      refine ⟨3599504522824223537336557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4799339363765631383115409 3599504522824223537336557)
                      ·
                        rfl

theorem cell23_7010010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2].length) (baseStart_7010010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010010 prefixEnd_7010010 := by exact prefixLift 7010010
  have htrace : WordTrace (prefixWord ++ tailWord_7010010) baseStart_7010010 baseEnd_7010010 := by
    simpa [prefixWord, tailWord_7010010, baseEnd_7010010] using wordTrace_append hprefix tailTrace_7010010
  have hstable : (prefixWord ++ tailWord_7010010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010010).length < 2 ^ (prefixWord ++ tailWord_7010010).sum := by decide
  have hdescent : baseEnd_7010010 < baseStart_7010010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010016 : List Nat := [2, 1, 1, 3, 1, 2, 5, 1, 7]
def baseStart_7010016 : Nat := 118140960795 + 7010016 * 2 ^ 59
def prefixEnd_7010016 : Nat := 4983230072969 + 3 ^ 40 * 7010016 * 2
def baseEnd_7010016 : Nat := 399945289300905612651281

theorem tailTrace_7010016 : CollatzResearch.WordTrace tailWord_7010016 prefixEnd_7010016 399945289300905612651281 := by
  unfold tailWord_7010016
  simp only [CollatzResearch.WordTrace]
  refine ⟨127838144085958361131360951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170450858781277814841814601 127838144085958361131360951)
  ·
    refine ⟨191757216128937541697041427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127838144085958361131360951 191757216128937541697041427)
    ·
      refine ⟨287635824193406312545562141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191757216128937541697041427 287635824193406312545562141)
      ·
        refine ⟨107863434072527367204585803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287635824193406312545562141 107863434072527367204585803)
        ·
          refine ⟨161795151108791050806878705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107863434072527367204585803 161795151108791050806878705)
          ·
            refine ⟨121346363331593288105159029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161795151108791050806878705 121346363331593288105159029)
            ·
              refine ⟨11376221562336870759858659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121346363331593288105159029 11376221562336870759858659)
              ·
                refine ⟨17064332343505306139787989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11376221562336870759858659 17064332343505306139787989)
                ·
                  refine ⟨399945289300905612651281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17064332343505306139787989 399945289300905612651281)
                  ·
                    rfl

theorem cell23_7010016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 7].length) (baseStart_7010016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010016 prefixEnd_7010016 := by exact prefixLift 7010016
  have htrace : WordTrace (prefixWord ++ tailWord_7010016) baseStart_7010016 baseEnd_7010016 := by
    simpa [prefixWord, tailWord_7010016, baseEnd_7010016] using wordTrace_append hprefix tailTrace_7010016
  have hstable : (prefixWord ++ tailWord_7010016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010016).length < 2 ^ (prefixWord ++ tailWord_7010016).sum := by decide
  have hdescent : baseEnd_7010016 < baseStart_7010016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010027 : List Nat := [1, 1, 1, 1, 2, 4, 6, 1, 2, 2, 2]
def baseStart_7010027 : Nat := 118140960795 + 7010027 * 2 ^ 59
def prefixEnd_7010027 : Nat := 4983230072969 + 3 ^ 40 * 7010027 * 2
def baseEnd_7010027 : Nat := 3599513251995349970823979

theorem tailTrace_7010027 : CollatzResearch.WordTrace tailWord_7010027 prefixEnd_7010027 3599513251995349970823979 := by
  unfold tailWord_7010027
  simp only [CollatzResearch.WordTrace]
  refine ⟨255676689374876871141372335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170451126249917914094248223 255676689374876871141372335)
  ·
    refine ⟨383515034062315306712058503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255676689374876871141372335 383515034062315306712058503)
    ·
      refine ⟨575272551093472960068087755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383515034062315306712058503 575272551093472960068087755)
      ·
        refine ⟨862908826640209440102131633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575272551093472960068087755 862908826640209440102131633)
        ·
          refine ⟨647181619980157080076598725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 862908826640209440102131633 647181619980157080076598725)
          ·
            refine ⟨121346553746279452514362261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 647181619980157080076598725 121346553746279452514362261)
            ·
              refine ⟨5688119706856849336610731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121346553746279452514362261 5688119706856849336610731)
              ·
                refine ⟨8532179560285274004916097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5688119706856849336610731 8532179560285274004916097)
                ·
                  refine ⟨6399134670213955503687073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8532179560285274004916097 6399134670213955503687073)
                  ·
                    refine ⟨4799351002660466627765305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6399134670213955503687073 4799351002660466627765305)
                    ·
                      refine ⟨3599513251995349970823979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4799351002660466627765305 3599513251995349970823979)
                      ·
                        rfl

theorem cell23_7010027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 2, 2, 2].length) (baseStart_7010027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010027 prefixEnd_7010027 := by exact prefixLift 7010027
  have htrace : WordTrace (prefixWord ++ tailWord_7010027) baseStart_7010027 baseEnd_7010027 := by
    simpa [prefixWord, tailWord_7010027, baseEnd_7010027] using wordTrace_append hprefix tailTrace_7010027
  have hstable : (prefixWord ++ tailWord_7010027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010027).length < 2 ^ (prefixWord ++ tailWord_7010027).sum := by decide
  have hdescent : baseEnd_7010027 < baseStart_7010027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010050 : List Nat := [3, 4, 1, 1, 1, 1, 2, 5, 5]
def baseStart_7010050 : Nat := 118140960795 + 7010050 * 2 ^ 59
def prefixEnd_7010050 : Nat := 4983230072969 + 3 ^ 40 * 7010050 * 2
def baseEnd_7010050 : Nat := 399947229116711486759597

theorem tailTrace_7010050 : CollatzResearch.WordTrace tailWord_7010050 prefixEnd_7010050 399947229116711486759597 := by
  unfold tailWord_7010050
  simp only [CollatzResearch.WordTrace]
  refine ⟨63919382063448386517364901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170451685502529030712973069 63919382063448386517364901)
  ·
    refine ⟨11984884136896572472005919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63919382063448386517364901 11984884136896572472005919)
    ·
      refine ⟨17977326205344858708008879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11984884136896572472005919 17977326205344858708008879)
      ·
        refine ⟨26965989308017288062013319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17977326205344858708008879 26965989308017288062013319)
        ·
          refine ⟨40448983962025932093019979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26965989308017288062013319 40448983962025932093019979)
          ·
            refine ⟨60673475943038898139529969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40448983962025932093019979 60673475943038898139529969)
            ·
              refine ⟨45505106957279173604647477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60673475943038898139529969 45505106957279173604647477)
              ·
                refine ⟨4266103777244922525435701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45505106957279173604647477 4266103777244922525435701)
                ·
                  refine ⟨399947229116711486759597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4266103777244922525435701 399947229116711486759597)
                  ·
                    rfl

theorem cell23_7010050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_7010050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010050 prefixEnd_7010050 := by exact prefixLift 7010050
  have htrace : WordTrace (prefixWord ++ tailWord_7010050) baseStart_7010050 baseEnd_7010050 := by
    simpa [prefixWord, tailWord_7010050, baseEnd_7010050] using wordTrace_append hprefix tailTrace_7010050
  have hstable : (prefixWord ++ tailWord_7010050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010050).length < 2 ^ (prefixWord ++ tailWord_7010050).sum := by decide
  have hdescent : baseEnd_7010050 < baseStart_7010050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010056 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 3, 2, 5]
def baseStart_7010056 : Nat := 118140960795 + 7010056 * 2 ^ 59
def prefixEnd_7010056 : Nat := 4983230072969 + 3 ^ 40 * 7010056 * 2
def baseEnd_7010056 : Nat := 3599528142934330357361345

theorem tailTrace_7010056 : CollatzResearch.WordTrace tailWord_7010056 prefixEnd_7010056 3599528142934330357361345 := by
  unfold tailWord_7010056
  simp only [CollatzResearch.WordTrace]
  refine ⟨127838873545885904547089011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170451831394514539396118681 127838873545885904547089011)
  ·
    refine ⟨191758310318828856820633517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127838873545885904547089011 191758310318828856820633517)
    ·
      refine ⟨71909366369560821307737569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191758310318828856820633517 71909366369560821307737569)
      ·
        refine ⟨53932024777170615980803177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71909366369560821307737569 53932024777170615980803177)
        ·
          refine ⟨40449018582877961985602383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53932024777170615980803177 40449018582877961985602383)
          ·
            refine ⟨60673527874316942978403575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40449018582877961985602383 60673527874316942978403575)
            ·
              refine ⟨91010291811475414467605363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60673527874316942978403575 91010291811475414467605363)
              ·
                refine ⟨136515437717213121701408045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91010291811475414467605363 136515437717213121701408045)
                ·
                  refine ⟨51193289143954920638028017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136515437717213121701408045 51193289143954920638028017)
                  ·
                    refine ⟨38394966857966190478521013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51193289143954920638028017 38394966857966190478521013)
                    ·
                      refine ⟨3599528142934330357361345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38394966857966190478521013 3599528142934330357361345)
                      ·
                        rfl

theorem cell23_7010056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_7010056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010056 prefixEnd_7010056 := by exact prefixLift 7010056
  have htrace : WordTrace (prefixWord ++ tailWord_7010056) baseStart_7010056 baseEnd_7010056 := by
    simpa [prefixWord, tailWord_7010056, baseEnd_7010056] using wordTrace_append hprefix tailTrace_7010056
  have hstable : (prefixWord ++ tailWord_7010056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010056).length < 2 ^ (prefixWord ++ tailWord_7010056).sum := by decide
  have hdescent : baseEnd_7010056 < baseStart_7010056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010083 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 1, 6, 2]
def baseStart_7010083 : Nat := 118140960795 + 7010083 * 2 ^ 59
def prefixEnd_7010083 : Nat := 4983230072969 + 3 ^ 40 * 7010083 * 2
def baseEnd_7010083 : Nat := 3599542006912001751723721

theorem tailTrace_7010083 : CollatzResearch.WordTrace tailWord_7010083 prefixEnd_7010083 3599542006912001751723721 := by
  unfold tailWord_7010083
  simp only [CollatzResearch.WordTrace]
  refine ⟨255678731862673992705410903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170452487908449328470273935 255678731862673992705410903)
  ·
    refine ⟨383518097794010989058116355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255678731862673992705410903 383518097794010989058116355)
    ·
      refine ⟨575277146691016483587174533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383518097794010989058116355 575277146691016483587174533)
      ·
        refine ⟨107864465004565590672595225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 575277146691016483587174533 107864465004565590672595225)
        ·
          refine ⟨80898348753424193004446419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107864465004565590672595225 80898348753424193004446419)
          ·
            refine ⟨121347523130136289506669629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80898348753424193004446419 121347523130136289506669629)
            ·
              refine ⟨45505321173801108565001111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121347523130136289506669629 45505321173801108565001111)
              ·
                refine ⟨68257981760701662847501667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45505321173801108565001111 68257981760701662847501667)
                ·
                  refine ⟨102386972641052494271252501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68257981760701662847501667 102386972641052494271252501)
                  ·
                    refine ⟨4799389342549335668964961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 102386972641052494271252501 4799389342549335668964961)
                    ·
                      refine ⟨3599542006912001751723721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4799389342549335668964961 3599542006912001751723721)
                      ·
                        rfl

theorem cell23_7010083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 6, 2].length) (baseStart_7010083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010083 prefixEnd_7010083 := by exact prefixLift 7010083
  have htrace : WordTrace (prefixWord ++ tailWord_7010083) baseStart_7010083 baseEnd_7010083 := by
    simpa [prefixWord, tailWord_7010083, baseEnd_7010083] using wordTrace_append hprefix tailTrace_7010083
  have hstable : (prefixWord ++ tailWord_7010083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010083).length < 2 ^ (prefixWord ++ tailWord_7010083).sum := by decide
  have hdescent : baseEnd_7010083 < baseStart_7010083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010100 : List Nat := [2, 5, 1, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_7010100 : Nat := 118140960795 + 7010100 * 2 ^ 59
def prefixEnd_7010100 : Nat := 4983230072969 + 3 ^ 40 * 7010100 * 2
def baseEnd_7010100 : Nat := 3599550736083128185211143

theorem tailTrace_7010100 : CollatzResearch.WordTrace tailWord_7010100 prefixEnd_7010100 3599550736083128185211143 := by
  unfold tailWord_7010100
  simp only [CollatzResearch.WordTrace]
  refine ⟨127839675951806202304389877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170452901269074936405853169 127839675951806202304389877)
  ·
    refine ⟨11984969620481831466036551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 127839675951806202304389877 11984969620481831466036551)
    ·
      refine ⟨17977454430722747199054827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11984969620481831466036551 17977454430722747199054827)
      ·
        refine ⟨26966181646084120798582241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17977454430722747199054827 26966181646084120798582241)
        ·
          refine ⟨20224636234563090598936681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26966181646084120798582241 20224636234563090598936681)
          ·
            refine ⟨15168477175922317949202511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20224636234563090598936681 15168477175922317949202511)
            ·
              refine ⟨22752715763883476923803767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15168477175922317949202511 22752715763883476923803767)
              ·
                refine ⟨34129073645825215385705651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22752715763883476923803767 34129073645825215385705651)
                ·
                  refine ⟨51193610468737823078558477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34129073645825215385705651 51193610468737823078558477)
                  ·
                    refine ⟨19197603925776683654459429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51193610468737823078558477 19197603925776683654459429)
                    ·
                      refine ⟨3599550736083128185211143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19197603925776683654459429 3599550736083128185211143)
                      ·
                        rfl

theorem cell23_7010100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_7010100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010100 prefixEnd_7010100 := by exact prefixLift 7010100
  have htrace : WordTrace (prefixWord ++ tailWord_7010100) baseStart_7010100 baseEnd_7010100 := by
    simpa [prefixWord, tailWord_7010100, baseEnd_7010100] using wordTrace_append hprefix tailTrace_7010100
  have hstable : (prefixWord ++ tailWord_7010100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010100).length < 2 ^ (prefixWord ++ tailWord_7010100).sum := by decide
  have hdescent : baseEnd_7010100 < baseStart_7010100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010103 : List Nat := [1, 1, 3, 1, 2, 1, 2, 5, 2, 2, 3]
def baseStart_7010103 : Nat := 118140960795 + 7010103 * 2 ^ 59
def prefixEnd_7010103 : Nat := 4983230072969 + 3 ^ 40 * 7010103 * 2
def baseEnd_7010103 : Nat := 3599552276525091673473629

theorem tailTrace_7010103 : CollatzResearch.WordTrace tailWord_7010103 prefixEnd_7010103 3599552276525091673473629 := by
  unfold tailWord_7010103
  simp only [CollatzResearch.WordTrace]
  refine ⟨255679461322601536121138963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170452974215067690747425975 255679461322601536121138963)
  ·
    refine ⟨383519191983902304181708445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255679461322601536121138963 383519191983902304181708445)
    ·
      refine ⟨143819696993963364068140667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383519191983902304181708445 143819696993963364068140667)
      ·
        refine ⟨215729545490945046102211001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143819696993963364068140667 215729545490945046102211001)
        ·
          refine ⟨161797159118208784576658251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215729545490945046102211001 161797159118208784576658251)
          ·
            refine ⟨242695738677313176864987377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161797159118208784576658251 242695738677313176864987377)
            ·
              refine ⟨182021804007984882648740533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242695738677313176864987377 182021804007984882648740533)
              ·
                refine ⟨17064544125748582748319425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 182021804007984882648740533 17064544125748582748319425)
                ·
                  refine ⟨12798408094311437061239569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17064544125748582748319425 12798408094311437061239569)
                  ·
                    refine ⟨9598806070733577795929677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12798408094311437061239569 9598806070733577795929677)
                    ·
                      refine ⟨3599552276525091673473629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9598806070733577795929677 3599552276525091673473629)
                      ·
                        rfl

theorem cell23_7010103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2, 3].length) (baseStart_7010103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010103 prefixEnd_7010103 := by exact prefixLift 7010103
  have htrace : WordTrace (prefixWord ++ tailWord_7010103) baseStart_7010103 baseEnd_7010103 := by
    simpa [prefixWord, tailWord_7010103, baseEnd_7010103] using wordTrace_append hprefix tailTrace_7010103
  have hstable : (prefixWord ++ tailWord_7010103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010103).length < 2 ^ (prefixWord ++ tailWord_7010103).sum := by decide
  have hdescent : baseEnd_7010103 < baseStart_7010103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010160 : List Nat := [2, 1, 1, 1, 4, 1, 1, 5, 2, 3, 2]
def baseStart_7010160 : Nat := 118140960795 + 7010160 * 2 ^ 59
def prefixEnd_7010160 : Nat := 4983230072969 + 3 ^ 40 * 7010160 * 2
def baseEnd_7010160 : Nat := 3599581544922397950460867

theorem tailTrace_7010160 : CollatzResearch.WordTrace tailWord_7010160 prefixEnd_7010160 3599581544922397950460867 := by
  unfold tailWord_7010160
  simp only [CollatzResearch.WordTrace]
  refine ⟨127840770141697517427981967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170454360188930023237309289 127840770141697517427981967)
  ·
    refine ⟨191761155212546276141972951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127840770141697517427981967 191761155212546276141972951)
    ·
      refine ⟨287641732818819414212959427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191761155212546276141972951 287641732818819414212959427)
      ·
        refine ⟨431462599228229121319439141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287641732818819414212959427 431462599228229121319439141)
        ·
          refine ⟨80899237355292960247394839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 431462599228229121319439141 80899237355292960247394839)
          ·
            refine ⟨121348856032939440371092259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80899237355292960247394839 121348856032939440371092259)
            ·
              refine ⟨182023284049409160556638389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121348856032939440371092259 182023284049409160556638389)
              ·
                refine ⟨17064682879632108802184849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 182023284049409160556638389 17064682879632108802184849)
                ·
                  refine ⟨12798512159724081601638637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17064682879632108802184849 12798512159724081601638637)
                  ·
                    refine ⟨4799442059896530600614489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12798512159724081601638637 4799442059896530600614489)
                    ·
                      refine ⟨3599581544922397950460867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4799442059896530600614489 3599581544922397950460867)
                      ·
                        rfl

theorem cell23_7010160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 2, 3, 2].length) (baseStart_7010160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010160 prefixEnd_7010160 := by exact prefixLift 7010160
  have htrace : WordTrace (prefixWord ++ tailWord_7010160) baseStart_7010160 baseEnd_7010160 := by
    simpa [prefixWord, tailWord_7010160, baseEnd_7010160] using wordTrace_append hprefix tailTrace_7010160
  have hstable : (prefixWord ++ tailWord_7010160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010160).length < 2 ^ (prefixWord ++ tailWord_7010160).sum := by decide
  have hdescent : baseEnd_7010160 < baseStart_7010160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010173 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 5, 1, 4]
def baseStart_7010173 : Nat := 118140960795 + 7010173 * 2 ^ 59
def prefixEnd_7010173 : Nat := 4983230072969 + 3 ^ 40 * 7010173 * 2
def baseEnd_7010173 : Nat := 3599588220170906399598307

theorem tailTrace_7010173 : CollatzResearch.WordTrace tailWord_7010173 prefixEnd_7010173 3599588220170906399598307 := by
  unfold tailWord_7010173
  simp only [CollatzResearch.WordTrace]
  refine ⟨255682014432347938076187173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170454676288231958717458115 255682014432347938076187173)
  ·
    refine ⟨47940377706065238389285095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255682014432347938076187173 47940377706065238389285095)
    ·
      refine ⟨71910566559097857583927643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47940377706065238389285095 71910566559097857583927643)
      ·
        refine ⟨107865849838646786375891465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71910566559097857583927643 107865849838646786375891465)
        ·
          refine ⟨80899387378985089781918599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107865849838646786375891465 80899387378985089781918599)
          ·
            refine ⟨121349081068477634672877899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80899387378985089781918599 121349081068477634672877899)
            ·
              refine ⟨182023621602716452009316849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121349081068477634672877899 182023621602716452009316849)
              ·
                refine ⟨136517716202037339006987637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182023621602716452009316849 136517716202037339006987637)
                ·
                  refine ⟨12798535893941000531905091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 136517716202037339006987637 12798535893941000531905091)
                  ·
                    refine ⟨19197803840911500797857637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12798535893941000531905091 19197803840911500797857637)
                    ·
                      refine ⟨3599588220170906399598307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19197803840911500797857637 3599588220170906399598307)
                      ·
                        rfl

theorem cell23_7010173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_7010173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010173 prefixEnd_7010173 := by exact prefixLift 7010173
  have htrace : WordTrace (prefixWord ++ tailWord_7010173) baseStart_7010173 baseEnd_7010173 := by
    simpa [prefixWord, tailWord_7010173, baseEnd_7010173] using wordTrace_append hprefix tailTrace_7010173
  have hstable : (prefixWord ++ tailWord_7010173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010173).length < 2 ^ (prefixWord ++ tailWord_7010173).sum := by decide
  have hdescent : baseEnd_7010173 < baseStart_7010173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010184 : List Nat := [2, 1, 3, 3, 3, 2, 1, 1, 3, 1, 3]
def baseStart_7010184 : Nat := 118140960795 + 7010184 * 2 ^ 59
def prefixEnd_7010184 : Nat := 4983230072969 + 3 ^ 40 * 7010184 * 2
def baseEnd_7010184 : Nat := 3599593868458105856560757

theorem tailTrace_7010184 : CollatzResearch.WordTrace tailWord_7010184 prefixEnd_7010184 3599593868458105856560757 := by
  unfold tailWord_7010184
  simp only [CollatzResearch.WordTrace]
  refine ⟨127841207817654043477418803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170454943756872057969891737 127841207817654043477418803)
  ·
    refine ⟨191761811726481065216128205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127841207817654043477418803 191761811726481065216128205)
    ·
      refine ⟨71910679397430399456048077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191761811726481065216128205 71910679397430399456048077)
      ·
        refine ⟨26966504774036399796018029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71910679397430399456048077 26966504774036399796018029)
        ·
          refine ⟨10112439290263649923506761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26966504774036399796018029 10112439290263649923506761)
          ·
            refine ⟨7584329467697737442630071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10112439290263649923506761 7584329467697737442630071)
            ·
              refine ⟨11376494201546606163945107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7584329467697737442630071 11376494201546606163945107)
              ·
                refine ⟨17064741302319909245917661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11376494201546606163945107 17064741302319909245917661)
                ·
                  refine ⟨6399277988369965967219123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17064741302319909245917661 6399277988369965967219123)
                  ·
                    refine ⟨9598916982554948950828685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6399277988369965967219123 9598916982554948950828685)
                    ·
                      refine ⟨3599593868458105856560757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9598916982554948950828685 3599593868458105856560757)
                      ·
                        rfl

theorem cell23_7010184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_7010184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010184 prefixEnd_7010184 := by exact prefixLift 7010184
  have htrace : WordTrace (prefixWord ++ tailWord_7010184) baseStart_7010184 baseEnd_7010184 := by
    simpa [prefixWord, tailWord_7010184, baseEnd_7010184] using wordTrace_append hprefix tailTrace_7010184
  have hstable : (prefixWord ++ tailWord_7010184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010184).length < 2 ^ (prefixWord ++ tailWord_7010184).sum := by decide
  have hdescent : baseEnd_7010184 < baseStart_7010184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010193 : List Nat := [1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 5]
def baseStart_7010193 : Nat := 118140960795 + 7010193 * 2 ^ 59
def prefixEnd_7010193 : Nat := 4983230072969 + 3 ^ 40 * 7010193 * 2
def baseEnd_7010193 : Nat := 3599598489783996321348215

theorem tailTrace_7010193 : CollatzResearch.WordTrace tailWord_7010193 prefixEnd_7010193 3599598489783996321348215 := by
  unfold tailWord_7010193
  simp only [CollatzResearch.WordTrace]
  refine ⟨255682743892275481491915233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170455162594850320994610155 255682743892275481491915233)
  ·
    refine ⟨191762057919206611118936425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255682743892275481491915233 191762057919206611118936425)
    ·
      refine ⟨143821543439404958339202319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191762057919206611118936425 143821543439404958339202319)
      ·
        refine ⟨215732315159107437508803479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143821543439404958339202319 215732315159107437508803479)
        ·
          refine ⟨323598472738661156263205219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215732315159107437508803479 323598472738661156263205219)
          ·
            refine ⟨485397709107991734394807829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323598472738661156263205219 485397709107991734394807829)
            ·
              refine ⟨22753017614437112549756617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 485397709107991734394807829 22753017614437112549756617)
              ·
                refine ⟨17064763210827834412317463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22753017614437112549756617 17064763210827834412317463)
                ·
                  refine ⟨25597144816241751618476195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17064763210827834412317463 25597144816241751618476195)
                  ·
                    refine ⟨38395717224362627427714293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25597144816241751618476195 38395717224362627427714293)
                    ·
                      refine ⟨3599598489783996321348215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38395717224362627427714293 3599598489783996321348215)
                      ·
                        rfl

theorem cell23_7010193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_7010193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010193 prefixEnd_7010193 := by exact prefixLift 7010193
  have htrace : WordTrace (prefixWord ++ tailWord_7010193) baseStart_7010193 baseEnd_7010193 := by
    simpa [prefixWord, tailWord_7010193, baseEnd_7010193] using wordTrace_append hprefix tailTrace_7010193
  have hstable : (prefixWord ++ tailWord_7010193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010193).length < 2 ^ (prefixWord ++ tailWord_7010193).sum := by decide
  have hdescent : baseEnd_7010193 < baseStart_7010193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010227 : List Nat := [1, 1, 1, 2, 3, 1, 7, 1, 1, 2, 3]
def baseStart_7010227 : Nat := 118140960795 + 7010227 * 2 ^ 59
def prefixEnd_7010227 : Nat := 4983230072969 + 3 ^ 40 * 7010227 * 2
def baseEnd_7010227 : Nat := 3599615948126249188323059

theorem tailTrace_7010227 : CollatzResearch.WordTrace tailWord_7010227 prefixEnd_7010227 3599615948126249188323059 := by
  unfold tailWord_7010227
  simp only [CollatzResearch.WordTrace]
  refine ⟨255683983974152305298652935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170455989316101536865768623 255683983974152305298652935)
  ·
    refine ⟨383525975961228457947979403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255683983974152305298652935 383525975961228457947979403)
    ·
      refine ⟨575288963941842686921969105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383525975961228457947979403 575288963941842686921969105)
      ·
        refine ⟨431466722956382015191476829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 575288963941842686921969105 431466722956382015191476829)
        ·
          refine ⟨161800021108643255696803811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 431466722956382015191476829 161800021108643255696803811)
          ·
            refine ⟨242700031662964883545205717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161800021108643255696803811 242700031662964883545205717)
            ·
              refine ⟨5688281992100739458090759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 242700031662964883545205717 5688281992100739458090759)
              ·
                refine ⟨8532422988151109187136139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5688281992100739458090759 8532422988151109187136139)
                ·
                  refine ⟨12798634482226663780704209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8532422988151109187136139 12798634482226663780704209)
                  ·
                    refine ⟨9598975861669997835528157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12798634482226663780704209 9598975861669997835528157)
                    ·
                      refine ⟨3599615948126249188323059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9598975861669997835528157 3599615948126249188323059)
                      ·
                        rfl

theorem cell23_7010227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 1, 2, 3].length) (baseStart_7010227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010227 prefixEnd_7010227 := by exact prefixLift 7010227
  have htrace : WordTrace (prefixWord ++ tailWord_7010227) baseStart_7010227 baseEnd_7010227 := by
    simpa [prefixWord, tailWord_7010227, baseEnd_7010227] using wordTrace_append hprefix tailTrace_7010227
  have hstable : (prefixWord ++ tailWord_7010227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010227).length < 2 ^ (prefixWord ++ tailWord_7010227).sum := by decide
  have hdescent : baseEnd_7010227 < baseStart_7010227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010230 : List Nat := [5, 1, 4, 13]
def baseStart_7010230 : Nat := 118140960795 + 7010230 * 2 ^ 59
def prefixEnd_7010230 : Nat := 4983230072969 + 3 ^ 40 * 7010230 * 2
def baseEnd_7010230 : Nat := 1645915632632927607035

theorem tailTrace_7010230 : CollatzResearch.WordTrace tailWord_7010230 prefixEnd_7010230 1645915632632927607035 := by
  unfold tailWord_7010230
  simp only [CollatzResearch.WordTrace]
  refine ⟨15980255837071339800688259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170456062262094291207341429 15980255837071339800688259)
  ·
    refine ⟨23970383755607009701032389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15980255837071339800688259 23970383755607009701032389)
    ·
      refine ⟨4494446954176314318943573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23970383755607009701032389 4494446954176314318943573)
      ·
        refine ⟨1645915632632927607035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 4494446954176314318943573 1645915632632927607035)
        ·
          rfl

theorem cell23_7010230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 13].length) (baseStart_7010230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010230 prefixEnd_7010230 := by exact prefixLift 7010230
  have htrace : WordTrace (prefixWord ++ tailWord_7010230) baseStart_7010230 baseEnd_7010230 := by
    simpa [prefixWord, tailWord_7010230, baseEnd_7010230] using wordTrace_append hprefix tailTrace_7010230
  have hstable : (prefixWord ++ tailWord_7010230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010230).length < 2 ^ (prefixWord ++ tailWord_7010230).sum := by decide
  have hdescent : baseEnd_7010230 < baseStart_7010230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010263 : List Nat := [1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 4]
def baseStart_7010263 : Nat := 118140960795 + 7010263 * 2 ^ 59
def prefixEnd_7010263 : Nat := 4983230072969 + 3 ^ 40 * 7010263 * 2
def baseEnd_7010263 : Nat := 3599634433429811047472893

theorem tailTrace_7010263 : CollatzResearch.WordTrace tailWord_7010263 prefixEnd_7010263 3599634433429811047472893 := by
  unfold tailWord_7010263
  simp only [CollatzResearch.WordTrace]
  refine ⟨255685297002021883446963443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170456864668014588964642295 255685297002021883446963443)
  ·
    refine ⟨383527945503032825170445165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255685297002021883446963443 383527945503032825170445165)
    ·
      refine ⟨143822979563637309438916937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383527945503032825170445165 143822979563637309438916937)
      ·
        refine ⟨107867234672727982079187703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143822979563637309438916937 107867234672727982079187703)
        ·
          refine ⟨161800852009091973118781555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107867234672727982079187703 161800852009091973118781555)
          ·
            refine ⟨242701278013637959678172333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161800852009091973118781555 242701278013637959678172333)
            ·
              refine ⟨91012979255114234879314625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242701278013637959678172333 91012979255114234879314625)
              ·
                refine ⟨68259734441335676159485969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91012979255114234879314625 68259734441335676159485969)
                ·
                  refine ⟨51194800831001757119614477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68259734441335676159485969 51194800831001757119614477)
                  ·
                    refine ⟨19198050311625658919855429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51194800831001757119614477 19198050311625658919855429)
                    ·
                      refine ⟨3599634433429811047472893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19198050311625658919855429 3599634433429811047472893)
                      ·
                        rfl

theorem cell23_7010263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_7010263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010263 prefixEnd_7010263 := by exact prefixLift 7010263
  have htrace : WordTrace (prefixWord ++ tailWord_7010263) baseStart_7010263 baseEnd_7010263 := by
    simpa [prefixWord, tailWord_7010263, baseEnd_7010263] using wordTrace_append hprefix tailTrace_7010263
  have hstable : (prefixWord ++ tailWord_7010263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010263).length < 2 ^ (prefixWord ++ tailWord_7010263).sum := by decide
  have hdescent : baseEnd_7010263 < baseStart_7010263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010283 : List Nat := [1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 5]
def baseStart_7010283 : Nat := 118140960795 + 7010283 * 2 ^ 59
def prefixEnd_7010283 : Nat := 4983230072969 + 3 ^ 40 * 7010283 * 2
def baseEnd_7010283 : Nat := 3599644703042900969222801

theorem tailTrace_7010283 : CollatzResearch.WordTrace tailWord_7010283 prefixEnd_7010283 3599644703042900969222801 := by
  unfold tailWord_7010283
  simp only [CollatzResearch.WordTrace]
  refine ⟨255686026461949426862691503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170457350974632951241794335 255686026461949426862691503)
  ·
    refine ⟨383529039692924140294037255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255686026461949426862691503 383529039692924140294037255)
    ·
      refine ⟨575293559539386210441055883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383529039692924140294037255 575293559539386210441055883)
      ·
        refine ⟨862940339309079315661583825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575293559539386210441055883 862940339309079315661583825)
        ·
          refine ⟨647205254481809486746187869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 862940339309079315661583825 647205254481809486746187869)
          ·
            refine ⟨242701970430678557529820451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 647205254481809486746187869 242701970430678557529820451)
            ·
              refine ⟨364052955646017836294730677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242701970430678557529820451 364052955646017836294730677)
              ·
                refine ⟨34129964591814172152631001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 364052955646017836294730677 34129964591814172152631001)
                ·
                  refine ⟨25597473443860629114473251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34129964591814172152631001 25597473443860629114473251)
                  ·
                    refine ⟨38396210165790943671709877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25597473443860629114473251 38396210165790943671709877)
                    ·
                      refine ⟨3599644703042900969222801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38396210165790943671709877 3599644703042900969222801)
                      ·
                        rfl

theorem cell23_7010283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 1, 5].length) (baseStart_7010283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010283 prefixEnd_7010283 := by exact prefixLift 7010283
  have htrace : WordTrace (prefixWord ++ tailWord_7010283) baseStart_7010283 baseEnd_7010283 := by
    simpa [prefixWord, tailWord_7010283, baseEnd_7010283] using wordTrace_append hprefix tailTrace_7010283
  have hstable : (prefixWord ++ tailWord_7010283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010283).length < 2 ^ (prefixWord ++ tailWord_7010283).sum := by decide
  have hdescent : baseEnd_7010283 < baseStart_7010283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010308 : List Nat := [2, 3, 2, 4, 1, 1, 3, 1, 2, 1, 3]
def baseStart_7010308 : Nat := 118140960795 + 7010308 * 2 ^ 59
def prefixEnd_7010308 : Nat := 4983230072969 + 3 ^ 40 * 7010308 * 2
def baseEnd_7010308 : Nat := 3599657540059263371410187

theorem tailTrace_7010308 : CollatzResearch.WordTrace tailWord_7010308 prefixEnd_7010308 3599657540059263371410187 := by
  unfold tailWord_7010308
  simp only [CollatzResearch.WordTrace]
  refine ⟨127843469143429428066175789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170457958857905904088234385 127843469143429428066175789)
  ·
    refine ⟨47941300928786035524815921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127843469143429428066175789 47941300928786035524815921)
    ·
      refine ⟨35955975696589526643611941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47941300928786035524815921 35955975696589526643611941)
      ·
        refine ⟨6741745443110536245677239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35955975696589526643611941 6741745443110536245677239)
        ·
          refine ⟨10112618164665804368515859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6741745443110536245677239 10112618164665804368515859)
          ·
            refine ⟨15168927246998706552773789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10112618164665804368515859 15168927246998706552773789)
            ·
              refine ⟨5688347717624514957290171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15168927246998706552773789 5688347717624514957290171)
              ·
                refine ⟨8532521576436772435935257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5688347717624514957290171 8532521576436772435935257)
                ·
                  refine ⟨6399391182327579326951443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8532521576436772435935257 6399391182327579326951443)
                  ·
                    refine ⟨9599086773491368990427165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6399391182327579326951443 9599086773491368990427165)
                    ·
                      refine ⟨3599657540059263371410187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9599086773491368990427165 3599657540059263371410187)
                      ·
                        rfl

theorem cell23_7010308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_7010308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010308 prefixEnd_7010308 := by exact prefixLift 7010308
  have htrace : WordTrace (prefixWord ++ tailWord_7010308) baseStart_7010308 baseEnd_7010308 := by
    simpa [prefixWord, tailWord_7010308, baseEnd_7010308] using wordTrace_append hprefix tailTrace_7010308
  have hstable : (prefixWord ++ tailWord_7010308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010308).length < 2 ^ (prefixWord ++ tailWord_7010308).sum := by decide
  have hdescent : baseEnd_7010308 < baseStart_7010308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010354 : List Nat := [3, 2, 1, 1, 2, 4, 3, 2, 5]
def baseStart_7010354 : Nat := 118140960795 + 7010354 * 2 ^ 59
def prefixEnd_7010354 : Nat := 4983230072969 + 3 ^ 40 * 7010354 * 2
def baseEnd_7010354 : Nat := 399964573352152243492775

theorem tailTrace_7010354 : CollatzResearch.WordTrace tailWord_7010354 prefixEnd_7010354 399964573352152243492775 := by
  unfold tailWord_7010354
  simp only [CollatzResearch.WordTrace]
  refine ⟨63922154011173051497131529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170459077363128137325684077 63922154011173051497131529)
  ·
    refine ⟨47941615508379788622848647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63922154011173051497131529 47941615508379788622848647)
    ·
      refine ⟨71912423262569682934272971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47941615508379788622848647 71912423262569682934272971)
      ·
        refine ⟨107868634893854524401409457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71912423262569682934272971 107868634893854524401409457)
        ·
          refine ⟨80901476170390893301057093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107868634893854524401409457 80901476170390893301057093)
          ·
            refine ⟨15169026781948292493948205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80901476170390893301057093 15169026781948292493948205)
            ·
              refine ⟨5688385043230609685230577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15169026781948292493948205 5688385043230609685230577)
              ·
                refine ⟨4266288782422957263922933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5688385043230609685230577 4266288782422957263922933)
                ·
                  refine ⟨399964573352152243492775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4266288782422957263922933 399964573352152243492775)
                  ·
                    rfl

theorem cell23_7010354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2, 5].length) (baseStart_7010354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010354 prefixEnd_7010354 := by exact prefixLift 7010354
  have htrace : WordTrace (prefixWord ++ tailWord_7010354) baseStart_7010354 baseEnd_7010354 := by
    simpa [prefixWord, tailWord_7010354, baseEnd_7010354] using wordTrace_append hprefix tailTrace_7010354
  have hstable : (prefixWord ++ tailWord_7010354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010354).length < 2 ^ (prefixWord ++ tailWord_7010354).sum := by decide
  have hdescent : baseEnd_7010354 < baseStart_7010354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010407 : List Nat := [1, 1, 5, 1, 1, 2, 1, 4, 2, 2, 3]
def baseStart_7010407 : Nat := 118140960795 + 7010407 * 2 ^ 59
def prefixEnd_7010407 : Nat := 4983230072969 + 3 ^ 40 * 7010407 * 2
def baseEnd_7010407 : Nat := 3599708374644058484072231

theorem tailTrace_7010407 : CollatzResearch.WordTrace tailWord_7010407 prefixEnd_7010407 3599708374644058484072231 := by
  unfold tailWord_7010407
  simp only [CollatzResearch.WordTrace]
  refine ⟨255690549113500196040205475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170460366075666797360136983 255690549113500196040205475)
  ·
    refine ⟨383535823670250294060308213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255690549113500196040205475 383535823670250294060308213)
    ·
      refine ⟨35956483469085965068153895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 383535823670250294060308213 35956483469085965068153895)
      ·
        refine ⟨53934725203628947602230843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35956483469085965068153895 53934725203628947602230843)
        ·
          refine ⟨80902087805443421403346265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53934725203628947602230843 80902087805443421403346265)
          ·
            refine ⟨60676565854082566052509699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80902087805443421403346265 60676565854082566052509699)
            ·
              refine ⟨91014848781123849078764549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60676565854082566052509699 91014848781123849078764549)
              ·
                refine ⟨17065284146460721702268353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91014848781123849078764549 17065284146460721702268353)
                ·
                  refine ⟨12798963109845541276701265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17065284146460721702268353 12798963109845541276701265)
                  ·
                    refine ⟨9599222332384155957525949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12798963109845541276701265 9599222332384155957525949)
                    ·
                      refine ⟨3599708374644058484072231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9599222332384155957525949 3599708374644058484072231)
                      ·
                        rfl

theorem cell23_7010407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_7010407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010407 prefixEnd_7010407 := by exact prefixLift 7010407
  have htrace : WordTrace (prefixWord ++ tailWord_7010407) baseStart_7010407 baseEnd_7010407 := by
    simpa [prefixWord, tailWord_7010407, baseEnd_7010407] using wordTrace_append hprefix tailTrace_7010407
  have hstable : (prefixWord ++ tailWord_7010407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010407).length < 2 ^ (prefixWord ++ tailWord_7010407).sum := by decide
  have hdescent : baseEnd_7010407 < baseStart_7010407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010478 : List Nat := [4, 1, 4, 2, 1, 1, 3, 1, 6]
def baseStart_7010478 : Nat := 118140960795 + 7010478 * 2 ^ 59
def prefixEnd_7010478 : Nat := 4983230072969 + 3 ^ 40 * 7010478 * 2
def baseEnd_7010478 : Nat := 399971647974503078476045

theorem tailTrace_7010478 : CollatzResearch.WordTrace tailWord_7010478 prefixEnd_7010478 399971647974503078476045 := by
  unfold tailWord_7010478
  simp only [CollatzResearch.WordTrace]
  refine ⟨31961642337030371895755011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170462092464161983444026725 31961642337030371895755011)
  ·
    refine ⟨47942463505545557843632517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31961642337030371895755011 47942463505545557843632517)
    ·
      refine ⟨8989211907289792095681097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47942463505545557843632517 8989211907289792095681097)
      ·
        refine ⟨6741908930467344071760823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8989211907289792095681097 6741908930467344071760823)
        ·
          refine ⟨10112863395701016107641235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6741908930467344071760823 10112863395701016107641235)
          ·
            refine ⟨15169295093551524161461853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10112863395701016107641235 15169295093551524161461853)
            ·
              refine ⟨5688485660081821560548195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15169295093551524161461853 5688485660081821560548195)
              ·
                refine ⟨8532728490122732340822293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5688485660081821560548195 8532728490122732340822293)
                ·
                  refine ⟨399971647974503078476045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8532728490122732340822293 399971647974503078476045)
                  ·
                    rfl

theorem cell23_7010478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 6].length) (baseStart_7010478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010478 prefixEnd_7010478 := by exact prefixLift 7010478
  have htrace : WordTrace (prefixWord ++ tailWord_7010478) baseStart_7010478 baseEnd_7010478 := by
    simpa [prefixWord, tailWord_7010478, baseEnd_7010478] using wordTrace_append hprefix tailTrace_7010478
  have hstable : (prefixWord ++ tailWord_7010478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010478).length < 2 ^ (prefixWord ++ tailWord_7010478).sum := by decide
  have hdescent : baseEnd_7010478 < baseStart_7010478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010487 : List Nat := [1, 1, 3, 1, 4, 2, 3, 1, 1, 6]
def baseStart_7010487 : Nat := 118140960795 + 7010487 * 2 ^ 59
def prefixEnd_7010487 : Nat := 4983230072969 + 3 ^ 40 * 7010487 * 2
def baseEnd_7010487 : Nat := 1199916484365472723690621

theorem tailTrace_7010487 : CollatzResearch.WordTrace tailWord_7010487 prefixEnd_7010487 1199916484365472723690621 := by
  unfold tailWord_7010487
  simp only [CollatzResearch.WordTrace]
  refine ⟨255693466953210369703117715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170462311302140246468745143 255693466953210369703117715)
  ·
    refine ⟨383540200429815554554676573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255693466953210369703117715 383540200429815554554676573)
    ·
      refine ⟨143827575161180832958003715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383540200429815554554676573 143827575161180832958003715)
      ·
        refine ⟨215741362741771249437005573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143827575161180832958003715 215741362741771249437005573)
        ·
          refine ⟨40451505514082109269438545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215741362741771249437005573 40451505514082109269438545)
          ·
            refine ⟨30338629135561581952078909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40451505514082109269438545 30338629135561581952078909)
            ·
              refine ⟨11376985925835593232029591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30338629135561581952078909 11376985925835593232029591)
              ·
                refine ⟨17065478888753389848044387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11376985925835593232029591 17065478888753389848044387)
                ·
                  refine ⟨25598218333130084772066581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17065478888753389848044387 25598218333130084772066581)
                  ·
                    refine ⟨1199916484365472723690621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25598218333130084772066581 1199916484365472723690621)
                    ·
                      rfl

theorem cell23_7010487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 6].length) (baseStart_7010487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010487 prefixEnd_7010487 := by exact prefixLift 7010487
  have htrace : WordTrace (prefixWord ++ tailWord_7010487) baseStart_7010487 baseEnd_7010487 := by
    simpa [prefixWord, tailWord_7010487, baseEnd_7010487] using wordTrace_append hprefix tailTrace_7010487
  have hstable : (prefixWord ++ tailWord_7010487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010487).length < 2 ^ (prefixWord ++ tailWord_7010487).sum := by decide
  have hdescent : baseEnd_7010487 < baseStart_7010487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010498 : List Nat := [3, 5, 1, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_7010498 : Nat := 118140960795 + 7010498 * 2 ^ 59
def prefixEnd_7010498 : Nat := 4983230072969 + 3 ^ 40 * 7010498 * 2
def baseEnd_7010498 : Nat := 3599755101383617628034313

theorem tailTrace_7010498 : CollatzResearch.WordTrace tailWord_7010498 prefixEnd_7010498 3599755101383617628034313 := by
  unfold tailWord_7010498
  simp only [CollatzResearch.WordTrace]
  refine ⟨63923467039042629645442037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170462578770780345721178765 63923467039042629645442037)
  ·
    refine ⟨5992825034910246529260191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63923467039042629645442037 5992825034910246529260191)
    ·
      refine ⟨8989237552365369793890287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5992825034910246529260191 8989237552365369793890287)
      ·
        refine ⟨13483856328548054690835431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8989237552365369793890287 13483856328548054690835431)
        ·
          refine ⟨20225784492822082036253147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13483856328548054690835431 20225784492822082036253147)
          ·
            refine ⟨30338676739233123054379721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20225784492822082036253147 30338676739233123054379721)
            ·
              refine ⟨22754007554424842290784791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30338676739233123054379721 22754007554424842290784791)
              ·
                refine ⟨34131011331637263436177187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22754007554424842290784791 34131011331637263436177187)
                ·
                  refine ⟨51196516997455895154265781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34131011331637263436177187 51196516997455895154265781)
                  ·
                    refine ⟨4799673468511490170712417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51196516997455895154265781 4799673468511490170712417)
                    ·
                      refine ⟨3599755101383617628034313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4799673468511490170712417 3599755101383617628034313)
                      ·
                        rfl

theorem cell23_7010498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_7010498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010498 prefixEnd_7010498 := by exact prefixLift 7010498
  have htrace : WordTrace (prefixWord ++ tailWord_7010498) baseStart_7010498 baseEnd_7010498 := by
    simpa [prefixWord, tailWord_7010498, baseEnd_7010498] using wordTrace_append hprefix tailTrace_7010498
  have hstable : (prefixWord ++ tailWord_7010498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010498).length < 2 ^ (prefixWord ++ tailWord_7010498).sum := by decide
  have hdescent : baseEnd_7010498 < baseStart_7010498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010514 : List Nat := [3, 2, 2, 2, 1, 3, 2, 1, 1, 1, 5]
def baseStart_7010514 : Nat := 118140960795 + 7010514 * 2 ^ 59
def prefixEnd_7010514 : Nat := 4983230072969 + 3 ^ 40 * 7010514 * 2
def baseEnd_7010514 : Nat := 3599763317074089565434239

theorem tailTrace_7010514 : CollatzResearch.WordTrace tailWord_7010514 prefixEnd_7010514 3599763317074089565434239 := by
  unfold tailWord_7010514
  simp only [CollatzResearch.WordTrace]
  refine ⟨63923612931028138328587649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170462967816075035542900397 63923612931028138328587649)
  ·
    refine ⟨47942709698271103746440737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63923612931028138328587649 47942709698271103746440737)
    ·
      refine ⟨35957032273703327809830553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47942709698271103746440737 35957032273703327809830553)
      ·
        refine ⟨26967774205277495857372915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35957032273703327809830553 26967774205277495857372915)
        ·
          refine ⟨40451661307916243786059373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26967774205277495857372915 40451661307916243786059373)
          ·
            refine ⟨15169372990468591419772265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40451661307916243786059373 15169372990468591419772265)
            ·
              refine ⟨11377029742851443564829199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15169372990468591419772265 11377029742851443564829199)
              ·
                refine ⟨17065544614277165347243799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11377029742851443564829199 17065544614277165347243799)
                ·
                  refine ⟨25598316921415748020865699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17065544614277165347243799 25598316921415748020865699)
                  ·
                    refine ⟨38397475382123622031298549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25598316921415748020865699 38397475382123622031298549)
                    ·
                      refine ⟨3599763317074089565434239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38397475382123622031298549 3599763317074089565434239)
                      ·
                        rfl

theorem cell23_7010514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_7010514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010514 prefixEnd_7010514 := by exact prefixLift 7010514
  have htrace : WordTrace (prefixWord ++ tailWord_7010514) baseStart_7010514 baseEnd_7010514 := by
    simpa [prefixWord, tailWord_7010514, baseEnd_7010514] using wordTrace_append hprefix tailTrace_7010514
  have hstable : (prefixWord ++ tailWord_7010514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010514).length < 2 ^ (prefixWord ++ tailWord_7010514).sum := by decide
  have hdescent : baseEnd_7010514 < baseStart_7010514 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010584 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 3, 4, 2]
def baseStart_7010584 : Nat := 118140960795 + 7010584 * 2 ^ 59
def prefixEnd_7010584 : Nat := 4983230072969 + 3 ^ 40 * 7010584 * 2
def baseEnd_7010584 : Nat := 3599799260719904291558917

theorem tailTrace_7010584 : CollatzResearch.WordTrace tailWord_7010584 prefixEnd_7010584 3599799260719904291558917 := by
  unfold tailWord_7010584
  simp only [CollatzResearch.WordTrace]
  refine ⟨127848502416929477634699403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170464669889239303512932537 127848502416929477634699403)
  ·
    refine ⟨191772753625394216452049105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127848502416929477634699403 191772753625394216452049105)
    ·
      refine ⟨143829565219045662339036829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191772753625394216452049105 143829565219045662339036829)
      ·
        refine ⟨53936086957142123377138811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143829565219045662339036829 53936086957142123377138811)
        ·
          refine ⟨80904130435713185065708217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53936086957142123377138811 80904130435713185065708217)
          ·
            refine ⟨60678097826784888799281163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80904130435713185065708217 60678097826784888799281163)
            ·
              refine ⟨91017146740177333198921745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60678097826784888799281163 91017146740177333198921745)
              ·
                refine ⟨68262860055132999899191309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91017146740177333198921745 68262860055132999899191309)
                ·
                  refine ⟨25598572520674874962196741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68262860055132999899191309 25598572520674874962196741)
                  ·
                    refine ⟨4799732347626539055411889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25598572520674874962196741 4799732347626539055411889)
                    ·
                      refine ⟨3599799260719904291558917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4799732347626539055411889 3599799260719904291558917)
                      ·
                        rfl

theorem cell23_7010584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_7010584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010584 prefixEnd_7010584 := by exact prefixLift 7010584
  have htrace : WordTrace (prefixWord ++ tailWord_7010584) baseStart_7010584 baseEnd_7010584 := by
    simpa [prefixWord, tailWord_7010584, baseEnd_7010584] using wordTrace_append hprefix tailTrace_7010584
  have hstable : (prefixWord ++ tailWord_7010584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010584).length < 2 ^ (prefixWord ++ tailWord_7010584).sum := by decide
  have hdescent : baseEnd_7010584 < baseStart_7010584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010587 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 2, 4, 3]
def baseStart_7010587 : Nat := 118140960795 + 7010587 * 2 ^ 59
def prefixEnd_7010587 : Nat := 4983230072969 + 3 ^ 40 * 7010587 * 2
def baseEnd_7010587 : Nat := 3599800801161867779821403

theorem tailTrace_7010587 : CollatzResearch.WordTrace tailWord_7010587 prefixEnd_7010587 3599800801161867779821403 := by
  unfold tailWord_7010587
  simp only [CollatzResearch.WordTrace]
  refine ⟨255697114252848086781758015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170464742835232057854505343 255697114252848086781758015)
  ·
    refine ⟨383545671379272130172637023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255697114252848086781758015 383545671379272130172637023)
    ·
      refine ⟨575318507068908195258955535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383545671379272130172637023 575318507068908195258955535)
      ·
        refine ⟨862977760603362292888433303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575318507068908195258955535 862977760603362292888433303)
        ·
          refine ⟨1294466640905043439332649955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 862977760603362292888433303 1294466640905043439332649955)
          ·
            refine ⟨1941699961357565158998974933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1294466640905043439332649955 1941699961357565158998974933)
            ·
              refine ⟨45508592844317933414038475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1941699961357565158998974933 45508592844317933414038475)
              ·
                refine ⟨68262889266476900121057713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45508592844317933414038475 68262889266476900121057713)
                ·
                  refine ⟨51197166949857675090793285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68262889266476900121057713 51197166949857675090793285)
                  ·
                    refine ⟨9599468803098314079523741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51197166949857675090793285 9599468803098314079523741)
                    ·
                      refine ⟨3599800801161867779821403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9599468803098314079523741 3599800801161867779821403)
                      ·
                        rfl

theorem cell23_7010587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4, 3].length) (baseStart_7010587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010587 prefixEnd_7010587 := by exact prefixLift 7010587
  have htrace : WordTrace (prefixWord ++ tailWord_7010587) baseStart_7010587 baseEnd_7010587 := by
    simpa [prefixWord, tailWord_7010587, baseEnd_7010587] using wordTrace_append hprefix tailTrace_7010587
  have hstable : (prefixWord ++ tailWord_7010587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010587).length < 2 ^ (prefixWord ++ tailWord_7010587).sum := by decide
  have hdescent : baseEnd_7010587 < baseStart_7010587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010594 : List Nat := [3, 3, 1, 1, 3, 2, 1, 1, 2, 6]
def baseStart_7010594 : Nat := 118140960795 + 7010594 * 2 ^ 59
def prefixEnd_7010594 : Nat := 4983230072969 + 3 ^ 40 * 7010594 * 2
def baseEnd_7010594 : Nat := 1199934798508816417477957

theorem tailTrace_7010594 : CollatzResearch.WordTrace tailWord_7010594 prefixEnd_7010594 1199934798508816417477957 := by
  unfold tailWord_7010594
  simp only [CollatzResearch.WordTrace]
  refine ⟨63924342390955681744315709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170464913042548484651508557 63924342390955681744315709)
  ·
    refine ⟨23971628396608380654118391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63924342390955681744315709 23971628396608380654118391)
    ·
      refine ⟨35957442594912570981177587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23971628396608380654118391 35957442594912570981177587)
      ·
        refine ⟨53936163892368856471766381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35957442594912570981177587 53936163892368856471766381)
        ·
          refine ⟨20226061459638321176912393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53936163892368856471766381 20226061459638321176912393)
          ·
            refine ⟨15169546094728740882684295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20226061459638321176912393 15169546094728740882684295)
            ·
              refine ⟨22754319142093111324026443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15169546094728740882684295 22754319142093111324026443)
              ·
                refine ⟨34131478713139666986039665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22754319142093111324026443 34131478713139666986039665)
                ·
                  refine ⟨25598609034854750239529749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34131478713139666986039665 25598609034854750239529749)
                  ·
                    refine ⟨1199934798508816417477957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25598609034854750239529749 1199934798508816417477957)
                    ·
                      rfl

theorem cell23_7010594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_7010594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010594 prefixEnd_7010594 := by exact prefixLift 7010594
  have htrace : WordTrace (prefixWord ++ tailWord_7010594) baseStart_7010594 baseEnd_7010594 := by
    simpa [prefixWord, tailWord_7010594, baseEnd_7010594] using wordTrace_append hprefix tailTrace_7010594
  have hstable : (prefixWord ++ tailWord_7010594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010594).length < 2 ^ (prefixWord ++ tailWord_7010594).sum := by decide
  have hdescent : baseEnd_7010594 < baseStart_7010594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010647 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 7]
def baseStart_7010647 : Nat := 118140960795 + 7010647 * 2 ^ 59
def prefixEnd_7010647 : Nat := 4983230072969 + 3 ^ 40 * 7010647 * 2
def baseEnd_7010647 : Nat := 3599831610001137545071127

theorem tailTrace_7010647 : CollatzResearch.WordTrace tailWord_7010647 prefixEnd_7010647 3599831610001137545071127 := by
  unfold tailWord_7010647
  simp only [CollatzResearch.WordTrace]
  refine ⟨255699302632630717028942195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170466201755087144685961463 255699302632630717028942195)
  ·
    refine ⟨383548953948946075543413293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255699302632630717028942195 383548953948946075543413293)
    ·
      refine ⟨143830857730854778328779985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383548953948946075543413293 143830857730854778328779985)
      ·
        refine ⟨107873143298141083746584989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143830857730854778328779985 107873143298141083746584989)
        ·
          refine ⟨40452428736802906404969371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107873143298141083746584989 40452428736802906404969371)
          ·
            refine ⟨60678643105204359607454057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40452428736802906404969371 60678643105204359607454057)
            ·
              refine ⟨45508982328903269705590543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60678643105204359607454057 45508982328903269705590543)
              ·
                refine ⟨68263473493354904558385815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45508982328903269705590543 68263473493354904558385815)
                ·
                  refine ⟨102395210240032356837578723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68263473493354904558385815 102395210240032356837578723)
                  ·
                    refine ⟨153592815360048535256368085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102395210240032356837578723 153592815360048535256368085)
                    ·
                      refine ⟨3599831610001137545071127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 153592815360048535256368085 3599831610001137545071127)
                      ·
                        rfl

theorem cell23_7010647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_7010647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010647 prefixEnd_7010647 := by exact prefixLift 7010647
  have htrace : WordTrace (prefixWord ++ tailWord_7010647) baseStart_7010647 baseEnd_7010647 := by
    simpa [prefixWord, tailWord_7010647, baseEnd_7010647] using wordTrace_append hprefix tailTrace_7010647
  have hstable : (prefixWord ++ tailWord_7010647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010647).length < 2 ^ (prefixWord ++ tailWord_7010647).sum := by decide
  have hdescent : baseEnd_7010647 < baseStart_7010647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010652 : List Nat := [2, 2, 4, 3, 2, 1, 1, 1, 1, 4, 2]
def baseStart_7010652 : Nat := 118140960795 + 7010652 * 2 ^ 59
def prefixEnd_7010652 : Nat := 4983230072969 + 3 ^ 40 * 7010652 * 2
def baseEnd_7010652 : Nat := 3599834177404410025508605

theorem tailTrace_7010652 : CollatzResearch.WordTrace tailWord_7010652 prefixEnd_7010652 3599834177404410025508605 := by
  unfold tailWord_7010652
  simp only [CollatzResearch.WordTrace]
  refine ⟨127849742498806301441437105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170466323331741735255249473 127849742498806301441437105)
  ·
    refine ⟨95887306874104726081077829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127849742498806301441437105 95887306874104726081077829)
    ·
      refine ⟨17978870038894636140202093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95887306874104726081077829 17978870038894636140202093)
      ·
        refine ⟨6742076264585488552575785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17978870038894636140202093 6742076264585488552575785)
        ·
          refine ⟨5056557198439116414431839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6742076264585488552575785 5056557198439116414431839)
          ·
            refine ⟨7584835797658674621647759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5056557198439116414431839 7584835797658674621647759)
            ·
              refine ⟨11377253696488011932471639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7584835797658674621647759 11377253696488011932471639)
              ·
                refine ⟨17065880544732017898707459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11377253696488011932471639 17065880544732017898707459)
                ·
                  refine ⟨25598820817098026848061189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17065880544732017898707459 25598820817098026848061189)
                  ·
                    refine ⟨4799778903205880034011473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25598820817098026848061189 4799778903205880034011473)
                    ·
                      refine ⟨3599834177404410025508605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4799778903205880034011473 3599834177404410025508605)
                      ·
                        rfl

theorem cell23_7010652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_7010652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010652 prefixEnd_7010652 := by exact prefixLift 7010652
  have htrace : WordTrace (prefixWord ++ tailWord_7010652) baseStart_7010652 baseEnd_7010652 := by
    simpa [prefixWord, tailWord_7010652, baseEnd_7010652] using wordTrace_append hprefix tailTrace_7010652
  have hstable : (prefixWord ++ tailWord_7010652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010652).length < 2 ^ (prefixWord ++ tailWord_7010652).sum := by decide
  have hdescent : baseEnd_7010652 < baseStart_7010652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010674 : List Nat := [3, 2, 1, 2, 1, 3, 2, 1, 1, 3, 4]
def baseStart_7010674 : Nat := 118140960795 + 7010674 * 2 ^ 59
def prefixEnd_7010674 : Nat := 4983230072969 + 3 ^ 40 * 7010674 * 2
def baseEnd_7010674 : Nat := 3599845473978808939433503

theorem tailTrace_7010674 : CollatzResearch.WordTrace tailWord_7010674 prefixEnd_7010674 3599845473978808939433503 := by
  unfold tailWord_7010674
  simp only [CollatzResearch.WordTrace]
  refine ⟨63925071850883225160043769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170466858269021933760116717 63925071850883225160043769)
  ·
    refine ⟨47943803888162418870032827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63925071850883225160043769 47943803888162418870032827)
    ·
      refine ⟨71915705832243628305049241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47943803888162418870032827 71915705832243628305049241)
      ·
        refine ⟨53936779374182721228786931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71915705832243628305049241 53936779374182721228786931)
        ·
          refine ⟨80905169061274081843180397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53936779374182721228786931 80905169061274081843180397)
          ·
            refine ⟨30339438397977780691192649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80905169061274081843180397 30339438397977780691192649)
            ·
              refine ⟨22754578798483335518394487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30339438397977780691192649 22754578798483335518394487)
              ·
                refine ⟨34131868197725003277591731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22754578798483335518394487 34131868197725003277591731)
                ·
                  refine ⟨51197802296587504916387597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34131868197725003277591731 51197802296587504916387597)
                  ·
                    refine ⟨19199175861220314343645349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51197802296587504916387597 19199175861220314343645349)
                    ·
                      refine ⟨3599845473978808939433503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19199175861220314343645349 3599845473978808939433503)
                      ·
                        rfl

theorem cell23_7010674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_7010674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010674 prefixEnd_7010674 := by exact prefixLift 7010674
  have htrace : WordTrace (prefixWord ++ tailWord_7010674) baseStart_7010674 baseEnd_7010674 := by
    simpa [prefixWord, tailWord_7010674, baseEnd_7010674] using wordTrace_append hprefix tailTrace_7010674
  have hstable : (prefixWord ++ tailWord_7010674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010674).length < 2 ^ (prefixWord ++ tailWord_7010674).sum := by decide
  have hdescent : baseEnd_7010674 < baseStart_7010674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010687 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 4]
def baseStart_7010687 : Nat := 118140960795 + 7010687 * 2 ^ 59
def prefixEnd_7010687 : Nat := 4983230072969 + 3 ^ 40 * 7010687 * 2
def baseEnd_7010687 : Nat := 3599852149227317388570943

theorem tailTrace_7010687 : CollatzResearch.WordTrace tailWord_7010687 prefixEnd_7010687 3599852149227317388570943 := by
  unfold tailWord_7010687
  simp only [CollatzResearch.WordTrace]
  refine ⟨255700761552485803860398315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170467174368323869240265543 255700761552485803860398315)
  ·
    refine ⟨383551142328728705790597473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255700761552485803860398315 383551142328728705790597473)
    ·
      refine ⟨287663356746546529342948105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383551142328728705790597473 287663356746546529342948105)
      ·
        refine ⟨215747517559909897007211079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287663356746546529342948105 215747517559909897007211079)
        ·
          refine ⟨323621276339864845510816619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215747517559909897007211079 323621276339864845510816619)
          ·
            refine ⟨485431914509797268266224929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323621276339864845510816619 485431914509797268266224929)
            ·
              refine ⟨364073935882347951199668697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 485431914509797268266224929 364073935882347951199668697)
              ·
                refine ⟨273055451911760963399751523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 364073935882347951199668697 273055451911760963399751523)
                ·
                  refine ⟨409583177867641445099627285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 273055451911760963399751523 409583177867641445099627285)
                  ·
                    refine ⟨19199211462545692739045029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 409583177867641445099627285 19199211462545692739045029)
                    ·
                      refine ⟨3599852149227317388570943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19199211462545692739045029 3599852149227317388570943)
                      ·
                        rfl

theorem cell23_7010687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_7010687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010687 prefixEnd_7010687 := by exact prefixLift 7010687
  have htrace : WordTrace (prefixWord ++ tailWord_7010687) baseStart_7010687 baseEnd_7010687 := by
    simpa [prefixWord, tailWord_7010687, baseEnd_7010687] using wordTrace_append hprefix tailTrace_7010687
  have hstable : (prefixWord ++ tailWord_7010687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010687).length < 2 ^ (prefixWord ++ tailWord_7010687).sum := by decide
  have hdescent : baseEnd_7010687 < baseStart_7010687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010691 : List Nat := [1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 4]
def baseStart_7010691 : Nat := 118140960795 + 7010691 * 2 ^ 59
def prefixEnd_7010691 : Nat := 4983230072969 + 3 ^ 40 * 7010691 * 2
def baseEnd_7010691 : Nat := 3599854203149935372920925

theorem tailTrace_7010691 : CollatzResearch.WordTrace tailWord_7010691 prefixEnd_7010691 3599854203149935372920925 := by
  unfold tailWord_7010691
  simp only [CollatzResearch.WordTrace]
  refine ⟨255700907444471312543543927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170467271629647541695695951 255700907444471312543543927)
  ·
    refine ⟨383551361166706968815315891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255700907444471312543543927 383551361166706968815315891)
    ·
      refine ⟨575327041750060453222973837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383551361166706968815315891 575327041750060453222973837)
      ·
        refine ⟨215747640656272669958615189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 575327041750060453222973837 215747640656272669958615189)
        ·
          refine ⟨10113170655762781404310087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 215747640656272669958615189 10113170655762781404310087)
          ·
            refine ⟨15169755983644172106465131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10113170655762781404310087 15169755983644172106465131)
            ·
              refine ⟨22754633975466258159697697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15169755983644172106465131 22754633975466258159697697)
              ·
                refine ⟨17065975481599693619773273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22754633975466258159697697 17065975481599693619773273)
                ·
                  refine ⟨12799481611199770214829955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17065975481599693619773273 12799481611199770214829955)
                  ·
                    refine ⟨19199222416799655322244933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12799481611199770214829955 19199222416799655322244933)
                    ·
                      refine ⟨3599854203149935372920925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19199222416799655322244933 3599854203149935372920925)
                      ·
                        rfl

theorem cell23_7010691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 4].length) (baseStart_7010691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010691 prefixEnd_7010691 := by exact prefixLift 7010691
  have htrace : WordTrace (prefixWord ++ tailWord_7010691) baseStart_7010691 baseEnd_7010691 := by
    simpa [prefixWord, tailWord_7010691, baseEnd_7010691] using wordTrace_append hprefix tailTrace_7010691
  have hstable : (prefixWord ++ tailWord_7010691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010691).length < 2 ^ (prefixWord ++ tailWord_7010691).sum := by decide
  have hdescent : baseEnd_7010691 < baseStart_7010691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010724 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 2, 5, 3]
def baseStart_7010724 : Nat := 118140960795 + 7010724 * 2 ^ 59
def prefixEnd_7010724 : Nat := 4983230072969 + 3 ^ 40 * 7010724 * 2
def baseEnd_7010724 : Nat := 3599871148011533743808273

theorem tailTrace_7010724 : CollatzResearch.WordTrace tailWord_7010724 prefixEnd_7010724 3599871148011533743808273 := by
  unfold tailWord_7010724
  simp only [CollatzResearch.WordTrace]
  refine ⟨127851055526675879589747613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170468074035567839452996817 127851055526675879589747613)
  ·
    refine ⟨47944145822503454846155355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127851055526675879589747613 47944145822503454846155355)
    ·
      refine ⟨71916218733755182269233033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47944145822503454846155355 71916218733755182269233033)
      ·
        refine ⟨53937164050316386701924775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71916218733755182269233033 53937164050316386701924775)
        ·
          refine ⟨80905746075474580052887163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53937164050316386701924775 80905746075474580052887163)
          ·
            refine ⟨121358619113211870079330745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80905746075474580052887163 121358619113211870079330745)
            ·
              refine ⟨91018964334908902559498059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121358619113211870079330745 91018964334908902559498059)
              ·
                refine ⟨136528446502363353839247089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91018964334908902559498059 136528446502363353839247089)
                ·
                  refine ⟨102396334876772515379435317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136528446502363353839247089 102396334876772515379435317)
                  ·
                    refine ⟨9599656394697423316822061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102396334876772515379435317 9599656394697423316822061)
                    ·
                      refine ⟨3599871148011533743808273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9599656394697423316822061 3599871148011533743808273)
                      ·
                        rfl

theorem cell23_7010724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_7010724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010724 prefixEnd_7010724 := by exact prefixLift 7010724
  have htrace : WordTrace (prefixWord ++ tailWord_7010724) baseStart_7010724 baseEnd_7010724 := by
    simpa [prefixWord, tailWord_7010724, baseEnd_7010724] using wordTrace_append hprefix tailTrace_7010724
  have hstable : (prefixWord ++ tailWord_7010724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010724).length < 2 ^ (prefixWord ++ tailWord_7010724).sum := by decide
  have hdescent : baseEnd_7010724 < baseStart_7010724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010728 : List Nat := [2, 1, 6, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_7010728 : Nat := 118140960795 + 7010728 * 2 ^ 59
def prefixEnd_7010728 : Nat := 4983230072969 + 3 ^ 40 * 7010728 * 2
def baseEnd_7010728 : Nat := 3599873201934151728158255

theorem tailTrace_7010728 : CollatzResearch.WordTrace tailWord_7010728 prefixEnd_7010728 3599873201934151728158255 := by
  unfold tailWord_7010728
  simp only [CollatzResearch.WordTrace]
  refine ⟨127851128472668633931320419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170468171296891511908427225 127851128472668633931320419)
  ·
    refine ⟨191776692709002950896980629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127851128472668633931320419 191776692709002950896980629)
    ·
      refine ⟨8989532470734513323295967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 191776692709002950896980629 8989532470734513323295967)
      ·
        refine ⟨13484298706101769984943951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8989532470734513323295967 13484298706101769984943951)
        ·
          refine ⟨20226448059152654977415927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13484298706101769984943951 20226448059152654977415927)
          ·
            refine ⟨30339672088728982466123891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20226448059152654977415927 30339672088728982466123891)
            ·
              refine ⟨45509508133093473699185837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30339672088728982466123891 45509508133093473699185837)
              ·
                refine ⟨17066065549910052637194689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45509508133093473699185837 17066065549910052637194689)
                ·
                  refine ⟨12799549162432539477896017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17066065549910052637194689 12799549162432539477896017)
                  ·
                    refine ⟨9599661871824404608422013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12799549162432539477896017 9599661871824404608422013)
                    ·
                      refine ⟨3599873201934151728158255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9599661871824404608422013 3599873201934151728158255)
                      ·
                        rfl

theorem cell23_7010728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_7010728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010728 prefixEnd_7010728 := by exact prefixLift 7010728
  have htrace : WordTrace (prefixWord ++ tailWord_7010728) baseStart_7010728 baseEnd_7010728 := by
    simpa [prefixWord, tailWord_7010728, baseEnd_7010728] using wordTrace_append hprefix tailTrace_7010728
  have hstable : (prefixWord ++ tailWord_7010728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010728).length < 2 ^ (prefixWord ++ tailWord_7010728).sum := by decide
  have hdescent : baseEnd_7010728 < baseStart_7010728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010781 : List Nat := [1, 4, 3, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_7010781 : Nat := 118140960795 + 7010781 * 2 ^ 59
def prefixEnd_7010781 : Nat := 4983230072969 + 3 ^ 40 * 7010781 * 2
def baseEnd_7010781 : Nat := 3599900416408840020795511

theorem tailTrace_7010781 : CollatzResearch.WordTrace tailWord_7010781 prefixEnd_7010781 3599900416408840020795511 := by
  unfold tailWord_7010781
  simp only [CollatzResearch.WordTrace]
  refine ⟨255704190014145257914320197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170469460009430171942880131 255704190014145257914320197)
  ·
    refine ⟨47944535627652235858935037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255704190014145257914320197 47944535627652235858935037)
    ·
      refine ⟨17979200860369588447100639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47944535627652235858935037 17979200860369588447100639)
      ·
        refine ⟨26968801290554382670650959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17979200860369588447100639 26968801290554382670650959)
        ·
          refine ⟨40453201935831574005976439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26968801290554382670650959 40453201935831574005976439)
          ·
            refine ⟨60679802903747361008964659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40453201935831574005976439 60679802903747361008964659)
            ·
              refine ⟨91019704355621041513446989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60679802903747361008964659 91019704355621041513446989)
              ·
                refine ⟨34132389133357890567542621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91019704355621041513446989 34132389133357890567542621)
                ·
                  refine ⟨12799645925009208962828483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34132389133357890567542621 12799645925009208962828483)
                  ·
                    refine ⟨19199468887513813444242725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12799645925009208962828483 19199468887513813444242725)
                    ·
                      refine ⟨3599900416408840020795511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19199468887513813444242725 3599900416408840020795511)
                      ·
                        rfl

theorem cell23_7010781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_7010781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010781 prefixEnd_7010781 := by exact prefixLift 7010781
  have htrace : WordTrace (prefixWord ++ tailWord_7010781) baseStart_7010781 baseEnd_7010781 := by
    simpa [prefixWord, tailWord_7010781, baseEnd_7010781] using wordTrace_append hprefix tailTrace_7010781
  have hstable : (prefixWord ++ tailWord_7010781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010781).length < 2 ^ (prefixWord ++ tailWord_7010781).sum := by decide
  have hdescent : baseEnd_7010781 < baseStart_7010781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010791 : List Nat := [1, 1, 5, 2, 1, 1, 2, 2, 4, 4]
def baseStart_7010791 : Nat := 118140960795 + 7010791 * 2 ^ 59
def prefixEnd_7010791 : Nat := 4983230072969 + 3 ^ 40 * 7010791 * 2
def baseEnd_7010791 : Nat := 1199968517071794993890155

theorem tailTrace_7010791 : CollatzResearch.WordTrace tailWord_7010791 prefixEnd_7010791 1199968517071794993890155 := by
  unfold tailWord_7010791
  simp only [CollatzResearch.WordTrace]
  refine ⟨255704554744109029622184227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170469703162739353081456151 255704554744109029622184227)
  ·
    refine ⟨383556832116163544433276341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255704554744109029622184227 383556832116163544433276341)
    ·
      refine ⟨35958453010890332290619657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 383556832116163544433276341 35958453010890332290619657)
      ·
        refine ⟨26968839758167749217964743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35958453010890332290619657 26968839758167749217964743)
        ·
          refine ⟨40453259637251623826947115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26968839758167749217964743 40453259637251623826947115)
          ·
            refine ⟨60679889455877435740420673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40453259637251623826947115 60679889455877435740420673)
            ·
              refine ⟨45509917091908076805315505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60679889455877435740420673 45509917091908076805315505)
              ·
                refine ⟨34132437818931057603986629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45509917091908076805315505 34132437818931057603986629)
                ·
                  refine ⟨6399832091049573300747493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34132437818931057603986629 6399832091049573300747493)
                  ·
                    refine ⟨1199968517071794993890155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6399832091049573300747493 1199968517071794993890155)
                    ·
                      rfl

theorem cell23_7010791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_7010791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010791 prefixEnd_7010791 := by exact prefixLift 7010791
  have htrace : WordTrace (prefixWord ++ tailWord_7010791) baseStart_7010791 baseEnd_7010791 := by
    simpa [prefixWord, tailWord_7010791, baseEnd_7010791] using wordTrace_append hprefix tailTrace_7010791
  have hstable : (prefixWord ++ tailWord_7010791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010791).length < 2 ^ (prefixWord ++ tailWord_7010791).sum := by decide
  have hdescent : baseEnd_7010791 < baseStart_7010791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010798 : List Nat := [4, 1, 2, 1, 2, 3, 1, 3, 1, 1, 4]
def baseStart_7010798 : Nat := 118140960795 + 7010798 * 2 ^ 59
def prefixEnd_7010798 : Nat := 4983230072969 + 3 ^ 40 * 7010798 * 2
def baseEnd_7010798 : Nat := 3599909145579966454282933

theorem tailTrace_7010798 : CollatzResearch.WordTrace tailWord_7010798 prefixEnd_7010798 3599909145579966454282933 := by
  unfold tailWord_7010798
  simp only [CollatzResearch.WordTrace]
  refine ⟨31963101256885458727211131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170469873370055779878459365 31963101256885458727211131)
  ·
    refine ⟨47944651885328188090816697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31963101256885458727211131 47944651885328188090816697)
    ·
      refine ⟨35958488913996141068112523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47944651885328188090816697 35958488913996141068112523)
      ·
        refine ⟨53937733370994211602168785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35958488913996141068112523 53937733370994211602168785)
        ·
          refine ⟨40453300028245658701626589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53937733370994211602168785 40453300028245658701626589)
          ·
            refine ⟨15169987510592122013109971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40453300028245658701626589 15169987510592122013109971)
            ·
              refine ⟨22754981265888183019664957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15169987510592122013109971 22754981265888183019664957)
              ·
                refine ⟨8533117974708068632374359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22754981265888183019664957 8533117974708068632374359)
                ·
                  refine ⟨12799676962062102948561539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8533117974708068632374359 12799676962062102948561539)
                  ·
                    refine ⟨19199515443093154422842309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12799676962062102948561539 19199515443093154422842309)
                    ·
                      refine ⟨3599909145579966454282933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19199515443093154422842309 3599909145579966454282933)
                      ·
                        rfl

theorem cell23_7010798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_7010798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010798 prefixEnd_7010798 := by exact prefixLift 7010798
  have htrace : WordTrace (prefixWord ++ tailWord_7010798) baseStart_7010798 baseEnd_7010798 := by
    simpa [prefixWord, tailWord_7010798, baseEnd_7010798] using wordTrace_append hprefix tailTrace_7010798
  have hstable : (prefixWord ++ tailWord_7010798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010798).length < 2 ^ (prefixWord ++ tailWord_7010798).sum := by decide
  have hdescent : baseEnd_7010798 < baseStart_7010798 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010815 : List Nat := [1, 1, 2, 2, 1, 2, 3, 6, 1, 2, 2]
def baseStart_7010815 : Nat := 118140960795 + 7010815 * 2 ^ 59
def prefixEnd_7010815 : Nat := 4983230072969 + 3 ^ 40 * 7010815 * 2
def baseEnd_7010815 : Nat := 3599917874751092887770355

theorem tailTrace_7010815 : CollatzResearch.WordTrace tailWord_7010815 prefixEnd_7010815 3599917874751092887770355 := by
  unfold tailWord_7010815
  simp only [CollatzResearch.WordTrace]
  refine ⟨255705430096022081721057899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170470286730681387814038599 255705430096022081721057899)
  ·
    refine ⟨383558145144033122581586849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255705430096022081721057899 383558145144033122581586849)
    ·
      refine ⟨287668608858024841936190137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383558145144033122581586849 287668608858024841936190137)
      ·
        refine ⟨215751456643518631452142603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287668608858024841936190137 215751456643518631452142603)
        ·
          refine ⟨323627184965277947178213905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215751456643518631452142603 323627184965277947178213905)
          ·
            refine ⟨242720388723958460383660429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323627184965277947178213905 242720388723958460383660429)
            ·
              refine ⟨91020145771484422643872661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242720388723958460383660429 91020145771484422643872661)
              ·
                refine ⟨4266569333038332311431531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91020145771484422643872661 4266569333038332311431531)
                ·
                  refine ⟨6399853999557498467147297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4266569333038332311431531 6399853999557498467147297)
                  ·
                    refine ⟨4799890499668123850360473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6399853999557498467147297 4799890499668123850360473)
                    ·
                      refine ⟨3599917874751092887770355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4799890499668123850360473 3599917874751092887770355)
                      ·
                        rfl

theorem cell23_7010815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6, 1, 2, 2].length) (baseStart_7010815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010815 prefixEnd_7010815 := by exact prefixLift 7010815
  have htrace : WordTrace (prefixWord ++ tailWord_7010815) baseStart_7010815 baseEnd_7010815 := by
    simpa [prefixWord, tailWord_7010815, baseEnd_7010815] using wordTrace_append hprefix tailTrace_7010815
  have hstable : (prefixWord ++ tailWord_7010815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010815).length < 2 ^ (prefixWord ++ tailWord_7010815).sum := by decide
  have hdescent : baseEnd_7010815 < baseStart_7010815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010828 : List Nat := [2, 2, 1, 2, 4, 3, 1, 1, 1, 2, 4]
def baseStart_7010828 : Nat := 118140960795 + 7010828 * 2 ^ 59
def prefixEnd_7010828 : Nat := 4983230072969 + 3 ^ 40 * 7010828 * 2
def baseEnd_7010828 : Nat := 3599924549999601336907795

theorem tailTrace_7010828 : CollatzResearch.WordTrace tailWord_7010828 prefixEnd_7010828 3599924549999601336907795 := by
  unfold tailWord_7010828
  simp only [CollatzResearch.WordTrace]
  refine ⟨127852952122487492470640569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170470602829983323294187425 127852952122487492470640569)
  ·
    refine ⟨95889714091865619352980427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127852952122487492470640569 95889714091865619352980427)
    ·
      refine ⟨143834571137798429029470641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95889714091865619352980427 143834571137798429029470641)
      ·
        refine ⟨107875928353348821772102981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143834571137798429029470641 107875928353348821772102981)
        ·
          refine ⟨20226736566252904082269309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107875928353348821772102981 20226736566252904082269309)
          ·
            refine ⟨7585026212344839030850991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20226736566252904082269309 7585026212344839030850991)
            ·
              refine ⟨11377539318517258546276487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7585026212344839030850991 11377539318517258546276487)
              ·
                refine ⟨17066308977775887819414731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11377539318517258546276487 17066308977775887819414731)
                ·
                  refine ⟨25599463466663831729122097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17066308977775887819414731 25599463466663831729122097)
                  ·
                    refine ⟨19199597599997873796841573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25599463466663831729122097 19199597599997873796841573)
                    ·
                      refine ⟨3599924549999601336907795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19199597599997873796841573 3599924549999601336907795)
                      ·
                        rfl

theorem cell23_7010828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_7010828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010828 prefixEnd_7010828 := by exact prefixLift 7010828
  have htrace : WordTrace (prefixWord ++ tailWord_7010828) baseStart_7010828 baseEnd_7010828 := by
    simpa [prefixWord, tailWord_7010828, baseEnd_7010828] using wordTrace_append hprefix tailTrace_7010828
  have hstable : (prefixWord ++ tailWord_7010828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010828).length < 2 ^ (prefixWord ++ tailWord_7010828).sum := by decide
  have hdescent : baseEnd_7010828 < baseStart_7010828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010831 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 6, 1, 3]
def baseStart_7010831 : Nat := 118140960795 + 7010831 * 2 ^ 59
def prefixEnd_7010831 : Nat := 4983230072969 + 3 ^ 40 * 7010831 * 2
def baseEnd_7010831 : Nat := 3599926090441564825170281

theorem tailTrace_7010831 : CollatzResearch.WordTrace tailWord_7010831 prefixEnd_7010831 3599926090441564825170281 := by
  unfold tailWord_7010831
  simp only [CollatzResearch.WordTrace]
  refine ⟨255706013663964116453640347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170470675775976077635760231 255706013663964116453640347)
  ·
    refine ⟨383559020495946174680460521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255706013663964116453640347 383559020495946174680460521)
    ·
      refine ⟨287669265371959631010345391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383559020495946174680460521 287669265371959631010345391)
      ·
        refine ⟨431503898057939446515518087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287669265371959631010345391 431503898057939446515518087)
        ·
          refine ⟨647255847086909169773277131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431503898057939446515518087 647255847086909169773277131)
          ·
            refine ⟨970883770630363754659915697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647255847086909169773277131 970883770630363754659915697)
            ·
              refine ⟨728162827972772815994936773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 970883770630363754659915697 728162827972772815994936773)
              ·
                refine ⟨136530530244894902999050645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 728162827972772815994936773 136530530244894902999050645)
                ·
                  refine ⟨6399868605229448578080499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 136530530244894902999050645 6399868605229448578080499)
                  ·
                    refine ⟨9599802907844172867120749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6399868605229448578080499 9599802907844172867120749)
                    ·
                      refine ⟨3599926090441564825170281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9599802907844172867120749 3599926090441564825170281)
                      ·
                        rfl

theorem cell23_7010831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6, 1, 3].length) (baseStart_7010831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010831 prefixEnd_7010831 := by exact prefixLift 7010831
  have htrace : WordTrace (prefixWord ++ tailWord_7010831) baseStart_7010831 baseEnd_7010831 := by
    simpa [prefixWord, tailWord_7010831, baseEnd_7010831] using wordTrace_append hprefix tailTrace_7010831
  have hstable : (prefixWord ++ tailWord_7010831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010831).length < 2 ^ (prefixWord ++ tailWord_7010831).sum := by decide
  have hdescent : baseEnd_7010831 < baseStart_7010831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010855 : List Nat := [1, 1, 7, 2, 2, 1, 9]
def baseStart_7010855 : Nat := 118140960795 + 7010855 * 2 ^ 59
def prefixEnd_7010855 : Nat := 4983230072969 + 3 ^ 40 * 7010855 * 2
def baseEnd_7010855 : Nat := 44443684123176206558891

theorem tailTrace_7010855 : CollatzResearch.WordTrace tailWord_7010855 prefixEnd_7010855 44443684123176206558891 := by
  unfold tailWord_7010855
  simp only [CollatzResearch.WordTrace]
  refine ⟨255706889015877168552514019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170471259343918112368342679 255706889015877168552514019)
  ·
    refine ⟨383560333523815752828771029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255706889015877168552514019 383560333523815752828771029)
    ·
      refine ⟨8989695316964431706924321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 383560333523815752828771029 8989695316964431706924321)
      ·
        refine ⟨6742271487723323780193241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8989695316964431706924321 6742271487723323780193241)
        ·
          refine ⟨5056703615792492835144931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6742271487723323780193241 5056703615792492835144931)
          ·
            refine ⟨7585055423688739252717397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5056703615792492835144931 7585055423688739252717397)
            ·
              refine ⟨44443684123176206558891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7585055423688739252717397 44443684123176206558891)
              ·
                rfl

theorem cell23_7010855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 9].length) (baseStart_7010855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010855 prefixEnd_7010855 := by exact prefixLift 7010855
  have htrace : WordTrace (prefixWord ++ tailWord_7010855) baseStart_7010855 baseEnd_7010855 := by
    simpa [prefixWord, tailWord_7010855, baseEnd_7010855] using wordTrace_append hprefix tailTrace_7010855
  have hstable : (prefixWord ++ tailWord_7010855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010855).length < 2 ^ (prefixWord ++ tailWord_7010855).sum := by decide
  have hdescent : baseEnd_7010855 < baseStart_7010855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010864 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 4, 6]
def baseStart_7010864 : Nat := 118140960795 + 7010864 * 2 ^ 59
def prefixEnd_7010864 : Nat := 4983230072969 + 3 ^ 40 * 7010864 * 2
def baseEnd_7010864 : Nat := 1199981011767721065352543

theorem tailTrace_7010864 : CollatzResearch.WordTrace tailWord_7010864 prefixEnd_7010864 1199981011767721065352543 := by
  unfold tailWord_7010864
  simp only [CollatzResearch.WordTrace]
  refine ⟨127853608636422281544795823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170471478181896375393061097 127853608636422281544795823)
  ·
    refine ⟨191780412954633422317193735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127853608636422281544795823 191780412954633422317193735)
    ·
      refine ⟨287670619431950133475790603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191780412954633422317193735 287670619431950133475790603)
      ·
        refine ⟨431505929147925200213685905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287670619431950133475790603 431505929147925200213685905)
        ·
          refine ⟨323629446860943900160264429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431505929147925200213685905 323629446860943900160264429)
          ·
            refine ⟨121361042572853962560099161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323629446860943900160264429 121361042572853962560099161)
            ·
              refine ⟨91020781929640471920074371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121361042572853962560099161 91020781929640471920074371)
              ·
                refine ⟨136531172894460707880111557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91020781929640471920074371 136531172894460707880111557)
                ·
                  refine ⟨25599594917711382727520917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136531172894460707880111557 25599594917711382727520917)
                  ·
                    refine ⟨1199981011767721065352543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25599594917711382727520917 1199981011767721065352543)
                    ·
                      rfl

theorem cell23_7010864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 4, 6].length) (baseStart_7010864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010864 prefixEnd_7010864 := by exact prefixLift 7010864
  have htrace : WordTrace (prefixWord ++ tailWord_7010864) baseStart_7010864 baseEnd_7010864 := by
    simpa [prefixWord, tailWord_7010864, baseEnd_7010864] using wordTrace_append hprefix tailTrace_7010864
  have hstable : (prefixWord ++ tailWord_7010864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010864).length < 2 ^ (prefixWord ++ tailWord_7010864).sum := by decide
  have hdescent : baseEnd_7010864 < baseStart_7010864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010921 : List Nat := [1, 2, 1, 1, 1, 4, 1, 4, 2, 3, 3]
def baseStart_7010921 : Nat := 118140960795 + 7010921 * 2 ^ 59
def prefixEnd_7010921 : Nat := 4983230072969 + 3 ^ 40 * 7010921 * 2
def baseEnd_7010921 : Nat := 3599972303700469473044867

theorem tailTrace_7010921 : CollatzResearch.WordTrace tailWord_7010921 prefixEnd_7010921 3599972303700469473044867 := by
  unfold tailWord_7010921
  simp only [CollatzResearch.WordTrace]
  refine ⟨255709296233638061824416617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170472864155758707882944411 255709296233638061824416617)
  ·
    refine ⟨191781972175228546368312463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255709296233638061824416617 191781972175228546368312463)
    ·
      refine ⟨287672958262842819552468695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191781972175228546368312463 287672958262842819552468695)
      ·
        refine ⟨431509437394264229328703043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287672958262842819552468695 431509437394264229328703043)
        ·
          refine ⟨647264156091396343993054565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431509437394264229328703043 647264156091396343993054565)
          ·
            refine ⟨121362029267136814498697731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 647264156091396343993054565 121362029267136814498697731)
            ·
              refine ⟨182043043900705221748046597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121362029267136814498697731 182043043900705221748046597)
              ·
                refine ⟨34133070731382229077758737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182043043900705221748046597 34133070731382229077758737)
                ·
                  refine ⟨25599803048536671808319053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34133070731382229077758737 25599803048536671808319053)
                  ·
                    refine ⟨9599926143201251928119645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25599803048536671808319053 9599926143201251928119645)
                    ·
                      refine ⟨3599972303700469473044867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9599926143201251928119645 3599972303700469473044867)
                      ·
                        rfl

theorem cell23_7010921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 3, 3].length) (baseStart_7010921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010921 prefixEnd_7010921 := by exact prefixLift 7010921
  have htrace : WordTrace (prefixWord ++ tailWord_7010921) baseStart_7010921 baseEnd_7010921 := by
    simpa [prefixWord, tailWord_7010921, baseEnd_7010921] using wordTrace_append hprefix tailTrace_7010921
  have hstable : (prefixWord ++ tailWord_7010921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010921).length < 2 ^ (prefixWord ++ tailWord_7010921).sum := by decide
  have hdescent : baseEnd_7010921 < baseStart_7010921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7010922 : List Nat := [3, 1, 3, 2, 1, 1, 4, 2, 2, 2, 2]
def baseStart_7010922 : Nat := 118140960795 + 7010922 * 2 ^ 59
def prefixEnd_7010922 : Nat := 4983230072969 + 3 ^ 40 * 7010922 * 2
def baseEnd_7010922 : Nat := 3599972817181123969132363

theorem tailTrace_7010922 : CollatzResearch.WordTrace tailWord_7010922 prefixEnd_7010922 3599972817181123969132363 := by
  unfold tailWord_7010922
  simp only [CollatzResearch.WordTrace]
  refine ⟨63927333176658609748800755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170472888471089625996802013 63927333176658609748800755)
  ·
    refine ⟨95890999764987914623201133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63927333176658609748800755 95890999764987914623201133)
    ·
      refine ⟨35959124911870467983700425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95890999764987914623201133 35959124911870467983700425)
      ·
        refine ⟨26969343683902850987775319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35959124911870467983700425 26969343683902850987775319)
        ·
          refine ⟨40454015525854276481662979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26969343683902850987775319 40454015525854276481662979)
          ·
            refine ⟨60681023288781414722494469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40454015525854276481662979 60681023288781414722494469)
            ·
              refine ⟨11377691866646515260467713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60681023288781414722494469 11377691866646515260467713)
              ·
                refine ⟨8533268899984886445350785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11377691866646515260467713 8533268899984886445350785)
                ·
                  refine ⟨6399951674988664834013089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8533268899984886445350785 6399951674988664834013089)
                  ·
                    refine ⟨4799963756241498625509817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6399951674988664834013089 4799963756241498625509817)
                    ·
                      refine ⟨3599972817181123969132363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4799963756241498625509817 3599972817181123969132363)
                      ·
                        rfl

theorem cell23_7010922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_7010922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7010922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7010922 prefixEnd_7010922 := by exact prefixLift 7010922
  have htrace : WordTrace (prefixWord ++ tailWord_7010922) baseStart_7010922 baseEnd_7010922 := by
    simpa [prefixWord, tailWord_7010922, baseEnd_7010922] using wordTrace_append hprefix tailTrace_7010922
  have hstable : (prefixWord ++ tailWord_7010922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7010922).length < 2 ^ (prefixWord ++ tailWord_7010922).sum := by decide
  have hdescent : baseEnd_7010922 < baseStart_7010922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7010922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011022 : List Nat := [4, 1, 1, 1, 3, 2, 3, 3, 1, 4]
def baseStart_7011022 : Nat := 118140960795 + 7011022 * 2 ^ 59
def prefixEnd_7011022 : Nat := 4983230072969 + 3 ^ 40 * 7011022 * 2
def baseEnd_7011022 : Nat := 1200008055082191192627301

theorem tailTrace_7011022 : CollatzResearch.WordTrace tailWord_7011022 prefixEnd_7011022 1200008055082191192627301 := by
  unfold tailWord_7011022
  simp only [CollatzResearch.WordTrace]
  refine ⟨31964122500784019509230415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170475320004181437382562213 31964122500784019509230415)
  ·
    refine ⟨47946183751176029263845623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31964122500784019509230415 47946183751176029263845623)
    ·
      refine ⟨71919275626764043895768435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47946183751176029263845623 71919275626764043895768435)
      ·
        refine ⟨107878913440146065843652653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71919275626764043895768435 107878913440146065843652653)
        ·
          refine ⟨40454592540054774691369745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107878913440146065843652653 40454592540054774691369745)
          ·
            refine ⟨30340944405041081018527309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40454592540054774691369745 30340944405041081018527309)
            ·
              refine ⟨11377854151890405381947741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30340944405041081018527309 11377854151890405381947741)
              ·
                refine ⟨4266695306958902018230403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11377854151890405381947741 4266695306958902018230403)
                ·
                  refine ⟨6400042960438353027345605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4266695306958902018230403 6400042960438353027345605)
                  ·
                    refine ⟨1200008055082191192627301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6400042960438353027345605 1200008055082191192627301)
                    ·
                      rfl

theorem cell23_7011022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_7011022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011022 prefixEnd_7011022 := by exact prefixLift 7011022
  have htrace : WordTrace (prefixWord ++ tailWord_7011022) baseStart_7011022 baseEnd_7011022 := by
    simpa [prefixWord, tailWord_7011022, baseEnd_7011022] using wordTrace_append hprefix tailTrace_7011022
  have hstable : (prefixWord ++ tailWord_7011022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011022).length < 2 ^ (prefixWord ++ tailWord_7011022).sum := by decide
  have hdescent : baseEnd_7011022 < baseStart_7011022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011051 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 4]
def baseStart_7011051 : Nat := 118140960795 + 7011051 * 2 ^ 59
def prefixEnd_7011051 : Nat := 4983230072969 + 3 ^ 40 * 7011051 * 2
def baseEnd_7011051 : Nat := 3600039056185553964419269

theorem tailTrace_7011051 : CollatzResearch.WordTrace tailWord_7011051 prefixEnd_7011051 3600039056185553964419269 := by
  unfold tailWord_7011051
  simp only [CollatzResearch.WordTrace]
  refine ⟨255714037723167094026649007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170476025148778062684432671 255714037723167094026649007)
  ·
    refine ⟨383571056584750641039973511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255714037723167094026649007 383571056584750641039973511)
    ·
      refine ⟨575356584877125961559960267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383571056584750641039973511 575356584877125961559960267)
      ·
        refine ⟨863034877315688942339940401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575356584877125961559960267 863034877315688942339940401)
        ·
          refine ⟨647276157986766706754955301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 863034877315688942339940401 647276157986766706754955301)
          ·
            refine ⟨121364279622518757516554119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 647276157986766706754955301 121364279622518757516554119)
            ·
              refine ⟨182046419433778136274831179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121364279622518757516554119 182046419433778136274831179)
              ·
                refine ⟨273069629150667204412246769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182046419433778136274831179 273069629150667204412246769)
                ·
                  refine ⟨204802221863000403309185077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 273069629150667204412246769 204802221863000403309185077)
                  ·
                    refine ⟨19200208299656287810236101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 204802221863000403309185077 19200208299656287810236101)
                    ·
                      refine ⟨3600039056185553964419269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19200208299656287810236101 3600039056185553964419269)
                      ·
                        rfl

theorem cell23_7011051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 4].length) (baseStart_7011051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011051 prefixEnd_7011051 := by exact prefixLift 7011051
  have htrace : WordTrace (prefixWord ++ tailWord_7011051) baseStart_7011051 baseEnd_7011051 := by
    simpa [prefixWord, tailWord_7011051, baseEnd_7011051] using wordTrace_append hprefix tailTrace_7011051
  have hstable : (prefixWord ++ tailWord_7011051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011051).length < 2 ^ (prefixWord ++ tailWord_7011051).sum := by decide
  have hdescent : baseEnd_7011051 < baseStart_7011051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011098 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4]
def baseStart_7011098 : Nat := 118140960795 + 7011098 * 2 ^ 59
def prefixEnd_7011098 : Nat := 4983230072969 + 3 ^ 40 * 7011098 * 2
def baseEnd_7011098 : Nat := 3600063189776315280531553

theorem tailTrace_7011098 : CollatzResearch.WordTrace tailWord_7011098 prefixEnd_7011098 3600063189776315280531553 := by
  unfold tailWord_7011098
  simp only [CollatzResearch.WordTrace]
  refine ⟨63928937988499205263402487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170477167969331214035739965 63928937988499205263402487)
  ·
    refine ⟨95893406982748807895103731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63928937988499205263402487 95893406982748807895103731)
    ·
      refine ⟨143840110474123211842655597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95893406982748807895103731 143840110474123211842655597)
      ·
        refine ⟨53940041427796204440995849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143840110474123211842655597 53940041427796204440995849)
        ·
          refine ⟨40455031070847153330746887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53940041427796204440995849 40455031070847153330746887)
          ·
            refine ⟨60682546606270729996120331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40455031070847153330746887 60682546606270729996120331)
            ·
              refine ⟨91023819909406094994180497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60682546606270729996120331 91023819909406094994180497)
              ·
                refine ⟨68267864932054571245635373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91023819909406094994180497 68267864932054571245635373)
                ·
                  refine ⟨25600449349520464217113265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68267864932054571245635373 25600449349520464217113265)
                  ·
                    refine ⟨19200337012140348162834949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25600449349520464217113265 19200337012140348162834949)
                    ·
                      refine ⟨3600063189776315280531553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19200337012140348162834949 3600063189776315280531553)
                      ·
                        rfl

theorem cell23_7011098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_7011098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011098 prefixEnd_7011098 := by exact prefixLift 7011098
  have htrace : WordTrace (prefixWord ++ tailWord_7011098) baseStart_7011098 baseEnd_7011098 := by
    simpa [prefixWord, tailWord_7011098, baseEnd_7011098] using wordTrace_append hprefix tailTrace_7011098
  have hstable : (prefixWord ++ tailWord_7011098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011098).length < 2 ^ (prefixWord ++ tailWord_7011098).sum := by decide
  have hdescent : baseEnd_7011098 < baseStart_7011098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011125 : List Nat := [1, 3, 3, 1, 3, 2, 3, 7]
def baseStart_7011125 : Nat := 118140960795 + 7011125 * 2 ^ 59
def prefixEnd_7011125 : Nat := 4983230072969 + 3 ^ 40 * 7011125 * 2
def baseEnd_7011125 : Nat := 133336187176073580551627

theorem tailTrace_7011125 : CollatzResearch.WordTrace tailWord_7011125 prefixEnd_7011125 133336187176073580551627 := by
  unfold tailWord_7011125
  simp only [CollatzResearch.WordTrace]
  refine ⟨255716736724899004664842829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170477824483266003109895219 255716736724899004664842829)
  ·
    refine ⟨95893776271837126749316061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255716736724899004664842829 95893776271837126749316061)
    ·
      refine ⟨35960166101938922530993523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95893776271837126749316061 35960166101938922530993523)
      ·
        refine ⟨53940249152908383796490285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35960166101938922530993523 53940249152908383796490285)
        ·
          refine ⟨20227593432340643923683857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53940249152908383796490285 20227593432340643923683857)
          ·
            refine ⟨15170695074255482942762893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20227593432340643923683857 15170695074255482942762893)
            ·
              refine ⟨5689010652845806103536085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15170695074255482942762893 5689010652845806103536085)
              ·
                refine ⟨133336187176073580551627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5689010652845806103536085 133336187176073580551627)
                ·
                  rfl

theorem cell23_7011125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 7].length) (baseStart_7011125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011125 prefixEnd_7011125 := by exact prefixLift 7011125
  have htrace : WordTrace (prefixWord ++ tailWord_7011125) baseStart_7011125 baseEnd_7011125 := by
    simpa [prefixWord, tailWord_7011125, baseEnd_7011125] using wordTrace_append hprefix tailTrace_7011125
  have hstable : (prefixWord ++ tailWord_7011125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011125).length < 2 ^ (prefixWord ++ tailWord_7011125).sum := by decide
  have hdescent : baseEnd_7011125 < baseStart_7011125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011131 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 11]
def baseStart_7011131 : Nat := 118140960795 + 7011131 * 2 ^ 59
def prefixEnd_7011131 : Nat := 4983230072969 + 3 ^ 40 * 7011131 * 2
def baseEnd_7011131 : Nat := 3600080134637913651418901

theorem tailTrace_7011131 : CollatzResearch.WordTrace tailWord_7011131 prefixEnd_7011131 3600080134637913651418901 := by
  unfold tailWord_7011131
  simp only [CollatzResearch.WordTrace]
  refine ⟨255716955562877267689561247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170477970375251511793040831 255716955562877267689561247)
  ·
    refine ⟨383575433344315901534341871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255716955562877267689561247 383575433344315901534341871)
    ·
      refine ⟨575363150016473852301512807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383575433344315901534341871 575363150016473852301512807)
      ·
        refine ⟨863044725024710778452269211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575363150016473852301512807 863044725024710778452269211)
        ·
          refine ⟨1294567087537066167678403817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 863044725024710778452269211 1294567087537066167678403817)
          ·
            refine ⟨970925315652799625758802863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1294567087537066167678403817 970925315652799625758802863)
            ·
              refine ⟨1456387973479199438638204295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 970925315652799625758802863 1456387973479199438638204295)
              ·
                refine ⟨2184581960218799157957306443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1456387973479199438638204295 2184581960218799157957306443)
                ·
                  refine ⟨3276872940328198736935959665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2184581960218799157957306443 3276872940328198736935959665)
                  ·
                    refine ⟨2457654705246149052701969749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3276872940328198736935959665 2457654705246149052701969749)
                    ·
                      refine ⟨3600080134637913651418901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 2457654705246149052701969749 3600080134637913651418901)
                      ·
                        rfl

theorem cell23_7011131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 11].length) (baseStart_7011131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011131 prefixEnd_7011131 := by exact prefixLift 7011131
  have htrace : WordTrace (prefixWord ++ tailWord_7011131) baseStart_7011131 baseEnd_7011131 := by
    simpa [prefixWord, tailWord_7011131, baseEnd_7011131] using wordTrace_append hprefix tailTrace_7011131
  have hstable : (prefixWord ++ tailWord_7011131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011131).length < 2 ^ (prefixWord ++ tailWord_7011131).sum := by decide
  have hdescent : baseEnd_7011131 < baseStart_7011131 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011135 : List Nat := [1, 1, 2, 2, 5, 1, 2, 2, 1, 3, 3]
def baseStart_7011135 : Nat := 118140960795 + 7011135 * 2 ^ 59
def prefixEnd_7011135 : Nat := 4983230072969 + 3 ^ 40 * 7011135 * 2
def baseEnd_7011135 : Nat := 3600082188560531635768883

theorem tailTrace_7011135 : CollatzResearch.WordTrace tailWord_7011135 prefixEnd_7011135 3600082188560531635768883 := by
  unfold tailWord_7011135
  simp only [CollatzResearch.WordTrace]
  refine ⟨255717101454862776372706859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170478067636575184248471239 255717101454862776372706859)
  ·
    refine ⟨383575652182294164559060289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255717101454862776372706859 383575652182294164559060289)
    ·
      refine ⟨287681739136720623419295217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383575652182294164559060289 287681739136720623419295217)
      ·
        refine ⟨215761304352540467564471413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287681739136720623419295217 215761304352540467564471413)
        ·
          refine ⟨20227622283050668834169195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 215761304352540467564471413 20227622283050668834169195)
          ·
            refine ⟨30341433424576003251253793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20227622283050668834169195 30341433424576003251253793)
            ·
              refine ⟨22756075068432002438440345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30341433424576003251253793 22756075068432002438440345)
              ·
                refine ⟨17067056301324001828830259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22756075068432002438440345 17067056301324001828830259)
                ·
                  refine ⟨25600584451986002743245389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17067056301324001828830259 25600584451986002743245389)
                  ·
                    refine ⟨9600219169494751028717021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25600584451986002743245389 9600219169494751028717021)
                    ·
                      refine ⟨3600082188560531635768883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9600219169494751028717021 3600082188560531635768883)
                      ·
                        rfl

theorem cell23_7011135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3, 3].length) (baseStart_7011135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011135 prefixEnd_7011135 := by exact prefixLift 7011135
  have htrace : WordTrace (prefixWord ++ tailWord_7011135) baseStart_7011135 baseEnd_7011135 := by
    simpa [prefixWord, tailWord_7011135, baseEnd_7011135] using wordTrace_append hprefix tailTrace_7011135
  have hstable : (prefixWord ++ tailWord_7011135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011135).length < 2 ^ (prefixWord ++ tailWord_7011135).sum := by decide
  have hdescent : baseEnd_7011135 < baseStart_7011135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011142 : List Nat := [6, 1, 1, 2, 2, 1, 10]
def baseStart_7011142 : Nat := 118140960795 + 7011142 * 2 ^ 59
def prefixEnd_7011142 : Nat := 4983230072969 + 3 ^ 40 * 7011142 * 2
def baseEnd_7011142 : Nat := 44445503492902630967671

theorem tailTrace_7011142 : CollatzResearch.WordTrace tailWord_7011142 prefixEnd_7011142 44445503492902630967671 := by
  unfold tailWord_7011142
  simp only [CollatzResearch.WordTrace]
  refine ⟨7991167398932419267756615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 170478237843891611045474453 7991167398932419267756615)
  ·
    refine ⟨11986751098398628901634923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7991167398932419267756615 11986751098398628901634923)
    ·
      refine ⟨17980126647597943352452385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11986751098398628901634923 17980126647597943352452385)
      ·
        refine ⟨13485094985698457514339289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17980126647597943352452385 13485094985698457514339289)
        ·
          refine ⟨10113821239273843135754467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13485094985698457514339289 10113821239273843135754467)
          ·
            refine ⟨15170731858910764703631701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10113821239273843135754467 15170731858910764703631701)
            ·
              refine ⟨44445503492902630967671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15170731858910764703631701 44445503492902630967671)
              ·
                rfl

theorem cell23_7011142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 10].length) (baseStart_7011142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011142 prefixEnd_7011142 := by exact prefixLift 7011142
  have htrace : WordTrace (prefixWord ++ tailWord_7011142) baseStart_7011142 baseEnd_7011142 := by
    simpa [prefixWord, tailWord_7011142, baseEnd_7011142] using wordTrace_append hprefix tailTrace_7011142
  have hstable : (prefixWord ++ tailWord_7011142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011142).length < 2 ^ (prefixWord ++ tailWord_7011142).sum := by decide
  have hdescent : baseEnd_7011142 < baseStart_7011142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011152 : List Nat := [2, 1, 1, 1, 1, 4, 5, 2, 2, 1, 3]
def baseStart_7011152 : Nat := 118140960795 + 7011152 * 2 ^ 59
def prefixEnd_7011152 : Nat := 4983230072969 + 3 ^ 40 * 7011152 * 2
def baseEnd_7011152 : Nat := 3600090917731658069256305

theorem tailTrace_7011152 : CollatzResearch.WordTrace tailWord_7011152 prefixEnd_7011152 3600090917731658069256305 := by
  unfold tailWord_7011152
  simp only [CollatzResearch.WordTrace]
  refine ⟨127858860747900594138037855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170478480997200792184050473 127858860747900594138037855)
  ·
    refine ⟨191788291121850891207056783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127858860747900594138037855 191788291121850891207056783)
    ·
      refine ⟨287682436682776336810585175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191788291121850891207056783 287682436682776336810585175)
      ·
        refine ⟨431523655024164505215877763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287682436682776336810585175 431523655024164505215877763)
        ·
          refine ⟨647285482536246757823816645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431523655024164505215877763 647285482536246757823816645)
          ·
            refine ⟨121366027975546267091965621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 647285482536246757823816645 121366027975546267091965621)
            ·
              refine ⟨11378065122707462539871777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121366027975546267091965621 11378065122707462539871777)
              ·
                refine ⟨8533548842030596904903833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11378065122707462539871777 8533548842030596904903833)
                ·
                  refine ⟨6400161631522947678677875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8533548842030596904903833 6400161631522947678677875)
                  ·
                    refine ⟨9600242447284421518016813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6400161631522947678677875 9600242447284421518016813)
                    ·
                      refine ⟨3600090917731658069256305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9600242447284421518016813 3600090917731658069256305)
                      ·
                        rfl

theorem cell23_7011152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 2, 1, 3].length) (baseStart_7011152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011152 prefixEnd_7011152 := by exact prefixLift 7011152
  have htrace : WordTrace (prefixWord ++ tailWord_7011152) baseStart_7011152 baseEnd_7011152 := by
    simpa [prefixWord, tailWord_7011152, baseEnd_7011152] using wordTrace_append hprefix tailTrace_7011152
  have hstable : (prefixWord ++ tailWord_7011152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011152).length < 2 ^ (prefixWord ++ tailWord_7011152).sum := by decide
  have hdescent : baseEnd_7011152 < baseStart_7011152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011168 : List Nat := [2, 1, 1, 3, 3, 1, 1, 3, 2, 6]
def baseStart_7011168 : Nat := 118140960795 + 7011168 * 2 ^ 59
def prefixEnd_7011168 : Nat := 4983230072969 + 3 ^ 40 * 7011168 * 2
def baseEnd_7011168 : Nat := 1200033044474043335552077

theorem tailTrace_7011168 : CollatzResearch.WordTrace tailWord_7011168 prefixEnd_7011168 1200033044474043335552077 := by
  unfold tailWord_7011168
  simp only [CollatzResearch.WordTrace]
  refine ⟨127859152531871611504329079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170478870042495482005772105 127859152531871611504329079)
  ·
    refine ⟨191788728797807417256493619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127859152531871611504329079 191788728797807417256493619)
    ·
      refine ⟨287683093196711125884740429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191788728797807417256493619 287683093196711125884740429)
      ·
        refine ⟨107881159948766672206777661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287683093196711125884740429 107881159948766672206777661)
        ·
          refine ⟨40455434980787502077541623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107881159948766672206777661 40455434980787502077541623)
          ·
            refine ⟨60683152471181253116312435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40455434980787502077541623 60683152471181253116312435)
            ·
              refine ⟨91024728706771879674468653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60683152471181253116312435 91024728706771879674468653)
              ·
                refine ⟨34134273265039454877925745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91024728706771879674468653 34134273265039454877925745)
                ·
                  refine ⟨25600704948779591158444309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34134273265039454877925745 25600704948779591158444309)
                  ·
                    refine ⟨1200033044474043335552077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25600704948779591158444309 1200033044474043335552077)
                    ·
                      rfl

theorem cell23_7011168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 2, 6].length) (baseStart_7011168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011168 prefixEnd_7011168 := by exact prefixLift 7011168
  have htrace : WordTrace (prefixWord ++ tailWord_7011168) baseStart_7011168 baseEnd_7011168 := by
    simpa [prefixWord, tailWord_7011168, baseEnd_7011168] using wordTrace_append hprefix tailTrace_7011168
  have hstable : (prefixWord ++ tailWord_7011168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011168).length < 2 ^ (prefixWord ++ tailWord_7011168).sum := by decide
  have hdescent : baseEnd_7011168 < baseStart_7011168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011226 : List Nat := [3, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2]
def baseStart_7011226 : Nat := 118140960795 + 7011226 * 2 ^ 59
def prefixEnd_7011226 : Nat := 4983230072969 + 3 ^ 40 * 7011226 * 2
def baseEnd_7011226 : Nat := 3600128915300090779730965

theorem tailTrace_7011226 : CollatzResearch.WordTrace tailWord_7011226 prefixEnd_7011226 3600128915300090779730965 := by
  unfold tailWord_7011226
  simp only [CollatzResearch.WordTrace]
  refine ⟨63930105124383274728567383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170480280331688732609513021 63930105124383274728567383)
  ·
    refine ⟨95895157686574912092851075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63930105124383274728567383 95895157686574912092851075)
    ·
      refine ⟨143842736529862368139276613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95895157686574912092851075 143842736529862368139276613)
      ·
        refine ⟨26970513099349194026114365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143842736529862368139276613 26970513099349194026114365)
        ·
          refine ⟨10113942412255947759792887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26970513099349194026114365 10113942412255947759792887)
          ·
            refine ⟨15170913618383921639689331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10113942412255947759792887 15170913618383921639689331)
            ·
              refine ⟨22756370427575882459533997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15170913618383921639689331 22756370427575882459533997)
              ·
                refine ⟨8533638910340955922325249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22756370427575882459533997 8533638910340955922325249)
                ·
                  refine ⟨6400229182755716941743937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8533638910340955922325249 6400229182755716941743937)
                  ·
                    refine ⟨4800171887066787706307953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6400229182755716941743937 4800171887066787706307953)
                    ·
                      refine ⟨3600128915300090779730965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4800171887066787706307953 3600128915300090779730965)
                      ·
                        rfl

theorem cell23_7011226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_7011226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011226 prefixEnd_7011226 := by exact prefixLift 7011226
  have htrace : WordTrace (prefixWord ++ tailWord_7011226) baseStart_7011226 baseEnd_7011226 := by
    simpa [prefixWord, tailWord_7011226, baseEnd_7011226] using wordTrace_append hprefix tailTrace_7011226
  have hstable : (prefixWord ++ tailWord_7011226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011226).length < 2 ^ (prefixWord ++ tailWord_7011226).sum := by decide
  have hdescent : baseEnd_7011226 < baseStart_7011226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011326 : List Nat := [4, 2, 2, 2, 2, 1, 2, 1, 3, 4]
def baseStart_7011326 : Nat := 118140960795 + 7011326 * 2 ^ 59
def prefixEnd_7011326 : Nat := 4983230072969 + 3 ^ 40 * 7011326 * 2
def baseEnd_7011326 : Nat := 1200060087788513462826835

theorem tailTrace_7011326 : CollatzResearch.WordTrace tailWord_7011326 prefixEnd_7011326 1200060087788513462826835 := by
  unfold tailWord_7011326
  simp only [CollatzResearch.WordTrace]
  refine ⟨31965508474646351999113729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170482711864780543995273221 31965508474646351999113729)
  ·
    refine ⟨23974131355984763999335297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31965508474646351999113729 23974131355984763999335297)
    ·
      refine ⟨17980598516988572999501473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23974131355984763999335297 17980598516988572999501473)
      ·
        refine ⟨13485448887741429749626105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17980598516988572999501473 13485448887741429749626105)
        ·
          refine ⟨10114086665806072312219579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13485448887741429749626105 10114086665806072312219579)
          ·
            refine ⟨15171129998709108468329369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10114086665806072312219579 15171129998709108468329369)
            ·
              refine ⟨11378347499031831351247027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15171129998709108468329369 11378347499031831351247027)
              ·
                refine ⟨17067521248547747026870541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11378347499031831351247027 17067521248547747026870541)
                ·
                  refine ⟨6400320468205405135076453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17067521248547747026870541 6400320468205405135076453)
                  ·
                    refine ⟨1200060087788513462826835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6400320468205405135076453 1200060087788513462826835)
                    ·
                      rfl

theorem cell23_7011326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_7011326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011326 prefixEnd_7011326 := by exact prefixLift 7011326
  have htrace : WordTrace (prefixWord ++ tailWord_7011326) baseStart_7011326 baseEnd_7011326 := by
    simpa [prefixWord, tailWord_7011326, baseEnd_7011326] using wordTrace_append hprefix tailTrace_7011326
  have hstable : (prefixWord ++ tailWord_7011326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011326).length < 2 ^ (prefixWord ++ tailWord_7011326).sum := by decide
  have hdescent : baseEnd_7011326 < baseStart_7011326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011349 : List Nat := [1, 3, 2, 1, 4, 1, 2, 2, 3, 1, 3]
def baseStart_7011349 : Nat := 118140960795 + 7011349 * 2 ^ 59
def prefixEnd_7011349 : Nat := 4983230072969 + 3 ^ 40 * 7011349 * 2
def baseEnd_7011349 : Nat := 3600192073420593798492899

theorem tailTrace_7011349 : CollatzResearch.WordTrace tailWord_7011349 prefixEnd_7011349 3600192073420593798492899 := by
  unfold tailWord_7011349
  simp only [CollatzResearch.WordTrace]
  refine ⟨255724906676087490920997101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170483271117391660613998067 255724906676087490920997101)
  ·
    refine ⟨95896840003532809095373913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255724906676087490920997101 95896840003532809095373913)
    ·
      refine ⟨71922630002649606821530435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95896840003532809095373913 71922630002649606821530435)
      ·
        refine ⟨107883945003974410232295653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71922630002649606821530435 107883945003974410232295653)
        ·
          refine ⟨20228239688245201918555435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107883945003974410232295653 20228239688245201918555435)
          ·
            refine ⟨30342359532367802877833153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20228239688245201918555435 30342359532367802877833153)
            ·
              refine ⟨22756769649275852158374865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30342359532367802877833153 22756769649275852158374865)
              ·
                refine ⟨17067577236956889118781149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22756769649275852158374865 17067577236956889118781149)
                ·
                  refine ⟨6400341463858833419542931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17067577236956889118781149 6400341463858833419542931)
                  ·
                    refine ⟨9600512195788250129314397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6400341463858833419542931 9600512195788250129314397)
                    ·
                      refine ⟨3600192073420593798492899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9600512195788250129314397 3600192073420593798492899)
                      ·
                        rfl

theorem cell23_7011349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_7011349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011349 prefixEnd_7011349 := by exact prefixLift 7011349
  have htrace : WordTrace (prefixWord ++ tailWord_7011349) baseStart_7011349 baseEnd_7011349 := by
    simpa [prefixWord, tailWord_7011349, baseEnd_7011349] using wordTrace_append hprefix tailTrace_7011349
  have hstable : (prefixWord ++ tailWord_7011349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011349).length < 2 ^ (prefixWord ++ tailWord_7011349).sum := by decide
  have hdescent : baseEnd_7011349 < baseStart_7011349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011352 : List Nat := [2, 1, 2, 3, 2, 2, 1, 4, 1, 5]
def baseStart_7011352 : Nat := 118140960795 + 7011352 * 2 ^ 59
def prefixEnd_7011352 : Nat := 4983230072969 + 3 ^ 40 * 7011352 * 2
def baseEnd_7011352 : Nat := 1200064537954185762251795

theorem tailTrace_7011352 : CollatzResearch.WordTrace tailWord_7011352 prefixEnd_7011352 1200064537954185762251795 := by
  unfold tailWord_7011352
  simp only [CollatzResearch.WordTrace]
  refine ⟨127862508047538311216678155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170483344063384414955570873 127862508047538311216678155)
  ·
    refine ⟨191793762071307466825017233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127862508047538311216678155 191793762071307466825017233)
    ·
      refine ⟨143845321553480600118762925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191793762071307466825017233 143845321553480600118762925)
      ·
        refine ⟨53941995582555225044536097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143845321553480600118762925 53941995582555225044536097)
        ·
          refine ⟨40456496686916418783402073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53941995582555225044536097 40456496686916418783402073)
          ·
            refine ⟨30342372515187314087551555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40456496686916418783402073 30342372515187314087551555)
            ·
              refine ⟨45513558772780971131327333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30342372515187314087551555 45513558772780971131327333)
              ·
                refine ⟨8533792269896432087123875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45513558772780971131327333 8533792269896432087123875)
                ·
                  refine ⟨12800688404844648130685813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8533792269896432087123875 12800688404844648130685813)
                  ·
                    refine ⟨1200064537954185762251795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12800688404844648130685813 1200064537954185762251795)
                    ·
                      rfl

theorem cell23_7011352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 1, 5].length) (baseStart_7011352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011352 prefixEnd_7011352 := by exact prefixLift 7011352
  have htrace : WordTrace (prefixWord ++ tailWord_7011352) baseStart_7011352 baseEnd_7011352 := by
    simpa [prefixWord, tailWord_7011352, baseEnd_7011352] using wordTrace_append hprefix tailTrace_7011352
  have hstable : (prefixWord ++ tailWord_7011352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011352).length < 2 ^ (prefixWord ++ tailWord_7011352).sum := by decide
  have hdescent : baseEnd_7011352 < baseStart_7011352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011355 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 4]
def baseStart_7011355 : Nat := 118140960795 + 7011355 * 2 ^ 59
def prefixEnd_7011355 : Nat := 4983230072969 + 3 ^ 40 * 7011355 * 2
def baseEnd_7011355 : Nat := 3600195154304520775017871

theorem tailTrace_7011355 : CollatzResearch.WordTrace tailWord_7011355 prefixEnd_7011355 3600195154304520775017871 := by
  unfold tailWord_7011355
  simp only [CollatzResearch.WordTrace]
  refine ⟨255725125514065753945715519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170483417009377169297143679 255725125514065753945715519)
  ·
    refine ⟨383587688271098630918573279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255725125514065753945715519 383587688271098630918573279)
    ·
      refine ⟨575381532406647946377859919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383587688271098630918573279 575381532406647946377859919)
      ·
        refine ⟨863072298609971919566789879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575381532406647946377859919 863072298609971919566789879)
        ·
          refine ⟨1294608447914957879350184819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 863072298609971919566789879 1294608447914957879350184819)
          ·
            refine ⟨1941912671872436819025277229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1294608447914957879350184819 1941912671872436819025277229)
            ·
              refine ⟨728217251952163807134478961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1941912671872436819025277229 728217251952163807134478961)
              ·
                refine ⟨546162938964122855350859221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 728217251952163807134478961 546162938964122855350859221)
                ·
                  refine ⟨12800693881971629422285763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 546162938964122855350859221 12800693881971629422285763)
                  ·
                    refine ⟨19201040822957444133428645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12800693881971629422285763 19201040822957444133428645)
                    ·
                      refine ⟨3600195154304520775017871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19201040822957444133428645 3600195154304520775017871)
                      ·
                        rfl

theorem cell23_7011355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 1, 4].length) (baseStart_7011355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011355 prefixEnd_7011355 := by exact prefixLift 7011355
  have htrace : WordTrace (prefixWord ++ tailWord_7011355) baseStart_7011355 baseEnd_7011355 := by
    simpa [prefixWord, tailWord_7011355, baseEnd_7011355] using wordTrace_append hprefix tailTrace_7011355
  have hstable : (prefixWord ++ tailWord_7011355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011355).length < 2 ^ (prefixWord ++ tailWord_7011355).sum := by decide
  have hdescent : baseEnd_7011355 < baseStart_7011355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011360 : List Nat := [2, 1, 1, 7, 2, 1, 1, 3, 1, 4]
def baseStart_7011360 : Nat := 118140960795 + 7011360 * 2 ^ 59
def prefixEnd_7011360 : Nat := 4983230072969 + 3 ^ 40 * 7011360 * 2
def baseEnd_7011360 : Nat := 1200065907235931085151783

theorem tailTrace_7011360 : CollatzResearch.WordTrace tailWord_7011360 prefixEnd_7011360 1200065907235931085151783 := by
  unfold tailWord_7011360
  simp only [CollatzResearch.WordTrace]
  refine ⟨127862653939523819899823767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170483538586031759866431689 127862653939523819899823767)
  ·
    refine ⟨191793980909285729849735651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127862653939523819899823767 191793980909285729849735651)
    ·
      refine ⟨287690971363928594774603477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191793980909285729849735651 287690971363928594774603477)
      ·
        refine ⟨6742757141342076440029769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 287690971363928594774603477 6742757141342076440029769)
        ·
          refine ⟨5057067856006557330022327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6742757141342076440029769 5057067856006557330022327)
          ·
            refine ⟨7585601784009835995033491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5057067856006557330022327 7585601784009835995033491)
            ·
              refine ⟨11378402676014753992550237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7585601784009835995033491 11378402676014753992550237)
              ·
                refine ⟨4266901003505532747206339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11378402676014753992550237 4266901003505532747206339)
                ·
                  refine ⟨6400351505258299120809509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4266901003505532747206339 6400351505258299120809509)
                  ·
                    refine ⟨1200065907235931085151783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6400351505258299120809509 1200065907235931085151783)
                    ·
                      rfl

theorem cell23_7011360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3, 1, 4].length) (baseStart_7011360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011360 prefixEnd_7011360 := by exact prefixLift 7011360
  have htrace : WordTrace (prefixWord ++ tailWord_7011360) baseStart_7011360 baseEnd_7011360 := by
    simpa [prefixWord, tailWord_7011360, baseEnd_7011360] using wordTrace_append hprefix tailTrace_7011360
  have hstable : (prefixWord ++ tailWord_7011360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011360).length < 2 ^ (prefixWord ++ tailWord_7011360).sum := by decide
  have hdescent : baseEnd_7011360 < baseStart_7011360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011365 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 3, 6]
def baseStart_7011365 : Nat := 118140960795 + 7011365 * 2 ^ 59
def prefixEnd_7011365 : Nat := 4983230072969 + 3 ^ 40 * 7011365 * 2
def baseEnd_7011365 : Nat := 1200066763037021911964275

theorem tailTrace_7011365 : CollatzResearch.WordTrace tailWord_7011365 prefixEnd_7011365 1200066763037021911964275 := by
  unfold tailWord_7011365
  simp only [CollatzResearch.WordTrace]
  refine ⟨255725490244029525653579549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170483660162686350435719699 255725490244029525653579549)
  ·
    refine ⟨95897058841511072120092331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255725490244029525653579549 95897058841511072120092331)
    ·
      refine ⟨143845588262266608180138497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95897058841511072120092331 143845588262266608180138497)
      ·
        refine ⟨107884191196699956135103873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143845588262266608180138497 107884191196699956135103873)
        ·
          refine ⟨80913143397524967101327905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107884191196699956135103873 80913143397524967101327905)
          ·
            refine ⟨60684857548143725325995929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80913143397524967101327905 60684857548143725325995929)
            ·
              refine ⟨45513643161107793994496947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60684857548143725325995929 45513643161107793994496947)
              ·
                refine ⟨68270464741661690991745421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45513643161107793994496947 68270464741661690991745421)
                ·
                  refine ⟨25601424278123134121904533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68270464741661690991745421 25601424278123134121904533)
                  ·
                    refine ⟨1200066763037021911964275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25601424278123134121904533 1200066763037021911964275)
                    ·
                      rfl

theorem cell23_7011365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 6].length) (baseStart_7011365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011365 prefixEnd_7011365 := by exact prefixLift 7011365
  have htrace : WordTrace (prefixWord ++ tailWord_7011365) baseStart_7011365 baseEnd_7011365 := by
    simpa [prefixWord, tailWord_7011365, baseEnd_7011365] using wordTrace_append hprefix tailTrace_7011365
  have hstable : (prefixWord ++ tailWord_7011365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011365).length < 2 ^ (prefixWord ++ tailWord_7011365).sum := by decide
  have hdescent : baseEnd_7011365 < baseStart_7011365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011372 : List Nat := [2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 4]
def baseStart_7011372 : Nat := 118140960795 + 7011372 * 2 ^ 59
def prefixEnd_7011372 : Nat := 4983230072969 + 3 ^ 40 * 7011372 * 2
def baseEnd_7011372 : Nat := 3600203883475647208505293

theorem tailTrace_7011372 : CollatzResearch.WordTrace tailWord_7011372 prefixEnd_7011372 3600203883475647208505293 := by
  unfold tailWord_7011372
  simp only [CollatzResearch.WordTrace]
  refine ⟨127862872777502082924542185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170483830370002777232722913 127862872777502082924542185)
  ·
    refine ⟨95897154583126562193406639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127862872777502082924542185 95897154583126562193406639)
    ·
      refine ⟨143845731874689843290109959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95897154583126562193406639 143845731874689843290109959)
      ·
        refine ⟨215768597812034764935164939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143845731874689843290109959 215768597812034764935164939)
        ·
          refine ⟨323652896718052147402747409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215768597812034764935164939 323652896718052147402747409)
          ·
            refine ⟨242739672538539110552060557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323652896718052147402747409 242739672538539110552060557)
            ·
              refine ⟨91027377201952166457022709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242739672538539110552060557 91027377201952166457022709)
              ·
                refine ⟨8533816612683015605345879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91027377201952166457022709 8533816612683015605345879)
                ·
                  refine ⟨12800724919024523408018819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8533816612683015605345879 12800724919024523408018819)
                  ·
                    refine ⟨19201087378536785112028229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12800724919024523408018819 19201087378536785112028229)
                    ·
                      refine ⟨3600203883475647208505293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19201087378536785112028229 3600203883475647208505293)
                      ·
                        rfl

theorem cell23_7011372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 4].length) (baseStart_7011372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011372 prefixEnd_7011372 := by exact prefixLift 7011372
  have htrace : WordTrace (prefixWord ++ tailWord_7011372) baseStart_7011372 baseEnd_7011372 := by
    simpa [prefixWord, tailWord_7011372, baseEnd_7011372] using wordTrace_append hprefix tailTrace_7011372
  have hstable : (prefixWord ++ tailWord_7011372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011372).length < 2 ^ (prefixWord ++ tailWord_7011372).sum := by decide
  have hdescent : baseEnd_7011372 < baseStart_7011372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011375 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 1, 8, 3]
def baseStart_7011375 : Nat := 118140960795 + 7011375 * 2 ^ 59
def prefixEnd_7011375 : Nat := 4983230072969 + 3 ^ 40 * 7011375 * 2
def baseEnd_7011375 : Nat := 3600205423917610696767779

theorem tailTrace_7011375 : CollatzResearch.WordTrace tailWord_7011375 prefixEnd_7011375 3600205423917610696767779 := by
  unfold tailWord_7011375
  simp only [CollatzResearch.WordTrace]
  refine ⟨255725854973993297361443579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170483903315995531574295719 255725854973993297361443579)
  ·
    refine ⟨383588782460989946042165369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255725854973993297361443579 383588782460989946042165369)
    ·
      refine ⟨287691586845742459531624027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383588782460989946042165369 287691586845742459531624027)
      ·
        refine ⟨431537380268613689297436041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287691586845742459531624027 431537380268613689297436041)
        ·
          refine ⟨323653035201460266973077031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431537380268613689297436041 323653035201460266973077031)
          ·
            refine ⟨485479552802190400459615547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323653035201460266973077031 485479552802190400459615547)
            ·
              refine ⟨728219329203285600689423321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485479552802190400459615547 728219329203285600689423321)
              ·
                refine ⟨546164496902464200517067491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 728219329203285600689423321 546164496902464200517067491)
                ·
                  refine ⟨819246745353696300775601237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 546164496902464200517067491 819246745353696300775601237)
                  ·
                    refine ⟨9600547797113628524714077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 819246745353696300775601237 9600547797113628524714077)
                    ·
                      refine ⟨3600205423917610696767779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9600547797113628524714077 3600205423917610696767779)
                      ·
                        rfl

theorem cell23_7011375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8, 3].length) (baseStart_7011375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011375 prefixEnd_7011375 := by exact prefixLift 7011375
  have htrace : WordTrace (prefixWord ++ tailWord_7011375) baseStart_7011375 baseEnd_7011375 := by
    simpa [prefixWord, tailWord_7011375, baseEnd_7011375] using wordTrace_append hprefix tailTrace_7011375
  have hstable : (prefixWord ++ tailWord_7011375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011375).length < 2 ^ (prefixWord ++ tailWord_7011375).sum := by decide
  have hdescent : baseEnd_7011375 < baseStart_7011375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011392 : List Nat := [2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 3]
def baseStart_7011392 : Nat := 118140960795 + 7011392 * 2 ^ 59
def prefixEnd_7011392 : Nat := 4983230072969 + 3 ^ 40 * 7011392 * 2
def baseEnd_7011392 : Nat := 3600214153088737130255201

theorem tailTrace_7011392 : CollatzResearch.WordTrace tailWord_7011392 prefixEnd_7011392 3600214153088737130255201 := by
  unfold tailWord_7011392
  simp only [CollatzResearch.WordTrace]
  refine ⟨127863237507465854632406215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170484316676621139509874953 127863237507465854632406215)
  ·
    refine ⟨191794856261198781948609323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127863237507465854632406215 191794856261198781948609323)
    ·
      refine ⟨287692284391798172922913985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191794856261198781948609323 287692284391798172922913985)
      ·
        refine ⟨215769213293848629692185489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287692284391798172922913985 215769213293848629692185489)
        ·
          refine ⟨161826909970386472269139117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215769213293848629692185489 161826909970386472269139117)
          ·
            refine ⟨60685091238894927100927169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161826909970386472269139117 60685091238894927100927169)
            ·
              refine ⟨45513818429171195325695377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60685091238894927100927169 45513818429171195325695377)
              ·
                refine ⟨34135363821878396494271533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45513818429171195325695377 34135363821878396494271533)
                ·
                  refine ⟨12800761433204398685351825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34135363821878396494271533 12800761433204398685351825)
                  ·
                    refine ⟨9600571074903299014013869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12800761433204398685351825 9600571074903299014013869)
                    ·
                      refine ⟨3600214153088737130255201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9600571074903299014013869 3600214153088737130255201)
                      ·
                        rfl

theorem cell23_7011392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 3].length) (baseStart_7011392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011392 prefixEnd_7011392 := by exact prefixLift 7011392
  have htrace : WordTrace (prefixWord ++ tailWord_7011392) baseStart_7011392 baseEnd_7011392 := by
    simpa [prefixWord, tailWord_7011392, baseEnd_7011392] using wordTrace_append hprefix tailTrace_7011392
  have hstable : (prefixWord ++ tailWord_7011392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011392).length < 2 ^ (prefixWord ++ tailWord_7011392).sum := by decide
  have hdescent : baseEnd_7011392 < baseStart_7011392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011395 : List Nat := [1, 1, 1, 3, 1, 2, 6, 8]
def baseStart_7011395 : Nat := 118140960795 + 7011395 * 2 ^ 59
def prefixEnd_7011395 : Nat := 4983230072969 + 3 ^ 40 * 7011395 * 2
def baseEnd_7011395 : Nat := 133341321982618541426581

theorem tailTrace_7011395 : CollatzResearch.WordTrace tailWord_7011395 prefixEnd_7011395 133341321982618541426581 := by
  unfold tailWord_7011395
  simp only [CollatzResearch.WordTrace]
  refine ⟨255726584433920840777171639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170484389622613893851447759 255726584433920840777171639)
  ·
    refine ⟨383589876650881261165757459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255726584433920840777171639 383589876650881261165757459)
    ·
      refine ⟨575384814976321891748636189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383589876650881261165757459 575384814976321891748636189)
      ·
        refine ⟨215769305616120709405738571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 575384814976321891748636189 215769305616120709405738571)
        ·
          refine ⟨323653958424181064108607857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215769305616120709405738571 323653958424181064108607857)
          ·
            refine ⟨242740468818135798081455893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323653958424181064108607857 242740468818135798081455893)
            ·
              refine ⟨11378459475850115535068245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 242740468818135798081455893 11378459475850115535068245)
              ·
                refine ⟨133341321982618541426581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11378459475850115535068245 133341321982618541426581)
                ·
                  rfl

theorem cell23_7011395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 8].length) (baseStart_7011395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011395 prefixEnd_7011395 := by exact prefixLift 7011395
  have htrace : WordTrace (prefixWord ++ tailWord_7011395) baseStart_7011395 baseEnd_7011395 := by
    simpa [prefixWord, tailWord_7011395, baseEnd_7011395] using wordTrace_append hprefix tailTrace_7011395
  have hstable : (prefixWord ++ tailWord_7011395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011395).length < 2 ^ (prefixWord ++ tailWord_7011395).sum := by decide
  have hdescent : baseEnd_7011395 < baseStart_7011395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011399 : List Nat := [1, 1, 4, 1, 3, 3, 1, 3, 2, 4]
def baseStart_7011399 : Nat := 118140960795 + 7011399 * 2 ^ 59
def prefixEnd_7011399 : Nat := 4983230072969 + 3 ^ 40 * 7011399 * 2
def baseEnd_7011399 : Nat := 1200072582484439534289223

theorem tailTrace_7011399 : CollatzResearch.WordTrace tailWord_7011399 prefixEnd_7011399 1200072582484439534289223 := by
  unfold tailWord_7011399
  simp only [CollatzResearch.WordTrace]
  refine ⟨255726730325906349460317251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170484486883937566306878167 255726730325906349460317251)
  ·
    refine ⟨383590095488859524190475877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255726730325906349460317251 383590095488859524190475877)
    ·
      refine ⟨71923142904161160785714227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 383590095488859524190475877 71923142904161160785714227)
      ·
        refine ⟨107884714356241741178571341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71923142904161160785714227 107884714356241741178571341)
        ·
          refine ⟨40456767883590652941964253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107884714356241741178571341 40456767883590652941964253)
          ·
            refine ⟨15171287956346494853236595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40456767883590652941964253 15171287956346494853236595)
            ·
              refine ⟨22756931934519742279854893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15171287956346494853236595 22756931934519742279854893)
              ·
                refine ⟨8533849475444903354945585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22756931934519742279854893 8533849475444903354945585)
                ·
                  refine ⟨6400387106583677516209189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8533849475444903354945585 6400387106583677516209189)
                  ·
                    refine ⟨1200072582484439534289223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6400387106583677516209189 1200072582484439534289223)
                    ·
                      rfl

theorem cell23_7011399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_7011399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011399 prefixEnd_7011399 := by exact prefixLift 7011399
  have htrace : WordTrace (prefixWord ++ tailWord_7011399) baseStart_7011399 baseEnd_7011399 := by
    simpa [prefixWord, tailWord_7011399, baseEnd_7011399] using wordTrace_append hprefix tailTrace_7011399
  have hstable : (prefixWord ++ tailWord_7011399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011399).length < 2 ^ (prefixWord ++ tailWord_7011399).sum := by decide
  have hdescent : baseEnd_7011399 < baseStart_7011399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011409 : List Nat := [1, 2, 2, 1, 3, 1, 5, 2, 1, 2, 3]
def baseStart_7011409 : Nat := 118140960795 + 7011409 * 2 ^ 59
def prefixEnd_7011409 : Nat := 4983230072969 + 3 ^ 40 * 7011409 * 2
def baseEnd_7011409 : Nat := 3600222882259863563742623

theorem tailTrace_7011409 : CollatzResearch.WordTrace tailWord_7011409 prefixEnd_7011409 3600222882259863563742623 := by
  unfold tailWord_7011409
  simp only [CollatzResearch.WordTrace]
  refine ⟨255727095055870121168181281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170484730037246747445454187 255727095055870121168181281)
  ·
    refine ⟨191795321291902590876135961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255727095055870121168181281 191795321291902590876135961)
    ·
      refine ⟨143846490968926943157101971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191795321291902590876135961 143846490968926943157101971)
      ·
        refine ⟨215769736453390414735652957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143846490968926943157101971 215769736453390414735652957)
        ·
          refine ⟨80913651170021405525869859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215769736453390414735652957 80913651170021405525869859)
          ·
            refine ⟨121370476755032108288804789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80913651170021405525869859 121370476755032108288804789)
            ·
              refine ⟨11378482195784260152075449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121370476755032108288804789 11378482195784260152075449)
              ·
                refine ⟨8533861646838195114056587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11378482195784260152075449 8533861646838195114056587)
                ·
                  refine ⟨12800792470257292671084881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8533861646838195114056587 12800792470257292671084881)
                  ·
                    refine ⟨9600594352692969503313661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12800792470257292671084881 9600594352692969503313661)
                    ·
                      refine ⟨3600222882259863563742623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9600594352692969503313661 3600222882259863563742623)
                      ·
                        rfl

theorem cell23_7011409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 2, 3].length) (baseStart_7011409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011409 prefixEnd_7011409 := by exact prefixLift 7011409
  have htrace : WordTrace (prefixWord ++ tailWord_7011409) baseStart_7011409 baseEnd_7011409 := by
    simpa [prefixWord, tailWord_7011409, baseEnd_7011409] using wordTrace_append hprefix tailTrace_7011409
  have hstable : (prefixWord ++ tailWord_7011409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011409).length < 2 ^ (prefixWord ++ tailWord_7011409).sum := by decide
  have hdescent : baseEnd_7011409 < baseStart_7011409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011426 : List Nat := [3, 3, 2, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_7011426 : Nat := 118140960795 + 7011426 * 2 ^ 59
def prefixEnd_7011426 : Nat := 4983230072969 + 3 ^ 40 * 7011426 * 2
def baseEnd_7011426 : Nat := 3600231611430989997230045

theorem tailTrace_7011426 : CollatzResearch.WordTrace tailWord_7011426 prefixEnd_7011426 3600231611430989997230045 := by
  unfold tailWord_7011426
  simp only [CollatzResearch.WordTrace]
  refine ⟨63931928774202133267887533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170485143397872355381033421 63931928774202133267887533)
  ·
    refine ⟨23974473290325799975457825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63931928774202133267887533 23974473290325799975457825)
    ·
      refine ⟨17980854967744349981593369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23974473290325799975457825 17980854967744349981593369)
      ·
        refine ⟨13485641225808262486195027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17980854967744349981593369 13485641225808262486195027)
        ·
          refine ⟨20228461838712393729292541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13485641225808262486195027 20228461838712393729292541)
          ·
            refine ⟨7585673189517147648484703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20228461838712393729292541 7585673189517147648484703)
            ·
              refine ⟨11378509784275721472727055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7585673189517147648484703 11378509784275721472727055)
              ·
                refine ⟨17067764676413582209090583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11378509784275721472727055 17067764676413582209090583)
                ·
                  refine ⟨25601647014620373313635875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17067764676413582209090583 25601647014620373313635875)
                  ·
                    refine ⟨38402470521930559970453813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25601647014620373313635875 38402470521930559970453813)
                    ·
                      refine ⟨3600231611430989997230045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38402470521930559970453813 3600231611430989997230045)
                      ·
                        rfl

theorem cell23_7011426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_7011426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011426 prefixEnd_7011426 := by exact prefixLift 7011426
  have htrace : WordTrace (prefixWord ++ tailWord_7011426) baseStart_7011426 baseEnd_7011426 := by
    simpa [prefixWord, tailWord_7011426, baseEnd_7011426] using wordTrace_append hprefix tailTrace_7011426
  have hstable : (prefixWord ++ tailWord_7011426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011426).length < 2 ^ (prefixWord ++ tailWord_7011426).sum := by decide
  have hdescent : baseEnd_7011426 < baseStart_7011426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011466 : List Nat := [3, 1, 2, 3, 1, 1, 2, 4, 1, 3, 2]
def baseStart_7011466 : Nat := 118140960795 + 7011466 * 2 ^ 59
def prefixEnd_7011466 : Nat := 4983230072969 + 3 ^ 40 * 7011466 * 2
def baseEnd_7011466 : Nat := 3600252150657169840729861

theorem tailTrace_7011466 : CollatzResearch.WordTrace tailWord_7011466 prefixEnd_7011466 3600252150657169840729861 := by
  unfold tailWord_7011466
  simp only [CollatzResearch.WordTrace]
  refine ⟨63932293504165904975751563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170486116011109079935337501 63932293504165904975751563)
  ·
    refine ⟨95898440256248857463627345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63932293504165904975751563 95898440256248857463627345)
    ·
      refine ⟨71923830192186643097720509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95898440256248857463627345 71923830192186643097720509)
      ·
        refine ⟨26971436322069991161645191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71923830192186643097720509 26971436322069991161645191)
        ·
          refine ⟨40457154483104986742467787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26971436322069991161645191 40457154483104986742467787)
          ·
            refine ⟨60685731724657480113701681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40457154483104986742467787 60685731724657480113701681)
            ·
              refine ⟨45514298793493110085276261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60685731724657480113701681 45514298793493110085276261)
              ·
                refine ⟨8533931023779958140989299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45514298793493110085276261 8533931023779958140989299)
                ·
                  refine ⟨12800896535669937211483949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8533931023779958140989299 12800896535669937211483949)
                  ·
                    refine ⟨4800336200876226454306481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12800896535669937211483949 4800336200876226454306481)
                    ·
                      refine ⟨3600252150657169840729861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4800336200876226454306481 3600252150657169840729861)
                      ·
                        rfl

theorem cell23_7011466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_7011466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011466 prefixEnd_7011466 := by exact prefixLift 7011466
  have htrace : WordTrace (prefixWord ++ tailWord_7011466) baseStart_7011466 baseEnd_7011466 := by
    simpa [prefixWord, tailWord_7011466, baseEnd_7011466] using wordTrace_append hprefix tailTrace_7011466
  have hstable : (prefixWord ++ tailWord_7011466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011466).length < 2 ^ (prefixWord ++ tailWord_7011466).sum := by decide
  have hdescent : baseEnd_7011466 < baseStart_7011466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011490 : List Nat := [3, 3, 1, 3, 2, 2, 1, 2, 2, 1, 3]
def baseStart_7011490 : Nat := 118140960795 + 7011490 * 2 ^ 59
def prefixEnd_7011490 : Nat := 4983230072969 + 3 ^ 40 * 7011490 * 2
def baseEnd_7011490 : Nat := 3600264474192877746829751

theorem tailTrace_7011490 : CollatzResearch.WordTrace tailWord_7011490 prefixEnd_7011490 3600264474192877746829751 := by
  unfold tailWord_7011490
  simp only [CollatzResearch.WordTrace]
  refine ⟨63932512342144168000469981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170486699579051114667919949 63932512342144168000469981)
  ·
    refine ⟨23974692128304063000176243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63932512342144168000469981 23974692128304063000176243)
    ·
      refine ⟨35962038192456094500264365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23974692128304063000176243 35962038192456094500264365)
      ·
        refine ⟨13485764322171035437599137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35962038192456094500264365 13485764322171035437599137)
        ·
          refine ⟨10114323241628276578199353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13485764322171035437599137 10114323241628276578199353)
          ·
            refine ⟨7585742431221207433649515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10114323241628276578199353 7585742431221207433649515)
            ·
              refine ⟨11378613646831811150474273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7585742431221207433649515 11378613646831811150474273)
              ·
                refine ⟨8533960235123858362855705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11378613646831811150474273 8533960235123858362855705)
                ·
                  refine ⟨6400470176342893772141779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8533960235123858362855705 6400470176342893772141779)
                  ·
                    refine ⟨9600705264514340658212669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6400470176342893772141779 9600705264514340658212669)
                    ·
                      refine ⟨3600264474192877746829751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9600705264514340658212669 3600264474192877746829751)
                      ·
                        rfl

theorem cell23_7011490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_7011490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011490 prefixEnd_7011490 := by exact prefixLift 7011490
  have htrace : WordTrace (prefixWord ++ tailWord_7011490) baseStart_7011490 baseEnd_7011490 := by
    simpa [prefixWord, tailWord_7011490, baseEnd_7011490] using wordTrace_append hprefix tailTrace_7011490
  have hstable : (prefixWord ++ tailWord_7011490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011490).length < 2 ^ (prefixWord ++ tailWord_7011490).sum := by decide
  have hdescent : baseEnd_7011490 < baseStart_7011490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011512 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 1, 5, 3]
def baseStart_7011512 : Nat := 118140960795 + 7011512 * 2 ^ 59
def prefixEnd_7011512 : Nat := 4983230072969 + 3 ^ 40 * 7011512 * 2
def baseEnd_7011512 : Nat := 3600275770767276660754649

theorem tailTrace_7011512 : CollatzResearch.WordTrace tailWord_7011512 prefixEnd_7011512 3600275770767276660754649 := by
  unfold tailWord_7011512
  simp only [CollatzResearch.WordTrace]
  refine ⟨127865425887248484879590395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170487234516331313172787193 127865425887248484879590395)
  ·
    refine ⟨191798138830872727319385593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127865425887248484879590395 191798138830872727319385593)
    ·
      refine ⟨143848604123154545489539195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191798138830872727319385593 143848604123154545489539195)
      ·
        refine ⟨215772906184731818234308793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143848604123154545489539195 215772906184731818234308793)
        ·
          refine ⟨161829679638548863675731595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215772906184731818234308793 161829679638548863675731595)
          ·
            refine ⟨242744519457823295513597393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161829679638548863675731595 242744519457823295513597393)
            ·
              refine ⟨182058389593367471635198045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242744519457823295513597393 182058389593367471635198045)
              ·
                refine ⟨68271896097512801863199267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182058389593367471635198045 68271896097512801863199267)
                ·
                  refine ⟨102407844146269202794798901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68271896097512801863199267 102407844146269202794798901)
                  ·
                    refine ⟨9600735388712737762012397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102407844146269202794798901 9600735388712737762012397)
                    ·
                      refine ⟨3600275770767276660754649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9600735388712737762012397 3600275770767276660754649)
                      ·
                        rfl

theorem cell23_7011512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 1, 5, 3].length) (baseStart_7011512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011512 prefixEnd_7011512 := by exact prefixLift 7011512
  have htrace : WordTrace (prefixWord ++ tailWord_7011512) baseStart_7011512 baseEnd_7011512 := by
    simpa [prefixWord, tailWord_7011512, baseEnd_7011512] using wordTrace_append hprefix tailTrace_7011512
  have hstable : (prefixWord ++ tailWord_7011512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011512).length < 2 ^ (prefixWord ++ tailWord_7011512).sum := by decide
  have hdescent : baseEnd_7011512 < baseStart_7011512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011533 : List Nat := [1, 6, 2, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_7011533 : Nat := 118140960795 + 7011533 * 2 ^ 59
def prefixEnd_7011533 : Nat := 4983230072969 + 3 ^ 40 * 7011533 * 2
def baseEnd_7011533 : Nat := 3600286553861021078592053

theorem tailTrace_7011533 : CollatzResearch.WordTrace tailWord_7011533 prefixEnd_7011533 3600286553861021078592053 := by
  unfold tailWord_7011533
  simp only [CollatzResearch.WordTrace]
  refine ⟨255731617707420890345695253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170487745138280593563796835 255731617707420890345695253)
  ·
    refine ⟨11987419580035354234954465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 255731617707420890345695253 11987419580035354234954465)
    ·
      refine ⟨8990564685026515676215849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11987419580035354234954465 8990564685026515676215849)
      ·
        refine ⟨6742923513769886757161887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8990564685026515676215849 6742923513769886757161887)
        ·
          refine ⟨10114385270654830135742831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6742923513769886757161887 10114385270654830135742831)
          ·
            refine ⟨15171577905982245203614247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10114385270654830135742831 15171577905982245203614247)
            ·
              refine ⟨22757366858973367805421371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15171577905982245203614247 22757366858973367805421371)
              ·
                refine ⟨34136050288460051708132057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22757366858973367805421371 34136050288460051708132057)
                ·
                  refine ⟨25602037716345038781099043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34136050288460051708132057 25602037716345038781099043)
                  ·
                    refine ⟨38403056574517558171648565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25602037716345038781099043 38403056574517558171648565)
                    ·
                      refine ⟨3600286553861021078592053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38403056574517558171648565 3600286553861021078592053)
                      ·
                        rfl

theorem cell23_7011533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_7011533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011533 prefixEnd_7011533 := by exact prefixLift 7011533
  have htrace : WordTrace (prefixWord ++ tailWord_7011533) baseStart_7011533 baseEnd_7011533 := by
    simpa [prefixWord, tailWord_7011533, baseEnd_7011533] using wordTrace_append hprefix tailTrace_7011533
  have hstable : (prefixWord ++ tailWord_7011533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011533).length < 2 ^ (prefixWord ++ tailWord_7011533).sum := by decide
  have hdescent : baseEnd_7011533 < baseStart_7011533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011569 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 1, 6, 2]
def baseStart_7011569 : Nat := 118140960795 + 7011569 * 2 ^ 59
def prefixEnd_7011569 : Nat := 4983230072969 + 3 ^ 40 * 7011569 * 2
def baseEnd_7011569 : Nat := 3600305039164582937741887

theorem tailTrace_7011569 : CollatzResearch.WordTrace tailWord_7011569 prefixEnd_7011569 3600305039164582937741887 := by
  unfold tailWord_7011569
  simp only [CollatzResearch.WordTrace]
  refine ⟨255732930735290468494005761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170488620490193645662670507 255732930735290468494005761)
  ·
    refine ⟨191799698051467851370504321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255732930735290468494005761 191799698051467851370504321)
    ·
      refine ⟨143849773538600888527878241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191799698051467851370504321 143849773538600888527878241)
      ·
        refine ⟨107887330153950666395908681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143849773538600888527878241 107887330153950666395908681)
        ·
          refine ⟨80915497615462999796931511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107887330153950666395908681 80915497615462999796931511)
          ·
            refine ⟨121373246423194499695397267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80915497615462999796931511 121373246423194499695397267)
            ·
              refine ⟨182059869634791749543095901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121373246423194499695397267 182059869634791749543095901)
              ·
                refine ⟨68272451113046906078660963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182059869634791749543095901 68272451113046906078660963)
                ·
                  refine ⟨102408676669570359117991445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68272451113046906078660963 102408676669570359117991445)
                  ·
                    refine ⟨4800406718886110583655849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 102408676669570359117991445 4800406718886110583655849)
                    ·
                      refine ⟨3600305039164582937741887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4800406718886110583655849 3600305039164582937741887)
                      ·
                        rfl

theorem cell23_7011569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 6, 2].length) (baseStart_7011569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011569 prefixEnd_7011569 := by exact prefixLift 7011569
  have htrace : WordTrace (prefixWord ++ tailWord_7011569) baseStart_7011569 baseEnd_7011569 := by
    simpa [prefixWord, tailWord_7011569, baseEnd_7011569] using wordTrace_append hprefix tailTrace_7011569
  have hstable : (prefixWord ++ tailWord_7011569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011569).length < 2 ^ (prefixWord ++ tailWord_7011569).sum := by decide
  have hdescent : baseEnd_7011569 < baseStart_7011569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011626 : List Nat := [3, 1, 4, 2, 1, 1, 2, 3, 6]
def baseStart_7011626 : Nat := 118140960795 + 7011626 * 2 ^ 59
def prefixEnd_7011626 : Nat := 4983230072969 + 3 ^ 40 * 7011626 * 2
def baseEnd_7011626 : Nat := 400037145284654357192125

theorem tailTrace_7011626 : CollatzResearch.WordTrace tailWord_7011626 prefixEnd_7011626 400037145284654357192125 := by
  unfold tailWord_7011626
  simp only [CollatzResearch.WordTrace]
  refine ⟨63933752424020991807207683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170490006464055978152553821 63933752424020991807207683)
  ·
    refine ⟨95900628636031487710811525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63933752424020991807207683 95900628636031487710811525)
    ·
      refine ⟨17981367869255903945777161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95900628636031487710811525 17981367869255903945777161)
      ·
        refine ⟨13486025901941927959332871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17981367869255903945777161 13486025901941927959332871)
        ·
          refine ⟨20229038852912891938999307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13486025901941927959332871 20229038852912891938999307)
          ·
            refine ⟨30343558279369337908498961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20229038852912891938999307 30343558279369337908498961)
            ·
              refine ⟨22757668709527003431374221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30343558279369337908498961 22757668709527003431374221)
              ·
                refine ⟨8534125766072626286765333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22757668709527003431374221 8534125766072626286765333)
                ·
                  refine ⟨400037145284654357192125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8534125766072626286765333 400037145284654357192125)
                  ·
                    rfl

theorem cell23_7011626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 6].length) (baseStart_7011626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011626 prefixEnd_7011626 := by exact prefixLift 7011626
  have htrace : WordTrace (prefixWord ++ tailWord_7011626) baseStart_7011626 baseEnd_7011626 := by
    simpa [prefixWord, tailWord_7011626, baseEnd_7011626] using wordTrace_append hprefix tailTrace_7011626
  have hstable : (prefixWord ++ tailWord_7011626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011626).length < 2 ^ (prefixWord ++ tailWord_7011626).sum := by decide
  have hdescent : baseEnd_7011626 < baseStart_7011626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011632 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 7]
def baseStart_7011632 : Nat := 118140960795 + 7011632 * 2 ^ 59
def prefixEnd_7011632 : Nat := 4983230072969 + 3 ^ 40 * 7011632 * 2
def baseEnd_7011632 : Nat := 3600337388445816191254097

theorem tailTrace_7011632 : CollatzResearch.WordTrace tailWord_7011632 prefixEnd_7011632 3600337388445816191254097 := by
  unfold tailWord_7011632
  simp only [CollatzResearch.WordTrace]
  refine ⟨127867614267031115126774575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170490152356041486835699433 127867614267031115126774575)
  ·
    refine ⟨191801421400546672690161863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127867614267031115126774575 191801421400546672690161863)
    ·
      refine ⟨287702132100820009035242795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191801421400546672690161863 287702132100820009035242795)
      ·
        refine ⟨431553198151230013552864193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287702132100820009035242795 431553198151230013552864193)
        ·
          refine ⟨323664898613422510164648145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431553198151230013552864193 323664898613422510164648145)
          ·
            refine ⟨242748673960066882623486109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323664898613422510164648145 242748673960066882623486109)
            ·
              refine ⟨91030752735025080983807291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242748673960066882623486109 91030752735025080983807291)
              ·
                refine ⟨136546129102537621475710937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91030752735025080983807291 136546129102537621475710937)
                ·
                  refine ⟨102409596826903216106783203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136546129102537621475710937 102409596826903216106783203)
                  ·
                    refine ⟨153614395240354824160174805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102409596826903216106783203 153614395240354824160174805)
                    ·
                      refine ⟨3600337388445816191254097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 153614395240354824160174805 3600337388445816191254097)
                      ·
                        rfl

theorem cell23_7011632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 7].length) (baseStart_7011632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011632 prefixEnd_7011632 := by exact prefixLift 7011632
  have htrace : WordTrace (prefixWord ++ tailWord_7011632) baseStart_7011632 baseEnd_7011632 := by
    simpa [prefixWord, tailWord_7011632, baseEnd_7011632] using wordTrace_append hprefix tailTrace_7011632
  have hstable : (prefixWord ++ tailWord_7011632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011632).length < 2 ^ (prefixWord ++ tailWord_7011632).sum := by decide
  have hdescent : baseEnd_7011632 < baseStart_7011632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011677 : List Nat := [1, 4, 5, 1, 1, 1, 3, 1, 6]
def baseStart_7011677 : Nat := 118140960795 + 7011677 * 2 ^ 59
def prefixEnd_7011677 : Nat := 4983230072969 + 3 ^ 40 * 7011677 * 2
def baseEnd_7011677 : Nat := 400040055008363168354599

theorem tailTrace_7011677 : CollatzResearch.WordTrace tailWord_7011677 prefixEnd_7011677 400040055008363168354599 := by
  unfold tailWord_7011677
  simp only [CollatzResearch.WordTrace]
  refine ⟨255736869818899202938937285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170491246545932801959291523 255736869818899202938937285)
  ·
    refine ⟨47950663091043600551050741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255736869818899202938937285 47950663091043600551050741)
    ·
      refine ⟨4495374664785337551661007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47950663091043600551050741 4495374664785337551661007)
      ·
        refine ⟨6743061997178006327491511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4495374664785337551661007 6743061997178006327491511)
        ·
          refine ⟨10114592995767009491237267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6743061997178006327491511 10114592995767009491237267)
          ·
            refine ⟨15171889493650514236855901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10114592995767009491237267 15171889493650514236855901)
            ·
              refine ⟨5689458560118942838820963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15171889493650514236855901 5689458560118942838820963)
              ·
                refine ⟨8534187840178414258231445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5689458560118942838820963 8534187840178414258231445)
                ·
                  refine ⟨400040055008363168354599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8534187840178414258231445 400040055008363168354599)
                  ·
                    rfl

theorem cell23_7011677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 6].length) (baseStart_7011677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011677 prefixEnd_7011677 := by exact prefixLift 7011677
  have htrace : WordTrace (prefixWord ++ tailWord_7011677) baseStart_7011677 baseEnd_7011677 := by
    simpa [prefixWord, tailWord_7011677, baseEnd_7011677] using wordTrace_append hprefix tailTrace_7011677
  have hstable : (prefixWord ++ tailWord_7011677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011677).length < 2 ^ (prefixWord ++ tailWord_7011677).sum := by decide
  have hdescent : baseEnd_7011677 < baseStart_7011677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011689 : List Nat := [1, 2, 1, 1, 1, 3, 2, 5, 1, 2, 4]
def baseStart_7011689 : Nat := 118140960795 + 7011689 * 2 ^ 59
def prefixEnd_7011689 : Nat := 4983230072969 + 3 ^ 40 * 7011689 * 2
def baseEnd_7011689 : Nat := 3600366656843122468241335

theorem tailTrace_7011689 : CollatzResearch.WordTrace tailWord_7011689 prefixEnd_7011689 3600366656843122468241335 := by
  unfold tailWord_7011689
  simp only [CollatzResearch.WordTrace]
  refine ⟨255737307494855728988374121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170491538329903819325582747 255737307494855728988374121)
  ·
    refine ⟨191802980621141796741280591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255737307494855728988374121 191802980621141796741280591)
    ·
      refine ⟨287704470931712695111920887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191802980621141796741280591 287704470931712695111920887)
      ·
        refine ⟨431556706397569042667881331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287704470931712695111920887 431556706397569042667881331)
        ·
          refine ⟨647335059596353564001821997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431556706397569042667881331 647335059596353564001821997)
          ·
            refine ⟨242750647348632586500683249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 647335059596353564001821997 242750647348632586500683249)
            ·
              refine ⟨182062985511474439875512437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242750647348632586500683249 182062985511474439875512437)
              ·
                refine ⟨17068404891700728738329291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 182062985511474439875512437 17068404891700728738329291)
                ·
                  refine ⟨25602607337551093107493937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17068404891700728738329291 25602607337551093107493937)
                  ·
                    refine ⟨19201955503163319830620453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25602607337551093107493937 19201955503163319830620453)
                    ·
                      refine ⟨3600366656843122468241335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19201955503163319830620453 3600366656843122468241335)
                      ·
                        rfl

theorem cell23_7011689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 2, 4].length) (baseStart_7011689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011689 prefixEnd_7011689 := by exact prefixLift 7011689
  have htrace : WordTrace (prefixWord ++ tailWord_7011689) baseStart_7011689 baseEnd_7011689 := by
    simpa [prefixWord, tailWord_7011689, baseEnd_7011689] using wordTrace_append hprefix tailTrace_7011689
  have hstable : (prefixWord ++ tailWord_7011689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011689).length < 2 ^ (prefixWord ++ tailWord_7011689).sum := by decide
  have hdescent : baseEnd_7011689 < baseStart_7011689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011693 : List Nat := [1, 5, 1, 1, 1, 4, 2, 2, 1, 1, 4]
def baseStart_7011693 : Nat := 118140960795 + 7011693 * 2 ^ 59
def prefixEnd_7011693 : Nat := 4983230072969 + 3 ^ 40 * 7011693 * 2
def baseEnd_7011693 : Nat := 3600368710765740452591317

theorem tailTrace_7011693 : CollatzResearch.WordTrace tailWord_7011693 prefixEnd_7011693 3600368710765740452591317 := by
  unfold tailWord_7011693
  simp only [CollatzResearch.WordTrace]
  refine ⟨255737453386841237671519733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170491635591227491781013155 255737453386841237671519733)
  ·
    refine ⟨23975386255016366031704975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 255737453386841237671519733 23975386255016366031704975)
    ·
      refine ⟨35963079382524549047557463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23975386255016366031704975 35963079382524549047557463)
      ·
        refine ⟨53944619073786823571336195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35963079382524549047557463 53944619073786823571336195)
        ·
          refine ⟨80916928610680235357004293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53944619073786823571336195 80916928610680235357004293)
          ·
            refine ⟨15171924114502544129438305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80916928610680235357004293 15171924114502544129438305)
            ·
              refine ⟨11378943085876908097078729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15171924114502544129438305 11378943085876908097078729)
              ·
                refine ⟨8534207314407681072809047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11378943085876908097078729 8534207314407681072809047)
                ·
                  refine ⟨12801310971611521609213571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8534207314407681072809047 12801310971611521609213571)
                  ·
                    refine ⟨19201966457417282413820357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12801310971611521609213571 19201966457417282413820357)
                    ·
                      refine ⟨3600368710765740452591317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19201966457417282413820357 3600368710765740452591317)
                      ·
                        rfl

theorem cell23_7011693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_7011693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011693 prefixEnd_7011693 := by exact prefixLift 7011693
  have htrace : WordTrace (prefixWord ++ tailWord_7011693) baseStart_7011693 baseEnd_7011693 := by
    simpa [prefixWord, tailWord_7011693, baseEnd_7011693] using wordTrace_append hprefix tailTrace_7011693
  have hstable : (prefixWord ++ tailWord_7011693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011693).length < 2 ^ (prefixWord ++ tailWord_7011693).sum := by decide
  have hdescent : baseEnd_7011693 < baseStart_7011693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011713 : List Nat := [1, 2, 4, 3, 2, 1, 2, 1, 1, 1, 5]
def baseStart_7011713 : Nat := 118140960795 + 7011713 * 2 ^ 59
def prefixEnd_7011713 : Nat := 4983230072969 + 3 ^ 40 * 7011713 * 2
def baseEnd_7011713 : Nat := 3600378980378830374341225

theorem tailTrace_7011713 : CollatzResearch.WordTrace tailWord_7011713 prefixEnd_7011713 3600378980378830374341225 := by
  unfold tailWord_7011713
  simp only [CollatzResearch.WordTrace]
  refine ⟨255738182846768781087247793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170492121897845854058165195 255738182846768781087247793)
  ·
    refine ⟨191803637135076585815435845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255738182846768781087247793 191803637135076585815435845)
    ·
      refine ⟨35963181962826859840394221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191803637135076585815435845 35963181962826859840394221)
      ·
        refine ⟨13486193236060072440147833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35963181962826859840394221 13486193236060072440147833)
        ·
          refine ⟨10114644927045054330110875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13486193236060072440147833 10114644927045054330110875)
          ·
            refine ⟨15171967390567581495166313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10114644927045054330110875 15171967390567581495166313)
            ·
              refine ⟨11378975542925686121374735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15171967390567581495166313 11378975542925686121374735)
              ·
                refine ⟨17068463314388529182062103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11378975542925686121374735 17068463314388529182062103)
                ·
                  refine ⟨25602694971582793773093155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17068463314388529182062103 25602694971582793773093155)
                  ·
                    refine ⟨38404042457374190659639733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25602694971582793773093155 38404042457374190659639733)
                    ·
                      refine ⟨3600378980378830374341225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38404042457374190659639733 3600378980378830374341225)
                      ·
                        rfl

theorem cell23_7011713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_7011713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011713 prefixEnd_7011713 := by exact prefixLift 7011713
  have htrace : WordTrace (prefixWord ++ tailWord_7011713) baseStart_7011713 baseEnd_7011713 := by
    simpa [prefixWord, tailWord_7011713, baseEnd_7011713] using wordTrace_append hprefix tailTrace_7011713
  have hstable : (prefixWord ++ tailWord_7011713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011713).length < 2 ^ (prefixWord ++ tailWord_7011713).sum := by decide
  have hdescent : baseEnd_7011713 < baseStart_7011713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011749 : List Nat := [1, 3, 1, 2, 1, 1, 2, 1, 4, 3, 4]
def baseStart_7011749 : Nat := 118140960795 + 7011749 * 2 ^ 59
def prefixEnd_7011749 : Nat := 4983230072969 + 3 ^ 40 * 7011749 * 2
def baseEnd_7011749 : Nat := 3600397465682392233491059

theorem tailTrace_7011749 : CollatzResearch.WordTrace tailWord_7011749 prefixEnd_7011749 3600397465682392233491059 := by
  unfold tailWord_7011749
  simp only [CollatzResearch.WordTrace]
  refine ⟨255739495874638359235558301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170492997249758906157038867 255739495874638359235558301)
  ·
    refine ⟨95902310952989384713334363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255739495874638359235558301 95902310952989384713334363)
    ·
      refine ⟨143853466429484077070001545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95902310952989384713334363 143853466429484077070001545)
      ·
        refine ⟨107890099822113057802501159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143853466429484077070001545 107890099822113057802501159)
        ·
          refine ⟨161835149733169586703751739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107890099822113057802501159 161835149733169586703751739)
          ·
            refine ⟨242752724599754380055627609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161835149733169586703751739 242752724599754380055627609)
            ·
              refine ⟨182064543449815785041720707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242752724599754380055627609 182064543449815785041720707)
              ·
                refine ⟨273096815174723677562581061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182064543449815785041720707 273096815174723677562581061)
                ·
                  refine ⟨51205652845260689542983949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 273096815174723677562581061 51205652845260689542983949)
                  ·
                    refine ⟨19202119816972758578618981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51205652845260689542983949 19202119816972758578618981)
                    ·
                      refine ⟨3600397465682392233491059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19202119816972758578618981 3600397465682392233491059)
                      ·
                        rfl

theorem cell23_7011749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_7011749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011749 prefixEnd_7011749 := by exact prefixLift 7011749
  have htrace : WordTrace (prefixWord ++ tailWord_7011749) baseStart_7011749 baseEnd_7011749 := by
    simpa [prefixWord, tailWord_7011749, baseEnd_7011749] using wordTrace_append hprefix tailTrace_7011749
  have hstable : (prefixWord ++ tailWord_7011749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011749).length < 2 ^ (prefixWord ++ tailWord_7011749).sum := by decide
  have hdescent : baseEnd_7011749 < baseStart_7011749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011786 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 2, 4, 3]
def baseStart_7011786 : Nat := 118140960795 + 7011786 * 2 ^ 59
def prefixEnd_7011786 : Nat := 4983230072969 + 3 ^ 40 * 7011786 * 2
def baseEnd_7011786 : Nat := 3600416464466608588728389

theorem tailTrace_7011786 : CollatzResearch.WordTrace tailWord_7011786 prefixEnd_7011786 3600416464466608588728389 := by
  unfold tailWord_7011786
  simp only [CollatzResearch.WordTrace]
  refine ⟨63935211343876078638663803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170493896917002876369770141 63935211343876078638663803)
  ·
    refine ⟨95902817015814117957995705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63935211343876078638663803 95902817015814117957995705)
    ·
      refine ⟨71927112761860588468496779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95902817015814117957995705 71927112761860588468496779)
      ·
        refine ⟨107890669142790882702745169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71927112761860588468496779 107890669142790882702745169)
        ·
          refine ⟨80918001857093162027058877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107890669142790882702745169 80918001857093162027058877)
          ·
            refine ⟨30344250696409935760147079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80918001857093162027058877 30344250696409935760147079)
            ·
              refine ⟨45516376044614903640220619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30344250696409935760147079 45516376044614903640220619)
              ·
                refine ⟨68274564066922355460330929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45516376044614903640220619 68274564066922355460330929)
                ·
                  refine ⟨51205923050191766595248197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68274564066922355460330929 51205923050191766595248197)
                  ·
                    refine ⟨9601110571910956236609037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51205923050191766595248197 9601110571910956236609037)
                    ·
                      refine ⟨3600416464466608588728389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9601110571910956236609037 3600416464466608588728389)
                      ·
                        rfl

theorem cell23_7011786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_7011786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011786 prefixEnd_7011786 := by exact prefixLift 7011786
  have htrace : WordTrace (prefixWord ++ tailWord_7011786) baseStart_7011786 baseEnd_7011786 := by
    simpa [prefixWord, tailWord_7011786, baseEnd_7011786] using wordTrace_append hprefix tailTrace_7011786
  have hstable : (prefixWord ++ tailWord_7011786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011786).length < 2 ^ (prefixWord ++ tailWord_7011786).sum := by decide
  have hdescent : baseEnd_7011786 < baseStart_7011786 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011800 : List Nat := [2, 1, 2, 2, 2, 1, 4, 3, 2, 2, 2]
def baseStart_7011800 : Nat := 118140960795 + 7011800 * 2 ^ 59
def prefixEnd_7011800 : Nat := 4983230072969 + 3 ^ 40 * 7011800 * 2
def baseEnd_7011800 : Nat := 3600423653195771533953325

theorem tailTrace_7011800 : CollatzResearch.WordTrace tailWord_7011800 prefixEnd_7011800 3600423653195771533953325 := by
  unfold tailWord_7011800
  simp only [CollatzResearch.WordTrace]
  refine ⟨127870677998726797472832427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170494237331635729963776569 127870677998726797472832427)
  ·
    refine ⟨191806016998090196209248641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127870677998726797472832427 191806016998090196209248641)
    ·
      refine ⟨143854512748567647156936481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191806016998090196209248641 143854512748567647156936481)
      ·
        refine ⟨107890884561425735367702361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143854512748567647156936481 107890884561425735367702361)
        ·
          refine ⟨80918163421069301525776771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107890884561425735367702361 80918163421069301525776771)
          ·
            refine ⟨121377245131603952288665157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80918163421069301525776771 121377245131603952288665157)
            ·
              refine ⟨22758233462175741054124717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121377245131603952288665157 22758233462175741054124717)
              ·
                refine ⟨8534337548315902895296769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22758233462175741054124717 8534337548315902895296769)
                ·
                  refine ⟨6400753161236927171472577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8534337548315902895296769 6400753161236927171472577)
                  ·
                    refine ⟨4800564870927695378604433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6400753161236927171472577 4800564870927695378604433)
                    ·
                      refine ⟨3600423653195771533953325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4800564870927695378604433 3600423653195771533953325)
                      ·
                        rfl

theorem cell23_7011800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 3, 2, 2, 2].length) (baseStart_7011800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011800 prefixEnd_7011800 := by exact prefixLift 7011800
  have htrace : WordTrace (prefixWord ++ tailWord_7011800) baseStart_7011800 baseEnd_7011800 := by
    simpa [prefixWord, tailWord_7011800, baseEnd_7011800] using wordTrace_append hprefix tailTrace_7011800
  have hstable : (prefixWord ++ tailWord_7011800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011800).length < 2 ^ (prefixWord ++ tailWord_7011800).sum := by decide
  have hdescent : baseEnd_7011800 < baseStart_7011800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011816 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 1, 5, 3]
def baseStart_7011816 : Nat := 118140960795 + 7011816 * 2 ^ 59
def prefixEnd_7011816 : Nat := 4983230072969 + 3 ^ 40 * 7011816 * 2
def baseEnd_7011816 : Nat := 3600431868886243471353251

theorem tailTrace_7011816 : CollatzResearch.WordTrace tailWord_7011816 prefixEnd_7011816 3600431868886243471353251 := by
  unfold tailWord_7011816
  simp only [CollatzResearch.WordTrace]
  refine ⟨127870969782697814839123651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170494626376930419785498201 127870969782697814839123651)
  ·
    refine ⟨191806454674046722258685477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127870969782697814839123651 191806454674046722258685477)
    ·
      refine ⟨35963710251383760423503527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191806454674046722258685477 35963710251383760423503527)
      ·
        refine ⟨53945565377075640635255291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35963710251383760423503527 53945565377075640635255291)
        ·
          refine ⟨80918348065613460952882937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53945565377075640635255291 80918348065613460952882937)
          ·
            refine ⟨60688761049210095714662203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80918348065613460952882937 60688761049210095714662203)
            ·
              refine ⟨91033141573815143571993305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60688761049210095714662203 91033141573815143571993305)
              ·
                refine ⟨68274856180361357678994979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91033141573815143571993305 68274856180361357678994979)
                ·
                  refine ⟨102412284270542036518492469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68274856180361357678994979 102412284270542036518492469)
                  ·
                    refine ⟨9601151650363315923608669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102412284270542036518492469 9601151650363315923608669)
                    ·
                      refine ⟨3600431868886243471353251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9601151650363315923608669 3600431868886243471353251)
                      ·
                        rfl

theorem cell23_7011816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_7011816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011816 prefixEnd_7011816 := by exact prefixLift 7011816
  have htrace : WordTrace (prefixWord ++ tailWord_7011816) baseStart_7011816 baseEnd_7011816 := by
    simpa [prefixWord, tailWord_7011816, baseEnd_7011816] using wordTrace_append hprefix tailTrace_7011816
  have hstable : (prefixWord ++ tailWord_7011816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011816).length < 2 ^ (prefixWord ++ tailWord_7011816).sum := by decide
  have hdescent : baseEnd_7011816 < baseStart_7011816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011821 : List Nat := [1, 5, 1, 3, 3, 1, 2, 1, 1, 3, 2]
def baseStart_7011821 : Nat := 118140960795 + 7011821 * 2 ^ 59
def prefixEnd_7011821 : Nat := 4983230072969 + 3 ^ 40 * 7011821 * 2
def baseEnd_7011821 : Nat := 3600434436289515951790729

theorem tailTrace_7011821 : CollatzResearch.WordTrace tailWord_7011821 prefixEnd_7011821 3600434436289515951790729 := by
  unfold tailWord_7011821
  simp only [CollatzResearch.WordTrace]
  refine ⟨255742121930377515532179317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170494747953585010354786211 255742121930377515532179317)
  ·
    refine ⟨23975823930972892081141811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 255742121930377515532179317 23975823930972892081141811)
    ·
      refine ⟨35963735896459338121712717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23975823930972892081141811 35963735896459338121712717)
      ·
        refine ⟨13486400961172251795642269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35963735896459338121712717 13486400961172251795642269)
        ·
          refine ⟨5057400360439594423365851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13486400961172251795642269 5057400360439594423365851)
          ·
            refine ⟨7586100540659391635048777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5057400360439594423365851 7586100540659391635048777)
            ·
              refine ⟨5689575405494543726286583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7586100540659391635048777 5689575405494543726286583)
              ·
                refine ⟨8534363108241815589429875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5689575405494543726286583 8534363108241815589429875)
                ·
                  refine ⟨12801544662362723384144813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8534363108241815589429875 12801544662362723384144813)
                  ·
                    refine ⟨4800579248386021269054305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12801544662362723384144813 4800579248386021269054305)
                    ·
                      refine ⟨3600434436289515951790729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4800579248386021269054305 3600434436289515951790729)
                      ·
                        rfl

theorem cell23_7011821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_7011821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011821 prefixEnd_7011821 := by exact prefixLift 7011821
  have htrace : WordTrace (prefixWord ++ tailWord_7011821) baseStart_7011821 baseEnd_7011821 := by
    simpa [prefixWord, tailWord_7011821, baseEnd_7011821] using wordTrace_append hprefix tailTrace_7011821
  have hstable : (prefixWord ++ tailWord_7011821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011821).length < 2 ^ (prefixWord ++ tailWord_7011821).sum := by decide
  have hdescent : baseEnd_7011821 < baseStart_7011821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011836 : List Nat := [2, 2, 2, 1, 2, 1, 2, 4, 2, 5]
def baseStart_7011836 : Nat := 118140960795 + 7011836 * 2 ^ 59
def prefixEnd_7011836 : Nat := 4983230072969 + 3 ^ 40 * 7011836 * 2
def baseEnd_7011836 : Nat := 1200147379499777797701053

theorem tailTrace_7011836 : CollatzResearch.WordTrace tailWord_7011836 prefixEnd_7011836 1200147379499777797701053 := by
  unfold tailWord_7011836
  simp only [CollatzResearch.WordTrace]
  refine ⟨127871334512661586546987681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170495112683548782062650241 127871334512661586546987681)
  ·
    refine ⟨95903500884496189910240761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127871334512661586546987681 95903500884496189910240761)
    ·
      refine ⟨71927625663372142432680571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95903500884496189910240761 71927625663372142432680571)
      ·
        refine ⟨107891438495058213649020857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71927625663372142432680571 107891438495058213649020857)
        ·
          refine ⟨80918578871293660236765643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107891438495058213649020857 80918578871293660236765643)
          ·
            refine ⟨121377868306940490355148465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80918578871293660236765643 121377868306940490355148465)
            ·
              refine ⟨91033401230205367766361349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121377868306940490355148465 91033401230205367766361349)
              ·
                refine ⟨17068762730663506456192753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91033401230205367766361349 17068762730663506456192753)
                ·
                  refine ⟨12801572047997629842144565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17068762730663506456192753 12801572047997629842144565)
                  ·
                    refine ⟨1200147379499777797701053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12801572047997629842144565 1200147379499777797701053)
                    ·
                      rfl

theorem cell23_7011836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_7011836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011836 prefixEnd_7011836 := by exact prefixLift 7011836
  have htrace : WordTrace (prefixWord ++ tailWord_7011836) baseStart_7011836 baseEnd_7011836 := by
    simpa [prefixWord, tailWord_7011836, baseEnd_7011836] using wordTrace_append hprefix tailTrace_7011836
  have hstable : (prefixWord ++ tailWord_7011836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011836).length < 2 ^ (prefixWord ++ tailWord_7011836).sum := by decide
  have hdescent : baseEnd_7011836 < baseStart_7011836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011893 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 4, 2, 3]
def baseStart_7011893 : Nat := 118140960795 + 7011893 * 2 ^ 59
def prefixEnd_7011893 : Nat := 4983230072969 + 3 ^ 40 * 7011893 * 2
def baseEnd_7011893 : Nat := 3600471406896639670090397

theorem tailTrace_7011893 : CollatzResearch.WordTrace tailWord_7011893 prefixEnd_7011893 3600471406896639670090397 := by
  unfold tailWord_7011893
  simp only [CollatzResearch.WordTrace]
  refine ⟨255744747986116671828800333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170496498657411114552533555 255744747986116671828800333)
  ·
    refine ⟨95904280494793751935800125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255744747986116671828800333 95904280494793751935800125)
    ·
      refine ⟨35964105185547656975925047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95904280494793751935800125 35964105185547656975925047)
      ·
        refine ⟨53946157778321485463887571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35964105185547656975925047 53946157778321485463887571)
        ·
          refine ⟨80919236667482228195831357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53946157778321485463887571 80919236667482228195831357)
          ·
            refine ⟨30344713750305835573436759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80919236667482228195831357 30344713750305835573436759)
            ·
              refine ⟨45517070625458753360155139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30344713750305835573436759 45517070625458753360155139)
              ·
                refine ⟨68275605938188130040232709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45517070625458753360155139 68275605938188130040232709)
                ·
                  refine ⟨12801676113410274382543633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68275605938188130040232709 12801676113410274382543633)
                  ·
                    refine ⟨9601257085057705786907725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12801676113410274382543633 9601257085057705786907725)
                    ·
                      refine ⟨3600471406896639670090397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9601257085057705786907725 3600471406896639670090397)
                      ·
                        rfl

theorem cell23_7011893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_7011893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011893 prefixEnd_7011893 := by exact prefixLift 7011893
  have htrace : WordTrace (prefixWord ++ tailWord_7011893) baseStart_7011893 baseEnd_7011893 := by
    simpa [prefixWord, tailWord_7011893, baseEnd_7011893] using wordTrace_append hprefix tailTrace_7011893
  have hstable : (prefixWord ++ tailWord_7011893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011893).length < 2 ^ (prefixWord ++ tailWord_7011893).sum := by decide
  have hdescent : baseEnd_7011893 < baseStart_7011893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011896 : List Nat := [2, 1, 2, 1, 4, 2, 2, 1, 8]
def baseStart_7011896 : Nat := 118140960795 + 7011896 * 2 ^ 59
def prefixEnd_7011896 : Nat := 4983230072969 + 3 ^ 40 * 7011896 * 2
def baseEnd_7011896 : Nat := 400052549704289239816987

theorem tailTrace_7011896 : CollatzResearch.WordTrace tailWord_7011896 prefixEnd_7011896 400052549704289239816987 := by
  unfold tailWord_7011896
  simp only [CollatzResearch.WordTrace]
  refine ⟨127872428702552901670579771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170496571603403868894106361 127872428702552901670579771)
  ·
    refine ⟨191808643053829352505869657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127872428702552901670579771 191808643053829352505869657)
    ·
      refine ⟨143856482290372014379402243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191808643053829352505869657 143856482290372014379402243)
      ·
        refine ⟨215784723435558021569103365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143856482290372014379402243 215784723435558021569103365)
        ·
          refine ⟨40459635644167129044206881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215784723435558021569103365 40459635644167129044206881)
          ·
            refine ⟨30344726733125346783155161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40459635644167129044206881 30344726733125346783155161)
            ·
              refine ⟨22758545049844010087366371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30344726733125346783155161 22758545049844010087366371)
              ·
                refine ⟨34137817574766015131049557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22758545049844010087366371 34137817574766015131049557)
                ·
                  refine ⟨400052549704289239816987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34137817574766015131049557 400052549704289239816987)
                  ·
                    rfl

theorem cell23_7011896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 8].length) (baseStart_7011896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011896 prefixEnd_7011896 := by exact prefixLift 7011896
  have htrace : WordTrace (prefixWord ++ tailWord_7011896) baseStart_7011896 baseEnd_7011896 := by
    simpa [prefixWord, tailWord_7011896, baseEnd_7011896] using wordTrace_append hprefix tailTrace_7011896
  have hstable : (prefixWord ++ tailWord_7011896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011896).length < 2 ^ (prefixWord ++ tailWord_7011896).sum := by decide
  have hdescent : baseEnd_7011896 < baseStart_7011896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011943 : List Nat := [1, 1, 5, 1, 1, 1, 2, 5, 1, 5]
def baseStart_7011943 : Nat := 118140960795 + 7011943 * 2 ^ 59
def prefixEnd_7011943 : Nat := 4983230072969 + 3 ^ 40 * 7011943 * 2
def baseEnd_7011943 : Nat := 1200165693643121491488389

theorem tailTrace_7011943 : CollatzResearch.WordTrace tailWord_7011943 prefixEnd_7011943 1200165693643121491488389 := by
  unfold tailWord_7011943
  simp only [CollatzResearch.WordTrace]
  refine ⟨255746571635935530368120483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170497714423957020245413655 255746571635935530368120483)
  ·
    refine ⟨383619857453903295552180725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255746571635935530368120483 383619857453903295552180725)
    ·
      refine ⟨35964361636303433958016943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 383619857453903295552180725 35964361636303433958016943)
      ·
        refine ⟨53946542454455150937025415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35964361636303433958016943 53946542454455150937025415)
        ·
          refine ⟨80919813681682726405538123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53946542454455150937025415 80919813681682726405538123)
          ·
            refine ⟨121379720522524089608307185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80919813681682726405538123 121379720522524089608307185)
            ·
              refine ⟨91034790391893067206230389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121379720522524089608307185 91034790391893067206230389)
              ·
                refine ⟨8534511599239975050584099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91034790391893067206230389 8534511599239975050584099)
                ·
                  refine ⟨12801767398859962575876149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8534511599239975050584099 12801767398859962575876149)
                  ·
                    refine ⟨1200165693643121491488389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12801767398859962575876149 1200165693643121491488389)
                    ·
                      rfl

theorem cell23_7011943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_7011943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011943 prefixEnd_7011943 := by exact prefixLift 7011943
  have htrace : WordTrace (prefixWord ++ tailWord_7011943) baseStart_7011943 baseEnd_7011943 := by
    simpa [prefixWord, tailWord_7011943, baseEnd_7011943] using wordTrace_append hprefix tailTrace_7011943
  have hstable : (prefixWord ++ tailWord_7011943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011943).length < 2 ^ (prefixWord ++ tailWord_7011943).sum := by decide
  have hdescent : baseEnd_7011943 < baseStart_7011943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7011973 : List Nat := [1, 3, 1, 1, 4, 1, 4, 1, 1, 6]
def baseStart_7011973 : Nat := 118140960795 + 7011973 * 2 ^ 59
def prefixEnd_7011973 : Nat := 4983230072969 + 3 ^ 40 * 7011973 * 2
def baseEnd_7011973 : Nat := 1200170828449666452363343

theorem tailTrace_7011973 : CollatzResearch.WordTrace tailWord_7011973 prefixEnd_7011973 1200170828449666452363343 := by
  unfold tailWord_7011973
  simp only [CollatzResearch.WordTrace]
  refine ⟨255747665825826845491712573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170498443883884563661141715 255747665825826845491712573)
  ·
    refine ⟨95905374684685067059392215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255747665825826845491712573 95905374684685067059392215)
    ·
      refine ⟨143858062027027600589088323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95905374684685067059392215 143858062027027600589088323)
      ·
        refine ⟨215787093040541400883632485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143858062027027600589088323 215787093040541400883632485)
        ·
          refine ⟨40460079945101512665681091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215787093040541400883632485 40460079945101512665681091)
          ·
            refine ⟨60690119917652268998521637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40460079945101512665681091 60690119917652268998521637)
            ·
              refine ⟨11379397484559800437222807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60690119917652268998521637 11379397484559800437222807)
              ·
                refine ⟨17069096226839700655834211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11379397484559800437222807 17069096226839700655834211)
                ·
                  refine ⟨25603644340259550983751317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17069096226839700655834211 25603644340259550983751317)
                  ·
                    refine ⟨1200170828449666452363343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25603644340259550983751317 1200170828449666452363343)
                    ·
                      rfl

theorem cell23_7011973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 6].length) (baseStart_7011973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7011973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7011973 prefixEnd_7011973 := by exact prefixLift 7011973
  have htrace : WordTrace (prefixWord ++ tailWord_7011973) baseStart_7011973 baseEnd_7011973 := by
    simpa [prefixWord, tailWord_7011973, baseEnd_7011973] using wordTrace_append hprefix tailTrace_7011973
  have hstable : (prefixWord ++ tailWord_7011973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7011973).length < 2 ^ (prefixWord ++ tailWord_7011973).sum := by decide
  have hdescent : baseEnd_7011973 < baseStart_7011973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7011973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012016 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 1, 9]
def baseStart_7012016 : Nat := 118140960795 + 7012016 * 2 ^ 59
def prefixEnd_7012016 : Nat := 4983230072969 + 3 ^ 40 * 7012016 * 2
def baseEnd_7012016 : Nat := 1200178188339047562950777

theorem tailTrace_7012016 : CollatzResearch.WordTrace tailWord_7012016 prefixEnd_7012016 1200178188339047562950777 := by
  unfold tailWord_7012016
  simp only [CollatzResearch.WordTrace]
  refine ⟨127874617082335531917763951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170499489443114042557018601 127874617082335531917763951)
  ·
    refine ⟨191811925623503297876645927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127874617082335531917763951 191811925623503297876645927)
    ·
      refine ⟨287717888435254946814968891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191811925623503297876645927 287717888435254946814968891)
      ·
        refine ⟨431576832652882420222453337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287717888435254946814968891 431576832652882420222453337)
        ·
          refine ⟨323682624489661815166840003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431576832652882420222453337 323682624489661815166840003)
          ·
            refine ⟨485523936734492722750260005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323682624489661815166840003 485523936734492722750260005)
            ·
              refine ⟨91035738137717385515673751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 485523936734492722750260005 91035738137717385515673751)
              ·
                refine ⟨136553607206576078273510627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91035738137717385515673751 136553607206576078273510627)
                ·
                  refine ⟨204830410809864117410265941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136553607206576078273510627 204830410809864117410265941)
                  ·
                    refine ⟨1200178188339047562950777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 204830410809864117410265941 1200178188339047562950777)
                    ·
                      rfl

theorem cell23_7012016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 9].length) (baseStart_7012016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012016 prefixEnd_7012016 := by exact prefixLift 7012016
  have htrace : WordTrace (prefixWord ++ tailWord_7012016) baseStart_7012016 baseEnd_7012016 := by
    simpa [prefixWord, tailWord_7012016, baseEnd_7012016] using wordTrace_append hprefix tailTrace_7012016
  have hstable : (prefixWord ++ tailWord_7012016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012016).length < 2 ^ (prefixWord ++ tailWord_7012016).sum := by decide
  have hdescent : baseEnd_7012016 < baseStart_7012016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012054 : List Nat := [5, 2, 1, 3, 2, 1, 9]
def baseStart_7012054 : Nat := 118140960795 + 7012054 * 2 ^ 59
def prefixEnd_7012054 : Nat := 4983230072969 + 3 ^ 40 * 7012054 * 2
def baseEnd_7012054 : Nat := 44451284904716216545397

theorem tailTrace_7012054 : CollatzResearch.WordTrace tailWord_7012054 prefixEnd_7012054 44451284904716216545397 := by
  unfold tailWord_7012054
  simp only [CollatzResearch.WordTrace]
  refine ⟨15984413758658337270338201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170500413425688930883607477 15984413758658337270338201)
  ·
    refine ⟨11988310318993752952753651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15984413758658337270338201 11988310318993752952753651)
    ·
      refine ⟨17982465478490629429130477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11988310318993752952753651 17982465478490629429130477)
      ·
        refine ⟨6743424554433986035923929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17982465478490629429130477 6743424554433986035923929)
        ·
          refine ⟨5057568415825489526942947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6743424554433986035923929 5057568415825489526942947)
          ·
            refine ⟨7586352623738234290414421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5057568415825489526942947 7586352623738234290414421)
            ·
              refine ⟨44451284904716216545397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7586352623738234290414421 44451284904716216545397)
              ·
                rfl

theorem cell23_7012054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 9].length) (baseStart_7012054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012054 prefixEnd_7012054 := by exact prefixLift 7012054
  have htrace : WordTrace (prefixWord ++ tailWord_7012054) baseStart_7012054 baseEnd_7012054 := by
    simpa [prefixWord, tailWord_7012054, baseEnd_7012054] using wordTrace_append hprefix tailTrace_7012054
  have hstable : (prefixWord ++ tailWord_7012054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012054).length < 2 ^ (prefixWord ++ tailWord_7012054).sum := by decide
  have hdescent : baseEnd_7012054 < baseStart_7012054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012057 : List Nat := [1, 2, 1, 2, 3, 3, 2, 3, 1, 3, 2]
def baseStart_7012057 : Nat := 118140960795 + 7012057 * 2 ^ 59
def prefixEnd_7012057 : Nat := 4983230072969 + 3 ^ 40 * 7012057 * 2
def baseEnd_7012057 : Nat := 3600555617723977028439643

theorem tailTrace_7012057 : CollatzResearch.WordTrace tailWord_7012057 prefixEnd_7012057 3600555617723977028439643 := by
  unfold tailWord_7012057
  simp only [CollatzResearch.WordTrace]
  refine ⟨255750729557522527837770425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170500486371681685225180283 255750729557522527837770425)
  ·
    refine ⟨191813047168141895878327819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255750729557522527837770425 191813047168141895878327819)
    ·
      refine ⟨287719570752212843817491729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191813047168141895878327819 287719570752212843817491729)
      ·
        refine ⟨215789678064159632863118797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287719570752212843817491729 215789678064159632863118797)
        ·
          refine ⟨80921129274059862323669549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215789678064159632863118797 80921129274059862323669549)
          ·
            refine ⟨30345423477772448371376081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80921129274059862323669549 30345423477772448371376081)
            ·
              refine ⟨22759067608329336278532061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30345423477772448371376081 22759067608329336278532061)
              ·
                refine ⟨8534650353123501104449523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22759067608329336278532061 8534650353123501104449523)
                ·
                  refine ⟨12801975529685251656674285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8534650353123501104449523 12801975529685251656674285)
                  ·
                    refine ⟨4800740823631969371252857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12801975529685251656674285 4800740823631969371252857)
                    ·
                      refine ⟨3600555617723977028439643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4800740823631969371252857 3600555617723977028439643)
                      ·
                        rfl

theorem cell23_7012057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 3, 2].length) (baseStart_7012057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012057 prefixEnd_7012057 := by exact prefixLift 7012057
  have htrace : WordTrace (prefixWord ++ tailWord_7012057) baseStart_7012057 baseEnd_7012057 := by
    simpa [prefixWord, tailWord_7012057, baseEnd_7012057] using wordTrace_append hprefix tailTrace_7012057
  have hstable : (prefixWord ++ tailWord_7012057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012057).length < 2 ^ (prefixWord ++ tailWord_7012057).sum := by decide
  have hdescent : baseEnd_7012057 < baseStart_7012057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012073 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 2, 4, 3]
def baseStart_7012073 : Nat := 118140960795 + 7012073 * 2 ^ 59
def prefixEnd_7012073 : Nat := 4983230072969 + 3 ^ 40 * 7012073 * 2
def baseEnd_7012073 : Nat := 3600563833414448965839569

theorem tailTrace_7012073 : CollatzResearch.WordTrace tailWord_7012073 prefixEnd_7012073 3600563833414448965839569 := by
  unfold tailWord_7012073
  simp only [CollatzResearch.WordTrace]
  refine ⟨255751313125464562570352873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170500875416976375046901915 255751313125464562570352873)
  ·
    refine ⟨191813484844098421927764655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255751313125464562570352873 191813484844098421927764655)
    ·
      refine ⟨287720227266147632891646983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191813484844098421927764655 287720227266147632891646983)
      ·
        refine ⟨431580340899221449337470475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287720227266147632891646983 431580340899221449337470475)
        ·
          refine ⟨647370511348832174006205713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431580340899221449337470475 647370511348832174006205713)
          ·
            refine ⟨485527883511624130504654285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 647370511348832174006205713 485527883511624130504654285)
            ·
              refine ⟨182072956316859048939245357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 485527883511624130504654285 182072956316859048939245357)
              ·
                refine ⟨68277358618822143352217009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182072956316859048939245357 68277358618822143352217009)
                ·
                  refine ⟨51208018964116607514162757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68277358618822143352217009 51208018964116607514162757)
                  ·
                    refine ⟨9601503555771863908905517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51208018964116607514162757 9601503555771863908905517)
                    ·
                      refine ⟨3600563833414448965839569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9601503555771863908905517 3600563833414448965839569)
                      ·
                        rfl

theorem cell23_7012073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 4, 3].length) (baseStart_7012073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012073 prefixEnd_7012073 := by exact prefixLift 7012073
  have htrace : WordTrace (prefixWord ++ tailWord_7012073) baseStart_7012073 baseEnd_7012073 := by
    simpa [prefixWord, tailWord_7012073, baseEnd_7012073] using wordTrace_append hprefix tailTrace_7012073
  have hstable : (prefixWord ++ tailWord_7012073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012073).length < 2 ^ (prefixWord ++ tailWord_7012073).sum := by decide
  have hdescent : baseEnd_7012073 < baseStart_7012073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012083 : List Nat := [1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 4]
def baseStart_7012083 : Nat := 118140960795 + 7012083 * 2 ^ 59
def prefixEnd_7012083 : Nat := 4983230072969 + 3 ^ 40 * 7012083 * 2
def baseEnd_7012083 : Nat := 3600568968220993926714523

theorem tailTrace_7012083 : CollatzResearch.WordTrace tailWord_7012083 prefixEnd_7012083 3600568968220993926714523 := by
  unfold tailWord_7012083
  simp only [CollatzResearch.WordTrace]
  refine ⟨255751677855428334278216903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170501118570285556185477935 255751677855428334278216903)
  ·
    refine ⟨383627516783142501417325355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255751677855428334278216903 383627516783142501417325355)
    ·
      refine ⟨575441275174713752125988033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383627516783142501417325355 575441275174713752125988033)
      ·
        refine ⟨431580956381035314094491025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 575441275174713752125988033 431580956381035314094491025)
        ·
          refine ⟨323685717285776485570868269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431580956381035314094491025 323685717285776485570868269)
          ·
            refine ⟨121382143982166182089075601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323685717285776485570868269 121382143982166182089075601)
            ·
              refine ⟨91036607986624636566806701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121382143982166182089075601 91036607986624636566806701)
              ·
                refine ⟨34138727994984238712552513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91036607986624636566806701 34138727994984238712552513)
                ·
                  refine ⟨25604045996238179034414385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34138727994984238712552513 25604045996238179034414385)
                  ·
                    refine ⟨19203034497178634275810789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25604045996238179034414385 19203034497178634275810789)
                    ·
                      refine ⟨3600568968220993926714523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19203034497178634275810789 3600568968220993926714523)
                      ·
                        rfl

theorem cell23_7012083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 4].length) (baseStart_7012083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012083 prefixEnd_7012083 := by exact prefixLift 7012083
  have htrace : WordTrace (prefixWord ++ tailWord_7012083) baseStart_7012083 baseEnd_7012083 := by
    simpa [prefixWord, tailWord_7012083, baseEnd_7012083] using wordTrace_append hprefix tailTrace_7012083
  have hstable : (prefixWord ++ tailWord_7012083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012083).length < 2 ^ (prefixWord ++ tailWord_7012083).sum := by decide
  have hdescent : baseEnd_7012083 < baseStart_7012083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012102 : List Nat := [6, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3]
def baseStart_7012102 : Nat := 118140960795 + 7012102 * 2 ^ 59
def prefixEnd_7012102 : Nat := 4983230072969 + 3 ^ 40 * 7012102 * 2
def baseEnd_7012102 : Nat := 3600578724353429352376937

theorem tailTrace_7012102 : CollatzResearch.WordTrace tailWord_7012102 prefixEnd_7012102 3600578724353429352376937 := by
  unfold tailWord_7012102
  simp only [CollatzResearch.WordTrace]
  refine ⟨7992261588823734391348705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 170501580561573000348772373 7992261588823734391348705)
  ·
    refine ⟨5994196191617800793511529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7992261588823734391348705 5994196191617800793511529)
    ·
      refine ⟨4495647143713350595133647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5994196191617800793511529 4495647143713350595133647)
      ·
        refine ⟨6743470715570025892700471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4495647143713350595133647 6743470715570025892700471)
        ·
          refine ⟨10115206073355038839050707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6743470715570025892700471 10115206073355038839050707)
          ·
            refine ⟨15172809110032558258576061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10115206073355038839050707 15172809110032558258576061)
            ·
              refine ⟨5689803416262209346966023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15172809110032558258576061 5689803416262209346966023)
              ·
                refine ⟨8534705124393314020449035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5689803416262209346966023 8534705124393314020449035)
                ·
                  refine ⟨12802057686589971030673553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8534705124393314020449035 12802057686589971030673553)
                  ·
                    refine ⟨9601543264942478273005165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12802057686589971030673553 9601543264942478273005165)
                    ·
                      refine ⟨3600578724353429352376937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9601543264942478273005165 3600578724353429352376937)
                      ·
                        rfl

theorem cell23_7012102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_7012102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012102 prefixEnd_7012102 := by exact prefixLift 7012102
  have htrace : WordTrace (prefixWord ++ tailWord_7012102) baseStart_7012102 baseEnd_7012102 := by
    simpa [prefixWord, tailWord_7012102, baseEnd_7012102] using wordTrace_append hprefix tailTrace_7012102
  have hstable : (prefixWord ++ tailWord_7012102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012102).length < 2 ^ (prefixWord ++ tailWord_7012102).sum := by decide
  have hdescent : baseEnd_7012102 < baseStart_7012102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012143 : List Nat := [1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 4]
def baseStart_7012143 : Nat := 118140960795 + 7012143 * 2 ^ 59
def prefixEnd_7012143 : Nat := 4983230072969 + 3 ^ 40 * 7012143 * 2
def baseEnd_7012143 : Nat := 3600599777060263691964247

theorem tailTrace_7012143 : CollatzResearch.WordTrace tailWord_7012143 prefixEnd_7012143 3600599777060263691964247 := by
  unfold tailWord_7012143
  simp only [CollatzResearch.WordTrace]
  refine ⟨255753866235210964525401083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170502577490140643016934055 255753866235210964525401083)
  ·
    refine ⟨383630799352816446788101625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255753866235210964525401083 383630799352816446788101625)
    ·
      refine ⟨287723099514612335091076219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383630799352816446788101625 287723099514612335091076219)
      ·
        refine ⟨431584649271918502636614329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287723099514612335091076219 431584649271918502636614329)
        ·
          refine ⟨323688486953938876977460747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431584649271918502636614329 323688486953938876977460747)
          ·
            refine ⟨485532730430908315466191121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323688486953938876977460747 485532730430908315466191121)
            ·
              refine ⟨364149547823181236599643341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 485532730430908315466191121 364149547823181236599643341)
              ·
                refine ⟨136556080433692963724866253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 364149547823181236599643341 136556080433692963724866253)
                ·
                  refine ⟨51208530162634861396824845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136556080433692963724866253 51208530162634861396824845)
                  ·
                    refine ⟨19203198810988073023809317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51208530162634861396824845 19203198810988073023809317)
                    ·
                      refine ⟨3600599777060263691964247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19203198810988073023809317 3600599777060263691964247)
                      ·
                        rfl

theorem cell23_7012143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 4].length) (baseStart_7012143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012143 prefixEnd_7012143 := by exact prefixLift 7012143
  have htrace : WordTrace (prefixWord ++ tailWord_7012143) baseStart_7012143 baseEnd_7012143 := by
    simpa [prefixWord, tailWord_7012143, baseEnd_7012143] using wordTrace_append hprefix tailTrace_7012143
  have hstable : (prefixWord ++ tailWord_7012143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012143).length < 2 ^ (prefixWord ++ tailWord_7012143).sum := by decide
  have hdescent : baseEnd_7012143 < baseStart_7012143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012157 : List Nat := [1, 4, 1, 4, 1, 1, 3, 1, 2, 5]
def baseStart_7012157 : Nat := 118140960795 + 7012157 * 2 ^ 59
def prefixEnd_7012157 : Nat := 4983230072969 + 3 ^ 40 * 7012157 * 2
def baseEnd_7012157 : Nat := 1200202321929808879063061

theorem tailTrace_7012157 : CollatzResearch.WordTrace tailWord_7012157 prefixEnd_7012157 1200202321929808879063061 := by
  unfold tailWord_7012157
  simp only [CollatzResearch.WordTrace]
  refine ⟨255754376857160244916410725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170502917904773496610940483 255754376857160244916410725)
  ·
    refine ⟨47953945660717545921827011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255754376857160244916410725 47953945660717545921827011)
    ·
      refine ⟨71930918491076318882740517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47953945660717545921827011 71930918491076318882740517)
      ·
        refine ⟨13487047217076809790513847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71930918491076318882740517 13487047217076809790513847)
        ·
          refine ⟨20230570825615214685770771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13487047217076809790513847 20230570825615214685770771)
          ·
            refine ⟨30345856238422822028656157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20230570825615214685770771 30345856238422822028656157)
            ·
              refine ⟨11379696089408558260746059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30345856238422822028656157 11379696089408558260746059)
              ·
                refine ⟨17069544134112837391119089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11379696089408558260746059 17069544134112837391119089)
                ·
                  refine ⟨12802158100584628043339317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17069544134112837391119089 12802158100584628043339317)
                  ·
                    refine ⟨1200202321929808879063061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12802158100584628043339317 1200202321929808879063061)
                    ·
                      rfl

theorem cell23_7012157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_7012157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012157 prefixEnd_7012157 := by exact prefixLift 7012157
  have htrace : WordTrace (prefixWord ++ tailWord_7012157) baseStart_7012157 baseEnd_7012157 := by
    simpa [prefixWord, tailWord_7012157, baseEnd_7012157] using wordTrace_append hprefix tailTrace_7012157
  have hstable : (prefixWord ++ tailWord_7012157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012157).length < 2 ^ (prefixWord ++ tailWord_7012157).sum := by decide
  have hdescent : baseEnd_7012157 < baseStart_7012157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012170 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 5, 4]
def baseStart_7012170 : Nat := 118140960795 + 7012170 * 2 ^ 59
def prefixEnd_7012170 : Nat := 4983230072969 + 3 ^ 40 * 7012170 * 2
def baseEnd_7012170 : Nat := 1200204547012645028775541

theorem tailTrace_7012170 : CollatzResearch.WordTrace tailWord_7012170 prefixEnd_7012170 1200204547012645028775541 := by
  unfold tailWord_7012170
  simp only [CollatzResearch.WordTrace]
  refine ⟨63938712751528287034158491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170503234004075432091089309 63938712751528287034158491)
  ·
    refine ⟨95908069127292430551237737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63938712751528287034158491 95908069127292430551237737)
    ·
      refine ⟨71931051845469322913428303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95908069127292430551237737 71931051845469322913428303)
      ·
        refine ⟨107896577768203984370142455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71931051845469322913428303 107896577768203984370142455)
        ·
          refine ⟨161844866652305976555213683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107896577768203984370142455 161844866652305976555213683)
          ·
            refine ⟨242767299978458964832820525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161844866652305976555213683 242767299978458964832820525)
            ·
              refine ⟨91037737491922111812307697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242767299978458964832820525 91037737491922111812307697)
              ·
                refine ⟨68278303118941583859230773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91037737491922111812307697 68278303118941583859230773)
                ·
                  refine ⟨6401090917400773486802885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68278303118941583859230773 6401090917400773486802885)
                  ·
                    refine ⟨1200204547012645028775541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6401090917400773486802885 1200204547012645028775541)
                    ·
                      rfl

theorem cell23_7012170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_7012170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012170 prefixEnd_7012170 := by exact prefixLift 7012170
  have htrace : WordTrace (prefixWord ++ tailWord_7012170) baseStart_7012170 baseEnd_7012170 := by
    simpa [prefixWord, tailWord_7012170, baseEnd_7012170] using wordTrace_append hprefix tailTrace_7012170
  have hstable : (prefixWord ++ tailWord_7012170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012170).length < 2 ^ (prefixWord ++ tailWord_7012170).sum := by decide
  have hdescent : baseEnd_7012170 < baseStart_7012170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012177 : List Nat := [1, 2, 2, 1, 5, 1, 1, 2, 2, 4, 2]
def baseStart_7012177 : Nat := 118140960795 + 7012177 * 2 ^ 59
def prefixEnd_7012177 : Nat := 4983230072969 + 3 ^ 40 * 7012177 * 2
def baseEnd_7012177 : Nat := 3600617235402516558939091

theorem tailTrace_7012177 : CollatzResearch.WordTrace tailWord_7012177 prefixEnd_7012177 3600617235402516558939091 := by
  unfold tailWord_7012177
  simp only [CollatzResearch.WordTrace]
  refine ⟨255755106317087788332138785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170503404211391858888092523 255755106317087788332138785)
  ·
    refine ⟨191816329737815841249104089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255755106317087788332138785 191816329737815841249104089)
    ·
      refine ⟨143862247303361880936828067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191816329737815841249104089 143862247303361880936828067)
      ·
        refine ⟨215793370955042821405242101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143862247303361880936828067 215793370955042821405242101)
        ·
          refine ⟨20230628527035264506741447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 215793370955042821405242101 20230628527035264506741447)
          ·
            refine ⟨30345942790552896760112171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20230628527035264506741447 30345942790552896760112171)
            ·
              refine ⟨45518914185829345140168257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30345942790552896760112171 45518914185829345140168257)
              ·
                refine ⟨34139185639372008855126193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45518914185829345140168257 34139185639372008855126193)
                ·
                  refine ⟨25604389229529006641344645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34139185639372008855126193 25604389229529006641344645)
                  ·
                    refine ⟨4800822980536688745252121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25604389229529006641344645 4800822980536688745252121)
                    ·
                      refine ⟨3600617235402516558939091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4800822980536688745252121 3600617235402516558939091)
                      ·
                        rfl

theorem cell23_7012177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 4, 2].length) (baseStart_7012177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012177 prefixEnd_7012177 := by exact prefixLift 7012177
  have htrace : WordTrace (prefixWord ++ tailWord_7012177) baseStart_7012177 baseEnd_7012177 := by
    simpa [prefixWord, tailWord_7012177, baseEnd_7012177] using wordTrace_append hprefix tailTrace_7012177
  have hstable : (prefixWord ++ tailWord_7012177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012177).length < 2 ^ (prefixWord ++ tailWord_7012177).sum := by decide
  have hdescent : baseEnd_7012177 < baseStart_7012177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012194 : List Nat := [3, 3, 2, 1, 2, 1, 2, 1, 2, 4, 2]
def baseStart_7012194 : Nat := 118140960795 + 7012194 * 2 ^ 59
def prefixEnd_7012194 : Nat := 4983230072969 + 3 ^ 40 * 7012194 * 2
def baseEnd_7012194 : Nat := 3600625964573642992426513

theorem tailTrace_7012194 : CollatzResearch.WordTrace tailWord_7012194 prefixEnd_7012194 3600625964573642992426513 := by
  unfold tailWord_7012194
  simp only [CollatzResearch.WordTrace]
  refine ⟨63938931589506550058876909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170503817572017466823671757 63938931589506550058876909)
  ·
    refine ⟨23977099346064956272078841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63938931589506550058876909 23977099346064956272078841)
    ·
      refine ⟨17982824509548717204059131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23977099346064956272078841 17982824509548717204059131)
      ·
        refine ⟨26974236764323075806088697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17982824509548717204059131 26974236764323075806088697)
        ·
          refine ⟨20230677573242306854566523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26974236764323075806088697 20230677573242306854566523)
          ·
            refine ⟨30346016359863460281849785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20230677573242306854566523 30346016359863460281849785)
            ·
              refine ⟨22759512269897595211387339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30346016359863460281849785 22759512269897595211387339)
              ·
                refine ⟨34139268404846392817081009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22759512269897595211387339 34139268404846392817081009)
                ·
                  refine ⟨25604451303634794612810757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34139268404846392817081009 25604451303634794612810757)
                  ·
                    refine ⟨4800834619431523989902017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25604451303634794612810757 4800834619431523989902017)
                    ·
                      refine ⟨3600625964573642992426513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4800834619431523989902017 3600625964573642992426513)
                      ·
                        rfl

theorem cell23_7012194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_7012194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012194 prefixEnd_7012194 := by exact prefixLift 7012194
  have htrace : WordTrace (prefixWord ++ tailWord_7012194) baseStart_7012194 baseEnd_7012194 := by
    simpa [prefixWord, tailWord_7012194, baseEnd_7012194] using wordTrace_append hprefix tailTrace_7012194
  have hstable : (prefixWord ++ tailWord_7012194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012194).length < 2 ^ (prefixWord ++ tailWord_7012194).sum := by decide
  have hdescent : baseEnd_7012194 < baseStart_7012194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012203 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 6]
def baseStart_7012203 : Nat := 118140960795 + 7012203 * 2 ^ 59
def prefixEnd_7012203 : Nat := 4983230072969 + 3 ^ 40 * 7012203 * 2
def baseEnd_7012203 : Nat := 3600630585899533457213971

theorem tailTrace_7012203 : CollatzResearch.WordTrace tailWord_7012203 prefixEnd_7012203 3600630585899533457213971 := by
  unfold tailWord_7012203
  simp only [CollatzResearch.WordTrace]
  refine ⟨255756054614993594772585263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170504036409995729848390175 255756054614993594772585263)
  ·
    refine ⟨383634081922490392158877895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255756054614993594772585263 383634081922490392158877895)
    ·
      refine ⟨575451122883735588238316843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383634081922490392158877895 575451122883735588238316843)
      ·
        refine ⟨863176684325603382357475265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575451122883735588238316843 863176684325603382357475265)
        ·
          refine ⟨647382513244202536768106449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 863176684325603382357475265 647382513244202536768106449)
          ·
            refine ⟨485536884933151902576079837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 647382513244202536768106449 485536884933151902576079837)
            ·
              refine ⟨182076331849931963466029939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 485536884933151902576079837 182076331849931963466029939)
              ·
                refine ⟨273114497774897945199044909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182076331849931963466029939 273114497774897945199044909)
                ·
                  refine ⟨102417936665586729449641841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 273114497774897945199044909 102417936665586729449641841)
                  ·
                    refine ⟨76813452499190047087231381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102417936665586729449641841 76813452499190047087231381)
                    ·
                      refine ⟨3600630585899533457213971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76813452499190047087231381 3600630585899533457213971)
                      ·
                        rfl

theorem cell23_7012203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 6].length) (baseStart_7012203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012203 prefixEnd_7012203 := by exact prefixLift 7012203
  have htrace : WordTrace (prefixWord ++ tailWord_7012203) baseStart_7012203 baseEnd_7012203 := by
    simpa [prefixWord, tailWord_7012203, baseEnd_7012203] using wordTrace_append hprefix tailTrace_7012203
  have hstable : (prefixWord ++ tailWord_7012203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012203).length < 2 ^ (prefixWord ++ tailWord_7012203).sum := by decide
  have hdescent : baseEnd_7012203 < baseStart_7012203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012210 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 1, 7, 3]
def baseStart_7012210 : Nat := 118140960795 + 7012210 * 2 ^ 59
def prefixEnd_7012210 : Nat := 4983230072969 + 3 ^ 40 * 7012210 * 2
def baseEnd_7012210 : Nat := 3600634180264114929826439

theorem tailTrace_7012210 : CollatzResearch.WordTrace tailWord_7012210 prefixEnd_7012210 3600634180264114929826439 := by
  unfold tailWord_7012210
  simp only [CollatzResearch.WordTrace]
  refine ⟨63939077481492058742022521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170504206617312156645393389 63939077481492058742022521)
  ·
    refine ⟨47954308111119044056516891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63939077481492058742022521 47954308111119044056516891)
    ·
      refine ⟨71931462166678566084775337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47954308111119044056516891 71931462166678566084775337)
      ·
        refine ⟨53948596625008924563581503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71931462166678566084775337 53948596625008924563581503)
        ·
          refine ⟨80922894937513386845372255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53948596625008924563581503 80922894937513386845372255)
          ·
            refine ⟨121384342406270080268058383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80922894937513386845372255 121384342406270080268058383)
            ·
              refine ⟨182076513609405120402087575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121384342406270080268058383 182076513609405120402087575)
              ·
                refine ⟨273114770414107680603131363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182076513609405120402087575 273114770414107680603131363)
                ·
                  refine ⟨409672155621161520904697045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 273114770414107680603131363 409672155621161520904697045)
                  ·
                    refine ⟨9601691147370973146203837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 409672155621161520904697045 9601691147370973146203837)
                    ·
                      refine ⟨3600634180264114929826439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9601691147370973146203837 3600634180264114929826439)
                      ·
                        rfl

theorem cell23_7012210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_7012210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012210 prefixEnd_7012210 := by exact prefixLift 7012210
  have htrace : WordTrace (prefixWord ++ tailWord_7012210) baseStart_7012210 baseEnd_7012210 := by
    simpa [prefixWord, tailWord_7012210, baseEnd_7012210] using wordTrace_append hprefix tailTrace_7012210
  have hstable : (prefixWord ++ tailWord_7012210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012210).length < 2 ^ (prefixWord ++ tailWord_7012210).sum := by decide
  have hdescent : baseEnd_7012210 < baseStart_7012210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012238 : List Nat := [4, 1, 1, 5, 2, 1, 1, 1, 3, 4]
def baseStart_7012238 : Nat := 118140960795 + 7012238 * 2 ^ 59
def prefixEnd_7012238 : Nat := 4983230072969 + 3 ^ 40 * 7012238 * 2
def baseEnd_7012238 : Nat := 1200216185907480273425437

theorem tailTrace_7012238 : CollatzResearch.WordTrace tailWord_7012238 prefixEnd_7012238 1200216185907480273425437 := by
  unfold tailWord_7012238
  simp only [CollatzResearch.WordTrace]
  refine ⟨31969666396233349468763671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170504887446577863833406245 31969666396233349468763671)
  ·
    refine ⟨47954499594350024203145507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31969666396233349468763671 47954499594350024203145507)
    ·
      refine ⟨71931749391525036304718261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47954499594350024203145507 71931749391525036304718261)
      ·
        refine ⟨6743601505455472153567337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71931749391525036304718261 6743601505455472153567337)
        ·
          refine ⟨5057701129091604115175503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6743601505455472153567337 5057701129091604115175503)
          ·
            refine ⟨7586551693637406172763255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5057701129091604115175503 7586551693637406172763255)
            ·
              refine ⟨11379827540456109259144883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7586551693637406172763255 11379827540456109259144883)
              ·
                refine ⟨17069741310684163888717325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11379827540456109259144883 17069741310684163888717325)
                ·
                  refine ⟨6401152991506561458268997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17069741310684163888717325 6401152991506561458268997)
                  ·
                    refine ⟨1200216185907480273425437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6401152991506561458268997 1200216185907480273425437)
                    ·
                      rfl

theorem cell23_7012238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_7012238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012238 prefixEnd_7012238 := by exact prefixLift 7012238
  have htrace : WordTrace (prefixWord ++ tailWord_7012238) baseStart_7012238 baseEnd_7012238 := by
    simpa [prefixWord, tailWord_7012238, baseEnd_7012238] using wordTrace_append hprefix tailTrace_7012238
  have hstable : (prefixWord ++ tailWord_7012238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012238).length < 2 ^ (prefixWord ++ tailWord_7012238).sum := by decide
  have hdescent : baseEnd_7012238 < baseStart_7012238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012277 : List Nat := [1, 3, 3, 2, 1, 3, 1, 2, 1, 6]
def baseStart_7012277 : Nat := 118140960795 + 7012277 * 2 ^ 59
def prefixEnd_7012277 : Nat := 4983230072969 + 3 ^ 40 * 7012277 * 2
def baseEnd_7012277 : Nat := 1200222861155988722562877

theorem tailTrace_7012277 : CollatzResearch.WordTrace tailWord_7012277 prefixEnd_7012277 1200222861155988722562877 := by
  unfold tailWord_7012277
  simp only [CollatzResearch.WordTrace]
  refine ⟨255758753616725505410779085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170505835744483670273852723 255758753616725505410779085)
  ·
    refine ⟨95909532606272064529042157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255758753616725505410779085 95909532606272064529042157)
    ·
      refine ⟨35966074727352024198390809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95909532606272064529042157 35966074727352024198390809)
      ·
        refine ⟨26974556045514018148793107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35966074727352024198390809 26974556045514018148793107)
        ·
          refine ⟨40461834068271027223189661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26974556045514018148793107 40461834068271027223189661)
          ·
            refine ⟨15173187775601635208696123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40461834068271027223189661 15173187775601635208696123)
            ·
              refine ⟨22759781663402452813044185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15173187775601635208696123 22759781663402452813044185)
              ·
                refine ⟨17069836247551839609783139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22759781663402452813044185 17069836247551839609783139)
                ·
                  refine ⟨25604754371327759414674709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17069836247551839609783139 25604754371327759414674709)
                  ·
                    refine ⟨1200222861155988722562877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25604754371327759414674709 1200222861155988722562877)
                    ·
                      rfl

theorem cell23_7012277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_7012277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012277 prefixEnd_7012277 := by exact prefixLift 7012277
  have htrace : WordTrace (prefixWord ++ tailWord_7012277) baseStart_7012277 baseEnd_7012277 := by
    simpa [prefixWord, tailWord_7012277, baseEnd_7012277] using wordTrace_append hprefix tailTrace_7012277
  have hstable : (prefixWord ++ tailWord_7012277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012277).length < 2 ^ (prefixWord ++ tailWord_7012277).sum := by decide
  have hdescent : baseEnd_7012277 < baseStart_7012277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012314 : List Nat := [3, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4]
def baseStart_7012314 : Nat := 118140960795 + 7012314 * 2 ^ 59
def prefixEnd_7012314 : Nat := 4983230072969 + 3 ^ 40 * 7012314 * 2
def baseEnd_7012314 : Nat := 3600687582252182522925961

theorem tailTrace_7012314 : CollatzResearch.WordTrace tailWord_7012314 prefixEnd_7012314 3600687582252182522925961 := by
  unfold tailWord_7012314
  simp only [CollatzResearch.WordTrace]
  refine ⟨63940025779397865182468999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170506735411727640486583997 63940025779397865182468999)
  ·
    refine ⟨95910038669096797773703499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63940025779397865182468999 95910038669096797773703499)
    ·
      refine ⟨143865058003645196660555249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95910038669096797773703499 143865058003645196660555249)
      ·
        refine ⟨107898793502733897495416437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143865058003645196660555249 107898793502733897495416437)
        ·
          refine ⟨10115511890881302890195291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107898793502733897495416437 10115511890881302890195291)
          ·
            refine ⟨15173267836321954335292937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10115511890881302890195291 15173267836321954335292937)
            ·
              refine ⟨11379950877241465751469703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15173267836321954335292937 11379950877241465751469703)
              ·
                refine ⟨17069926315862198627204555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11379950877241465751469703 17069926315862198627204555)
                ·
                  refine ⟨25604889473793297940806833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17069926315862198627204555 25604889473793297940806833)
                  ·
                    refine ⟨19203667105344973455605125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25604889473793297940806833 19203667105344973455605125)
                    ·
                      refine ⟨3600687582252182522925961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19203667105344973455605125 3600687582252182522925961)
                      ·
                        rfl

theorem cell23_7012314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_7012314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012314 prefixEnd_7012314 := by exact prefixLift 7012314
  have htrace : WordTrace (prefixWord ++ tailWord_7012314) baseStart_7012314 baseEnd_7012314 := by
    simpa [prefixWord, tailWord_7012314, baseEnd_7012314] using wordTrace_append hprefix tailTrace_7012314
  have hstable : (prefixWord ++ tailWord_7012314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012314).length < 2 ^ (prefixWord ++ tailWord_7012314).sum := by decide
  have hdescent : baseEnd_7012314 < baseStart_7012314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012334 : List Nat := [4, 1, 2, 1, 3, 1, 2, 2, 1, 3, 3]
def baseStart_7012334 : Nat := 118140960795 + 7012334 * 2 ^ 59
def prefixEnd_7012334 : Nat := 4983230072969 + 3 ^ 40 * 7012334 * 2
def baseEnd_7012334 : Nat := 3600697851865272444675869

theorem tailTrace_7012334 : CollatzResearch.WordTrace tailWord_7012334 prefixEnd_7012334 3600697851865272444675869 := by
  unfold tailWord_7012334
  simp only [CollatzResearch.WordTrace]
  refine ⟨31970104072189875518200507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170507221718346002763736037 31970104072189875518200507)
  ·
    refine ⟨47955156108284813277300761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31970104072189875518200507 47955156108284813277300761)
    ·
      refine ⟨35966367081213609957975571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47955156108284813277300761 35966367081213609957975571)
      ·
        refine ⟨53949550621820414936963357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35966367081213609957975571 53949550621820414936963357)
        ·
          refine ⟨20231081483182655601361259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53949550621820414936963357 20231081483182655601361259)
          ·
            refine ⟨30346622224773983402041889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20231081483182655601361259 30346622224773983402041889)
            ·
              refine ⟨22759966668580487551531417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30346622224773983402041889 22759966668580487551531417)
              ·
                refine ⟨17069975001435365663648563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22759966668580487551531417 17069975001435365663648563)
                ·
                  refine ⟨25604962502153048495472845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17069975001435365663648563 25604962502153048495472845)
                  ·
                    refine ⟨9601860938307393185802317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25604962502153048495472845 9601860938307393185802317)
                    ·
                      refine ⟨3600697851865272444675869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9601860938307393185802317 3600697851865272444675869)
                      ·
                        rfl

theorem cell23_7012334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_7012334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012334 prefixEnd_7012334 := by exact prefixLift 7012334
  have htrace : WordTrace (prefixWord ++ tailWord_7012334) baseStart_7012334 baseEnd_7012334 := by
    simpa [prefixWord, tailWord_7012334, baseEnd_7012334] using wordTrace_append hprefix tailTrace_7012334
  have hstable : (prefixWord ++ tailWord_7012334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012334).length < 2 ^ (prefixWord ++ tailWord_7012334).sum := by decide
  have hdescent : baseEnd_7012334 < baseStart_7012334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012365 : List Nat := [1, 7, 1, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_7012365 : Nat := 118140960795 + 7012365 * 2 ^ 59
def prefixEnd_7012365 : Nat := 4983230072969 + 3 ^ 40 * 7012365 * 2
def baseEnd_7012365 : Nat := 3600713769765561823388227

theorem tailTrace_7012365 : CollatzResearch.WordTrace tailWord_7012365 prefixEnd_7012365 3600713769765561823388227 := by
  unfold tailWord_7012365
  simp only [CollatzResearch.WordTrace]
  refine ⟨255761963240406696439982549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170507975493604464293321699 255761963240406696439982549)
  ·
    refine ⟨5994421013447031947812091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 255761963240406696439982549 5994421013447031947812091)
    ·
      refine ⟨8991631520170547921718137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5994421013447031947812091 8991631520170547921718137)
      ·
        refine ⟨6743723640127910941288603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8991631520170547921718137 6743723640127910941288603)
        ·
          refine ⟨10115585460191866411932905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6743723640127910941288603 10115585460191866411932905)
          ·
            refine ⟨7586689095143899808949679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10115585460191866411932905 7586689095143899808949679)
            ·
              refine ⟨11380033642715849713424519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7586689095143899808949679 11380033642715849713424519)
              ·
                refine ⟨17070050464073774570136779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11380033642715849713424519 17070050464073774570136779)
                ·
                  refine ⟨25605075696110661855205169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17070050464073774570136779 25605075696110661855205169)
                  ·
                    refine ⟨19203806772082996391403877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25605075696110661855205169 19203806772082996391403877)
                    ·
                      refine ⟨3600713769765561823388227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19203806772082996391403877 3600713769765561823388227)
                      ·
                        rfl

theorem cell23_7012365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_7012365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012365 prefixEnd_7012365 := by exact prefixLift 7012365
  have htrace : WordTrace (prefixWord ++ tailWord_7012365) baseStart_7012365 baseEnd_7012365 := by
    simpa [prefixWord, tailWord_7012365, baseEnd_7012365] using wordTrace_append hprefix tailTrace_7012365
  have hstable : (prefixWord ++ tailWord_7012365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012365).length < 2 ^ (prefixWord ++ tailWord_7012365).sum := by decide
  have hdescent : baseEnd_7012365 < baseStart_7012365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012394 : List Nat := [3, 1, 4, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_7012394 : Nat := 118140960795 + 7012394 * 2 ^ 59
def prefixEnd_7012394 : Nat := 4983230072969 + 3 ^ 40 * 7012394 * 2
def baseEnd_7012394 : Nat := 3600728660704542209925593

theorem tailTrace_7012394 : CollatzResearch.WordTrace tailWord_7012394 prefixEnd_7012394 3600728660704542209925593 := by
  unfold tailWord_7012394
  simp only [CollatzResearch.WordTrace]
  refine ⟨63940755239325408598197059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170508680638201089595192157 63940755239325408598197059)
  ·
    refine ⟨95911132858988112897295589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63940755239325408598197059 95911132858988112897295589)
    ·
      refine ⟨17983337411060271168242923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95911132858988112897295589 17983337411060271168242923)
      ·
        refine ⟨26975006116590406752364385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17983337411060271168242923 26975006116590406752364385)
        ·
          refine ⟨20231254587442805064273289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26975006116590406752364385 20231254587442805064273289)
          ·
            refine ⟨15173440940582103798204967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20231254587442805064273289 15173440940582103798204967)
            ·
              refine ⟨22760161410873155697307451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15173440940582103798204967 22760161410873155697307451)
              ·
                refine ⟨34140242116309733545961177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22760161410873155697307451 34140242116309733545961177)
                ·
                  refine ⟨25605181587232300159470883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34140242116309733545961177 25605181587232300159470883)
                  ·
                    refine ⟨38407772380848450239206325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25605181587232300159470883 38407772380848450239206325)
                    ·
                      refine ⟨3600728660704542209925593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38407772380848450239206325 3600728660704542209925593)
                      ·
                        rfl

theorem cell23_7012394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_7012394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012394 prefixEnd_7012394 := by exact prefixLift 7012394
  have htrace : WordTrace (prefixWord ++ tailWord_7012394) baseStart_7012394 baseEnd_7012394 := by
    simpa [prefixWord, tailWord_7012394, baseEnd_7012394] using wordTrace_append hprefix tailTrace_7012394
  have hstable : (prefixWord ++ tailWord_7012394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012394).length < 2 ^ (prefixWord ++ tailWord_7012394).sum := by decide
  have hdescent : baseEnd_7012394 < baseStart_7012394 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012407 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 4, 3, 3]
def baseStart_7012407 : Nat := 118140960795 + 7012407 * 2 ^ 59
def prefixEnd_7012407 : Nat := 4983230072969 + 3 ^ 40 * 7012407 * 2
def baseEnd_7012407 : Nat := 3600735335953050659063033

theorem tailTrace_7012407 : CollatzResearch.WordTrace tailWord_7012407 prefixEnd_7012407 3600735335953050659063033 := by
  unfold tailWord_7012407
  simp only [CollatzResearch.WordTrace]
  refine ⟨255763495106254537613011475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170508996737503025075340983 255763495106254537613011475)
  ·
    refine ⟨383645242659381806419517213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255763495106254537613011475 383645242659381806419517213)
    ·
      refine ⟨143866965997268177407318955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383645242659381806419517213 143866965997268177407318955)
      ·
        refine ⟨215800448995902266110978433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143866965997268177407318955 215800448995902266110978433)
        ·
          refine ⟨161850336746926699583233825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215800448995902266110978433 161850336746926699583233825)
          ·
            refine ⟨121387752560195024687425369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161850336746926699583233825 121387752560195024687425369)
            ·
              refine ⟨91040814420146268515569027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121387752560195024687425369 91040814420146268515569027)
              ·
                refine ⟨136561221630219402773353541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91040814420146268515569027 136561221630219402773353541)
                ·
                  refine ⟨25605229055666138020003789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136561221630219402773353541 25605229055666138020003789)
                  ·
                    refine ⟨9601960895874801757501421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25605229055666138020003789 9601960895874801757501421)
                    ·
                      refine ⟨3600735335953050659063033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9601960895874801757501421 3600735335953050659063033)
                      ·
                        rfl

theorem cell23_7012407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 3, 3].length) (baseStart_7012407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012407 prefixEnd_7012407 := by exact prefixLift 7012407
  have htrace : WordTrace (prefixWord ++ tailWord_7012407) baseStart_7012407 baseEnd_7012407 := by
    simpa [prefixWord, tailWord_7012407, baseEnd_7012407] using wordTrace_append hprefix tailTrace_7012407
  have hstable : (prefixWord ++ tailWord_7012407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012407).length < 2 ^ (prefixWord ++ tailWord_7012407).sum := by decide
  have hdescent : baseEnd_7012407 < baseStart_7012407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012444 : List Nat := [2, 2, 4, 1, 1, 2, 1, 3, 2, 5]
def baseStart_7012444 : Nat := 118140960795 + 7012444 * 2 ^ 59
def prefixEnd_7012444 : Nat := 4983230072969 + 3 ^ 40 * 7012444 * 2
def baseEnd_7012444 : Nat := 1200251444912422338100121

theorem tailTrace_7012444 : CollatzResearch.WordTrace tailWord_7012444 prefixEnd_7012444 1200251444912422338100121 := by
  unfold tailWord_7012444
  simp only [CollatzResearch.WordTrace]
  refine ⟨127882422303560246466054193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170509896404746995288072257 127882422303560246466054193)
  ·
    refine ⟨95911816727670184849540645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127882422303560246466054193 95911816727670184849540645)
    ·
      refine ⟨17983465636438159659288871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95911816727670184849540645 17983465636438159659288871)
      ·
        refine ⟨26975198454657239488933307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17983465636438159659288871 26975198454657239488933307)
        ·
          refine ⟨40462797681985859233399961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26975198454657239488933307 40462797681985859233399961)
          ·
            refine ⟨30347098261489394425049971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40462797681985859233399961 30347098261489394425049971)
            ·
              refine ⟨45520647392234091637574957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30347098261489394425049971 45520647392234091637574957)
              ·
                refine ⟨17070242772087784364090609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45520647392234091637574957 17070242772087784364090609)
                ·
                  refine ⟨12802682079065838273067957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17070242772087784364090609 12802682079065838273067957)
                  ·
                    refine ⟨1200251444912422338100121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12802682079065838273067957 1200251444912422338100121)
                    ·
                      rfl

theorem cell23_7012444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_7012444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012444 prefixEnd_7012444 := by exact prefixLift 7012444
  have htrace : WordTrace (prefixWord ++ tailWord_7012444) baseStart_7012444 baseEnd_7012444 := by
    simpa [prefixWord, tailWord_7012444, baseEnd_7012444] using wordTrace_append hprefix tailTrace_7012444
  have hstable : (prefixWord ++ tailWord_7012444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012444).length < 2 ^ (prefixWord ++ tailWord_7012444).sum := by decide
  have hdescent : baseEnd_7012444 < baseStart_7012444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012464 : List Nat := [2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 4]
def baseStart_7012464 : Nat := 118140960795 + 7012464 * 2 ^ 59
def prefixEnd_7012464 : Nat := 4983230072969 + 3 ^ 40 * 7012464 * 2
def baseEnd_7012464 : Nat := 3600764604350356936050271

theorem tailTrace_7012464 : CollatzResearch.WordTrace tailWord_7012464 prefixEnd_7012464 3600764604350356936050271 := by
  unfold tailWord_7012464
  simp only [CollatzResearch.WordTrace]
  refine ⟨127882787033524018173918223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170510382711365357565224297 127882787033524018173918223)
  ·
    refine ⟨191824180550286027260877335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127882787033524018173918223 191824180550286027260877335)
    ·
      refine ⟨287736270825429040891316003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191824180550286027260877335 287736270825429040891316003)
      ·
        refine ⟨431604406238143561336974005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287736270825429040891316003 431604406238143561336974005)
        ·
          refine ⟨40462913084825958875341313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 431604406238143561336974005 40462913084825958875341313)
          ·
            refine ⟨30347184813619469156505985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40462913084825958875341313 30347184813619469156505985)
            ·
              refine ⟨22760388610214601867379489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30347184813619469156505985 22760388610214601867379489)
              ·
                refine ⟨17070291457660951400534617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22760388610214601867379489 17070291457660951400534617)
                ·
                  refine ⟨12802718593245713550400963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17070291457660951400534617 12802718593245713550400963)
                  ·
                    refine ⟨19204077889868570325601445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12802718593245713550400963 19204077889868570325601445)
                    ·
                      refine ⟨3600764604350356936050271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19204077889868570325601445 3600764604350356936050271)
                      ·
                        rfl

theorem cell23_7012464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 4].length) (baseStart_7012464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012464 prefixEnd_7012464 := by exact prefixLift 7012464
  have htrace : WordTrace (prefixWord ++ tailWord_7012464) baseStart_7012464 baseEnd_7012464 := by
    simpa [prefixWord, tailWord_7012464, baseEnd_7012464] using wordTrace_append hprefix tailTrace_7012464
  have hstable : (prefixWord ++ tailWord_7012464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012464).length < 2 ^ (prefixWord ++ tailWord_7012464).sum := by decide
  have hdescent : baseEnd_7012464 < baseStart_7012464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012484 : List Nat := [2, 3, 2, 1, 2, 1, 2, 2, 1, 4, 3]
def baseStart_7012484 : Nat := 118140960795 + 7012484 * 2 ^ 59
def prefixEnd_7012484 : Nat := 4983230072969 + 3 ^ 40 * 7012484 * 2
def baseEnd_7012484 : Nat := 3600774873963446857800179

theorem tailTrace_7012484 : CollatzResearch.WordTrace tailWord_7012484 prefixEnd_7012484 3600774873963446857800179 := by
  unfold tailWord_7012484
  simp only [CollatzResearch.WordTrace]
  refine ⟨127883151763487789881782253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170510869017983719842376337 127883151763487789881782253)
  ·
    refine ⟨47956181911307921205668345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127883151763487789881782253 47956181911307921205668345)
    ·
      refine ⟨35967136433480940904251259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47956181911307921205668345 35967136433480940904251259)
      ·
        refine ⟨53950704650221411356376889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35967136433480940904251259 53950704650221411356376889)
        ·
          refine ⟨40463028487666058517282667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53950704650221411356376889 40463028487666058517282667)
          ·
            refine ⟨60694542731499087775924001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40463028487666058517282667 60694542731499087775924001)
            ·
              refine ⟨45520907048624315831943001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60694542731499087775924001 45520907048624315831943001)
              ·
                refine ⟨34140680286468236873957251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45520907048624315831943001 34140680286468236873957251)
                ·
                  refine ⟨51211020429702355310935877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34140680286468236873957251 51211020429702355310935877)
                  ·
                    refine ⟨9602066330569191620800477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51211020429702355310935877 9602066330569191620800477)
                    ·
                      refine ⟨3600774873963446857800179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9602066330569191620800477 3600774873963446857800179)
                      ·
                        rfl

theorem cell23_7012484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_7012484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012484 prefixEnd_7012484 := by exact prefixLift 7012484
  have htrace : WordTrace (prefixWord ++ tailWord_7012484) baseStart_7012484 baseEnd_7012484 := by
    simpa [prefixWord, tailWord_7012484, baseEnd_7012484] using wordTrace_append hprefix tailTrace_7012484
  have hstable : (prefixWord ++ tailWord_7012484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012484).length < 2 ^ (prefixWord ++ tailWord_7012484).sum := by decide
  have hdescent : baseEnd_7012484 < baseStart_7012484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012508 : List Nat := [2, 2, 3, 2, 1, 1, 4, 3, 1, 4]
def baseStart_7012508 : Nat := 118140960795 + 7012508 * 2 ^ 59
def prefixEnd_7012508 : Nat := 4983230072969 + 3 ^ 40 * 7012508 * 2
def baseEnd_7012508 : Nat := 1200262399166384921300023

theorem tailTrace_7012508 : CollatzResearch.WordTrace tailWord_7012508 prefixEnd_7012508 1200262399166384921300023 := by
  unfold tailWord_7012508
  simp only [CollatzResearch.WordTrace]
  refine ⟨127883589439444315931219089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170511452585925754574958785 127883589439444315931219089)
  ·
    refine ⟨95912692079583236948414317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127883589439444315931219089 95912692079583236948414317)
    ·
      refine ⟨35967259529843713855655369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95912692079583236948414317 35967259529843713855655369)
      ·
        refine ⟨26975444647382785391741527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35967259529843713855655369 26975444647382785391741527)
        ·
          refine ⟨40463166971074178087612291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26975444647382785391741527 40463166971074178087612291)
          ·
            refine ⟨60694750456611267131418437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40463166971074178087612291 60694750456611267131418437)
            ·
              refine ⟨11380265710614612587140957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60694750456611267131418437 11380265710614612587140957)
              ·
                refine ⟨4267599641480479720177859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11380265710614612587140957 4267599641480479720177859)
                ·
                  refine ⟨6401399462220719580266789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4267599641480479720177859 6401399462220719580266789)
                  ·
                    refine ⟨1200262399166384921300023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6401399462220719580266789 1200262399166384921300023)
                    ·
                      rfl

theorem cell23_7012508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_7012508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012508 prefixEnd_7012508 := by exact prefixLift 7012508
  have htrace : WordTrace (prefixWord ++ tailWord_7012508) baseStart_7012508 baseEnd_7012508 := by
    simpa [prefixWord, tailWord_7012508, baseEnd_7012508] using wordTrace_append hprefix tailTrace_7012508
  have hstable : (prefixWord ++ tailWord_7012508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012508).length < 2 ^ (prefixWord ++ tailWord_7012508).sum := by decide
  have hdescent : baseEnd_7012508 < baseStart_7012508 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012548 : List Nat := [2, 3, 3, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_7012548 : Nat := 118140960795 + 7012548 * 2 ^ 59
def prefixEnd_7012548 : Nat := 4983230072969 + 3 ^ 40 * 7012548 * 2
def baseEnd_7012548 : Nat := 3600807736725334607399885

theorem tailTrace_7012548 : CollatzResearch.WordTrace tailWord_7012548 prefixEnd_7012548 3600807736725334607399885 := by
  unfold tailWord_7012548
  simp only [CollatzResearch.WordTrace]
  refine ⟨127884318899371859346947149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170512425199162479129262865 127884318899371859346947149)
  ·
    refine ⟨47956619587264447255105181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127884318899371859346947149 47956619587264447255105181)
    ·
      refine ⟨17983732345224167720664443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47956619587264447255105181 17983732345224167720664443)
      ·
        refine ⟨26975598517836251580996665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17983732345224167720664443 26975598517836251580996665)
        ·
          refine ⟨20231698888377188685747499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26975598517836251580996665 20231698888377188685747499)
          ·
            refine ⟨30347548332565783028621249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20231698888377188685747499 30347548332565783028621249)
            ·
              refine ⟨22760661249424337271465937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30347548332565783028621249 22760661249424337271465937)
              ·
                refine ⟨17070495937068252953599453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22760661249424337271465937 17070495937068252953599453)
                ·
                  refine ⟨6401435976400594857599795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17070495937068252953599453 6401435976400594857599795)
                  ·
                    refine ⟨9602153964600892286399693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6401435976400594857599795 9602153964600892286399693)
                    ·
                      refine ⟨3600807736725334607399885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9602153964600892286399693 3600807736725334607399885)
                      ·
                        rfl

theorem cell23_7012548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_7012548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012548 prefixEnd_7012548 := by exact prefixLift 7012548
  have htrace : WordTrace (prefixWord ++ tailWord_7012548) baseStart_7012548 baseEnd_7012548 := by
    simpa [prefixWord, tailWord_7012548, baseEnd_7012548] using wordTrace_append hprefix tailTrace_7012548
  have hstable : (prefixWord ++ tailWord_7012548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012548).length < 2 ^ (prefixWord ++ tailWord_7012548).sum := by decide
  have hdescent : baseEnd_7012548 < baseStart_7012548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012571 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 7, 2, 2]
def baseStart_7012571 : Nat := 118140960795 + 7012571 * 2 ^ 59
def prefixEnd_7012571 : Nat := 4983230072969 + 3 ^ 40 * 7012571 * 2
def baseEnd_7012571 : Nat := 3600819546780388017412279

theorem tailTrace_7012571 : CollatzResearch.WordTrace tailWord_7012571 prefixEnd_7012571 3600819546780388017412279 := by
  unfold tailWord_7012571
  simp only [CollatzResearch.WordTrace]
  refine ⟨255769476677660393621981567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170512984451773595747987711 255769476677660393621981567)
  ·
    refine ⟨383654215016490590432972351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255769476677660393621981567 383654215016490590432972351)
    ·
      refine ⟨575481322524735885649458527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383654215016490590432972351 575481322524735885649458527)
      ·
        refine ⟨863221983787103828474187791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575481322524735885649458527 863221983787103828474187791)
        ·
          refine ⟨1294832975680655742711281687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 863221983787103828474187791 1294832975680655742711281687)
          ·
            refine ⟨1942249463520983614066922531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1294832975680655742711281687 1942249463520983614066922531)
            ·
              refine ⟨2913374195281475421100383797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1942249463520983614066922531 2913374195281475421100383797)
              ·
                refine ⟨273128830807638320728160981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2913374195281475421100383797 273128830807638320728160981)
                ·
                  refine ⟨6401456972054023142066273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 273128830807638320728160981 6401456972054023142066273)
                  ·
                    refine ⟨4801092729040517356549705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6401456972054023142066273 4801092729040517356549705)
                    ·
                      refine ⟨3600819546780388017412279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4801092729040517356549705 3600819546780388017412279)
                      ·
                        rfl

theorem cell23_7012571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 2, 2].length) (baseStart_7012571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012571 prefixEnd_7012571 := by exact prefixLift 7012571
  have htrace : WordTrace (prefixWord ++ tailWord_7012571) baseStart_7012571 baseEnd_7012571 := by
    simpa [prefixWord, tailWord_7012571, baseEnd_7012571] using wordTrace_append hprefix tailTrace_7012571
  have hstable : (prefixWord ++ tailWord_7012571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012571).length < 2 ^ (prefixWord ++ tailWord_7012571).sum := by decide
  have hdescent : baseEnd_7012571 < baseStart_7012571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012581 : List Nat := [1, 3, 1, 4, 2, 1, 2, 1, 4, 4]
def baseStart_7012581 : Nat := 118140960795 + 7012581 * 2 ^ 59
def prefixEnd_7012581 : Nat := 4983230072969 + 3 ^ 40 * 7012581 * 2
def baseEnd_7012581 : Nat := 1200274893862310992762411

theorem tailTrace_7012581 : CollatzResearch.WordTrace tailWord_7012581 prefixEnd_7012581 1200274893862310992762411 := by
  unfold tailWord_7012581
  simp only [CollatzResearch.WordTrace]
  refine ⟨255769841407624165329845597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170513227605082776886563731 255769841407624165329845597)
  ·
    refine ⟨95913690527859061998692099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255769841407624165329845597 95913690527859061998692099)
    ·
      refine ⟨143870535791788592998038149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95913690527859061998692099 143870535791788592998038149)
      ·
        refine ⟨26975725460960361187132153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143870535791788592998038149 26975725460960361187132153)
        ·
          refine ⟨20231794095720270890349115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26975725460960361187132153 20231794095720270890349115)
          ·
            refine ⟨30347691143580406335523673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20231794095720270890349115 30347691143580406335523673)
            ·
              refine ⟨22760768357685304751642755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30347691143580406335523673 22760768357685304751642755)
              ·
                refine ⟨34141152536527957127464133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22760768357685304751642755 34141152536527957127464133)
                ·
                  refine ⟨6401466100598991961399525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34141152536527957127464133 6401466100598991961399525)
                  ·
                    refine ⟨1200274893862310992762411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6401466100598991961399525 1200274893862310992762411)
                    ·
                      rfl

theorem cell23_7012581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4, 4].length) (baseStart_7012581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012581 prefixEnd_7012581 := by exact prefixLift 7012581
  have htrace : WordTrace (prefixWord ++ tailWord_7012581) baseStart_7012581 baseEnd_7012581 := by
    simpa [prefixWord, tailWord_7012581, baseEnd_7012581] using wordTrace_append hprefix tailTrace_7012581
  have hstable : (prefixWord ++ tailWord_7012581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012581).length < 2 ^ (prefixWord ++ tailWord_7012581).sum := by decide
  have hdescent : baseEnd_7012581 < baseStart_7012581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012584 : List Nat := [2, 1, 4, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_7012584 : Nat := 118140960795 + 7012584 * 2 ^ 59
def prefixEnd_7012584 : Nat := 4983230072969 + 3 ^ 40 * 7012584 * 2
def baseEnd_7012584 : Nat := 3600826222028896466549719

theorem tailTrace_7012584 : CollatzResearch.WordTrace tailWord_7012584 prefixEnd_7012584 3600826222028896466549719 := by
  unfold tailWord_7012584
  simp only [CollatzResearch.WordTrace]
  refine ⟨127884975413306648421102403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170513300551075531228136537 127884975413306648421102403)
  ·
    refine ⟨191827463119959972631653605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127884975413306648421102403 191827463119959972631653605)
    ·
      refine ⟨35967649334992494868435051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191827463119959972631653605 35967649334992494868435051)
      ·
        refine ⟨53951474002488742302652577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35967649334992494868435051 53951474002488742302652577)
        ·
          refine ⟨40463605501866556726989433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53951474002488742302652577 40463605501866556726989433)
          ·
            refine ⟨30347704126399917545242075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40463605501866556726989433 30347704126399917545242075)
            ·
              refine ⟨45521556189599876317863113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30347704126399917545242075 45521556189599876317863113)
              ·
                refine ⟨34141167142199907238397335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45521556189599876317863113 34141167142199907238397335)
                ·
                  refine ⟨51211750713299860857596003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34141167142199907238397335 51211750713299860857596003)
                  ·
                    refine ⟨76817626069949791286394005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51211750713299860857596003 76817626069949791286394005)
                    ·
                      refine ⟨3600826222028896466549719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76817626069949791286394005 3600826222028896466549719)
                      ·
                        rfl

theorem cell23_7012584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_7012584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012584 prefixEnd_7012584 := by exact prefixLift 7012584
  have htrace : WordTrace (prefixWord ++ tailWord_7012584) baseStart_7012584 baseEnd_7012584 := by
    simpa [prefixWord, tailWord_7012584, baseEnd_7012584] using wordTrace_append hprefix tailTrace_7012584
  have hstable : (prefixWord ++ tailWord_7012584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012584).length < 2 ^ (prefixWord ++ tailWord_7012584).sum := by decide
  have hdescent : baseEnd_7012584 < baseStart_7012584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012594 : List Nat := [3, 2, 1, 3, 2, 1, 1, 10]
def baseStart_7012594 : Nat := 118140960795 + 7012594 * 2 ^ 59
def prefixEnd_7012594 : Nat := 4983230072969 + 3 ^ 40 * 7012594 * 2
def baseEnd_7012594 : Nat := 133364124327238571386099

theorem tailTrace_7012594 : CollatzResearch.WordTrace tailWord_7012594 prefixEnd_7012594 133364124327238571386099 := by
  unfold tailWord_7012594
  simp only [CollatzResearch.WordTrace]
  refine ⟨63942578889144267137517209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170513543704384712366712557 63942578889144267137517209)
  ·
    refine ⟨47956934166858200353137907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63942578889144267137517209 47956934166858200353137907)
    ·
      refine ⟨71935401250287300529706861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47956934166858200353137907 71935401250287300529706861)
      ·
        refine ⟨26975775468857737698640073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71935401250287300529706861 26975775468857737698640073)
        ·
          refine ⟨20231831601643303273980055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26975775468857737698640073 20231831601643303273980055)
          ·
            refine ⟨30347747402464954910970083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20231831601643303273980055 30347747402464954910970083)
            ·
              refine ⟨45521621103697432366455125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30347747402464954910970083 45521621103697432366455125)
              ·
                refine ⟨133364124327238571386099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 45521621103697432366455125 133364124327238571386099)
                ·
                  rfl

theorem cell23_7012594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 10].length) (baseStart_7012594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012594 prefixEnd_7012594 := by exact prefixLift 7012594
  have htrace : WordTrace (prefixWord ++ tailWord_7012594) baseStart_7012594 baseEnd_7012594 := by
    simpa [prefixWord, tailWord_7012594, baseEnd_7012594] using wordTrace_append hprefix tailTrace_7012594
  have hstable : (prefixWord ++ tailWord_7012594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012594).length < 2 ^ (prefixWord ++ tailWord_7012594).sum := by decide
  have hdescent : baseEnd_7012594 < baseStart_7012594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012639 : List Nat := [1, 1, 2, 4, 3, 3, 2, 2, 1, 2, 2]
def baseStart_7012639 : Nat := 118140960795 + 7012639 * 2 ^ 59
def prefixEnd_7012639 : Nat := 4983230072969 + 3 ^ 40 * 7012639 * 2
def baseEnd_7012639 : Nat := 3600854463464893751361967

theorem tailTrace_7012639 : CollatzResearch.WordTrace tailWord_7012639 prefixEnd_7012639 3600854463464893751361967 := by
  unfold tailWord_7012639
  simp only [CollatzResearch.WordTrace]
  refine ⟨255771956841414041235456971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170514637894276027490304647 255771956841414041235456971)
  ·
    refine ⟨383657935262121061853185457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255771956841414041235456971 383657935262121061853185457)
    ·
      refine ⟨287743451446590796389889093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383657935262121061853185457 287743451446590796389889093)
      ·
        refine ⟨53951897146235774323104205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 287743451446590796389889093 53951897146235774323104205)
        ·
          refine ⟨20231961429838415371164077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53951897146235774323104205 20231961429838415371164077)
          ·
            refine ⟨7586985536189405764186529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20231961429838415371164077 7586985536189405764186529)
            ·
              refine ⟨5690239152142054323139897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7586985536189405764186529 5690239152142054323139897)
              ·
                refine ⟨4267679364106540742354923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5690239152142054323139897 4267679364106540742354923)
                ·
                  refine ⟨6401519046159811113532385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4267679364106540742354923 6401519046159811113532385)
                  ·
                    refine ⟨4801139284619858335149289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6401519046159811113532385 4801139284619858335149289)
                    ·
                      refine ⟨3600854463464893751361967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4801139284619858335149289 3600854463464893751361967)
                      ·
                        rfl

theorem cell23_7012639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_7012639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012639 prefixEnd_7012639 := by exact prefixLift 7012639
  have htrace : WordTrace (prefixWord ++ tailWord_7012639) baseStart_7012639 baseEnd_7012639 := by
    simpa [prefixWord, tailWord_7012639, baseEnd_7012639] using wordTrace_append hprefix tailTrace_7012639
  have hstable : (prefixWord ++ tailWord_7012639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012639).length < 2 ^ (prefixWord ++ tailWord_7012639).sum := by decide
  have hdescent : baseEnd_7012639 < baseStart_7012639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012664 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 4, 1, 5]
def baseStart_7012664 : Nat := 118140960795 + 7012664 * 2 ^ 59
def prefixEnd_7012664 : Nat := 4983230072969 + 3 ^ 40 * 7012664 * 2
def baseEnd_7012664 : Nat := 3600867300481256153549351

theorem tailTrace_7012664 : CollatzResearch.WordTrace tailWord_7012664 prefixEnd_7012664 3600867300481256153549351 := by
  unfold tailWord_7012664
  simp only [CollatzResearch.WordTrace]
  refine ⟨127886434333161735252558523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170515245777548980336744697 127886434333161735252558523)
  ·
    refine ⟨191829651499742602878837785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127886434333161735252558523 191829651499742602878837785)
    ·
      refine ⟨143872238624806952159128339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191829651499742602878837785 143872238624806952159128339)
      ·
        refine ⟨215808357937210428238692509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143872238624806952159128339 215808357937210428238692509)
        ·
          refine ⟨80928134226453910589509691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215808357937210428238692509 80928134226453910589509691)
          ·
            refine ⟨121392201339680865884264537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80928134226453910589509691 121392201339680865884264537)
            ·
              refine ⟨91044151004760649413198403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121392201339680865884264537 91044151004760649413198403)
              ·
                refine ⟨136566226507140974119797605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91044151004760649413198403 136566226507140974119797605)
                ·
                  refine ⟨25606167470088932647462051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136566226507140974119797605 25606167470088932647462051)
                  ·
                    refine ⟨38409251205133398971193077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25606167470088932647462051 38409251205133398971193077)
                    ·
                      refine ⟨3600867300481256153549351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38409251205133398971193077 3600867300481256153549351)
                      ·
                        rfl

theorem cell23_7012664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_7012664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012664 prefixEnd_7012664 := by exact prefixLift 7012664
  have htrace : WordTrace (prefixWord ++ tailWord_7012664) baseStart_7012664 baseEnd_7012664 := by
    simpa [prefixWord, tailWord_7012664, baseEnd_7012664] using wordTrace_append hprefix tailTrace_7012664
  have hstable : (prefixWord ++ tailWord_7012664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012664).length < 2 ^ (prefixWord ++ tailWord_7012664).sum := by decide
  have hdescent : baseEnd_7012664 < baseStart_7012664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012684 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 9]
def baseStart_7012684 : Nat := 118140960795 + 7012684 * 2 ^ 59
def prefixEnd_7012684 : Nat := 4983230072969 + 3 ^ 40 * 7012684 * 2
def baseEnd_7012684 : Nat := 400097507788260675033251

theorem tailTrace_7012684 : CollatzResearch.WordTrace tailWord_7012684 prefixEnd_7012684 400097507788260675033251 := by
  unfold tailWord_7012684
  simp only [CollatzResearch.WordTrace]
  refine ⟨127886799063125506960422553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170515732084167342613896737 127886799063125506960422553)
  ·
    refine ⟨95915099297344130220316915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127886799063125506960422553 95915099297344130220316915)
    ·
      refine ⟨143872648946016195330475373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95915099297344130220316915 143872648946016195330475373)
      ·
        refine ⟨53952243354756073248928265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143872648946016195330475373 53952243354756073248928265)
        ·
          refine ⟨40464182516067054936696199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53952243354756073248928265 40464182516067054936696199)
          ·
            refine ⟨60696273774100582405044299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40464182516067054936696199 60696273774100582405044299)
            ·
              refine ⟨91044410661150873607566449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60696273774100582405044299 91044410661150873607566449)
              ·
                refine ⟨68283307995863155205674837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91044410661150873607566449 68283307995863155205674837)
                ·
                  refine ⟨400097507788260675033251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68283307995863155205674837 400097507788260675033251)
                  ·
                    rfl

theorem cell23_7012684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 9].length) (baseStart_7012684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012684 prefixEnd_7012684 := by exact prefixLift 7012684
  have htrace : WordTrace (prefixWord ++ tailWord_7012684) baseStart_7012684 baseEnd_7012684 := by
    simpa [prefixWord, tailWord_7012684, baseEnd_7012684] using wordTrace_append hprefix tailTrace_7012684
  have hstable : (prefixWord ++ tailWord_7012684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012684).length < 2 ^ (prefixWord ++ tailWord_7012684).sum := by decide
  have hdescent : baseEnd_7012684 < baseStart_7012684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012808 : List Nat := [2, 1, 3, 1, 3, 3, 2, 2, 6]
def baseStart_7012808 : Nat := 118140960795 + 7012808 * 2 ^ 59
def prefixEnd_7012808 : Nat := 4983230072969 + 3 ^ 40 * 7012808 * 2
def baseEnd_7012808 : Nat := 400104582410611510016521

theorem tailTrace_7012808 : CollatzResearch.WordTrace tailWord_7012808 prefixEnd_7012808 400104582410611510016521 := by
  unfold tailWord_7012808
  simp only [CollatzResearch.WordTrace]
  refine ⟨127889060388900891549179539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170518747185201188732239385 127889060388900891549179539)
  ·
    refine ⟨191833590583351337323769309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127889060388900891549179539 191833590583351337323769309)
    ·
      refine ⟨71937596468756751496413491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191833590583351337323769309 71937596468756751496413491)
      ·
        refine ⟨107906394703135127244620237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71937596468756751496413491 107906394703135127244620237)
        ·
          refine ⟨40464898013675672716732589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107906394703135127244620237 40464898013675672716732589)
          ·
            refine ⟨15174336755128377268774721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40464898013675672716732589 15174336755128377268774721)
            ·
              refine ⟨11380752566346282951581041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15174336755128377268774721 11380752566346282951581041)
              ·
                refine ⟨8535564424759712213685781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11380752566346282951581041 8535564424759712213685781)
                ·
                  refine ⟨400104582410611510016521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8535564424759712213685781 400104582410611510016521)
                  ·
                    rfl

theorem cell23_7012808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 6].length) (baseStart_7012808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012808 prefixEnd_7012808 := by exact prefixLift 7012808
  have htrace : WordTrace (prefixWord ++ tailWord_7012808) baseStart_7012808 baseEnd_7012808 := by
    simpa [prefixWord, tailWord_7012808, baseEnd_7012808] using wordTrace_append hprefix tailTrace_7012808
  have hstable : (prefixWord ++ tailWord_7012808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012808).length < 2 ^ (prefixWord ++ tailWord_7012808).sum := by decide
  have hdescent : baseEnd_7012808 < baseStart_7012808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012812 : List Nat := [2, 2, 1, 4, 3, 1, 1, 4, 1, 4]
def baseStart_7012812 : Nat := 118140960795 + 7012812 * 2 ^ 59
def prefixEnd_7012812 : Nat := 4983230072969 + 3 ^ 40 * 7012812 * 2
def baseEnd_7012812 : Nat := 1200314431872707191499557

theorem tailTrace_7012812 : CollatzResearch.WordTrace tailWord_7012812 prefixEnd_7012812 1200314431872707191499557 := by
  unfold tailWord_7012812
  simp only [CollatzResearch.WordTrace]
  refine ⟨127889133334893645890752345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170518844446524861187669793 127889133334893645890752345)
  ·
    refine ⟨95916850001170234418064259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127889133334893645890752345 95916850001170234418064259)
    ·
      refine ⟨143875275001755351627096389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95916850001170234418064259 143875275001755351627096389)
      ·
        refine ⟨26976614062829128430080573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143875275001755351627096389 26976614062829128430080573)
        ·
          refine ⟨10116230273560923161280215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26976614062829128430080573 10116230273560923161280215)
          ·
            refine ⟨15174345410341384741920323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10116230273560923161280215 15174345410341384741920323)
            ·
              refine ⟨22761518115512077112880485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15174345410341384741920323 22761518115512077112880485)
              ·
                refine ⟨4267784646658514458665091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22761518115512077112880485 4267784646658514458665091)
                ·
                  refine ⟨6401676969987771687997637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4267784646658514458665091 6401676969987771687997637)
                  ·
                    refine ⟨1200314431872707191499557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6401676969987771687997637 1200314431872707191499557)
                    ·
                      rfl

theorem cell23_7012812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4, 1, 4].length) (baseStart_7012812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012812 prefixEnd_7012812 := by exact prefixLift 7012812
  have htrace : WordTrace (prefixWord ++ tailWord_7012812) baseStart_7012812 baseEnd_7012812 := by
    simpa [prefixWord, tailWord_7012812, baseEnd_7012812] using wordTrace_append hprefix tailTrace_7012812
  have hstable : (prefixWord ++ tailWord_7012812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012812).length < 2 ^ (prefixWord ++ tailWord_7012812).sum := by decide
  have hdescent : baseEnd_7012812 < baseStart_7012812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012851 : List Nat := [1, 1, 1, 2, 2, 2, 3, 4, 1, 6]
def baseStart_7012851 : Nat := 118140960795 + 7012851 * 2 ^ 59
def prefixEnd_7012851 : Nat := 4983230072969 + 3 ^ 40 * 7012851 * 2
def baseEnd_7012851 : Nat := 1200321107121215640636997

theorem tailTrace_7012851 : CollatzResearch.WordTrace tailWord_7012851 prefixEnd_7012851 1200321107121215640636997 := by
  unfold tailWord_7012851
  simp only [CollatzResearch.WordTrace]
  refine ⟨255779689116646001442174407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170519792744430667628116271 255779689116646001442174407)
  ·
    refine ⟨383669533674969002163261611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255779689116646001442174407 383669533674969002163261611)
    ·
      refine ⟨575504300512453503244892417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383669533674969002163261611 575504300512453503244892417)
      ·
        refine ⟨431628225384340127433669313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 575504300512453503244892417 431628225384340127433669313)
        ·
          refine ⟨323721169038255095575251985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431628225384340127433669313 323721169038255095575251985)
          ·
            refine ⟨242790876778691321681438989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323721169038255095575251985 242790876778691321681438989)
            ·
              refine ⟨91046578792009245630539621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242790876778691321681438989 91046578792009245630539621)
              ·
                refine ⟨17071233523501733555726179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91046578792009245630539621 17071233523501733555726179)
                ·
                  refine ⟨25606850285252600333589269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17071233523501733555726179 25606850285252600333589269)
                  ·
                    refine ⟨1200321107121215640636997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25606850285252600333589269 1200321107121215640636997)
                    ·
                      rfl

theorem cell23_7012851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 6].length) (baseStart_7012851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012851 prefixEnd_7012851 := by exact prefixLift 7012851
  have htrace : WordTrace (prefixWord ++ tailWord_7012851) baseStart_7012851 baseEnd_7012851 := by
    simpa [prefixWord, tailWord_7012851, baseEnd_7012851] using wordTrace_append hprefix tailTrace_7012851
  have hstable : (prefixWord ++ tailWord_7012851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012851).length < 2 ^ (prefixWord ++ tailWord_7012851).sum := by decide
  have hdescent : baseEnd_7012851 < baseStart_7012851 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012878 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5]
def baseStart_7012878 : Nat := 118140960795 + 7012878 * 2 ^ 59
def prefixEnd_7012878 : Nat := 4983230072969 + 3 ^ 40 * 7012878 * 2
def baseEnd_7012878 : Nat := 3600977185341318316273367

theorem tailTrace_7012878 : CollatzResearch.WordTrace tailWord_7012878 prefixEnd_7012878 3600977185341318316273367 := by
  unfold tailWord_7012878
  simp only [CollatzResearch.WordTrace]
  refine ⟨31972584235943523131675911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170520449258365456702271525 31972584235943523131675911)
  ·
    refine ⟨47958876353915284697513867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31972584235943523131675911 47958876353915284697513867)
    ·
      refine ⟨71938314530872927046270801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47958876353915284697513867 71938314530872927046270801)
      ·
        refine ⟨53953735898154695284703101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71938314530872927046270801 53953735898154695284703101)
        ·
          refine ⟨20232650961808010731763663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53953735898154695284703101 20232650961808010731763663)
          ·
            refine ⟨30348976442712016097645495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20232650961808010731763663 30348976442712016097645495)
            ·
              refine ⟨45523464664068024146468243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30348976442712016097645495 45523464664068024146468243)
              ·
                refine ⟨68285196996102036219702365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45523464664068024146468243 68285196996102036219702365)
                ·
                  refine ⟨25606948873538263582388387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68285196996102036219702365 25606948873538263582388387)
                  ·
                    refine ⟨38410423310307395373582581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25606948873538263582388387 38410423310307395373582581)
                    ·
                      refine ⟨3600977185341318316273367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38410423310307395373582581 3600977185341318316273367)
                      ·
                        rfl

theorem cell23_7012878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_7012878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012878 prefixEnd_7012878 := by exact prefixLift 7012878
  have htrace : WordTrace (prefixWord ++ tailWord_7012878) baseStart_7012878 baseEnd_7012878 := by
    simpa [prefixWord, tailWord_7012878, baseEnd_7012878] using wordTrace_append hprefix tailTrace_7012878
  have hstable : (prefixWord ++ tailWord_7012878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012878).length < 2 ^ (prefixWord ++ tailWord_7012878).sum := by decide
  have hdescent : baseEnd_7012878 < baseStart_7012878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012888 : List Nat := [2, 1, 2, 3, 3, 2, 1, 1, 1, 1, 6]
def baseStart_7012888 : Nat := 118140960795 + 7012888 * 2 ^ 59
def prefixEnd_7012888 : Nat := 4983230072969 + 3 ^ 40 * 7012888 * 2
def baseEnd_7012888 : Nat := 3600982320147863277148321

theorem tailTrace_7012888 : CollatzResearch.WordTrace tailWord_7012888 prefixEnd_7012888 3600982320147863277148321 := by
  unfold tailWord_7012888
  simp only [CollatzResearch.WordTrace]
  refine ⟨127890519308755978380635659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170520692411674637840847545 127890519308755978380635659)
  ·
    refine ⟨191835778963133967570953489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127890519308755978380635659 191835778963133967570953489)
    ·
      refine ⟨143876834222350475678215117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191835778963133967570953489 143876834222350475678215117)
      ·
        refine ⟨53953812833381428379330669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143876834222350475678215117 53953812833381428379330669)
        ·
          refine ⟨20232679812518035642249001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53953812833381428379330669 20232679812518035642249001)
          ·
            refine ⟨15174509859388526731686751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20232679812518035642249001 15174509859388526731686751)
            ·
              refine ⟨22761764789082790097530127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15174509859388526731686751 22761764789082790097530127)
              ·
                refine ⟨34142647183624185146295191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22761764789082790097530127 34142647183624185146295191)
                ·
                  refine ⟨51213970775436277719442787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34142647183624185146295191 51213970775436277719442787)
                  ·
                    refine ⟨76820956163154416579164181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51213970775436277719442787 76820956163154416579164181)
                    ·
                      refine ⟨3600982320147863277148321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76820956163154416579164181 3600982320147863277148321)
                      ·
                        rfl

theorem cell23_7012888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_7012888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012888 prefixEnd_7012888 := by exact prefixLift 7012888
  have htrace : WordTrace (prefixWord ++ tailWord_7012888) baseStart_7012888 baseEnd_7012888 := by
    simpa [prefixWord, tailWord_7012888, baseEnd_7012888] using wordTrace_append hprefix tailTrace_7012888
  have hstable : (prefixWord ++ tailWord_7012888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012888).length < 2 ^ (prefixWord ++ tailWord_7012888).sum := by decide
  have hdescent : baseEnd_7012888 < baseStart_7012888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012892 : List Nat := [2, 2, 3, 1, 2, 2, 2, 2, 3, 2, 2]
def baseStart_7012892 : Nat := 118140960795 + 7012892 * 2 ^ 59
def prefixEnd_7012892 : Nat := 4983230072969 + 3 ^ 40 * 7012892 * 2
def baseEnd_7012892 : Nat := 3600984374070481261498303

theorem tailTrace_7012892 : CollatzResearch.WordTrace tailWord_7012892 prefixEnd_7012892 3600984374070481261498303 := by
  unfold tailWord_7012892
  simp only [CollatzResearch.WordTrace]
  refine ⟨127890592254748732722208465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170520789672998310296277953 127890592254748732722208465)
  ·
    refine ⟨95917944191061549541656349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127890592254748732722208465 95917944191061549541656349)
    ·
      refine ⟨35969229071648081078121131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95917944191061549541656349 35969229071648081078121131)
      ·
        refine ⟨53953843607472121617181697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35969229071648081078121131 53953843607472121617181697)
        ·
          refine ⟨40465382705604091212886273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53953843607472121617181697 40465382705604091212886273)
          ·
            refine ⟨30349037029203068409664705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40465382705604091212886273 30349037029203068409664705)
            ·
              refine ⟨22761777771902301307248529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30349037029203068409664705 22761777771902301307248529)
              ·
                refine ⟨17071333328926725980436397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22761777771902301307248529 17071333328926725980436397)
                ·
                  refine ⟨6401749998347522242663649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17071333328926725980436397 6401749998347522242663649)
                  ·
                    refine ⟨4801312498760641681997737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6401749998347522242663649 4801312498760641681997737)
                    ·
                      refine ⟨3600984374070481261498303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4801312498760641681997737 3600984374070481261498303)
                      ·
                        rfl

theorem cell23_7012892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_7012892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012892 prefixEnd_7012892 := by exact prefixLift 7012892
  have htrace : WordTrace (prefixWord ++ tailWord_7012892) baseStart_7012892 baseEnd_7012892 := by
    simpa [prefixWord, tailWord_7012892, baseEnd_7012892] using wordTrace_append hprefix tailTrace_7012892
  have hstable : (prefixWord ++ tailWord_7012892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012892).length < 2 ^ (prefixWord ++ tailWord_7012892).sum := by decide
  have hdescent : baseEnd_7012892 < baseStart_7012892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012903 : List Nat := [1, 1, 7, 2, 1, 2, 1, 3, 1, 1, 3]
def baseStart_7012903 : Nat := 118140960795 + 7012903 * 2 ^ 59
def prefixEnd_7012903 : Nat := 4983230072969 + 3 ^ 40 * 7012903 * 2
def baseEnd_7012903 : Nat := 3600990022357680718460753

theorem tailTrace_7012903 : CollatzResearch.WordTrace tailWord_7012903 prefixEnd_7012903 3600990022357680718460753 := by
  unfold tailWord_7012903
  simp only [CollatzResearch.WordTrace]
  refine ⟨255781585712457614323067363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170521057141638409548711575 255781585712457614323067363)
  ·
    refine ⟨383672378568686421484601045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255781585712457614323067363 383672378568686421484601045)
    ·
      refine ⟨8992321372703588003545337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 383672378568686421484601045 8992321372703588003545337)
      ·
        refine ⟨6744241029527691002659003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8992321372703588003545337 6744241029527691002659003)
        ·
          refine ⟨10116361544291536503988505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6744241029527691002659003 10116361544291536503988505)
          ·
            refine ⟨7587271158218652377991379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10116361544291536503988505 7587271158218652377991379)
            ·
              refine ⟨11380906737327978566987069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7587271158218652377991379 11380906737327978566987069)
              ·
                refine ⟨4267840026497991962620151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11380906737327978566987069 4267840026497991962620151)
                ·
                  refine ⟨6401760039746987943930227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4267840026497991962620151 6401760039746987943930227)
                  ·
                    refine ⟨9602640059620481915895341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6401760039746987943930227 9602640059620481915895341)
                    ·
                      refine ⟨3600990022357680718460753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9602640059620481915895341 3600990022357680718460753)
                      ·
                        rfl

theorem cell23_7012903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_7012903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012903 prefixEnd_7012903 := by exact prefixLift 7012903
  have htrace : WordTrace (prefixWord ++ tailWord_7012903) baseStart_7012903 baseEnd_7012903 := by
    simpa [prefixWord, tailWord_7012903, baseEnd_7012903] using wordTrace_append hprefix tailTrace_7012903
  have hstable : (prefixWord ++ tailWord_7012903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012903).length < 2 ^ (prefixWord ++ tailWord_7012903).sum := by decide
  have hdescent : baseEnd_7012903 < baseStart_7012903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012908 : List Nat := [2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 3]
def baseStart_7012908 : Nat := 118140960795 + 7012908 * 2 ^ 59
def prefixEnd_7012908 : Nat := 4983230072969 + 3 ^ 40 * 7012908 * 2
def baseEnd_7012908 : Nat := 3600992589760953198898229

theorem tailTrace_7012908 : CollatzResearch.WordTrace tailWord_7012908 prefixEnd_7012908 3600992589760953198898229 := by
  unfold tailWord_7012908
  simp only [CollatzResearch.WordTrace]
  refine ⟨127890884038719750088499689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170521178718293000117999585 127890884038719750088499689)
  ·
    refine ⟨95918163029039812566374767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127890884038719750088499689 95918163029039812566374767)
    ·
      refine ⟨143877244543559718849562151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95918163029039812566374767 143877244543559718849562151)
      ·
        refine ⟨215815866815339578274343227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143877244543559718849562151 215815866815339578274343227)
        ·
          refine ⟨323723800223009367411514841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215815866815339578274343227 323723800223009367411514841)
          ·
            refine ⟨242792850167257025558636131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323723800223009367411514841 242792850167257025558636131)
            ·
              refine ⟨364189275250885538337954197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242792850167257025558636131 364189275250885538337954197)
              ·
                refine ⟨17071372277385259609591603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 364189275250885538337954197 17071372277385259609591603)
                ·
                  refine ⟨25607058416077889414387405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17071372277385259609591603 25607058416077889414387405)
                  ·
                    refine ⟨9602646906029208530395277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25607058416077889414387405 9602646906029208530395277)
                    ·
                      refine ⟨3600992589760953198898229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9602646906029208530395277 3600992589760953198898229)
                      ·
                        rfl

theorem cell23_7012908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 3].length) (baseStart_7012908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012908 prefixEnd_7012908 := by exact prefixLift 7012908
  have htrace : WordTrace (prefixWord ++ tailWord_7012908) baseStart_7012908 baseEnd_7012908 := by
    simpa [prefixWord, tailWord_7012908, baseEnd_7012908] using wordTrace_append hprefix tailTrace_7012908
  have hstable : (prefixWord ++ tailWord_7012908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012908).length < 2 ^ (prefixWord ++ tailWord_7012908).sum := by decide
  have hdescent : baseEnd_7012908 < baseStart_7012908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012952 : List Nat := [2, 1, 2, 2, 1, 2, 5, 2, 1, 3, 2]
def baseStart_7012952 : Nat := 118140960795 + 7012952 * 2 ^ 59
def prefixEnd_7012952 : Nat := 4983230072969 + 3 ^ 40 * 7012952 * 2
def baseEnd_7012952 : Nat := 3601015182909751026748027

theorem tailTrace_7012952 : CollatzResearch.WordTrace tailWord_7012952 prefixEnd_7012952 3601015182909751026748027 := by
  unfold tailWord_7012952
  simp only [CollatzResearch.WordTrace]
  refine ⟨127891686444640047845800555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170522248592853397127734073 127891686444640047845800555)
  ·
    refine ⟨191837529666960071768700833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127891686444640047845800555 191837529666960071768700833)
    ·
      refine ⟨143878147250220053826525625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191837529666960071768700833 143878147250220053826525625)
      ·
        refine ⟨107908610437665040369894219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143878147250220053826525625 107908610437665040369894219)
        ·
          refine ⟨161862915656497560554841329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107908610437665040369894219 161862915656497560554841329)
          ·
            refine ⟨121397186742373170416130997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161862915656497560554841329 121397186742373170416130997)
            ·
              refine ⟨11380986257097484726512281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121397186742373170416130997 11380986257097484726512281)
              ·
                refine ⟨8535739692823113544884211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11380986257097484726512281 8535739692823113544884211)
                ·
                  refine ⟨12803609539234670317326317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8535739692823113544884211 12803609539234670317326317)
                  ·
                    refine ⟨4801353577213001368997369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12803609539234670317326317 4801353577213001368997369)
                    ·
                      refine ⟨3601015182909751026748027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4801353577213001368997369 3601015182909751026748027)
                      ·
                        rfl

theorem cell23_7012952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 2, 1, 3, 2].length) (baseStart_7012952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012952 prefixEnd_7012952 := by exact prefixLift 7012952
  have htrace : WordTrace (prefixWord ++ tailWord_7012952) baseStart_7012952 baseEnd_7012952 := by
    simpa [prefixWord, tailWord_7012952, baseEnd_7012952] using wordTrace_append hprefix tailTrace_7012952
  have hstable : (prefixWord ++ tailWord_7012952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012952).length < 2 ^ (prefixWord ++ tailWord_7012952).sum := by decide
  have hdescent : baseEnd_7012952 < baseStart_7012952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7012971 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 11]
def baseStart_7012971 : Nat := 118140960795 + 7012971 * 2 ^ 59
def prefixEnd_7012971 : Nat := 4983230072969 + 3 ^ 40 * 7012971 * 2
def baseEnd_7012971 : Nat := 400113882115798494712271

theorem tailTrace_7012971 : CollatzResearch.WordTrace tailWord_7012971 prefixEnd_7012971 400113882115798494712271 := by
  unfold tailWord_7012971
  simp only [CollatzResearch.WordTrace]
  refine ⟨255784065876211261936542767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170522710584140841291028511 255784065876211261936542767)
  ·
    refine ⟨383676098814316892904814151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255784065876211261936542767 383676098814316892904814151)
    ·
      refine ⟨575514148221475339357221227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383676098814316892904814151 575514148221475339357221227)
      ·
        refine ⟨863271222332213009035831841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575514148221475339357221227 863271222332213009035831841)
        ·
          refine ⟨647453416749159756776873881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 863271222332213009035831841 647453416749159756776873881)
          ·
            refine ⟨485590062561869817582655411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 647453416749159756776873881 485590062561869817582655411)
            ·
              refine ⟨728385093842804726373983117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485590062561869817582655411 728385093842804726373983117)
              ·
                refine ⟨273144410191051772390243669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 728385093842804726373983117 273144410191051772390243669)
                ·
                  refine ⟨400113882115798494712271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 273144410191051772390243669 400113882115798494712271)
                  ·
                    rfl

theorem cell23_7012971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 11].length) (baseStart_7012971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7012971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7012971 prefixEnd_7012971 := by exact prefixLift 7012971
  have htrace : WordTrace (prefixWord ++ tailWord_7012971) baseStart_7012971 baseEnd_7012971 := by
    simpa [prefixWord, tailWord_7012971, baseEnd_7012971] using wordTrace_append hprefix tailTrace_7012971
  have hstable : (prefixWord ++ tailWord_7012971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7012971).length < 2 ^ (prefixWord ++ tailWord_7012971).sum := by decide
  have hdescent : baseEnd_7012971 < baseStart_7012971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7012971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013092 : List Nat := [2, 3, 1, 1, 1, 5, 1, 2, 2, 2, 3]
def baseStart_7013092 : Nat := 118140960795 + 7013092 * 2 ^ 59
def prefixEnd_7013092 : Nat := 4983230072969 + 3 ^ 40 * 7013092 * 2
def baseEnd_7013092 : Nat := 3601087070201380478997383

theorem tailTrace_7013092 : CollatzResearch.WordTrace tailWord_7013092 prefixEnd_7013092 3601087070201380478997383 := by
  unfold tailWord_7013092
  simp only [CollatzResearch.WordTrace]
  refine ⟨127894239554386449800848765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170525652739181933067798353 127894239554386449800848765)
  ·
    refine ⟨47960339832894918675318287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127894239554386449800848765 47960339832894918675318287)
    ·
      refine ⟨71940509749342378012977431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47960339832894918675318287 71940509749342378012977431)
      ·
        refine ⟨107910764624013567019466147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71940509749342378012977431 107910764624013567019466147)
        ·
          refine ⟨161866146936020350529199221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107910764624013567019466147 161866146936020350529199221)
          ·
            refine ⟨15174951275251907862112427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 161866146936020350529199221 15174951275251907862112427)
            ·
              refine ⟨22762426912877861793168641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15174951275251907862112427 22762426912877861793168641)
              ·
                refine ⟨17071820184658396344876481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22762426912877861793168641 17071820184658396344876481)
                ·
                  refine ⟨12803865138493797258657361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17071820184658396344876481 12803865138493797258657361)
                  ·
                    refine ⟨9602898853870347943993021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12803865138493797258657361 9602898853870347943993021)
                    ·
                      refine ⟨3601087070201380478997383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9602898853870347943993021 3601087070201380478997383)
                      ·
                        rfl

theorem cell23_7013092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_7013092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013092 prefixEnd_7013092 := by exact prefixLift 7013092
  have htrace : WordTrace (prefixWord ++ tailWord_7013092) baseStart_7013092 baseEnd_7013092 := by
    simpa [prefixWord, tailWord_7013092, baseEnd_7013092] using wordTrace_append hprefix tailTrace_7013092
  have hstable : (prefixWord ++ tailWord_7013092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013092).length < 2 ^ (prefixWord ++ tailWord_7013092).sum := by decide
  have hdescent : baseEnd_7013092 < baseStart_7013092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013139 : List Nat := [1, 1, 1, 2, 1, 3, 4, 5, 1, 1, 3]
def baseStart_7013139 : Nat := 118140960795 + 7013139 * 2 ^ 59
def prefixEnd_7013139 : Nat := 4983230072969 + 3 ^ 40 * 7013139 * 2
def baseEnd_7013139 : Nat := 3601111203792141795109667

theorem tailTrace_7013139 : CollatzResearch.WordTrace tailWord_7013139 prefixEnd_7013139 3601111203792141795109667 := by
  unfold tailWord_7013139
  simp only [CollatzResearch.WordTrace]
  refine ⟨255790193339602626628658471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170526795559735084419105647 255790193339602626628658471)
  ·
    refine ⟨383685290009403939942987707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255790193339602626628658471 383685290009403939942987707)
    ·
      refine ⟨575527935014105909914481561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383685290009403939942987707 575527935014105909914481561)
      ·
        refine ⟨431645951260579432435861171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 575527935014105909914481561 431645951260579432435861171)
        ·
          refine ⟨647468926890869148653791757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431645951260579432435861171 647468926890869148653791757)
          ·
            refine ⟨242800847584075930745171909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 647468926890869148653791757 242800847584075930745171909)
            ·
              refine ⟨45525158922014237014719733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 242800847584075930745171909 45525158922014237014719733)
              ·
                refine ⟨4267983648938834720129975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45525158922014237014719733 4267983648938834720129975)
                ·
                  refine ⟨6401975473408252080194963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4267983648938834720129975 6401975473408252080194963)
                  ·
                    refine ⟨9602963210112378120292445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6401975473408252080194963 9602963210112378120292445)
                    ·
                      refine ⟨3601111203792141795109667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9602963210112378120292445 3601111203792141795109667)
                      ·
                        rfl

theorem cell23_7013139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5, 1, 1, 3].length) (baseStart_7013139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013139 prefixEnd_7013139 := by exact prefixLift 7013139
  have htrace : WordTrace (prefixWord ++ tailWord_7013139) baseStart_7013139 baseEnd_7013139 := by
    simpa [prefixWord, tailWord_7013139, baseEnd_7013139] using wordTrace_append hprefix tailTrace_7013139
  have hstable : (prefixWord ++ tailWord_7013139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013139).length < 2 ^ (prefixWord ++ tailWord_7013139).sum := by decide
  have hdescent : baseEnd_7013139 < baseStart_7013139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013196 : List Nat := [2, 2, 1, 3, 3, 3, 2, 1, 1, 1, 4]
def baseStart_7013196 : Nat := 118140960795 + 7013196 * 2 ^ 59
def prefixEnd_7013196 : Nat := 4983230072969 + 3 ^ 40 * 7013196 * 2
def baseEnd_7013196 : Nat := 3601140472189448072096905

theorem tailTrace_7013196 : CollatzResearch.WordTrace tailWord_7013196 prefixEnd_7013196 3601140472189448072096905 := by
  unfold tailWord_7013196
  simp only [CollatzResearch.WordTrace]
  refine ⟨127896136150198062681741721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170528181533597416908988961 127896136150198062681741721)
  ·
    refine ⟨95922102112648547011306291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127896136150198062681741721 95922102112648547011306291)
    ·
      refine ⟨143883153168972820516959437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95922102112648547011306291 143883153168972820516959437)
      ·
        refine ⟨53956182438364807693859789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143883153168972820516959437 53956182438364807693859789)
        ·
          refine ⟨20233568414386802885197421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53956182438364807693859789 20233568414386802885197421)
          ·
            refine ⟨7587588155395051081949033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20233568414386802885197421 7587588155395051081949033)
            ·
              refine ⟨5690691116546288311461775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7587588155395051081949033 5690691116546288311461775)
              ·
                refine ⟨8536036674819432467192663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5690691116546288311461775 8536036674819432467192663)
                ·
                  refine ⟨12804055012229148700788995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8536036674819432467192663 12804055012229148700788995)
                  ·
                    refine ⟨19206082518343723051183493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12804055012229148700788995 19206082518343723051183493)
                    ·
                      refine ⟨3601140472189448072096905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19206082518343723051183493 3601140472189448072096905)
                      ·
                        rfl

theorem cell23_7013196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_7013196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013196 prefixEnd_7013196 := by exact prefixLift 7013196
  have htrace : WordTrace (prefixWord ++ tailWord_7013196) baseStart_7013196 baseEnd_7013196 := by
    simpa [prefixWord, tailWord_7013196, baseEnd_7013196] using wordTrace_append hprefix tailTrace_7013196
  have hstable : (prefixWord ++ tailWord_7013196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013196).length < 2 ^ (prefixWord ++ tailWord_7013196).sum := by decide
  have hdescent : baseEnd_7013196 < baseStart_7013196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013235 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 4]
def baseStart_7013235 : Nat := 118140960795 + 7013235 * 2 ^ 59
def prefixEnd_7013235 : Nat := 4983230072969 + 3 ^ 40 * 7013235 * 2
def baseEnd_7013235 : Nat := 3601160497934973419509225

theorem tailTrace_7013235 : CollatzResearch.WordTrace tailWord_7013235 prefixEnd_7013235 3601160497934973419509225 := by
  unfold tailWord_7013235
  simp only [CollatzResearch.WordTrace]
  refine ⟨255793694747254835024153159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170529129831503223349435439 255793694747254835024153159)
  ·
    refine ⟨383690542120882252536229739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255793694747254835024153159 383690542120882252536229739)
    ·
      refine ⟨575535813181323378804344609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383690542120882252536229739 575535813181323378804344609)
      ·
        refine ⟨431651859885992534103258457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 575535813181323378804344609 431651859885992534103258457)
        ·
          refine ⟨323738894914494400577443843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431651859885992534103258457 323738894914494400577443843)
          ·
            refine ⟨485608342371741600866165765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323738894914494400577443843 485608342371741600866165765)
            ·
              refine ⟨91051564194701550162406081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 485608342371741600866165765 91051564194701550162406081)
              ·
                refine ⟨68288673146026162621804561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91051564194701550162406081 68288673146026162621804561)
                ·
                  refine ⟨51216504859519621966353421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68288673146026162621804561 51216504859519621966353421)
                  ·
                    refine ⟨19206189322319858237382533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51216504859519621966353421 19206189322319858237382533)
                    ·
                      refine ⟨3601160497934973419509225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19206189322319858237382533 3601160497934973419509225)
                      ·
                        rfl

theorem cell23_7013235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 4].length) (baseStart_7013235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013235 prefixEnd_7013235 := by exact prefixLift 7013235
  have htrace : WordTrace (prefixWord ++ tailWord_7013235) baseStart_7013235 baseEnd_7013235 := by
    simpa [prefixWord, tailWord_7013235, baseEnd_7013235] using wordTrace_append hprefix tailTrace_7013235
  have hstable : (prefixWord ++ tailWord_7013235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013235).length < 2 ^ (prefixWord ++ tailWord_7013235).sum := by decide
  have hdescent : baseEnd_7013235 < baseStart_7013235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013245 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 1, 8]
def baseStart_7013245 : Nat := 118140960795 + 7013245 * 2 ^ 59
def prefixEnd_7013245 : Nat := 4983230072969 + 3 ^ 40 * 7013245 * 2
def baseEnd_7013245 : Nat := 1200388544247172793461393

theorem tailTrace_7013245 : CollatzResearch.WordTrace tailWord_7013245 prefixEnd_7013245 1200388544247172793461393 := by
  unfold tailWord_7013245
  simp only [CollatzResearch.WordTrace]
  refine ⟨255794059477218606732017189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170529372984812404488011459 255794059477218606732017189)
  ·
    refine ⟨47961386151978488762253223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255794059477218606732017189 47961386151978488762253223)
    ·
      refine ⟨71942079227967733143379835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47961386151978488762253223 71942079227967733143379835)
      ·
        refine ⟨107913118841951599715069753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71942079227967733143379835 107913118841951599715069753)
        ·
          refine ⟨80934839131463699786302315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107913118841951599715069753 80934839131463699786302315)
          ·
            refine ⟨121402258697195549679453473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80934839131463699786302315 121402258697195549679453473)
            ·
              refine ⟨91051694022896662259590105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121402258697195549679453473 91051694022896662259590105)
              ·
                refine ⟨68288770517172496694692579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91051694022896662259590105 68288770517172496694692579)
                ·
                  refine ⟨102433155775758745042038869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68288770517172496694692579 102433155775758745042038869)
                  ·
                    refine ⟨1200388544247172793461393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102433155775758745042038869 1200388544247172793461393)
                    ·
                      rfl

theorem cell23_7013245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_7013245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013245 prefixEnd_7013245 := by exact prefixLift 7013245
  have htrace : WordTrace (prefixWord ++ tailWord_7013245) baseStart_7013245 baseEnd_7013245 := by
    simpa [prefixWord, tailWord_7013245, baseEnd_7013245] using wordTrace_append hprefix tailTrace_7013245
  have hstable : (prefixWord ++ tailWord_7013245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013245).length < 2 ^ (prefixWord ++ tailWord_7013245).sum := by decide
  have hdescent : baseEnd_7013245 < baseStart_7013245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013256 : List Nat := [2, 1, 3, 3, 2, 1, 2, 3, 1, 3, 2]
def baseStart_7013256 : Nat := 118140960795 + 7013256 * 2 ^ 59
def prefixEnd_7013256 : Nat := 4983230072969 + 3 ^ 40 * 7013256 * 2
def baseEnd_7013256 : Nat := 3601171281028717837346629

theorem tailTrace_7013256 : CollatzResearch.WordTrace tailWord_7013256 prefixEnd_7013256 3601171281028717837346629 := by
  unfold tailWord_7013256
  simp only [CollatzResearch.WordTrace]
  refine ⟨127897230340089377805333811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170529640453452503740445081 127897230340089377805333811)
  ·
    refine ⟨191845845510134066708000717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127897230340089377805333811 191845845510134066708000717)
    ·
      refine ⟨71942192066300275015500269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 191845845510134066708000717 71942192066300275015500269)
      ·
        refine ⟨26978322024862603130812601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71942192066300275015500269 26978322024862603130812601)
        ·
          refine ⟨20233741518646952348109451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26978322024862603130812601 20233741518646952348109451)
          ·
            refine ⟨30350612277970428522164177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20233741518646952348109451 30350612277970428522164177)
            ·
              refine ⟨22762959208477821391623133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30350612277970428522164177 22762959208477821391623133)
              ·
                refine ⟨8536109703179183021858675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22762959208477821391623133 8536109703179183021858675)
                ·
                  refine ⟨12804164554768774532788013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8536109703179183021858675 12804164554768774532788013)
                  ·
                    refine ⟨4801561708038290449795505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12804164554768774532788013 4801561708038290449795505)
                    ·
                      refine ⟨3601171281028717837346629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4801561708038290449795505 3601171281028717837346629)
                      ·
                        rfl

theorem cell23_7013256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_7013256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013256 prefixEnd_7013256 := by exact prefixLift 7013256
  have htrace : WordTrace (prefixWord ++ tailWord_7013256) baseStart_7013256 baseEnd_7013256 := by
    simpa [prefixWord, tailWord_7013256, baseEnd_7013256] using wordTrace_append hprefix tailTrace_7013256
  have hstable : (prefixWord ++ tailWord_7013256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013256).length < 2 ^ (prefixWord ++ tailWord_7013256).sum := by decide
  have hdescent : baseEnd_7013256 < baseStart_7013256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013315 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 7]
def baseStart_7013315 : Nat := 118140960795 + 7013315 * 2 ^ 59
def prefixEnd_7013315 : Nat := 4983230072969 + 3 ^ 40 * 7013315 * 2
def baseEnd_7013315 : Nat := 3601201576387333106508857

theorem tailTrace_7013315 : CollatzResearch.WordTrace tailWord_7013315 prefixEnd_7013315 3601201576387333106508857 := by
  unfold tailWord_7013315
  simp only [CollatzResearch.WordTrace]
  refine ⟨255796612586965008687065399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170531075057976672458043599 255796612586965008687065399)
  ·
    refine ⟨383694918880447513030598099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255796612586965008687065399 383694918880447513030598099)
    ·
      refine ⟨575542378320671269545897149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383694918880447513030598099 575542378320671269545897149)
      ·
        refine ⟨215828391870251726079711431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 575542378320671269545897149 215828391870251726079711431)
        ·
          refine ⟨323742587805377589119567147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215828391870251726079711431 323742587805377589119567147)
          ·
            refine ⟨485613881708066383679350721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323742587805377589119567147 485613881708066383679350721)
            ·
              refine ⟨364210411281049787759513041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 485613881708066383679350721 364210411281049787759513041)
              ·
                refine ⟨273157808460787340819634781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 364210411281049787759513041 273157808460787340819634781)
                ·
                  refine ⟨102434178172795252807363043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 273157808460787340819634781 102434178172795252807363043)
                  ·
                    refine ⟨153651267259192879211044565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102434178172795252807363043 153651267259192879211044565)
                    ·
                      refine ⟨3601201576387333106508857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 153651267259192879211044565 3601201576387333106508857)
                      ·
                        rfl

theorem cell23_7013315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_7013315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013315 prefixEnd_7013315 := by exact prefixLift 7013315
  have htrace : WordTrace (prefixWord ++ tailWord_7013315) baseStart_7013315 baseEnd_7013315 := by
    simpa [prefixWord, tailWord_7013315, baseEnd_7013315] using wordTrace_append hprefix tailTrace_7013315
  have hstable : (prefixWord ++ tailWord_7013315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013315).length < 2 ^ (prefixWord ++ tailWord_7013315).sum := by decide
  have hdescent : baseEnd_7013315 < baseStart_7013315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013326 : List Nat := [4, 1, 1, 1, 2, 3, 4, 2, 5]
def baseStart_7013326 : Nat := 118140960795 + 7013326 * 2 ^ 59
def prefixEnd_7013326 : Nat := 4983230072969 + 3 ^ 40 * 7013326 * 2
def baseEnd_7013326 : Nat := 400134136074948062607923

theorem tailTrace_7013326 : CollatzResearch.WordTrace tailWord_7013326 prefixEnd_7013326 400134136074948062607923 := by
  unfold tailWord_7013326
  simp only [CollatzResearch.WordTrace]
  refine ⟨31974626723740644695714479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170531342526616771710477221 31974626723740644695714479)
  ·
    refine ⟨47961940085610967043571719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31974626723740644695714479 47961940085610967043571719)
    ·
      refine ⟨71942910128416450565357579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47961940085610967043571719 71942910128416450565357579)
      ·
        refine ⟨107914365192624675848036369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71942910128416450565357579 107914365192624675848036369)
        ·
          refine ⟨80935773894468506886027277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107914365192624675848036369 80935773894468506886027277)
          ·
            refine ⟨30350915210425690082260229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80935773894468506886027277 30350915210425690082260229)
            ·
              refine ⟨5690796601954816890423793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30350915210425690082260229 5690796601954816890423793)
              ·
                refine ⟨4268097451466112667817845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5690796601954816890423793 4268097451466112667817845)
                ·
                  refine ⟨400134136074948062607923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4268097451466112667817845 400134136074948062607923)
                  ·
                    rfl

theorem cell23_7013326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2, 5].length) (baseStart_7013326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013326 prefixEnd_7013326 := by exact prefixLift 7013326
  have htrace : WordTrace (prefixWord ++ tailWord_7013326) baseStart_7013326 baseEnd_7013326 := by
    simpa [prefixWord, tailWord_7013326, baseEnd_7013326] using wordTrace_append hprefix tailTrace_7013326
  have hstable : (prefixWord ++ tailWord_7013326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013326).length < 2 ^ (prefixWord ++ tailWord_7013326).sum := by decide
  have hdescent : baseEnd_7013326 < baseStart_7013326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013359 : List Nat := [1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 4]
def baseStart_7013359 : Nat := 118140960795 + 7013359 * 2 ^ 59
def prefixEnd_7013359 : Nat := 4983230072969 + 3 ^ 40 * 7013359 * 2
def baseEnd_7013359 : Nat := 3601224169536130934358655

theorem tailTrace_7013359 : CollatzResearch.WordTrace tailWord_7013359 prefixEnd_7013359 3601224169536130934358655 := by
  unfold tailWord_7013359
  simp only [CollatzResearch.WordTrace]
  refine ⟨255798217398805604201667131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170532144932537069467778087 255798217398805604201667131)
  ·
    refine ⟨383697326098208406302500697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255798217398805604201667131 383697326098208406302500697)
    ·
      refine ⟨287772994573656304726875523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383697326098208406302500697 287772994573656304726875523)
      ·
        refine ⟨431659491860484457090313285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287772994573656304726875523 431659491860484457090313285)
        ·
          refine ⟨80936154723840835704433741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 431659491860484457090313285 80936154723840835704433741)
          ·
            refine ⟨30351058021440313389162653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80936154723840835704433741 30351058021440313389162653)
            ·
              refine ⟨11381646758040117520935995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30351058021440313389162653 11381646758040117520935995)
              ·
                refine ⟨17072470137060176281403993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11381646758040117520935995 17072470137060176281403993)
                ·
                  refine ⟨12804352602795132211052995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17072470137060176281403993 12804352602795132211052995)
                  ·
                    refine ⟨19206528904192698316579493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12804352602795132211052995 19206528904192698316579493)
                    ·
                      refine ⟨3601224169536130934358655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19206528904192698316579493 3601224169536130934358655)
                      ·
                        rfl

theorem cell23_7013359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 4].length) (baseStart_7013359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013359 prefixEnd_7013359 := by exact prefixLift 7013359
  have htrace : WordTrace (prefixWord ++ tailWord_7013359) baseStart_7013359 baseEnd_7013359 := by
    simpa [prefixWord, tailWord_7013359, baseEnd_7013359] using wordTrace_append hprefix tailTrace_7013359
  have hstable : (prefixWord ++ tailWord_7013359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013359).length < 2 ^ (prefixWord ++ tailWord_7013359).sum := by decide
  have hdescent : baseEnd_7013359 < baseStart_7013359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013372 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 2, 1, 6]
def baseStart_7013372 : Nat := 118140960795 + 7013372 * 2 ^ 59
def prefixEnd_7013372 : Nat := 4983230072969 + 3 ^ 40 * 7013372 * 2
def baseEnd_7013372 : Nat := 3601230844784639383496095

theorem tailTrace_7013372 : CollatzResearch.WordTrace tailWord_7013372 prefixEnd_7013372 3601230844784639383496095 := by
  unfold tailWord_7013372
  simp only [CollatzResearch.WordTrace]
  refine ⟨127899345773879253710945185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170532461031839004947926913 127899345773879253710945185)
  ·
    refine ⟨95924509330409440283208889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127899345773879253710945185 95924509330409440283208889)
    ·
      refine ⟨71943381997807080212406667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95924509330409440283208889 71943381997807080212406667)
      ·
        refine ⟨107915072996710620318610001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71943381997807080212406667 107915072996710620318610001)
        ·
          refine ⟨80936304747532965238957501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107915072996710620318610001 80936304747532965238957501)
          ·
            refine ⟨30351114280324861964609063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80936304747532965238957501 30351114280324861964609063)
            ·
              refine ⟨45526671420487292946913595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30351114280324861964609063 45526671420487292946913595)
              ·
                refine ⟨68290007130730939420370393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45526671420487292946913595 68290007130730939420370393)
                ·
                  refine ⟨51217505348048204565277795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68290007130730939420370393 51217505348048204565277795)
                  ·
                    refine ⟨76826258022072306847916693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51217505348048204565277795 76826258022072306847916693)
                    ·
                      refine ⟨3601230844784639383496095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76826258022072306847916693 3601230844784639383496095)
                      ·
                        rfl

theorem cell23_7013372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_7013372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013372 prefixEnd_7013372 := by exact prefixLift 7013372
  have htrace : WordTrace (prefixWord ++ tailWord_7013372) baseStart_7013372 baseEnd_7013372 := by
    simpa [prefixWord, tailWord_7013372, baseEnd_7013372] using wordTrace_append hprefix tailTrace_7013372
  have hstable : (prefixWord ++ tailWord_7013372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013372).length < 2 ^ (prefixWord ++ tailWord_7013372).sum := by decide
  have hdescent : baseEnd_7013372 < baseStart_7013372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013386 : List Nat := [3, 1, 2, 2, 3, 2, 2, 1, 3, 4]
def baseStart_7013386 : Nat := 118140960795 + 7013386 * 2 ^ 59
def prefixEnd_7013386 : Nat := 4983230072969 + 3 ^ 40 * 7013386 * 2
def baseEnd_7013386 : Nat := 1200412677837934109573677

theorem tailTrace_7013386 : CollatzResearch.WordTrace tailWord_7013386 prefixEnd_7013386 1200412677837934109573677 := by
  unfold tailWord_7013386
  simp only [CollatzResearch.WordTrace]
  refine ⟨63949800542426946953225003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170532801446471858541933341 63949800542426946953225003)
  ·
    refine ⟨95924700813640420429837505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63949800542426946953225003 95924700813640420429837505)
    ·
      refine ⟨71943525610230315322378129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95924700813640420429837505 71943525610230315322378129)
      ·
        refine ⟨53957644207672736491783597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71943525610230315322378129 53957644207672736491783597)
        ·
          refine ⟨20234116577877276184418849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53957644207672736491783597 20234116577877276184418849)
          ·
            refine ⟨15175587433407957138314137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20234116577877276184418849 15175587433407957138314137)
            ·
              refine ⟨11381690575055967853735603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15175587433407957138314137 11381690575055967853735603)
              ·
                refine ⟨17072535862583951780603405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11381690575055967853735603 17072535862583951780603405)
                ·
                  refine ⟨6402200948468981917726277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17072535862583951780603405 6402200948468981917726277)
                  ·
                    refine ⟨1200412677837934109573677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6402200948468981917726277 1200412677837934109573677)
                    ·
                      rfl

theorem cell23_7013386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_7013386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013386 prefixEnd_7013386 := by exact prefixLift 7013386
  have htrace : WordTrace (prefixWord ++ tailWord_7013386) baseStart_7013386 baseEnd_7013386 := by
    simpa [prefixWord, tailWord_7013386, baseEnd_7013386] using wordTrace_append hprefix tailTrace_7013386
  have hstable : (prefixWord ++ tailWord_7013386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013386).length < 2 ^ (prefixWord ++ tailWord_7013386).sum := by decide
  have hdescent : baseEnd_7013386 < baseStart_7013386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013392 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 3]
def baseStart_7013392 : Nat := 118140960795 + 7013392 * 2 ^ 59
def prefixEnd_7013392 : Nat := 4983230072969 + 3 ^ 40 * 7013392 * 2
def baseEnd_7013392 : Nat := 3601241114397729305246003

theorem tailTrace_7013392 : CollatzResearch.WordTrace tailWord_7013392 prefixEnd_7013392 3601241114397729305246003 := by
  unfold tailWord_7013392
  simp only [CollatzResearch.WordTrace]
  refine ⟨127899710503843025418809215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170532947338457367225078953 127899710503843025418809215)
  ·
    refine ⟨191849565755764538128213823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127899710503843025418809215 191849565755764538128213823)
    ·
      refine ⟨287774348633646807192320735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191849565755764538128213823 287774348633646807192320735)
      ·
        refine ⟨431661522950470210788481103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287774348633646807192320735 431661522950470210788481103)
        ·
          refine ⟨647492284425705316182721655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431661522950470210788481103 647492284425705316182721655)
          ·
            refine ⟨971238426638557974274082483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647492284425705316182721655 971238426638557974274082483)
            ·
              refine ⟨1456857639957836961411123725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 971238426638557974274082483 1456857639957836961411123725)
              ·
                refine ⟨546321614984188860529171397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1456857639957836961411123725 546321614984188860529171397)
                ·
                  refine ⟨102435302809535411349219637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 546321614984188860529171397 102435302809535411349219637)
                  ·
                    refine ⟨9603309638393944813989341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 102435302809535411349219637 9603309638393944813989341)
                    ·
                      refine ⟨3601241114397729305246003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9603309638393944813989341 3601241114397729305246003)
                      ·
                        rfl

theorem cell23_7013392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 3].length) (baseStart_7013392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013392 prefixEnd_7013392 := by exact prefixLift 7013392
  have htrace : WordTrace (prefixWord ++ tailWord_7013392) baseStart_7013392 baseEnd_7013392 := by
    simpa [prefixWord, tailWord_7013392, baseEnd_7013392] using wordTrace_append hprefix tailTrace_7013392
  have hstable : (prefixWord ++ tailWord_7013392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013392).length < 2 ^ (prefixWord ++ tailWord_7013392).sum := by decide
  have hdescent : baseEnd_7013392 < baseStart_7013392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013402 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6]
def baseStart_7013402 : Nat := 118140960795 + 7013402 * 2 ^ 59
def prefixEnd_7013402 : Nat := 4983230072969 + 3 ^ 40 * 7013402 * 2
def baseEnd_7013402 : Nat := 3601246249204274266120957

theorem tailTrace_7013402 : CollatzResearch.WordTrace tailWord_7013402 prefixEnd_7013402 3601246249204274266120957 := by
  unfold tailWord_7013402
  simp only [CollatzResearch.WordTrace]
  refine ⟨63949946434412455636370615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170533190491766548363654973 63949946434412455636370615)
  ·
    refine ⟨95924919651618683454555923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63949946434412455636370615 95924919651618683454555923)
    ·
      refine ⟨143887379477428025181833885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95924919651618683454555923 143887379477428025181833885)
      ·
        refine ⟨53957767304035509443187707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143887379477428025181833885 53957767304035509443187707)
        ·
          refine ⟨80936650956053264164781561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53957767304035509443187707 80936650956053264164781561)
          ·
            refine ⟨60702488217039948123586171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80936650956053264164781561 60702488217039948123586171)
            ·
              refine ⟨91053732325559922185379257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60702488217039948123586171 91053732325559922185379257)
              ·
                refine ⟨68290299244169941639034443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91053732325559922185379257 68290299244169941639034443)
                ·
                  refine ⟨102435448866254912458551665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68290299244169941639034443 102435448866254912458551665)
                  ·
                    refine ⟨76826586649691184343913749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 102435448866254912458551665 76826586649691184343913749)
                    ·
                      refine ⟨3601246249204274266120957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76826586649691184343913749 3601246249204274266120957)
                      ·
                        rfl

theorem cell23_7013402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_7013402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013402 prefixEnd_7013402 := by exact prefixLift 7013402
  have htrace : WordTrace (prefixWord ++ tailWord_7013402) baseStart_7013402 baseEnd_7013402 := by
    simpa [prefixWord, tailWord_7013402, baseEnd_7013402] using wordTrace_append hprefix tailTrace_7013402
  have hstable : (prefixWord ++ tailWord_7013402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013402).length < 2 ^ (prefixWord ++ tailWord_7013402).sum := by decide
  have hdescent : baseEnd_7013402 < baseStart_7013402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013419 : List Nat := [1, 1, 1, 1, 2, 1, 5, 3, 1, 5, 2]
def baseStart_7013419 : Nat := 118140960795 + 7013419 * 2 ^ 59
def prefixEnd_7013419 : Nat := 4983230072969 + 3 ^ 40 * 7013419 * 2
def baseEnd_7013419 : Nat := 3601254978375400699608379

theorem tailTrace_7013419 : CollatzResearch.WordTrace tailWord_7013419 prefixEnd_7013419 3601254978375400699608379 := by
  unfold tailWord_7013419
  simp only [CollatzResearch.WordTrace]
  refine ⟨255800405778588234448851311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170533603852392156299234207 255800405778588234448851311)
  ·
    refine ⟨383700608667882351673276967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255800405778588234448851311 383700608667882351673276967)
    ·
      refine ⟨575550913001823527509915451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383700608667882351673276967 575550913001823527509915451)
      ·
        refine ⟨863326369502735291264873177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575550913001823527509915451 863326369502735291264873177)
        ·
          refine ⟨647494777127051468448654883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 863326369502735291264873177 647494777127051468448654883)
          ·
            refine ⟨971242165690577202672982325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647494777127051468448654883 971242165690577202672982325)
            ·
              refine ⟨91053953033491612750592093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 971242165690577202672982325 91053953033491612750592093)
              ·
                refine ⟨34145232387559354781472035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91053953033491612750592093 34145232387559354781472035)
                ·
                  refine ⟨51217848581339032172208053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34145232387559354781472035 51217848581339032172208053)
                  ·
                    refine ⟨4801673304500534266144505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51217848581339032172208053 4801673304500534266144505)
                    ·
                      refine ⟨3601254978375400699608379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4801673304500534266144505 3601254978375400699608379)
                      ·
                        rfl

theorem cell23_7013419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 5, 2].length) (baseStart_7013419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013419 prefixEnd_7013419 := by exact prefixLift 7013419
  have htrace : WordTrace (prefixWord ++ tailWord_7013419) baseStart_7013419 baseEnd_7013419 := by
    simpa [prefixWord, tailWord_7013419, baseEnd_7013419] using wordTrace_append hprefix tailTrace_7013419
  have hstable : (prefixWord ++ tailWord_7013419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013419).length < 2 ^ (prefixWord ++ tailWord_7013419).sum := by decide
  have hdescent : baseEnd_7013419 < baseStart_7013419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013436 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 4, 3, 2]
def baseStart_7013436 : Nat := 118140960795 + 7013436 * 2 ^ 59
def prefixEnd_7013436 : Nat := 4983230072969 + 3 ^ 40 * 7013436 * 2
def baseEnd_7013436 : Nat := 3601263707546527133095801

theorem tailTrace_7013436 : CollatzResearch.WordTrace tailWord_7013436 prefixEnd_7013436 3601263707546527133095801 := by
  unfold tailWord_7013436
  simp only [CollatzResearch.WordTrace]
  refine ⟨127900512909763323176110081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170534017213017764234813441 127900512909763323176110081)
  ·
    refine ⟨95925384682322492382082561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127900512909763323176110081 95925384682322492382082561)
    ·
      refine ⟨71944038511741869286561921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95925384682322492382082561 71944038511741869286561921)
      ·
        refine ⟨53958028883806401964921441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71944038511741869286561921 53958028883806401964921441)
        ·
          refine ⟨40468521662854801473691081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53958028883806401964921441 40468521662854801473691081)
          ·
            refine ⟨30351391247141101105268311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40468521662854801473691081 30351391247141101105268311)
            ·
              refine ⟨45527086870711651657902467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30351391247141101105268311 45527086870711651657902467)
              ·
                refine ⟨68290630306067477486853701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45527086870711651657902467 68290630306067477486853701)
                ·
                  refine ⟨12804493182387652028785069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68290630306067477486853701 12804493182387652028785069)
                  ·
                    refine ⟨4801684943395369510794401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12804493182387652028785069 4801684943395369510794401)
                    ·
                      refine ⟨3601263707546527133095801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4801684943395369510794401 3601263707546527133095801)
                      ·
                        rfl

theorem cell23_7013436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_7013436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013436 prefixEnd_7013436 := by exact prefixLift 7013436
  have htrace : WordTrace (prefixWord ++ tailWord_7013436) baseStart_7013436 baseEnd_7013436 := by
    simpa [prefixWord, tailWord_7013436, baseEnd_7013436] using wordTrace_append hprefix tailTrace_7013436
  have hstable : (prefixWord ++ tailWord_7013436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013436).length < 2 ^ (prefixWord ++ tailWord_7013436).sum := by decide
  have hdescent : baseEnd_7013436 < baseStart_7013436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013449 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 2, 6, 2]
def baseStart_7013449 : Nat := 118140960795 + 7013449 * 2 ^ 59
def prefixEnd_7013449 : Nat := 4983230072969 + 3 ^ 40 * 7013449 * 2
def baseEnd_7013449 : Nat := 3601270382795035582233241

theorem tailTrace_7013449 : CollatzResearch.WordTrace tailWord_7013449 prefixEnd_7013449 3601270382795035582233241 := by
  unfold tailWord_7013449
  simp only [CollatzResearch.WordTrace]
  refine ⟨255801499968479549572443401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170534333312319699714962267 255801499968479549572443401)
  ·
    refine ⟨191851124976359662179332551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255801499968479549572443401 191851124976359662179332551)
    ·
      refine ⟨287776687464539493268998827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191851124976359662179332551 287776687464539493268998827)
      ·
        refine ⟨431665031196809239903498241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287776687464539493268998827 431665031196809239903498241)
        ·
          refine ⟨323748773397606929927623681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431665031196809239903498241 323748773397606929927623681)
          ·
            refine ⟨242811580048205197445717761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323748773397606929927623681 242811580048205197445717761)
            ·
              refine ⟨182108685036153898084288321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242811580048205197445717761 182108685036153898084288321)
              ·
                refine ⟨136581513777115423563216241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182108685036153898084288321 136581513777115423563216241)
                ·
                  refine ⟨102436135332836567672412181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136581513777115423563216241 102436135332836567672412181)
                  ·
                    refine ⟨4801693843726714109644321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 102436135332836567672412181 4801693843726714109644321)
                    ·
                      refine ⟨3601270382795035582233241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4801693843726714109644321 3601270382795035582233241)
                      ·
                        rfl

theorem cell23_7013449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 6, 2].length) (baseStart_7013449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013449 prefixEnd_7013449 := by exact prefixLift 7013449
  have htrace : WordTrace (prefixWord ++ tailWord_7013449) baseStart_7013449 baseEnd_7013449 := by
    simpa [prefixWord, tailWord_7013449, baseEnd_7013449] using wordTrace_append hprefix tailTrace_7013449
  have hstable : (prefixWord ++ tailWord_7013449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013449).length < 2 ^ (prefixWord ++ tailWord_7013449).sum := by decide
  have hdescent : baseEnd_7013449 < baseStart_7013449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013472 : List Nat := [2, 1, 1, 3, 2, 2, 1, 11]
def baseStart_7013472 : Nat := 118140960795 + 7013472 * 2 ^ 59
def prefixEnd_7013472 : Nat := 4983230072969 + 3 ^ 40 * 7013472 * 2
def baseEnd_7013472 : Nat := 133380821957410703416505

theorem tailTrace_7013472 : CollatzResearch.WordTrace tailWord_7013472 prefixEnd_7013472 133380821957410703416505 := by
  unfold tailWord_7013472
  simp only [CollatzResearch.WordTrace]
  refine ⟨127901169423698112250265335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170534892564930816333687113 127901169423698112250265335)
  ·
    refine ⟨191851754135547168375398003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127901169423698112250265335 191851754135547168375398003)
    ·
      refine ⟨287777631203320752563097005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191851754135547168375398003 287777631203320752563097005)
      ·
        refine ⟨107916611701245282211161377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287777631203320752563097005 107916611701245282211161377)
        ·
          refine ⟨80937458775933961658371033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107916611701245282211161377 80937458775933961658371033)
          ·
            refine ⟨60703094081950471243778275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80937458775933961658371033 60703094081950471243778275)
            ·
              refine ⟨91054641122925706865667413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60703094081950471243778275 91054641122925706865667413)
              ·
                refine ⟨133380821957410703416505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 91054641122925706865667413 133380821957410703416505)
                ·
                  rfl

theorem cell23_7013472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 11].length) (baseStart_7013472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013472 prefixEnd_7013472 := by exact prefixLift 7013472
  have htrace : WordTrace (prefixWord ++ tailWord_7013472) baseStart_7013472 baseEnd_7013472 := by
    simpa [prefixWord, tailWord_7013472, baseEnd_7013472] using wordTrace_append hprefix tailTrace_7013472
  have hstable : (prefixWord ++ tailWord_7013472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013472).length < 2 ^ (prefixWord ++ tailWord_7013472).sum := by decide
  have hdescent : baseEnd_7013472 < baseStart_7013472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013479 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_7013479 : Nat := 118140960795 + 7013479 * 2 ^ 59
def prefixEnd_7013479 : Nat := 4983230072969 + 3 ^ 40 * 7013479 * 2
def baseEnd_7013479 : Nat := 3601285787214670464858103

theorem tailTrace_7013479 : CollatzResearch.WordTrace tailWord_7013479 prefixEnd_7013479 3601285787214670464858103 := by
  unfold tailWord_7013479
  simp only [CollatzResearch.WordTrace]
  refine ⟨255802594158370864696035491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170535062772247243130690327 255802594158370864696035491)
  ·
    refine ⟨383703891237556297044053237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255802594158370864696035491 383703891237556297044053237)
    ·
      refine ⟨35972239803520902847879991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 383703891237556297044053237 35972239803520902847879991)
      ·
        refine ⟨53958359705281354271819987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35972239803520902847879991 53958359705281354271819987)
        ·
          refine ⟨80937539557922031407729981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53958359705281354271819987 80937539557922031407729981)
          ·
            refine ⟨30351577334220761777898743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80937539557922031407729981 30351577334220761777898743)
            ·
              refine ⟨45527366001331142666848115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30351577334220761777898743 45527366001331142666848115)
              ·
                refine ⟨68291049001996714000272173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45527366001331142666848115 68291049001996714000272173)
                ·
                  refine ⟨25609143375748767750102065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68291049001996714000272173 25609143375748767750102065)
                  ·
                    refine ⟨19206857531811575812576549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25609143375748767750102065 19206857531811575812576549)
                    ·
                      refine ⟨3601285787214670464858103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19206857531811575812576549 3601285787214670464858103)
                      ·
                        rfl

theorem cell23_7013479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_7013479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013479 prefixEnd_7013479 := by exact prefixLift 7013479
  have htrace : WordTrace (prefixWord ++ tailWord_7013479) baseStart_7013479 baseEnd_7013479 := by
    simpa [prefixWord, tailWord_7013479, baseEnd_7013479] using wordTrace_append hprefix tailTrace_7013479
  have hstable : (prefixWord ++ tailWord_7013479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013479).length < 2 ^ (prefixWord ++ tailWord_7013479).sum := by decide
  have hdescent : baseEnd_7013479 < baseStart_7013479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013480 : List Nat := [2, 1, 4, 4, 1, 1, 3, 1, 1, 5]
def baseStart_7013480 : Nat := 118140960795 + 7013480 * 2 ^ 59
def prefixEnd_7013480 : Nat := 4983230072969 + 3 ^ 40 * 7013480 * 2
def baseEnd_7013480 : Nat := 1200428766898441653648533

theorem tailTrace_7013480 : CollatzResearch.WordTrace tailWord_7013480 prefixEnd_7013480 1200428766898441653648533 := by
  unfold tailWord_7013480
  simp only [CollatzResearch.WordTrace]
  refine ⟨127901315315683620933410947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170535087087578161244547929 127901315315683620933410947)
  ·
    refine ⟨191851972973525431400116421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127901315315683620933410947 191851972973525431400116421)
    ·
      refine ⟨35972244932536018387521829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 191851972973525431400116421 35972244932536018387521829)
      ·
        refine ⟨6744795924850503447660343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35972244932536018387521829 6744795924850503447660343)
        ·
          refine ⟨10117193887275755171490515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6744795924850503447660343 10117193887275755171490515)
          ·
            refine ⟨15175790830913632757235773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10117193887275755171490515 15175790830913632757235773)
            ·
              refine ⟨5690921561592612283963415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15175790830913632757235773 5690921561592612283963415)
              ·
                refine ⟨8536382342388918425945123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5690921561592612283963415 8536382342388918425945123)
                ·
                  refine ⟨12804573513583377638917685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8536382342388918425945123 12804573513583377638917685)
                  ·
                    refine ⟨1200428766898441653648533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12804573513583377638917685 1200428766898441653648533)
                    ·
                      rfl

theorem cell23_7013480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_7013480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013480 prefixEnd_7013480 := by exact prefixLift 7013480
  have htrace : WordTrace (prefixWord ++ tailWord_7013480) baseStart_7013480 baseEnd_7013480 := by
    simpa [prefixWord, tailWord_7013480, baseEnd_7013480] using wordTrace_append hprefix tailTrace_7013480
  have hstable : (prefixWord ++ tailWord_7013480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013480).length < 2 ^ (prefixWord ++ tailWord_7013480).sum := by decide
  have hdescent : baseEnd_7013480 < baseStart_7013480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013486 : List Nat := [4, 1, 2, 2, 1, 2, 3, 1, 1, 1, 5]
def baseStart_7013486 : Nat := 118140960795 + 7013486 * 2 ^ 59
def prefixEnd_7013486 : Nat := 4983230072969 + 3 ^ 40 * 7013486 * 2
def baseEnd_7013486 : Nat := 3601289381579251937470571

theorem tailTrace_7013486 : CollatzResearch.WordTrace tailWord_7013486 prefixEnd_7013486 3601289381579251937470571 := by
  unfold tailWord_7013486
  simp only [CollatzResearch.WordTrace]
  refine ⟨31975356183668188111442539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170535232979563669927693541 31975356183668188111442539)
  ·
    refine ⟨47963034275502282167163809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31975356183668188111442539 47963034275502282167163809)
    ·
      refine ⟨35972275706626711625372857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47963034275502282167163809 35972275706626711625372857)
      ·
        refine ⟨26979206779970033719029643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35972275706626711625372857 26979206779970033719029643)
        ·
          refine ⟨40468810169955050578544465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26979206779970033719029643 40468810169955050578544465)
          ·
            refine ⟨30351607627466287933908349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40468810169955050578544465 30351607627466287933908349)
            ·
              refine ⟨11381852860299857975215631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30351607627466287933908349 11381852860299857975215631)
              ·
                refine ⟨17072779290449786962823447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11381852860299857975215631 17072779290449786962823447)
                ·
                  refine ⟨25609168935674680444235171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17072779290449786962823447 25609168935674680444235171)
                  ·
                    refine ⟨38413753403512020666352757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25609168935674680444235171 38413753403512020666352757)
                    ·
                      refine ⟨3601289381579251937470571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38413753403512020666352757 3601289381579251937470571)
                      ·
                        rfl

theorem cell23_7013486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_7013486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013486 prefixEnd_7013486 := by exact prefixLift 7013486
  have htrace : WordTrace (prefixWord ++ tailWord_7013486) baseStart_7013486 baseEnd_7013486 := by
    simpa [prefixWord, tailWord_7013486, baseEnd_7013486] using wordTrace_append hprefix tailTrace_7013486
  have hstable : (prefixWord ++ tailWord_7013486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013486).length < 2 ^ (prefixWord ++ tailWord_7013486).sum := by decide
  have hdescent : baseEnd_7013486 < baseStart_7013486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013500 : List Nat := [2, 2, 2, 1, 1, 3, 3, 4, 1, 2, 2]
def baseStart_7013500 : Nat := 118140960795 + 7013500 * 2 ^ 59
def prefixEnd_7013500 : Nat := 4983230072969 + 3 ^ 40 * 7013500 * 2
def baseEnd_7013500 : Nat := 3601296570308414882695507

theorem tailTrace_7013500 : CollatzResearch.WordTrace tailWord_7013500 prefixEnd_7013500 3601296570308414882695507 := by
  unfold tailWord_7013500
  simp only [CollatzResearch.WordTrace]
  refine ⟨127901680045647392641274977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170535573394196523521699969 127901680045647392641274977)
  ·
    refine ⟨95926260034235544480956233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127901680045647392641274977 95926260034235544480956233)
    ·
      refine ⟨71944695025676658360717175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95926260034235544480956233 71944695025676658360717175)
      ·
        refine ⟨107917042538514987541075763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71944695025676658360717175 107917042538514987541075763)
        ·
          refine ⟨161875563807772481311613645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107917042538514987541075763 161875563807772481311613645)
          ·
            refine ⟨60703336427914680491855117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161875563807772481311613645 60703336427914680491855117)
            ·
              refine ⟨22763751160468005184445669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60703336427914680491855117 22763751160468005184445669)
              ·
                refine ⟨4268203342587750972083563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22763751160468005184445669 4268203342587750972083563)
                ·
                  refine ⟨6402305013881626458125345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4268203342587750972083563 6402305013881626458125345)
                  ·
                    refine ⟨4801728760411219843594009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6402305013881626458125345 4801728760411219843594009)
                    ·
                      refine ⟨3601296570308414882695507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4801728760411219843594009 3601296570308414882695507)
                      ·
                        rfl

theorem cell23_7013500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4, 1, 2, 2].length) (baseStart_7013500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013500 prefixEnd_7013500 := by exact prefixLift 7013500
  have htrace : WordTrace (prefixWord ++ tailWord_7013500) baseStart_7013500 baseEnd_7013500 := by
    simpa [prefixWord, tailWord_7013500, baseEnd_7013500] using wordTrace_append hprefix tailTrace_7013500
  have hstable : (prefixWord ++ tailWord_7013500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013500).length < 2 ^ (prefixWord ++ tailWord_7013500).sum := by decide
  have hdescent : baseEnd_7013500 < baseStart_7013500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013534 : List Nat := [4, 3, 1, 1, 2, 2, 2, 3, 1, 2, 2]
def baseStart_7013534 : Nat := 118140960795 + 7013534 * 2 ^ 59
def prefixEnd_7013534 : Nat := 4983230072969 + 3 ^ 40 * 7013534 * 2
def baseEnd_7013534 : Nat := 3601314028650667749670351

theorem tailTrace_7013534 : CollatzResearch.WordTrace tailWord_7013534 prefixEnd_7013534 3601314028650667749670351 := by
  unfold tailWord_7013534
  simp only [CollatzResearch.WordTrace]
  refine ⟨31975575021646451136160957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170536400115447739392858437 31975575021646451136160957)
  ·
    refine ⟨11990840633117419176060359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31975575021646451136160957 11990840633117419176060359)
    ·
      refine ⟨17986260949676128764090539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11990840633117419176060359 17986260949676128764090539)
      ·
        refine ⟨26979391424514193146135809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17986260949676128764090539 26979391424514193146135809)
        ·
          refine ⟨20234543568385644859601857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26979391424514193146135809 20234543568385644859601857)
          ·
            refine ⟨15175907676289233644701393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20234543568385644859601857 15175907676289233644701393)
            ·
              refine ⟨11381930757216925233526045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15175907676289233644701393 11381930757216925233526045)
              ·
                refine ⟨4268224033956346962572267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11381930757216925233526045 4268224033956346962572267)
                ·
                  refine ⟨6402336050934520443858401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4268224033956346962572267 6402336050934520443858401)
                  ·
                    refine ⟨4801752038200890332893801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6402336050934520443858401 4801752038200890332893801)
                    ·
                      refine ⟨3601314028650667749670351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4801752038200890332893801 3601314028650667749670351)
                      ·
                        rfl

theorem cell23_7013534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_7013534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013534 prefixEnd_7013534 := by exact prefixLift 7013534
  have htrace : WordTrace (prefixWord ++ tailWord_7013534) baseStart_7013534 baseEnd_7013534 := by
    simpa [prefixWord, tailWord_7013534, baseEnd_7013534] using wordTrace_append hprefix tailTrace_7013534
  have hstable : (prefixWord ++ tailWord_7013534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013534).length < 2 ^ (prefixWord ++ tailWord_7013534).sum := by decide
  have hdescent : baseEnd_7013534 < baseStart_7013534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013566 : List Nat := [4, 2, 1, 1, 3, 1, 2, 1, 2, 6]
def baseStart_7013566 : Nat := 118140960795 + 7013566 * 2 ^ 59
def prefixEnd_7013566 : Nat := 4983230072969 + 3 ^ 40 * 7013566 * 2
def baseEnd_7013566 : Nat := 1200443486677203874823401

theorem tailTrace_7013566 : CollatzResearch.WordTrace tailWord_7013566 prefixEnd_7013566 1200443486677203874823401 := by
  unfold tailWord_7013566
  simp only [CollatzResearch.WordTrace]
  refine ⟨31975720913631959819306569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170537178206037119036301701 31975720913631959819306569)
  ·
    refine ⟨23981790685223969864479927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31975720913631959819306569 23981790685223969864479927)
    ·
      refine ⟨35972686027835954796719891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23981790685223969864479927 35972686027835954796719891)
      ·
        refine ⟨53959029041753932195079837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35972686027835954796719891 53959029041753932195079837)
        ·
          refine ⟨20234635890657724573154939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53959029041753932195079837 20234635890657724573154939)
          ·
            refine ⟨30351953835986586859732409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20234635890657724573154939 30351953835986586859732409)
            ·
              refine ⟨22763965376989940144799307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30351953835986586859732409 22763965376989940144799307)
              ·
                refine ⟨34145948065484910217198961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22763965376989940144799307 34145948065484910217198961)
                ·
                  refine ⟨25609461049113682662899221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34145948065484910217198961 25609461049113682662899221)
                  ·
                    refine ⟨1200443486677203874823401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25609461049113682662899221 1200443486677203874823401)
                    ·
                      rfl

theorem cell23_7013566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_7013566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013566 prefixEnd_7013566 := by exact prefixLift 7013566
  have htrace : WordTrace (prefixWord ++ tailWord_7013566) baseStart_7013566 baseEnd_7013566 := by
    simpa [prefixWord, tailWord_7013566, baseEnd_7013566] using wordTrace_append hprefix tailTrace_7013566
  have hstable : (prefixWord ++ tailWord_7013566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013566).length < 2 ^ (prefixWord ++ tailWord_7013566).sum := by decide
  have hdescent : baseEnd_7013566 < baseStart_7013566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013574 : List Nat := [6, 1, 2, 2, 2, 1, 2, 7]
def baseStart_7013574 : Nat := 118140960795 + 7013574 * 2 ^ 59
def prefixEnd_7013574 : Nat := 4983230072969 + 3 ^ 40 * 7013574 * 2
def baseEnd_7013574 : Nat := 133382761773216577524821

theorem tailTrace_7013574 : CollatzResearch.WordTrace tailWord_7013574 prefixEnd_7013574 133382761773216577524821 := by
  unfold tailWord_7013574
  simp only [CollatzResearch.WordTrace]
  refine ⟨7993939346657084247523243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 170537372728684463947162517 7993939346657084247523243)
  ·
    refine ⟨11990909019985626371284865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7993939346657084247523243 11990909019985626371284865)
    ·
      refine ⟨8993181764989219778463649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11990909019985626371284865 8993181764989219778463649)
      ·
        refine ⟨6744886323741914833847737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8993181764989219778463649 6744886323741914833847737)
        ·
          refine ⟨5058664742806436125385803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6744886323741914833847737 5058664742806436125385803)
          ·
            refine ⟨7587997114209654188078705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5058664742806436125385803 7587997114209654188078705)
            ·
              refine ⟨5690997835657240641059029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7587997114209654188078705 5690997835657240641059029)
              ·
                refine ⟨133382761773216577524821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5690997835657240641059029 133382761773216577524821)
                ·
                  rfl

theorem cell23_7013574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_7013574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013574 prefixEnd_7013574 := by exact prefixLift 7013574
  have htrace : WordTrace (prefixWord ++ tailWord_7013574) baseStart_7013574 baseEnd_7013574 := by
    simpa [prefixWord, tailWord_7013574, baseEnd_7013574] using wordTrace_append hprefix tailTrace_7013574
  have hstable : (prefixWord ++ tailWord_7013574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013574).length < 2 ^ (prefixWord ++ tailWord_7013574).sum := by decide
  have hdescent : baseEnd_7013574 < baseStart_7013574 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013613 : List Nat := [1, 5, 1, 2, 2, 3, 1, 1, 7]
def baseStart_7013613 : Nat := 118140960795 + 7013613 * 2 ^ 59
def prefixEnd_7013613 : Nat := 4983230072969 + 3 ^ 40 * 7013613 * 2
def baseEnd_7013613 : Nat := 400150510402485882286943

theorem tailTrace_7013613 : CollatzResearch.WordTrace tailWord_7013613 prefixEnd_7013613 400150510402485882286943 := by
  unfold tailWord_7013613
  simp only [CollatzResearch.WordTrace]
  refine ⟨255807481539885405581413493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170538321026590270387608995 255807481539885405581413493)
  ·
    refine ⟨23981951394364256773257515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 255807481539885405581413493 23981951394364256773257515)
    ·
      refine ⟨35972927091546385159886273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23981951394364256773257515 35972927091546385159886273)
      ·
        refine ⟨26979695318659788869914705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35972927091546385159886273 26979695318659788869914705)
        ·
          refine ⟨20234771488994841652436029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26979695318659788869914705 20234771488994841652436029)
          ·
            refine ⟨7588039308373065619663511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20234771488994841652436029 7588039308373065619663511)
            ·
              refine ⟨11382058962559598429495267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7588039308373065619663511 11382058962559598429495267)
              ·
                refine ⟨17073088443839397644242901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11382058962559598429495267 17073088443839397644242901)
                ·
                  refine ⟨400150510402485882286943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17073088443839397644242901 400150510402485882286943)
                  ·
                    rfl

theorem cell23_7013613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_7013613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013613 prefixEnd_7013613 := by exact prefixLift 7013613
  have htrace : WordTrace (prefixWord ++ tailWord_7013613) baseStart_7013613 baseEnd_7013613 := by
    simpa [prefixWord, tailWord_7013613, baseEnd_7013613] using wordTrace_append hprefix tailTrace_7013613
  have hstable : (prefixWord ++ tailWord_7013613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013613).length < 2 ^ (prefixWord ++ tailWord_7013613).sum := by decide
  have hdescent : baseEnd_7013613 < baseStart_7013613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013619 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 7]
def baseStart_7013619 : Nat := 118140960795 + 7013619 * 2 ^ 59
def prefixEnd_7013619 : Nat := 4983230072969 + 3 ^ 40 * 7013619 * 2
def baseEnd_7013619 : Nat := 3601357674506299917107459

theorem tailTrace_7013619 : CollatzResearch.WordTrace tailWord_7013619 prefixEnd_7013619 3601357674506299917107459 := by
  unfold tailWord_7013619
  simp only [CollatzResearch.WordTrace]
  refine ⟨255807700377863668606131911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170538466918575779070754607 255807700377863668606131911)
  ·
    refine ⟨383711550566795502909197867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255807700377863668606131911 383711550566795502909197867)
    ·
      refine ⟨575567325850193254363796801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383711550566795502909197867 575567325850193254363796801)
      ·
        refine ⟨431675494387644940772847601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 575567325850193254363796801 431675494387644940772847601)
        ·
          refine ⟨323756620790733705579635701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431675494387644940772847601 323756620790733705579635701)
          ·
            refine ⟨30352183199131284898090847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 323756620790733705579635701 30352183199131284898090847)
            ·
              refine ⟨45528274798696927347136271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30352183199131284898090847 45528274798696927347136271)
              ·
                refine ⟨68292412198045391020704407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45528274798696927347136271 68292412198045391020704407)
                ·
                  refine ⟨102438618297068086531056611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68292412198045391020704407 102438618297068086531056611)
                  ·
                    refine ⟨153657927445602129796584917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 102438618297068086531056611 153657927445602129796584917)
                    ·
                      refine ⟨3601357674506299917107459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 153657927445602129796584917 3601357674506299917107459)
                      ·
                        rfl

theorem cell23_7013619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 7].length) (baseStart_7013619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013619 prefixEnd_7013619 := by exact prefixLift 7013619
  have htrace : WordTrace (prefixWord ++ tailWord_7013619) baseStart_7013619 baseEnd_7013619 := by
    simpa [prefixWord, tailWord_7013619, baseEnd_7013619] using wordTrace_append hprefix tailTrace_7013619
  have hstable : (prefixWord ++ tailWord_7013619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013619).length < 2 ^ (prefixWord ++ tailWord_7013619).sum := by decide
  have hdescent : baseEnd_7013619 < baseStart_7013619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013659 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 6]
def baseStart_7013659 : Nat := 118140960795 + 7013659 * 2 ^ 59
def prefixEnd_7013659 : Nat := 4983230072969 + 3 ^ 40 * 7013659 * 2
def baseEnd_7013659 : Nat := 3601378213732479760607275

theorem tailTrace_7013659 : CollatzResearch.WordTrace tailWord_7013659 prefixEnd_7013659 3601378213732479760607275 := by
  unfold tailWord_7013659
  simp only [CollatzResearch.WordTrace]
  refine ⟨255809159297718755437588031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170539439531812503625058687 255809159297718755437588031)
  ·
    refine ⟨383713738946578133156382047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255809159297718755437588031 383713738946578133156382047)
    ·
      refine ⟨575570608419867199734573071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383713738946578133156382047 575570608419867199734573071)
      ·
        refine ⟨863355912629800799601859607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575570608419867199734573071 863355912629800799601859607)
        ·
          refine ⟨1295033868944701199402789411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 863355912629800799601859607 1295033868944701199402789411)
          ·
            refine ⟨1942550803417051799104184117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1295033868944701199402789411 1942550803417051799104184117)
            ·
              refine ⟨182114137820348606166017261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1942550803417051799104184117 182114137820348606166017261)
              ·
                refine ⟨68292801682630727312256473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182114137820348606166017261 68292801682630727312256473)
                ·
                  refine ⟨51219601261973045484192355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68292801682630727312256473 51219601261973045484192355)
                  ·
                    refine ⟨76829401892959568226288533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51219601261973045484192355 76829401892959568226288533)
                    ·
                      refine ⟨3601378213732479760607275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76829401892959568226288533 3601378213732479760607275)
                      ·
                        rfl

theorem cell23_7013659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 6].length) (baseStart_7013659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013659 prefixEnd_7013659 := by exact prefixLift 7013659
  have htrace : WordTrace (prefixWord ++ tailWord_7013659) baseStart_7013659 baseEnd_7013659 := by
    simpa [prefixWord, tailWord_7013659, baseEnd_7013659] using wordTrace_append hprefix tailTrace_7013659
  have hstable : (prefixWord ++ tailWord_7013659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013659).length < 2 ^ (prefixWord ++ tailWord_7013659).sum := by decide
  have hdescent : baseEnd_7013659 < baseStart_7013659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013700 : List Nat := [2, 3, 4, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_7013700 : Nat := 118140960795 + 7013700 * 2 ^ 59
def prefixEnd_7013700 : Nat := 4983230072969 + 3 ^ 40 * 7013700 * 2
def baseEnd_7013700 : Nat := 3601399266439314100194587

theorem tailTrace_7013700 : CollatzResearch.WordTrace tailWord_7013700 prefixEnd_7013700 3601399266439314100194587 := by
  unfold tailWord_7013700
  simp only [CollatzResearch.WordTrace]
  refine ⟨127905327345285109719915277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170540436460380146293220369 127905327345285109719915277)
  ·
    refine ⟨47964497754481916144968229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127905327345285109719915277 47964497754481916144968229)
    ·
      refine ⟨8993343328965359277181543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47964497754481916144968229 8993343328965359277181543)
      ·
        refine ⟨13490014993448038915772315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8993343328965359277181543 13490014993448038915772315)
        ·
          refine ⟨20235022490172058373658473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13490014993448038915772315 20235022490172058373658473)
          ·
            refine ⟨15176266867629043780243855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20235022490172058373658473 15176266867629043780243855)
            ·
              refine ⟨22764400301443565670365783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15176266867629043780243855 22764400301443565670365783)
              ·
                refine ⟨34146600452165348505548675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22764400301443565670365783 34146600452165348505548675)
                ·
                  refine ⟨51219900678248022758323013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34146600452165348505548675 51219900678248022758323013)
                  ·
                    refine ⟨9603731377171504267185565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51219900678248022758323013 9603731377171504267185565)
                    ·
                      refine ⟨3601399266439314100194587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9603731377171504267185565 3601399266439314100194587)
                      ·
                        rfl

theorem cell23_7013700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_7013700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013700 prefixEnd_7013700 := by exact prefixLift 7013700
  have htrace : WordTrace (prefixWord ++ tailWord_7013700) baseStart_7013700 baseEnd_7013700 := by
    simpa [prefixWord, tailWord_7013700, baseEnd_7013700] using wordTrace_append hprefix tailTrace_7013700
  have hstable : (prefixWord ++ tailWord_7013700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013700).length < 2 ^ (prefixWord ++ tailWord_7013700).sum := by decide
  have hdescent : baseEnd_7013700 < baseStart_7013700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013713 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 5, 1, 3]
def baseStart_7013713 : Nat := 118140960795 + 7013713 * 2 ^ 59
def prefixEnd_7013713 : Nat := 4983230072969 + 3 ^ 40 * 7013713 * 2
def baseEnd_7013713 : Nat := 3601405941687822549332027

theorem tailTrace_7013713 : CollatzResearch.WordTrace tailWord_7013713 prefixEnd_7013713 3601405941687822549332027 := by
  unfold tailWord_7013713
  simp only [CollatzResearch.WordTrace]
  refine ⟨255811128839523122660053793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170540752559682081773369195 255811128839523122660053793)
  ·
    refine ⟨191858346629642341995040345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255811128839523122660053793 191858346629642341995040345)
    ·
      refine ⟨143893759972231756496280259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191858346629642341995040345 143893759972231756496280259)
      ·
        refine ⟨215840639958347634744420389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143893759972231756496280259 215840639958347634744420389)
        ·
          refine ⟨40470119992190181514578823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 215840639958347634744420389 40470119992190181514578823)
          ·
            refine ⟨60705179988285272271868235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40470119992190181514578823 60705179988285272271868235)
            ·
              refine ⟨91057769982427908407802353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60705179988285272271868235 91057769982427908407802353)
              ·
                refine ⟨68293327486820931305851765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91057769982427908407802353 68293327486820931305851765)
                ·
                  refine ⟨6402499451889462309923603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68293327486820931305851765 6402499451889462309923603)
                  ·
                    refine ⟨9603749177834193464885405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6402499451889462309923603 9603749177834193464885405)
                    ·
                      refine ⟨3601405941687822549332027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9603749177834193464885405 3601405941687822549332027)
                      ·
                        rfl

theorem cell23_7013713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 5, 1, 3].length) (baseStart_7013713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013713 prefixEnd_7013713 := by exact prefixLift 7013713
  have htrace : WordTrace (prefixWord ++ tailWord_7013713) baseStart_7013713 baseEnd_7013713 := by
    simpa [prefixWord, tailWord_7013713, baseEnd_7013713] using wordTrace_append hprefix tailTrace_7013713
  have hstable : (prefixWord ++ tailWord_7013713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013713).length < 2 ^ (prefixWord ++ tailWord_7013713).sum := by decide
  have hdescent : baseEnd_7013713 < baseStart_7013713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013753 : List Nat := [1, 2, 1, 3, 2, 1, 3, 4, 1, 1, 4]
def baseStart_7013753 : Nat := 118140960795 + 7013753 * 2 ^ 59
def prefixEnd_7013753 : Nat := 4983230072969 + 3 ^ 40 * 7013753 * 2
def baseEnd_7013753 : Nat := 3601426480914002392831843

theorem tailTrace_7013753 : CollatzResearch.WordTrace tailWord_7013753 prefixEnd_7013753 3601426480914002392831843 := by
  unfold tailWord_7013753
  simp only [CollatzResearch.WordTrace]
  refine ⟨255812587759378209491509913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170541725172918806327673275 255812587759378209491509913)
  ·
    refine ⟨191859440819533657118632435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255812587759378209491509913 191859440819533657118632435)
    ·
      refine ⟨287789161229300485677948653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191859440819533657118632435 287789161229300485677948653)
      ·
        refine ⟨107920935460987682129230745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287789161229300485677948653 107920935460987682129230745)
        ·
          refine ⟨80940701595740761596923059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107920935460987682129230745 80940701595740761596923059)
          ·
            refine ⟨121411052393611142395384589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80940701595740761596923059 121411052393611142395384589)
            ·
              refine ⟨45529144647604178398269221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121411052393611142395384589 45529144647604178398269221)
              ·
                refine ⟨8536714621425783449675479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45529144647604178398269221 8536714621425783449675479)
                ·
                  refine ⟨12805071932138675174513219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8536714621425783449675479 12805071932138675174513219)
                  ·
                    refine ⟨19207607898208012761769829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12805071932138675174513219 19207607898208012761769829)
                    ·
                      refine ⟨3601426480914002392831843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19207607898208012761769829 3601426480914002392831843)
                      ·
                        rfl

theorem cell23_7013753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_7013753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013753 prefixEnd_7013753 := by exact prefixLift 7013753
  have htrace : WordTrace (prefixWord ++ tailWord_7013753) baseStart_7013753 baseEnd_7013753 := by
    simpa [prefixWord, tailWord_7013753, baseEnd_7013753] using wordTrace_append hprefix tailTrace_7013753
  have hstable : (prefixWord ++ tailWord_7013753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013753).length < 2 ^ (prefixWord ++ tailWord_7013753).sum := by decide
  have hdescent : baseEnd_7013753 < baseStart_7013753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013756 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 3, 1, 5]
def baseStart_7013756 : Nat := 118140960795 + 7013756 * 2 ^ 59
def prefixEnd_7013756 : Nat := 4983230072969 + 3 ^ 40 * 7013756 * 2
def baseEnd_7013756 : Nat := 3601428021355965881094329

theorem tailTrace_7013756 : CollatzResearch.WordTrace tailWord_7013756 prefixEnd_7013756 3601428021355965881094329 := by
  unfold tailWord_7013756
  simp only [CollatzResearch.WordTrace]
  refine ⟨127906348589183670501934561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170541798118911560669246081 127906348589183670501934561)
  ·
    refine ⟨95929761441887752876450921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127906348589183670501934561 95929761441887752876450921)
    ·
      refine ⟨71947321081415814657338191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95929761441887752876450921 71947321081415814657338191)
      ·
        refine ⟨107920981622123721986007287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71947321081415814657338191 107920981622123721986007287)
        ·
          refine ⟨161881472433185582979010931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107920981622123721986007287 161881472433185582979010931)
          ·
            refine ⟨242822208649778374468516397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161881472433185582979010931 242822208649778374468516397)
            ·
              refine ⟨91058328243666890425693649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242822208649778374468516397 91058328243666890425693649)
              ·
                refine ⟨68293746182750167819270237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91058328243666890425693649 68293746182750167819270237)
                ·
                  refine ⟨25610154818531312932226339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68293746182750167819270237 25610154818531312932226339)
                  ·
                    refine ⟨38415232227796969398339509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25610154818531312932226339 38415232227796969398339509)
                    ·
                      refine ⟨3601428021355965881094329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38415232227796969398339509 3601428021355965881094329)
                      ·
                        rfl

theorem cell23_7013756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_7013756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013756 prefixEnd_7013756 := by exact prefixLift 7013756
  have htrace : WordTrace (prefixWord ++ tailWord_7013756) baseStart_7013756 baseEnd_7013756 := by
    simpa [prefixWord, tailWord_7013756, baseEnd_7013756] using wordTrace_append hprefix tailTrace_7013756
  have hstable : (prefixWord ++ tailWord_7013756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013756).length < 2 ^ (prefixWord ++ tailWord_7013756).sum := by decide
  have hdescent : baseEnd_7013756 < baseStart_7013756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013758 : List Nat := [4, 2, 3, 2, 2, 1, 1, 3, 1, 4]
def baseStart_7013758 : Nat := 118140960795 + 7013758 * 2 ^ 59
def prefixEnd_7013758 : Nat := 4983230072969 + 3 ^ 40 * 7013758 * 2
def baseEnd_7013758 : Nat := 1200476349439091624423107

theorem tailTrace_7013758 : CollatzResearch.WordTrace tailWord_7013758 prefixEnd_7013758 1200476349439091624423107 := by
  unfold tailWord_7013758
  simp only [CollatzResearch.WordTrace]
  refine ⟨31976596265545011918180241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170541846749573396896961285 31976596265545011918180241)
  ·
    refine ⟨23982447199158758938635181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31976596265545011918180241 23982447199158758938635181)
    ·
      refine ⟨8993417699684534601988193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23982447199158758938635181 8993417699684534601988193)
      ·
        refine ⟨6745063274763400951491145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8993417699684534601988193 6745063274763400951491145)
        ·
          refine ⟨5058797456072550713618359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6745063274763400951491145 5058797456072550713618359)
          ·
            refine ⟨7588196184108826070427539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5058797456072550713618359 7588196184108826070427539)
            ·
              refine ⟨11382294276163239105641309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7588196184108826070427539 11382294276163239105641309)
              ·
                refine ⟨4268360353561214664615491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11382294276163239105641309 4268360353561214664615491)
                ·
                  refine ⟨6402540530341821996923237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4268360353561214664615491 6402540530341821996923237)
                  ·
                    refine ⟨1200476349439091624423107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6402540530341821996923237 1200476349439091624423107)
                    ·
                      rfl

theorem cell23_7013758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_7013758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013758 prefixEnd_7013758 := by exact prefixLift 7013758
  have htrace : WordTrace (prefixWord ++ tailWord_7013758) baseStart_7013758 baseEnd_7013758 := by
    simpa [prefixWord, tailWord_7013758, baseEnd_7013758] using wordTrace_append hprefix tailTrace_7013758
  have hstable : (prefixWord ++ tailWord_7013758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013758).length < 2 ^ (prefixWord ++ tailWord_7013758).sum := by decide
  have hdescent : baseEnd_7013758 < baseStart_7013758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013763 : List Nat := [1, 1, 1, 3, 5, 1, 1, 2, 4, 4]
def baseStart_7013763 : Nat := 118140960795 + 7013763 * 2 ^ 59
def prefixEnd_7013763 : Nat := 4983230072969 + 3 ^ 40 * 7013763 * 2
def baseEnd_7013763 : Nat := 1200477205240182451235599

theorem tailTrace_7013763 : CollatzResearch.WordTrace tailWord_7013763 prefixEnd_7013763 1200477205240182451235599 := by
  unfold tailWord_7013763
  simp only [CollatzResearch.WordTrace]
  refine ⟨255812952489341981199373943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170541968326227987466249295 255812952489341981199373943)
  ·
    refine ⟨383719428734012971799060915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255812952489341981199373943 383719428734012971799060915)
    ·
      refine ⟨575579143101019457698591373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383719428734012971799060915 575579143101019457698591373)
      ·
        refine ⟨215842178662882296636971765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 575579143101019457698591373 215842178662882296636971765)
        ·
          refine ⟨20235204249645215309716103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 215842178662882296636971765 20235204249645215309716103)
          ·
            refine ⟨30352806374467822964574155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20235204249645215309716103 30352806374467822964574155)
            ·
              refine ⟨45529209561701734446861233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30352806374467822964574155 45529209561701734446861233)
              ·
                refine ⟨34146907171276300835145925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45529209561701734446861233 34146907171276300835145925)
                ·
                  refine ⟨6402545094614306406589861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34146907171276300835145925 6402545094614306406589861)
                  ·
                    refine ⟨1200477205240182451235599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6402545094614306406589861 1200477205240182451235599)
                    ·
                      rfl

theorem cell23_7013763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4, 4].length) (baseStart_7013763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013763 prefixEnd_7013763 := by exact prefixLift 7013763
  have htrace : WordTrace (prefixWord ++ tailWord_7013763) baseStart_7013763 baseEnd_7013763 := by
    simpa [prefixWord, tailWord_7013763, baseEnd_7013763] using wordTrace_append hprefix tailTrace_7013763
  have hstable : (prefixWord ++ tailWord_7013763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013763).length < 2 ^ (prefixWord ++ tailWord_7013763).sum := by decide
  have hdescent : baseEnd_7013763 < baseStart_7013763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013764 : List Nat := [2, 3, 2, 1, 1, 5, 1, 3, 1, 1, 3]
def baseStart_7013764 : Nat := 118140960795 + 7013764 * 2 ^ 59
def prefixEnd_7013764 : Nat := 4983230072969 + 3 ^ 40 * 7013764 * 2
def baseEnd_7013764 : Nat := 3601432129201201849794293

theorem tailTrace_7013764 : CollatzResearch.WordTrace tailWord_7013764 prefixEnd_7013764 3601432129201201849794293 := by
  unfold tailWord_7013764
  simp only [CollatzResearch.WordTrace]
  refine ⟨127906494481169179185080173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170541992641558905580106897 127906494481169179185080173)
  ·
    refine ⟨47964935430438442194405065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127906494481169179185080173 47964935430438442194405065)
    ·
      refine ⟨35973701572828831645803799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47964935430438442194405065 35973701572828831645803799)
      ·
        refine ⟨53960552359243247468705699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35973701572828831645803799 53960552359243247468705699)
        ·
          refine ⟨80940828538864871203058549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53960552359243247468705699 80940828538864871203058549)
          ·
            refine ⟨7588202675518581675286739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80940828538864871203058549 7588202675518581675286739)
            ·
              refine ⟨11382304013277872512930109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7588202675518581675286739 11382304013277872512930109)
              ·
                refine ⟨4268364004979202192348791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11382304013277872512930109 4268364004979202192348791)
                ·
                  refine ⟨6402546007468803288523187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4268364004979202192348791 6402546007468803288523187)
                  ·
                    refine ⟨9603819011203204932784781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6402546007468803288523187 9603819011203204932784781)
                    ·
                      refine ⟨3601432129201201849794293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9603819011203204932784781 3601432129201201849794293)
                      ·
                        rfl

theorem cell23_7013764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_7013764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013764 prefixEnd_7013764 := by exact prefixLift 7013764
  have htrace : WordTrace (prefixWord ++ tailWord_7013764) baseStart_7013764 baseEnd_7013764 := by
    simpa [prefixWord, tailWord_7013764, baseEnd_7013764] using wordTrace_append hprefix tailTrace_7013764
  have hstable : (prefixWord ++ tailWord_7013764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013764).length < 2 ^ (prefixWord ++ tailWord_7013764).sum := by decide
  have hdescent : baseEnd_7013764 < baseStart_7013764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013780 : List Nat := [2, 4, 2, 1, 2, 1, 2, 1, 4, 4]
def baseStart_7013780 : Nat := 118140960795 + 7013780 * 2 ^ 59
def prefixEnd_7013780 : Nat := 4983230072969 + 3 ^ 40 * 7013780 * 2
def baseEnd_7013780 : Nat := 1200480114963891262398073

theorem tailTrace_7013780 : CollatzResearch.WordTrace tailWord_7013780 prefixEnd_7013780 1200480114963891262398073 := by
  unfold tailWord_7013780
  simp only [CollatzResearch.WordTrace]
  refine ⟨127906786265140196551371397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170542381686853595401828529 127906786265140196551371397)
  ·
    refine ⟨23982522424713786853382137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 127906786265140196551371397 23982522424713786853382137)
    ·
      refine ⟨17986891818535340140036603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23982522424713786853382137 17986891818535340140036603)
      ·
        refine ⟨26980337727803010210054905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17986891818535340140036603 26980337727803010210054905)
        ·
          refine ⟨20235253295852257657541179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26980337727803010210054905 20235253295852257657541179)
          ·
            refine ⟨30352879943778386486311769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20235253295852257657541179 30352879943778386486311769)
            ·
              refine ⟨22764659957833789864733827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30352879943778386486311769 22764659957833789864733827)
              ·
                refine ⟨34146989936750684797100741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22764659957833789864733827 34146989936750684797100741)
                ·
                  refine ⟨6402560613140753399456389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34146989936750684797100741 6402560613140753399456389)
                  ·
                    refine ⟨1200480114963891262398073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6402560613140753399456389 1200480114963891262398073)
                    ·
                      rfl

theorem cell23_7013780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_7013780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013780 prefixEnd_7013780 := by exact prefixLift 7013780
  have htrace : WordTrace (prefixWord ++ tailWord_7013780) baseStart_7013780 baseEnd_7013780 := by
    simpa [prefixWord, tailWord_7013780, baseEnd_7013780] using wordTrace_append hprefix tailTrace_7013780
  have hstable : (prefixWord ++ tailWord_7013780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013780).length < 2 ^ (prefixWord ++ tailWord_7013780).sum := by decide
  have hdescent : baseEnd_7013780 < baseStart_7013780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013796 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 1, 4, 6]
def baseStart_7013796 : Nat := 118140960795 + 7013796 * 2 ^ 59
def prefixEnd_7013796 : Nat := 4983230072969 + 3 ^ 40 * 7013796 * 2
def baseEnd_7013796 : Nat := 3601448560582145724594145

theorem tailTrace_7013796 : CollatzResearch.WordTrace tailWord_7013796 prefixEnd_7013796 3601448560582145724594145 := by
  unfold tailWord_7013796
  simp only [CollatzResearch.WordTrace]
  refine ⟨127907078049111213917662621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170542770732148285223550161 127907078049111213917662621)
  ·
    refine ⟨47965154268416705219123483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 127907078049111213917662621 47965154268416705219123483)
    ·
      refine ⟨71947731402625057828685225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47965154268416705219123483 71947731402625057828685225)
      ·
        refine ⟨53960798551968793371513919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71947731402625057828685225 53960798551968793371513919)
        ·
          refine ⟨80941197827953190057270879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53960798551968793371513919 80941197827953190057270879)
          ·
            refine ⟨121411796741929785085906319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80941197827953190057270879 121411796741929785085906319)
            ·
              refine ⟨182117695112894677628859479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121411796741929785085906319 182117695112894677628859479)
              ·
                refine ⟨273176542669342016443289219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182117695112894677628859479 273176542669342016443289219)
                ·
                  refine ⟨409764814004013024664933829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 273176542669342016443289219 409764814004013024664933829)
                  ·
                    refine ⟨76830902625752442124675093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 409764814004013024664933829 76830902625752442124675093)
                    ·
                      refine ⟨3601448560582145724594145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76830902625752442124675093 3601448560582145724594145)
                      ·
                        rfl

theorem cell23_7013796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_7013796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013796 prefixEnd_7013796 := by exact prefixLift 7013796
  have htrace : WordTrace (prefixWord ++ tailWord_7013796) baseStart_7013796 baseEnd_7013796 := by
    simpa [prefixWord, tailWord_7013796, baseEnd_7013796] using wordTrace_append hprefix tailTrace_7013796
  have hstable : (prefixWord ++ tailWord_7013796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013796).length < 2 ^ (prefixWord ++ tailWord_7013796).sum := by decide
  have hdescent : baseEnd_7013796 < baseStart_7013796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013816 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 1, 4, 5]
def baseStart_7013816 : Nat := 118140960795 + 7013816 * 2 ^ 59
def prefixEnd_7013816 : Nat := 4983230072969 + 3 ^ 40 * 7013816 * 2
def baseEnd_7013816 : Nat := 3601458830195235646344053

theorem tailTrace_7013816 : CollatzResearch.WordTrace tailWord_7013816 prefixEnd_7013816 3601458830195235646344053 := by
  unfold tailWord_7013816
  simp only [CollatzResearch.WordTrace]
  refine ⟨127907442779074985625526651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170543257038766647500702201 127907442779074985625526651)
  ·
    refine ⟨191861164168612478438289977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127907442779074985625526651 191861164168612478438289977)
    ·
      refine ⟨143895873126459358828717483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191861164168612478438289977 143895873126459358828717483)
      ·
        refine ⟨215843809689689038243076225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143895873126459358828717483 215843809689689038243076225)
        ·
          refine ⟨161882857267266778682307169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215843809689689038243076225 161882857267266778682307169)
          ·
            refine ⟨121412142950450084011730377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161882857267266778682307169 121412142950450084011730377)
            ·
              refine ⟨91059107212837563008797783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121412142950450084011730377 91059107212837563008797783)
              ·
                refine ⟨136588660819256344513196675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91059107212837563008797783 136588660819256344513196675)
                ·
                  refine ⟨204882991228884516769795013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136588660819256344513196675 204882991228884516769795013)
                  ·
                    refine ⟨38415560855415846894336565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 204882991228884516769795013 38415560855415846894336565)
                    ·
                      refine ⟨3601458830195235646344053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38415560855415846894336565 3601458830195235646344053)
                      ·
                        rfl

theorem cell23_7013816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_7013816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013816 prefixEnd_7013816 := by exact prefixLift 7013816
  have htrace : WordTrace (prefixWord ++ tailWord_7013816) baseStart_7013816 baseEnd_7013816 := by
    simpa [prefixWord, tailWord_7013816, baseEnd_7013816] using wordTrace_append hprefix tailTrace_7013816
  have hstable : (prefixWord ++ tailWord_7013816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013816).length < 2 ^ (prefixWord ++ tailWord_7013816).sum := by decide
  have hdescent : baseEnd_7013816 < baseStart_7013816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013853 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 1, 8]
def baseStart_7013853 : Nat := 118140960795 + 7013853 * 2 ^ 59
def prefixEnd_7013853 : Nat := 4983230072969 + 3 ^ 40 * 7013853 * 2
def baseEnd_7013853 : Nat := 1200492609659817333860461

theorem tailTrace_7013853 : CollatzResearch.WordTrace tailWord_7013853 prefixEnd_7013853 1200492609659817333860461 := by
  unfold tailWord_7013853
  simp only [CollatzResearch.WordTrace]
  refine ⟨255816235059015926570150213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170544156706010617713433475 255816235059015926570150213)
  ·
    refine ⟨47965544073565486231903165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255816235059015926570150213 47965544073565486231903165)
    ·
      refine ⟨17987079027587057336963687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47965544073565486231903165 17987079027587057336963687)
      ·
        refine ⟨26980618541380586005445531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17987079027587057336963687 26980618541380586005445531)
        ·
          refine ⟨40470927812070879008168297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26980618541380586005445531 40470927812070879008168297)
          ·
            refine ⟨30353195859053159256126223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40470927812070879008168297 30353195859053159256126223)
            ·
              refine ⟨45529793788579738884189335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30353195859053159256126223 45529793788579738884189335)
              ·
                refine ⟨68294690682869608326284003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45529793788579738884189335 68294690682869608326284003)
                ·
                  refine ⟨102442036024304412489426005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68294690682869608326284003 102442036024304412489426005)
                  ·
                    refine ⟨1200492609659817333860461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102442036024304412489426005 1200492609659817333860461)
                    ·
                      rfl

theorem cell23_7013853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_7013853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013853 prefixEnd_7013853 := by exact prefixLift 7013853
  have htrace : WordTrace (prefixWord ++ tailWord_7013853) baseStart_7013853 baseEnd_7013853 := by
    simpa [prefixWord, tailWord_7013853, baseEnd_7013853] using wordTrace_append hprefix tailTrace_7013853
  have hstable : (prefixWord ++ tailWord_7013853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013853).length < 2 ^ (prefixWord ++ tailWord_7013853).sum := by decide
  have hdescent : baseEnd_7013853 < baseStart_7013853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013900 : List Nat := [2, 2, 1, 2, 5, 1, 2, 1, 7]
def baseStart_7013900 : Nat := 118140960795 + 7013900 * 2 ^ 59
def prefixEnd_7013900 : Nat := 4983230072969 + 3 ^ 40 * 7013900 * 2
def baseEnd_7013900 : Nat := 400166884730023701965963

theorem tailTrace_7013900 : CollatzResearch.WordTrace tailWord_7013900 prefixEnd_7013900 400166884730023701965963 := by
  unfold tailWord_7013900
  simp only [CollatzResearch.WordTrace]
  refine ⟨127908974644922826798555577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170545299526563769064740769 127908974644922826798555577)
  ·
    refine ⟨95931730983692120098916683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127908974644922826798555577 95931730983692120098916683)
    ·
      refine ⟨143897596475538180148375025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95931730983692120098916683 143897596475538180148375025)
      ·
        refine ⟨107923197356653635111281269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143897596475538180148375025 107923197356653635111281269)
        ·
          refine ⟨10117799752186278291682619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 107923197356653635111281269 10117799752186278291682619)
          ·
            refine ⟨15176699628279417437523929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10117799752186278291682619 15176699628279417437523929)
            ·
              refine ⟨11382524721209563078142947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15176699628279417437523929 11382524721209563078142947)
              ·
                refine ⟨17073787081814344617214421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11382524721209563078142947 17073787081814344617214421)
                ·
                  refine ⟨400166884730023701965963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17073787081814344617214421 400166884730023701965963)
                  ·
                    rfl

theorem cell23_7013900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 7].length) (baseStart_7013900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013900 prefixEnd_7013900 := by exact prefixLift 7013900
  have htrace : WordTrace (prefixWord ++ tailWord_7013900) baseStart_7013900 baseEnd_7013900 := by
    simpa [prefixWord, tailWord_7013900, baseEnd_7013900] using wordTrace_append hprefix tailTrace_7013900
  have hstable : (prefixWord ++ tailWord_7013900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013900).length < 2 ^ (prefixWord ++ tailWord_7013900).sum := by decide
  have hdescent : baseEnd_7013900 < baseStart_7013900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013930 : List Nat := [3, 1, 4, 1, 1, 1, 2, 3, 2, 5]
def baseStart_7013930 : Nat := 118140960795 + 7013930 * 2 ^ 59
def prefixEnd_7013930 : Nat := 4983230072969 + 3 ^ 40 * 7013930 * 2
def baseEnd_7013930 : Nat := 1200505788996616066772843

theorem tailTrace_7013930 : CollatzResearch.WordTrace tailWord_7013930 prefixEnd_7013930 1200505788996616066772843 := by
  unfold tailWord_7013930
  simp only [CollatzResearch.WordTrace]
  refine ⟨63954760869934242180175811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170546028986491312480468829 63954760869934242180175811)
  ·
    refine ⟨95932141304901363270263717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63954760869934242180175811 95932141304901363270263717)
    ·
      refine ⟨17987276494669005613174447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95932141304901363270263717 17987276494669005613174447)
      ·
        refine ⟨26980914742003508419761671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17987276494669005613174447 26980914742003508419761671)
        ·
          refine ⟨40471372113005262629642507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26980914742003508419761671 40471372113005262629642507)
          ·
            refine ⟨60707058169507893944463761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40471372113005262629642507 60707058169507893944463761)
            ·
              refine ⟨45530293627130920458347821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60707058169507893944463761 45530293627130920458347821)
              ·
                refine ⟨17073860110174095171880433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45530293627130920458347821 17073860110174095171880433)
                ·
                  refine ⟨12805395082630571378910325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17073860110174095171880433 12805395082630571378910325)
                  ·
                    refine ⟨1200505788996616066772843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12805395082630571378910325 1200505788996616066772843)
                    ·
                      rfl

theorem cell23_7013930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_7013930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013930 prefixEnd_7013930 := by exact prefixLift 7013930
  have htrace : WordTrace (prefixWord ++ tailWord_7013930) baseStart_7013930 baseEnd_7013930 := by
    simpa [prefixWord, tailWord_7013930, baseEnd_7013930] using wordTrace_append hprefix tailTrace_7013930
  have hstable : (prefixWord ++ tailWord_7013930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013930).length < 2 ^ (prefixWord ++ tailWord_7013930).sum := by decide
  have hdescent : baseEnd_7013930 < baseStart_7013930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013934 : List Nat := [4, 1, 3, 1, 2, 3, 1, 3, 5]
def baseStart_7013934 : Nat := 118140960795 + 7013934 * 2 ^ 59
def prefixEnd_7013934 : Nat := 4983230072969 + 3 ^ 40 * 7013934 * 2
def baseEnd_7013934 : Nat := 400168824545829576074279

theorem tailTrace_7013934 : CollatzResearch.WordTrace tailWord_7013934 prefixEnd_7013934 400168824545829576074279 := by
  unfold tailWord_7013934
  simp only [CollatzResearch.WordTrace]
  refine ⟨31977398671465309675481107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170546126247814984935899237 31977398671465309675481107)
  ·
    refine ⟨47966098007197964513221661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31977398671465309675481107 47966098007197964513221661)
    ·
      refine ⟨17987286752699236692458123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47966098007197964513221661 17987286752699236692458123)
      ·
        refine ⟨26980930129048855038687185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17987286752699236692458123 26980930129048855038687185)
        ·
          refine ⟨20235697596786641279015389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26980930129048855038687185 20235697596786641279015389)
          ·
            refine ⟨7588386598794990479630771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20235697596786641279015389 7588386598794990479630771)
            ·
              refine ⟨11382579898192485719446157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7588386598794990479630771 11382579898192485719446157)
              ·
                refine ⟨4268467461822182144792309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11382579898192485719446157 4268467461822182144792309)
                ·
                  refine ⟨400168824545829576074279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4268467461822182144792309 400168824545829576074279)
                  ·
                    rfl

theorem cell23_7013934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 3, 5].length) (baseStart_7013934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013934 prefixEnd_7013934 := by exact prefixLift 7013934
  have htrace : WordTrace (prefixWord ++ tailWord_7013934) baseStart_7013934 baseEnd_7013934 := by
    simpa [prefixWord, tailWord_7013934, baseEnd_7013934] using wordTrace_append hprefix tailTrace_7013934
  have hstable : (prefixWord ++ tailWord_7013934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013934).length < 2 ^ (prefixWord ++ tailWord_7013934).sum := by decide
  have hdescent : baseEnd_7013934 < baseStart_7013934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7013987 : List Nat := [1, 1, 1, 5, 1, 4, 2, 1, 2, 2, 3]
def baseStart_7013987 : Nat := 118140960795 + 7013987 * 2 ^ 59
def prefixEnd_7013987 : Nat := 4983230072969 + 3 ^ 40 * 7013987 * 2
def baseEnd_7013987 : Nat := 3601546635387154477305767

theorem tailTrace_7013987 : CollatzResearch.WordTrace tailWord_7013987 prefixEnd_7013987 3601546635387154477305767 := by
  unfold tailWord_7013987
  simp only [CollatzResearch.WordTrace]
  refine ⟨255821122440530467455528215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170547414960353644970352143 255821122440530467455528215)
  ·
    refine ⟨383731683660795701183292323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255821122440530467455528215 383731683660795701183292323)
    ·
      refine ⟨575597525491193551774938485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383731683660795701183292323 575597525491193551774938485)
      ·
        refine ⟨53962268014799395478900483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 575597525491193551774938485 53962268014799395478900483)
        ·
          refine ⟨80943402022199093218350725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53962268014799395478900483 80943402022199093218350725)
          ·
            refine ⟨15176887879162329978440761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80943402022199093218350725 15176887879162329978440761)
            ·
              refine ⟨11382665909371747483830571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15176887879162329978440761 11382665909371747483830571)
              ·
                refine ⟨17073998864057621225745857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11382665909371747483830571 17073998864057621225745857)
                ·
                  refine ⟨12805499148043215919309393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17073998864057621225745857 12805499148043215919309393)
                  ·
                    refine ⟨9604124361032411939482045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12805499148043215919309393 9604124361032411939482045)
                    ·
                      refine ⟨3601546635387154477305767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9604124361032411939482045 3601546635387154477305767)
                      ·
                        rfl

theorem cell23_7013987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_7013987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7013987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7013987 prefixEnd_7013987 := by exact prefixLift 7013987
  have htrace : WordTrace (prefixWord ++ tailWord_7013987) baseStart_7013987 baseEnd_7013987 := by
    simpa [prefixWord, tailWord_7013987, baseEnd_7013987] using wordTrace_append hprefix tailTrace_7013987
  have hstable : (prefixWord ++ tailWord_7013987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7013987).length < 2 ^ (prefixWord ++ tailWord_7013987).sum := by decide
  have hdescent : baseEnd_7013987 < baseStart_7013987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7013987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014044 : List Nat := [2, 2, 3, 2, 3, 1, 1, 1, 1, 5, 2]
def baseStart_7014044 : Nat := 118140960795 + 7014044 * 2 ^ 59
def prefixEnd_7014044 : Nat := 4983230072969 + 3 ^ 40 * 7014044 * 2
def baseEnd_7014044 : Nat := 3601575903784460754293005

theorem tailTrace_7014044 : CollatzResearch.WordTrace tailWord_7014044 prefixEnd_7014044 3601575903784460754293005 := by
  unfold tailWord_7014044
  simp only [CollatzResearch.WordTrace]
  refine ⟨127911600700661983095176593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170548800934215977460235457 127911600700661983095176593)
  ·
    refine ⟨95933700525496487321382445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127911600700661983095176593 95933700525496487321382445)
    ·
      refine ⟨35975137697061182745518417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95933700525496487321382445 35975137697061182745518417)
      ·
        refine ⟨26981353272795887059138813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35975137697061182745518417 26981353272795887059138813)
        ·
          refine ⟨10118007477298457647177055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26981353272795887059138813 10118007477298457647177055)
          ·
            refine ⟨15177011215947686470765583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10118007477298457647177055 15177011215947686470765583)
            ·
              refine ⟨22765516823921529706148375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15177011215947686470765583 22765516823921529706148375)
              ·
                refine ⟨34148275235882294559222563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22765516823921529706148375 34148275235882294559222563)
                ·
                  refine ⟨51222412853823441838833845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34148275235882294559222563 51222412853823441838833845)
                  ·
                    refine ⟨4802101205045947672390673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51222412853823441838833845 4802101205045947672390673)
                    ·
                      refine ⟨3601575903784460754293005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4802101205045947672390673 3601575903784460754293005)
                      ·
                        rfl

theorem cell23_7014044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_7014044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014044 prefixEnd_7014044 := by exact prefixLift 7014044
  have htrace : WordTrace (prefixWord ++ tailWord_7014044) baseStart_7014044 baseEnd_7014044 := by
    simpa [prefixWord, tailWord_7014044, baseEnd_7014044] using wordTrace_append hprefix tailTrace_7014044
  have hstable : (prefixWord ++ tailWord_7014044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014044).length < 2 ^ (prefixWord ++ tailWord_7014044).sum := by decide
  have hdescent : baseEnd_7014044 < baseStart_7014044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014063 : List Nat := [1, 1, 2, 1, 2, 4, 12]
def baseStart_7014063 : Nat := 118140960795 + 7014063 * 2 ^ 59
def prefixEnd_7014063 : Nat := 4983230072969 + 3 ^ 40 * 7014063 * 2
def baseEnd_7014063 : Nat := 44464020492801187406857

theorem tailTrace_7014063 : CollatzResearch.WordTrace tailWord_7014063 prefixEnd_7014063 44464020492801187406857 := by
  unfold tailWord_7014063
  simp only [CollatzResearch.WordTrace]
  refine ⟨255823894388255132435294843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170549262925503421623529895 255823894388255132435294843)
  ·
    refine ⟨383735841582382698652942265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255823894388255132435294843 383735841582382698652942265)
    ·
      refine ⟨287801881186787023989706699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 383735841582382698652942265 287801881186787023989706699)
      ·
        refine ⟨431702821780180535984560049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287801881186787023989706699 431702821780180535984560049)
        ·
          refine ⟨323777116335135401988420037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431702821780180535984560049 323777116335135401988420037)
          ·
            refine ⟨60708209312837887872828757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 323777116335135401988420037 60708209312837887872828757)
            ·
              refine ⟨44464020492801187406857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 60708209312837887872828757 44464020492801187406857)
              ·
                rfl

theorem cell23_7014063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 12].length) (baseStart_7014063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014063 prefixEnd_7014063 := by exact prefixLift 7014063
  have htrace : WordTrace (prefixWord ++ tailWord_7014063) baseStart_7014063 baseEnd_7014063 := by
    simpa [prefixWord, tailWord_7014063, baseEnd_7014063] using wordTrace_append hprefix tailTrace_7014063
  have hstable : (prefixWord ++ tailWord_7014063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014063).length < 2 ^ (prefixWord ++ tailWord_7014063).sum := by decide
  have hdescent : baseEnd_7014063 < baseStart_7014063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014074 : List Nat := [3, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2]
def baseStart_7014074 : Nat := 118140960795 + 7014074 * 2 ^ 59
def prefixEnd_7014074 : Nat := 4983230072969 + 3 ^ 40 * 7014074 * 2
def baseEnd_7014074 : Nat := 3601591308204095636917867

theorem tailTrace_7014074 : CollatzResearch.WordTrace tailWord_7014074 prefixEnd_7014074 3601591308204095636917867 := by
  unfold tailWord_7014074
  simp only [CollatzResearch.WordTrace]
  refine ⟨63956073897803820328486319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170549530394143520875963517 63956073897803820328486319)
  ·
    refine ⟨95934110846705730492729479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63956073897803820328486319 95934110846705730492729479)
    ·
      refine ⟨143901166270058595739094219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95934110846705730492729479 143901166270058595739094219)
      ·
        refine ⟨215851749405087893608641329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143901166270058595739094219 215851749405087893608641329)
        ·
          refine ⟨161888812053815920206480997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215851749405087893608641329 161888812053815920206480997)
          ·
            refine ⟨30354152260090485038715187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 161888812053815920206480997 30354152260090485038715187)
            ·
              refine ⟨45531228390135727558072781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30354152260090485038715187 45531228390135727558072781)
              ·
                refine ⟨17074210646300897834277293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45531228390135727558072781 17074210646300897834277293)
                ·
                  refine ⟨6402828992362836687853985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17074210646300897834277293 6402828992362836687853985)
                  ·
                    refine ⟨4802121744272127515890489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6402828992362836687853985 4802121744272127515890489)
                    ·
                      refine ⟨3601591308204095636917867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4802121744272127515890489 3601591308204095636917867)
                      ·
                        rfl

theorem cell23_7014074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2].length) (baseStart_7014074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014074 prefixEnd_7014074 := by exact prefixLift 7014074
  have htrace : WordTrace (prefixWord ++ tailWord_7014074) baseStart_7014074 baseEnd_7014074 := by
    simpa [prefixWord, tailWord_7014074, baseEnd_7014074] using wordTrace_append hprefix tailTrace_7014074
  have hstable : (prefixWord ++ tailWord_7014074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014074).length < 2 ^ (prefixWord ++ tailWord_7014074).sum := by decide
  have hdescent : baseEnd_7014074 < baseStart_7014074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014094 : List Nat := [4, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3]
def baseStart_7014094 : Nat := 118140960795 + 7014094 * 2 ^ 59
def prefixEnd_7014094 : Nat := 4983230072969 + 3 ^ 40 * 7014094 * 2
def baseEnd_7014094 : Nat := 3601601577817185558667775

theorem tailTrace_7014094 : CollatzResearch.WordTrace tailWord_7014094 prefixEnd_7014094 3601601577817185558667775 := by
  unfold tailWord_7014094
  simp only [CollatzResearch.WordTrace]
  refine ⟨31978128131392853091209167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170550016700761883153115557 31978128131392853091209167)
  ·
    refine ⟨47967192197089279636813751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31978128131392853091209167 47967192197089279636813751)
    ·
      refine ⟨71950788295633919455220627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47967192197089279636813751 71950788295633919455220627)
      ·
        refine ⟨107926182443450879182830941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71950788295633919455220627 107926182443450879182830941)
        ·
          refine ⟨40472318416294079693561603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107926182443450879182830941 40472318416294079693561603)
          ·
            refine ⟨60708477624441119540342405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40472318416294079693561603 60708477624441119540342405)
            ·
              refine ⟨11382839554582709913814201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60708477624441119540342405 11382839554582709913814201)
              ·
                refine ⟨8537129665937032435360651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11382839554582709913814201 8537129665937032435360651)
                ·
                  refine ⟨12805694498905548653040977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8537129665937032435360651 12805694498905548653040977)
                  ·
                    refine ⟨9604270874179161489780733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12805694498905548653040977 9604270874179161489780733)
                    ·
                      refine ⟨3601601577817185558667775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9604270874179161489780733 3601601577817185558667775)
                      ·
                        rfl

theorem cell23_7014094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_7014094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014094 prefixEnd_7014094 := by exact prefixLift 7014094
  have htrace : WordTrace (prefixWord ++ tailWord_7014094) baseStart_7014094 baseEnd_7014094 := by
    simpa [prefixWord, tailWord_7014094, baseEnd_7014094] using wordTrace_append hprefix tailTrace_7014094
  have hstable : (prefixWord ++ tailWord_7014094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014094).length < 2 ^ (prefixWord ++ tailWord_7014094).sum := by decide
  have hdescent : baseEnd_7014094 < baseStart_7014094 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014097 : List Nat := [1, 2, 2, 1, 2, 6, 2, 7]
def baseStart_7014097 : Nat := 118140960795 + 7014097 * 2 ^ 59
def prefixEnd_7014097 : Nat := 4983230072969 + 3 ^ 40 * 7014097 * 2
def baseEnd_7014097 : Nat := 133392708083672186923343

theorem tailTrace_7014097 : CollatzResearch.WordTrace tailWord_7014097 prefixEnd_7014097 133392708083672186923343 := by
  unfold tailWord_7014097
  simp only [CollatzResearch.WordTrace]
  refine ⟨255825134470131956242032545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170550089646754637494688363 255825134470131956242032545)
  ·
    refine ⟨191868850852598967181524409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255825134470131956242032545 191868850852598967181524409)
    ·
      refine ⟨143901638139449225386143307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191868850852598967181524409 143901638139449225386143307)
      ·
        refine ⟨215852457209173838079214961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143901638139449225386143307 215852457209173838079214961)
        ·
          refine ⟨161889342906880378559411221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215852457209173838079214961 161889342906880378559411221)
          ·
            refine ⟨7588562948760017744972401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 161889342906880378559411221 7588562948760017744972401)
            ·
              refine ⟨5691422211570013308729301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7588562948760017744972401 5691422211570013308729301)
              ·
                refine ⟨133392708083672186923343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5691422211570013308729301 133392708083672186923343)
                ·
                  rfl

theorem cell23_7014097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 7].length) (baseStart_7014097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014097 prefixEnd_7014097 := by exact prefixLift 7014097
  have htrace : WordTrace (prefixWord ++ tailWord_7014097) baseStart_7014097 baseEnd_7014097 := by
    simpa [prefixWord, tailWord_7014097, baseEnd_7014097] using wordTrace_append hprefix tailTrace_7014097
  have hstable : (prefixWord ++ tailWord_7014097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014097).length < 2 ^ (prefixWord ++ tailWord_7014097).sum := by decide
  have hdescent : baseEnd_7014097 < baseStart_7014097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014102 : List Nat := [5, 2, 1, 3, 1, 2, 1, 3, 1, 1, 3]
def baseStart_7014102 : Nat := 118140960795 + 7014102 * 2 ^ 59
def prefixEnd_7014102 : Nat := 4983230072969 + 3 ^ 40 * 7014102 * 2
def baseEnd_7014102 : Nat := 3601605685662421527367739

theorem tailTrace_7014102 : CollatzResearch.WordTrace tailWord_7014102 prefixEnd_7014102 3601605685662421527367739 := by
  unfold tailWord_7014102
  simp only [CollatzResearch.WordTrace]
  refine ⟨15989082302194615130997785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170550211223409228063976373 15989082302194615130997785)
  ·
    refine ⟨11991811726645961348248339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15989082302194615130997785 11991811726645961348248339)
    ·
      refine ⟨17987717589968942022372509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11991811726645961348248339 17987717589968942022372509)
      ·
        refine ⟨6745394096238353258389691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17987717589968942022372509 6745394096238353258389691)
        ·
          refine ⟨10118091144357529887584537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6745394096238353258389691 10118091144357529887584537)
          ·
            refine ⟨7588568358268147415688403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10118091144357529887584537 7588568358268147415688403)
            ·
              refine ⟨11382852537402221123532605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7588568358268147415688403 11382852537402221123532605)
              ·
                refine ⟨4268569701525832921324727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11382852537402221123532605 4268569701525832921324727)
                ·
                  refine ⟨6402854552288749381987091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4268569701525832921324727 6402854552288749381987091)
                  ·
                    refine ⟨9604281828433124072980637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6402854552288749381987091 9604281828433124072980637)
                    ·
                      refine ⟨3601605685662421527367739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9604281828433124072980637 3601605685662421527367739)
                      ·
                        rfl

theorem cell23_7014102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_7014102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014102 prefixEnd_7014102 := by exact prefixLift 7014102
  have htrace : WordTrace (prefixWord ++ tailWord_7014102) baseStart_7014102 baseEnd_7014102 := by
    simpa [prefixWord, tailWord_7014102, baseEnd_7014102] using wordTrace_append hprefix tailTrace_7014102
  have hstable : (prefixWord ++ tailWord_7014102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014102).length < 2 ^ (prefixWord ++ tailWord_7014102).sum := by decide
  have hdescent : baseEnd_7014102 < baseStart_7014102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014125 : List Nat := [1, 5, 1, 2, 1, 3, 3, 2, 1, 2, 2]
def baseStart_7014125 : Nat := 118140960795 + 7014125 * 2 ^ 59
def prefixEnd_7014125 : Nat := 4983230072969 + 3 ^ 40 * 7014125 * 2
def baseEnd_7014125 : Nat := 3601617495717474937380133

theorem tailTrace_7014125 : CollatzResearch.WordTrace tailWord_7014125 prefixEnd_7014125 3601617495717474937380133 := by
  unfold tailWord_7014125
  simp only [CollatzResearch.WordTrace]
  refine ⟨255826155714030517024051829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170550770476020344682701219 255826155714030517024051829)
  ·
    refine ⟨23983702098190360971004859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 255826155714030517024051829 23983702098190360971004859)
    ·
      refine ⟨35975553147285541456507289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23983702098190360971004859 35975553147285541456507289)
      ·
        refine ⟨26981664860464156092380467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35975553147285541456507289 26981664860464156092380467)
        ·
          refine ⟨40472497290696234138570701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26981664860464156092380467 40472497290696234138570701)
          ·
            refine ⟨15177186484011087801964013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40472497290696234138570701 15177186484011087801964013)
            ·
              refine ⟨5691444931504157925736505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15177186484011087801964013 5691444931504157925736505)
              ·
                refine ⟨4268583698628118444302379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5691444931504157925736505 4268583698628118444302379)
                ·
                  refine ⟨6402875547942177666453569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4268583698628118444302379 6402875547942177666453569)
                  ·
                    refine ⟨4802156660956633249840177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6402875547942177666453569 4802156660956633249840177)
                    ·
                      refine ⟨3601617495717474937380133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4802156660956633249840177 3601617495717474937380133)
                      ·
                        rfl

theorem cell23_7014125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_7014125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014125 prefixEnd_7014125 := by exact prefixLift 7014125
  have htrace : WordTrace (prefixWord ++ tailWord_7014125) baseStart_7014125 baseEnd_7014125 := by
    simpa [prefixWord, tailWord_7014125, baseEnd_7014125] using wordTrace_append hprefix tailTrace_7014125
  have hstable : (prefixWord ++ tailWord_7014125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014125).length < 2 ^ (prefixWord ++ tailWord_7014125).sum := by decide
  have hdescent : baseEnd_7014125 < baseStart_7014125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014140 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 1, 8]
def baseStart_7014140 : Nat := 118140960795 + 7014140 * 2 ^ 59
def prefixEnd_7014140 : Nat := 4983230072969 + 3 ^ 40 * 7014140 * 2
def baseEnd_7014140 : Nat := 1200541732642430792897521

theorem tailTrace_7014140 : CollatzResearch.WordTrace tailWord_7014140 prefixEnd_7014140 1200541732642430792897521 := by
  unfold tailWord_7014140
  simp only [CollatzResearch.WordTrace]
  refine ⟨127913351404488087292923937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170551135205984116390565249 127913351404488087292923937)
  ·
    refine ⟨95935013553366065469692953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127913351404488087292923937 95935013553366065469692953)
    ·
      refine ⟨71951260165024549102269715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95935013553366065469692953 71951260165024549102269715)
      ·
        refine ⟨107926890247536823653404573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71951260165024549102269715 107926890247536823653404573)
        ·
          refine ⟨40472583842826308870026715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107926890247536823653404573 40472583842826308870026715)
          ·
            refine ⟨60708875764239463305040073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40472583842826308870026715 60708875764239463305040073)
            ·
              refine ⟨45531656823179597478780055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60708875764239463305040073 45531656823179597478780055)
              ·
                refine ⟨68297485234769396218170083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45531656823179597478780055 68297485234769396218170083)
                ·
                  refine ⟨102446227852154094327255125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68297485234769396218170083 102446227852154094327255125)
                  ·
                    refine ⟨1200541732642430792897521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102446227852154094327255125 1200541732642430792897521)
                    ·
                      rfl

theorem cell23_7014140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_7014140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014140 prefixEnd_7014140 := by exact prefixLift 7014140
  have htrace : WordTrace (prefixWord ++ tailWord_7014140) baseStart_7014140 baseEnd_7014140 := by
    simpa [prefixWord, tailWord_7014140, baseEnd_7014140] using wordTrace_append hprefix tailTrace_7014140
  have hstable : (prefixWord ++ tailWord_7014140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014140).length < 2 ^ (prefixWord ++ tailWord_7014140).sum := by decide
  have hdescent : baseEnd_7014140 < baseStart_7014140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014151 : List Nat := [1, 1, 4, 4, 2, 1, 1, 1, 3, 3, 2]
def baseStart_7014151 : Nat := 118140960795 + 7014151 * 2 ^ 59
def prefixEnd_7014151 : Nat := 4983230072969 + 3 ^ 40 * 7014151 * 2
def baseEnd_7014151 : Nat := 3601630846214491835655013

theorem tailTrace_7014151 : CollatzResearch.WordTrace tailWord_7014151 prefixEnd_7014151 3601630846214491835655013 := by
  unfold tailWord_7014151
  simp only [CollatzResearch.WordTrace]
  refine ⟨255827104011936323464498307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170551402674624215642998871 255827104011936323464498307)
  ·
    refine ⟨383740656017904485196747461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255827104011936323464498307 383740656017904485196747461)
    ·
      refine ⟨71951373003357090974390149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 383740656017904485196747461 71951373003357090974390149)
      ·
        refine ⟨13490882438129454557698153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71951373003357090974390149 13490882438129454557698153)
        ·
          refine ⟨10118161828597090918273615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13490882438129454557698153 10118161828597090918273615)
          ·
            refine ⟨15177242742895636377410423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10118161828597090918273615 15177242742895636377410423)
            ·
              refine ⟨22765864114343454566115635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15177242742895636377410423 22765864114343454566115635)
              ·
                refine ⟨34148796171515181849173453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22765864114343454566115635 34148796171515181849173453)
                ·
                  refine ⟨12805798564318193193440045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34148796171515181849173453 12805798564318193193440045)
                  ·
                    refine ⟨4802174461619322447540017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12805798564318193193440045 4802174461619322447540017)
                    ·
                      refine ⟨3601630846214491835655013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4802174461619322447540017 3601630846214491835655013)
                      ·
                        rfl

theorem cell23_7014151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_7014151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014151 prefixEnd_7014151 := by exact prefixLift 7014151
  have htrace : WordTrace (prefixWord ++ tailWord_7014151) baseStart_7014151 baseEnd_7014151 := by
    simpa [prefixWord, tailWord_7014151, baseEnd_7014151] using wordTrace_append hprefix tailTrace_7014151
  have hstable : (prefixWord ++ tailWord_7014151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014151).length < 2 ^ (prefixWord ++ tailWord_7014151).sum := by decide
  have hdescent : baseEnd_7014151 < baseStart_7014151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014167 : List Nat := [1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 5]
def baseStart_7014167 : Nat := 118140960795 + 7014167 * 2 ^ 59
def prefixEnd_7014167 : Nat := 4983230072969 + 3 ^ 40 * 7014167 * 2
def baseEnd_7014167 : Nat := 3601639061904963773054939

theorem tailTrace_7014167 : CollatzResearch.WordTrace tailWord_7014167 prefixEnd_7014167 3601639061904963773054939 := by
  unfold tailWord_7014167
  simp only [CollatzResearch.WordTrace]
  refine ⟨255827687579878358197080755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170551791719918905464720503 255827687579878358197080755)
  ·
    refine ⟨383741531369817537295621133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255827687579878358197080755 383741531369817537295621133)
    ·
      refine ⟨143903074263681576485857925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383741531369817537295621133 143903074263681576485857925)
      ·
        refine ⟨26981826424440295591098361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 143903074263681576485857925 26981826424440295591098361)
        ·
          refine ⟨20236369818330221693323771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26981826424440295591098361 20236369818330221693323771)
          ·
            refine ⟨30354554727495332539985657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20236369818330221693323771 30354554727495332539985657)
            ·
              refine ⟨22765916045621499404989243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30354554727495332539985657 22765916045621499404989243)
              ·
                refine ⟨34148874068432249107483865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22765916045621499404989243 34148874068432249107483865)
                ·
                  refine ⟨25611655551324186830612899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34148874068432249107483865 25611655551324186830612899)
                  ·
                    refine ⟨38417483326986280245919349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25611655551324186830612899 38417483326986280245919349)
                    ·
                      refine ⟨3601639061904963773054939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38417483326986280245919349 3601639061904963773054939)
                      ·
                        rfl

theorem cell23_7014167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_7014167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014167 prefixEnd_7014167 := by exact prefixLift 7014167
  have htrace : WordTrace (prefixWord ++ tailWord_7014167) baseStart_7014167 baseEnd_7014167 := by
    simpa [prefixWord, tailWord_7014167, baseEnd_7014167] using wordTrace_append hprefix tailTrace_7014167
  have hstable : (prefixWord ++ tailWord_7014167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014167).length < 2 ^ (prefixWord ++ tailWord_7014167).sum := by decide
  have hdescent : baseEnd_7014167 < baseStart_7014167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014181 : List Nat := [1, 3, 1, 2, 3, 2, 1, 4, 2, 2, 2]
def baseStart_7014181 : Nat := 118140960795 + 7014181 * 2 ^ 59
def prefixEnd_7014181 : Nat := 4983230072969 + 3 ^ 40 * 7014181 * 2
def baseEnd_7014181 : Nat := 3601646250634126718279875

theorem tailTrace_7014181 : CollatzResearch.WordTrace tailWord_7014181 prefixEnd_7014181 3601646250634126718279875 := by
  unfold tailWord_7014181
  simp only [CollatzResearch.WordTrace]
  refine ⟨255828198201827638588090397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170552132134551759058726931 255828198201827638588090397)
  ·
    refine ⟨95935574325685364470533899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255828198201827638588090397 95935574325685364470533899)
    ·
      refine ⟨143903361488528046705800849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95935574325685364470533899 143903361488528046705800849)
      ·
        refine ⟨107927521116396035029350637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143903361488528046705800849 107927521116396035029350637)
        ·
          refine ⟨40472820418648513136006489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107927521116396035029350637 40472820418648513136006489)
          ·
            refine ⟨30354615313986384852004867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40472820418648513136006489 30354615313986384852004867)
            ·
              refine ⟨45531922970979577278007301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30354615313986384852004867 45531922970979577278007301)
              ·
                refine ⟨8537235557058670739626369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45531922970979577278007301 8537235557058670739626369)
                ·
                  refine ⟨6402926667794003054719777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8537235557058670739626369 6402926667794003054719777)
                  ·
                    refine ⟨4802195000845502291039833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6402926667794003054719777 4802195000845502291039833)
                    ·
                      refine ⟨3601646250634126718279875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4802195000845502291039833 3601646250634126718279875)
                      ·
                        rfl

theorem cell23_7014181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2, 2, 2].length) (baseStart_7014181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014181 prefixEnd_7014181 := by exact prefixLift 7014181
  have htrace : WordTrace (prefixWord ++ tailWord_7014181) baseStart_7014181 baseEnd_7014181 := by
    simpa [prefixWord, tailWord_7014181, baseEnd_7014181] using wordTrace_append hprefix tailTrace_7014181
  have hstable : (prefixWord ++ tailWord_7014181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014181).length < 2 ^ (prefixWord ++ tailWord_7014181).sum := by decide
  have hdescent : baseEnd_7014181 < baseStart_7014181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014198 : List Nat := [5, 1, 2, 2, 1, 2, 2, 1, 1, 4, 2]
def baseStart_7014198 : Nat := 118140960795 + 7014198 * 2 ^ 59
def prefixEnd_7014198 : Nat := 4983230072969 + 3 ^ 40 * 7014198 * 2
def baseEnd_7014198 : Nat := 3601654979805253151767297

theorem tailTrace_7014198 : CollatzResearch.WordTrace tailWord_7014198 prefixEnd_7014198 3601654979805253151767297 := by
  unfold tailWord_7014198
  simp only [CollatzResearch.WordTrace]
  refine ⟨15989301140172878155716203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 170552545495177366994306165 15989301140172878155716203)
  ·
    refine ⟨23983951710259317233574305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15989301140172878155716203 23983951710259317233574305)
    ·
      refine ⟨17987963782694487925180729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23983951710259317233574305 17987963782694487925180729)
      ·
        refine ⟨13490972837020865943885547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17987963782694487925180729 13490972837020865943885547)
        ·
          refine ⟨20236459255531298915828321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13490972837020865943885547 20236459255531298915828321)
          ·
            refine ⟨15177344441648474186871241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20236459255531298915828321 15177344441648474186871241)
            ·
              refine ⟨11383008331236355640153431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15177344441648474186871241 11383008331236355640153431)
              ·
                refine ⟨17074512496854533460230147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11383008331236355640153431 17074512496854533460230147)
                ·
                  refine ⟨25611768745281800190345221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17074512496854533460230147 25611768745281800190345221)
                  ·
                    refine ⟨4802206639740337535689729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25611768745281800190345221 4802206639740337535689729)
                    ·
                      refine ⟨3601654979805253151767297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4802206639740337535689729 3601654979805253151767297)
                      ·
                        rfl

theorem cell23_7014198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_7014198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014198 prefixEnd_7014198 := by exact prefixLift 7014198
  have htrace : WordTrace (prefixWord ++ tailWord_7014198) baseStart_7014198 baseEnd_7014198 := by
    simpa [prefixWord, tailWord_7014198, baseEnd_7014198] using wordTrace_append hprefix tailTrace_7014198
  have hstable : (prefixWord ++ tailWord_7014198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014198).length < 2 ^ (prefixWord ++ tailWord_7014198).sum := by decide
  have hdescent : baseEnd_7014198 < baseStart_7014198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014221 : List Nat := [1, 6, 1, 2, 1, 1, 1, 5, 5]
def baseStart_7014221 : Nat := 118140960795 + 7014221 * 2 ^ 59
def prefixEnd_7014221 : Nat := 4983230072969 + 3 ^ 40 * 7014221 * 2
def baseEnd_7014221 : Nat := 400185198873367395753299

theorem tailTrace_7014221 : CollatzResearch.WordTrace tailWord_7014221 prefixEnd_7014221 400185198873367395753299 := by
  unfold tailWord_7014221
  simp only [CollatzResearch.WordTrace]
  refine ⟨255829657121682725419546517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170553104747788483613031011 255829657121682725419546517)
  ·
    refine ⟨11992015177578877754041243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 255829657121682725419546517 11992015177578877754041243)
    ·
      refine ⟨17988022766368316631061865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11992015177578877754041243 17988022766368316631061865)
      ·
        refine ⟨13491017074776237473296399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17988022766368316631061865 13491017074776237473296399)
        ·
          refine ⟨20236525612164356209944599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13491017074776237473296399 20236525612164356209944599)
          ·
            refine ⟨30354788418246534314916899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20236525612164356209944599 30354788418246534314916899)
            ·
              refine ⟨45532182627369801472375349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30354788418246534314916899 45532182627369801472375349)
              ·
                refine ⟨4268642121315918888035189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45532182627369801472375349 4268642121315918888035189)
                ·
                  refine ⟨400185198873367395753299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4268642121315918888035189 400185198873367395753299)
                  ·
                    rfl

theorem cell23_7014221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_7014221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014221 prefixEnd_7014221 := by exact prefixLift 7014221
  have htrace : WordTrace (prefixWord ++ tailWord_7014221) baseStart_7014221 baseEnd_7014221 := by
    simpa [prefixWord, tailWord_7014221, baseEnd_7014221] using wordTrace_append hprefix tailTrace_7014221
  have hstable : (prefixWord ++ tailWord_7014221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014221).length < 2 ^ (prefixWord ++ tailWord_7014221).sum := by decide
  have hdescent : baseEnd_7014221 < baseStart_7014221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014254 : List Nat := [4, 1, 2, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_7014254 : Nat := 118140960795 + 7014254 * 2 ^ 59
def prefixEnd_7014254 : Nat := 4983230072969 + 3 ^ 40 * 7014254 * 2
def baseEnd_7014254 : Nat := 3601683734721904932667039

theorem tailTrace_7014254 : CollatzResearch.WordTrace tailWord_7014254 prefixEnd_7014254 3601683734721904932667039 := by
  unfold tailWord_7014254
  simp only [CollatzResearch.WordTrace]
  refine ⟨31978857591320396506937227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170553907153708781370331877 31978857591320396506937227)
  ·
    refine ⟨47968286386980594760405841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31978857591320396506937227 47968286386980594760405841)
    ·
      refine ⟨35976214790235446070304381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47968286386980594760405841 35976214790235446070304381)
      ·
        refine ⟨13491080546338292276364143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35976214790235446070304381 13491080546338292276364143)
        ·
          refine ⟨20236620819507438414546215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13491080546338292276364143 20236620819507438414546215)
          ·
            refine ⟨30354931229261157621819323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20236620819507438414546215 30354931229261157621819323)
            ·
              refine ⟨45532396843891736432728985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30354931229261157621819323 45532396843891736432728985)
              ·
                refine ⟨34149297632918802324546739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45532396843891736432728985 34149297632918802324546739)
                ·
                  refine ⟨51223946449378203486820109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34149297632918802324546739 51223946449378203486820109)
                  ·
                    refine ⟨19208979918516826307557541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51223946449378203486820109 19208979918516826307557541)
                    ·
                      refine ⟨3601683734721904932667039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19208979918516826307557541 3601683734721904932667039)
                      ·
                        rfl

theorem cell23_7014254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_7014254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014254 prefixEnd_7014254 := by exact prefixLift 7014254
  have htrace : WordTrace (prefixWord ++ tailWord_7014254) baseStart_7014254 baseEnd_7014254 := by
    simpa [prefixWord, tailWord_7014254, baseEnd_7014254] using wordTrace_append hprefix tailTrace_7014254
  have hstable : (prefixWord ++ tailWord_7014254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014254).length < 2 ^ (prefixWord ++ tailWord_7014254).sum := by decide
  have hdescent : baseEnd_7014254 < baseStart_7014254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014257 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 3, 4, 3]
def baseStart_7014257 : Nat := 118140960795 + 7014257 * 2 ^ 59
def prefixEnd_7014257 : Nat := 4983230072969 + 3 ^ 40 * 7014257 * 2
def baseEnd_7014257 : Nat := 3601685275163868420929525

theorem tailTrace_7014257 : CollatzResearch.WordTrace tailWord_7014257 prefixEnd_7014257 3601685275163868420929525 := by
  unfold tailWord_7014257
  simp only [CollatzResearch.WordTrace]
  refine ⟨255830970149552303567857025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170553980099701535711904683 255830970149552303567857025)
  ·
    refine ⟨191873227612164227675892769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255830970149552303567857025 191873227612164227675892769)
    ·
      refine ⟨143904920709123170756919577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191873227612164227675892769 143904920709123170756919577)
      ·
        refine ⟨107928690531842378067689683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143904920709123170756919577 107928690531842378067689683)
        ·
          refine ⟨161893035797763567101534525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107928690531842378067689683 161893035797763567101534525)
          ·
            refine ⟨60709888424161337663075447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161893035797763567101534525 60709888424161337663075447)
            ·
              refine ⟨91064832636242006494613171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60709888424161337663075447 91064832636242006494613171)
              ·
                refine ⟨136597248954363009741919757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91064832636242006494613171 136597248954363009741919757)
                ·
                  refine ⟨51223968357886128653219909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 136597248954363009741919757 51223968357886128653219909)
                  ·
                    refine ⟨9604494067103649122478733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51223968357886128653219909 9604494067103649122478733)
                    ·
                      refine ⟨3601685275163868420929525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9604494067103649122478733 3601685275163868420929525)
                      ·
                        rfl

theorem cell23_7014257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_7014257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014257 prefixEnd_7014257 := by exact prefixLift 7014257
  have htrace : WordTrace (prefixWord ++ tailWord_7014257) baseStart_7014257 baseEnd_7014257 := by
    simpa [prefixWord, tailWord_7014257, baseEnd_7014257] using wordTrace_append hprefix tailTrace_7014257
  have hstable : (prefixWord ++ tailWord_7014257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014257).length < 2 ^ (prefixWord ++ tailWord_7014257).sum := by decide
  have hdescent : baseEnd_7014257 < baseStart_7014257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014307 : List Nat := [1, 1, 1, 4, 1, 2, 1, 4, 3, 5]
def baseStart_7014307 : Nat := 118140960795 + 7014307 * 2 ^ 59
def prefixEnd_7014307 : Nat := 4983230072969 + 3 ^ 40 * 7014307 * 2
def baseEnd_7014307 : Nat := 1200570316398864408434765

theorem tailTrace_7014307 : CollatzResearch.WordTrace tailWord_7014307 prefixEnd_7014307 1200570316398864408434765 := by
  unfold tailWord_7014307
  simp only [CollatzResearch.WordTrace]
  refine ⟨255832793799371162107177175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170555195866247441404784783 255832793799371162107177175)
  ·
    refine ⟨383749190699056743160765763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255832793799371162107177175 383749190699056743160765763)
    ·
      refine ⟨575623786048585114741148645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383749190699056743160765763 575623786048585114741148645)
      ·
        refine ⟨107929459884109709013965371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 575623786048585114741148645 107929459884109709013965371)
        ·
          refine ⟨161894189826164563520948057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107929459884109709013965371 161894189826164563520948057)
          ·
            refine ⟨121420642369623422640711043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161894189826164563520948057 121420642369623422640711043)
            ·
              refine ⟨182130963554435133961066565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121420642369623422640711043 182130963554435133961066565)
              ·
                refine ⟨34149555666456587617699981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182130963554435133961066565 34149555666456587617699981)
                ·
                  refine ⟨12806083374921220356637493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34149555666456587617699981 12806083374921220356637493)
                  ·
                    refine ⟨1200570316398864408434765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12806083374921220356637493 1200570316398864408434765)
                    ·
                      rfl

theorem cell23_7014307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 5].length) (baseStart_7014307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014307 prefixEnd_7014307 := by exact prefixLift 7014307
  have htrace : WordTrace (prefixWord ++ tailWord_7014307) baseStart_7014307 baseEnd_7014307 := by
    simpa [prefixWord, tailWord_7014307, baseEnd_7014307] using wordTrace_append hprefix tailTrace_7014307
  have hstable : (prefixWord ++ tailWord_7014307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014307).length < 2 ^ (prefixWord ++ tailWord_7014307).sum := by decide
  have hdescent : baseEnd_7014307 < baseStart_7014307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014311 : List Nat := [1, 1, 6, 1, 2, 1, 4, 1, 6]
def baseStart_7014311 : Nat := 118140960795 + 7014311 * 2 ^ 59
def prefixEnd_7014311 : Nat := 4983230072969 + 3 ^ 40 * 7014311 * 2
def baseEnd_7014311 : Nat := 400190333679912356628253

theorem tailTrace_7014311 : CollatzResearch.WordTrace tailWord_7014311 prefixEnd_7014311 400190333679912356628253 := by
  unfold tailWord_7014311
  simp only [CollatzResearch.WordTrace]
  refine ⟨255832939691356670790322787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170555293127571113860215191 255832939691356670790322787)
  ·
    refine ⟨383749409537035006185484181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255832939691356670790322787 383749409537035006185484181)
    ·
      refine ⟨17988253572048515914944571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 383749409537035006185484181 17988253572048515914944571)
      ·
        refine ⟨26982380358072773872416857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17988253572048515914944571 26982380358072773872416857)
        ·
          refine ⟨20236785268554580404312643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26982380358072773872416857 20236785268554580404312643)
          ·
            refine ⟨30355177902831870606468965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20236785268554580404312643 30355177902831870606468965)
            ·
              refine ⟨5691595856780975738712931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30355177902831870606468965 5691595856780975738712931)
              ·
                refine ⟨8537393785171463608069397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5691595856780975738712931 8537393785171463608069397)
                ·
                  refine ⟨400190333679912356628253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8537393785171463608069397 400190333679912356628253)
                  ·
                    rfl

theorem cell23_7014311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 6].length) (baseStart_7014311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014311 prefixEnd_7014311 := by exact prefixLift 7014311
  have htrace : WordTrace (prefixWord ++ tailWord_7014311) baseStart_7014311 baseEnd_7014311 := by
    simpa [prefixWord, tailWord_7014311, baseEnd_7014311] using wordTrace_append hprefix tailTrace_7014311
  have hstable : (prefixWord ++ tailWord_7014311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014311).length < 2 ^ (prefixWord ++ tailWord_7014311).sum := by decide
  have hdescent : baseEnd_7014311 < baseStart_7014311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014371 : List Nat := [1, 1, 1, 6, 1, 2, 2, 3, 2, 4]
def baseStart_7014371 : Nat := 118140960795 + 7014371 * 2 ^ 59
def prefixEnd_7014371 : Nat := 4983230072969 + 3 ^ 40 * 7014371 * 2
def baseEnd_7014371 : Nat := 1200581270652826991634667

theorem tailTrace_7014371 : CollatzResearch.WordTrace tailWord_7014371 prefixEnd_7014371 1200581270652826991634667 := by
  unfold tailWord_7014371
  simp only [CollatzResearch.WordTrace]
  refine ⟨255835128071139301037506967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170556752047426200691671311 255835128071139301037506967)
  ·
    refine ⟨383752692106708951556260451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255835128071139301037506967 383752692106708951556260451)
    ·
      refine ⟨575629038160063427334390677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383752692106708951556260451 575629038160063427334390677)
      ·
        refine ⟨26982611163752973156299563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 575629038160063427334390677 26982611163752973156299563)
        ·
          refine ⟨40473916745629459734449345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26982611163752973156299563 40473916745629459734449345)
          ·
            refine ⟨30355437559222094800837009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40473916745629459734449345 30355437559222094800837009)
            ·
              refine ⟨22766578169416571100627757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30355437559222094800837009 22766578169416571100627757)
              ·
                refine ⟨8537466813531214162735409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22766578169416571100627757 8537466813531214162735409)
                ·
                  refine ⟨6403100110148410622051557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8537466813531214162735409 6403100110148410622051557)
                  ·
                    refine ⟨1200581270652826991634667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6403100110148410622051557 1200581270652826991634667)
                    ·
                      rfl

theorem cell23_7014371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2, 4].length) (baseStart_7014371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014371 prefixEnd_7014371 := by exact prefixLift 7014371
  have htrace : WordTrace (prefixWord ++ tailWord_7014371) baseStart_7014371 baseEnd_7014371 := by
    simpa [prefixWord, tailWord_7014371, baseEnd_7014371] using wordTrace_append hprefix tailTrace_7014371
  have hstable : (prefixWord ++ tailWord_7014371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014371).length < 2 ^ (prefixWord ++ tailWord_7014371).sum := by decide
  have hdescent : baseEnd_7014371 < baseStart_7014371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014378 : List Nat := [3, 1, 3, 1, 2, 1, 3, 2, 3, 2, 2]
def baseStart_7014378 : Nat := 118140960795 + 7014378 * 2 ^ 59
def prefixEnd_7014378 : Nat := 4983230072969 + 3 ^ 40 * 7014378 * 2
def baseEnd_7014378 : Nat := 3601747406323062447516469

theorem tailTrace_7014378 : CollatzResearch.WordTrace tailWord_7014378 prefixEnd_7014378 3601747406323062447516469 := by
  unfold tailWord_7014378
  simp only [CollatzResearch.WordTrace]
  refine ⟨63958845845528485308252947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170556922254742627488674525 63958845845528485308252947)
  ·
    refine ⟨95938268768292727962379421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63958845845528485308252947 95938268768292727962379421)
    ·
      refine ⟨35976850788109772985892283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95938268768292727962379421 35976850788109772985892283)
      ·
        refine ⟨53965276182164659478838425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35976850788109772985892283 53965276182164659478838425)
        ·
          refine ⟨40473957136623494609128819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53965276182164659478838425 40473957136623494609128819)
          ·
            refine ⟨60710935704935241913693229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40473957136623494609128819 60710935704935241913693229)
            ·
              refine ⟨22766600889350715717634961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60710935704935241913693229 22766600889350715717634961)
              ·
                refine ⟨17074950667013036788226221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22766600889350715717634961 17074950667013036788226221)
                ·
                  refine ⟨6403106500129888795584833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17074950667013036788226221 6403106500129888795584833)
                  ·
                    refine ⟨4802329875097416596688625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6403106500129888795584833 4802329875097416596688625)
                    ·
                      refine ⟨3601747406323062447516469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4802329875097416596688625 3601747406323062447516469)
                      ·
                        rfl

theorem cell23_7014378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_7014378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014378 prefixEnd_7014378 := by exact prefixLift 7014378
  have htrace : WordTrace (prefixWord ++ tailWord_7014378) baseStart_7014378 baseEnd_7014378 := by
    simpa [prefixWord, tailWord_7014378, baseEnd_7014378] using wordTrace_append hprefix tailTrace_7014378
  have hstable : (prefixWord ++ tailWord_7014378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014378).length < 2 ^ (prefixWord ++ tailWord_7014378).sum := by decide
  have hdescent : baseEnd_7014378 < baseStart_7014378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014411 : List Nat := [1, 1, 1, 1, 6, 1, 3, 1, 4, 1, 3]
def baseStart_7014411 : Nat := 118140960795 + 7014411 * 2 ^ 59
def prefixEnd_7014411 : Nat := 4983230072969 + 3 ^ 40 * 7014411 * 2
def baseEnd_7014411 : Nat := 3601764351184660818403817

theorem tailTrace_7014411 : CollatzResearch.WordTrace tailWord_7014411 prefixEnd_7014411 3601764351184660818403817 := by
  unfold tailWord_7014411
  simp only [CollatzResearch.WordTrace]
  refine ⟨255836586990994387868963087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170557724660662925245975391 255836586990994387868963087)
  ·
    refine ⟨383754880486491581803444631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255836586990994387868963087 383754880486491581803444631)
    ·
      refine ⟨575632320729737372705166947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383754880486491581803444631 575632320729737372705166947)
      ·
        refine ⟨863448481094606059057750421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575632320729737372705166947 863448481094606059057750421)
        ·
          refine ⟨40474147551309659018332051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 863448481094606059057750421 40474147551309659018332051)
          ·
            refine ⟨60711221326964488527498077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40474147551309659018332051 60711221326964488527498077)
            ·
              refine ⟨22766707997611683197811779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60711221326964488527498077 22766707997611683197811779)
              ·
                refine ⟨34150061996417524796717669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22766707997611683197811779 34150061996417524796717669)
                ·
                  refine ⟨6403136624328285899384563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34150061996417524796717669 6403136624328285899384563)
                  ·
                    refine ⟨9604704936492428849076845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6403136624328285899384563 9604704936492428849076845)
                    ·
                      refine ⟨3601764351184660818403817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9604704936492428849076845 3601764351184660818403817)
                      ·
                        rfl

theorem cell23_7014411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4, 1, 3].length) (baseStart_7014411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014411 prefixEnd_7014411 := by exact prefixLift 7014411
  have htrace : WordTrace (prefixWord ++ tailWord_7014411) baseStart_7014411 baseEnd_7014411 := by
    simpa [prefixWord, tailWord_7014411, baseEnd_7014411] using wordTrace_append hprefix tailTrace_7014411
  have hstable : (prefixWord ++ tailWord_7014411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014411).length < 2 ^ (prefixWord ++ tailWord_7014411).sum := by decide
  have hdescent : baseEnd_7014411 < baseStart_7014411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014427 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 1, 8]
def baseStart_7014427 : Nat := 118140960795 + 7014427 * 2 ^ 59
def prefixEnd_7014427 : Nat := 4983230072969 + 3 ^ 40 * 7014427 * 2
def baseEnd_7014427 : Nat := 1200590855625044251934581

theorem tailTrace_7014427 : CollatzResearch.WordTrace tailWord_7014427 prefixEnd_7014427 1200590855625044251934581 := by
  unfold tailWord_7014427
  simp only [CollatzResearch.WordTrace]
  refine ⟨255837170558936422601545535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170558113705957615067697023 255837170558936422601545535)
  ·
    refine ⟨383755755838404633902318303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255837170558936422601545535 383755755838404633902318303)
    ·
      refine ⟨575633633757606950853477455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383755755838404633902318303 575633633757606950853477455)
      ·
        refine ⟨863450450636410426280216183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575633633757606950853477455 863450450636410426280216183)
        ·
          refine ⟨1295175675954615639420324275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 863450450636410426280216183 1295175675954615639420324275)
          ·
            refine ⟨1942763513931923459130486413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1295175675954615639420324275 1942763513931923459130486413)
            ·
              refine ⟨728536317724471297173932405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1942763513931923459130486413 728536317724471297173932405)
              ·
                refine ⟨68300279786669184110056163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 728536317724471297173932405 68300279786669184110056163)
                ·
                  refine ⟨102450419680003776165084245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68300279786669184110056163 102450419680003776165084245)
                  ·
                    refine ⟨1200590855625044251934581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102450419680003776165084245 1200590855625044251934581)
                    ·
                      rfl

theorem cell23_7014427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 8].length) (baseStart_7014427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014427 prefixEnd_7014427 := by exact prefixLift 7014427
  have htrace : WordTrace (prefixWord ++ tailWord_7014427) baseStart_7014427 baseEnd_7014427 := by
    simpa [prefixWord, tailWord_7014427, baseEnd_7014427] using wordTrace_append hprefix tailTrace_7014427
  have hstable : (prefixWord ++ tailWord_7014427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014427).length < 2 ^ (prefixWord ++ tailWord_7014427).sum := by decide
  have hdescent : baseEnd_7014427 < baseStart_7014427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014428 : List Nat := [2, 2, 3, 1, 3, 3, 1, 1, 1, 3, 3]
def baseStart_7014428 : Nat := 118140960795 + 7014428 * 2 ^ 59
def prefixEnd_7014428 : Nat := 4983230072969 + 3 ^ 40 * 7014428 * 2
def baseEnd_7014428 : Nat := 3601773080355787251891239

theorem tailTrace_7014428 : CollatzResearch.WordTrace tailWord_7014428 prefixEnd_7014428 3601773080355787251891239 := by
  unfold tailWord_7014428
  simp only [CollatzResearch.WordTrace]
  refine ⟨127918603515966399886165969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170558138021288533181554625 127918603515966399886165969)
  ·
    refine ⟨95938952636974799914624477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127918603515966399886165969 95938952636974799914624477)
    ·
      refine ⟨35977107238865549967984179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95938952636974799914624477 35977107238865549967984179)
      ·
        refine ⟨53965660858298324951976269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35977107238865549967984179 53965660858298324951976269)
        ·
          refine ⟨20237122821861871856991101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53965660858298324951976269 20237122821861871856991101)
          ·
            refine ⟨7588921058198201946371663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20237122821861871856991101 7588921058198201946371663)
            ·
              refine ⟨11383381587297302919557495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7588921058198201946371663 11383381587297302919557495)
              ·
                refine ⟨17075072380945954379336243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11383381587297302919557495 17075072380945954379336243)
                ·
                  refine ⟨25612608571418931569004365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17075072380945954379336243 25612608571418931569004365)
                  ·
                    refine ⟨9604728214282099338376637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25612608571418931569004365 9604728214282099338376637)
                    ·
                      refine ⟨3601773080355787251891239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9604728214282099338376637 3601773080355787251891239)
                      ·
                        rfl

theorem cell23_7014428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_7014428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014428 prefixEnd_7014428 := by exact prefixLift 7014428
  have htrace : WordTrace (prefixWord ++ tailWord_7014428) baseStart_7014428 baseEnd_7014428 := by
    simpa [prefixWord, tailWord_7014428, baseEnd_7014428] using wordTrace_append hprefix tailTrace_7014428
  have hstable : (prefixWord ++ tailWord_7014428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014428).length < 2 ^ (prefixWord ++ tailWord_7014428).sum := by decide
  have hdescent : baseEnd_7014428 < baseStart_7014428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014451 : List Nat := [1, 1, 1, 2, 4, 1, 2, 4, 1, 4, 2]
def baseStart_7014451 : Nat := 118140960795 + 7014451 * 2 ^ 59
def prefixEnd_7014451 : Nat := 4983230072969 + 3 ^ 40 * 7014451 * 2
def baseEnd_7014451 : Nat := 3601784890410840661903633

theorem tailTrace_7014451 : CollatzResearch.WordTrace tailWord_7014451 prefixEnd_7014451 3601784890410840661903633 := by
  unfold tailWord_7014451
  simp only [CollatzResearch.WordTrace]
  refine ⟨255838045910849474700419207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170558697273899649800279471 255838045910849474700419207)
  ·
    refine ⟨383757068866274212050628811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255838045910849474700419207 383757068866274212050628811)
    ·
      refine ⟨575635603299411318075943217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383757068866274212050628811 575635603299411318075943217)
      ·
        refine ⟨431726702474558488556957413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 575635603299411318075943217 431726702474558488556957413)
        ·
          refine ⟨80948756713979716604429515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 431726702474558488556957413 80948756713979716604429515)
          ·
            refine ⟨121423135070969574906644273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80948756713979716604429515 121423135070969574906644273)
            ·
              refine ⟨91067351303227181179983205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121423135070969574906644273 91067351303227181179983205)
              ·
                refine ⟨17075128369355096471246851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91067351303227181179983205 17075128369355096471246851)
                ·
                  refine ⟨25612692554032644706870277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17075128369355096471246851 25612692554032644706870277)
                  ·
                    refine ⟨4802379853881120882538177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25612692554032644706870277 4802379853881120882538177)
                    ·
                      refine ⟨3601784890410840661903633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4802379853881120882538177 3601784890410840661903633)
                      ·
                        rfl

theorem cell23_7014451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 4, 2].length) (baseStart_7014451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014451 prefixEnd_7014451 := by exact prefixLift 7014451
  have htrace : WordTrace (prefixWord ++ tailWord_7014451) baseStart_7014451 baseEnd_7014451 := by
    simpa [prefixWord, tailWord_7014451, baseEnd_7014451] using wordTrace_append hprefix tailTrace_7014451
  have hstable : (prefixWord ++ tailWord_7014451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014451).length < 2 ^ (prefixWord ++ tailWord_7014451).sum := by decide
  have hdescent : baseEnd_7014451 < baseStart_7014451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014485 : List Nat := [1, 3, 2, 2, 1, 4, 1, 3, 2, 2, 2]
def baseStart_7014485 : Nat := 118140960795 + 7014485 * 2 ^ 59
def prefixEnd_7014485 : Nat := 4983230072969 + 3 ^ 40 * 7014485 * 2
def baseEnd_7014485 : Nat := 3601802348753093528878477

theorem tailTrace_7014485 : CollatzResearch.WordTrace tailWord_7014485 prefixEnd_7014485 3601802348753093528878477 := by
  unfold tailWord_7014485
  simp only [CollatzResearch.WordTrace]
  refine ⟨255839285992726298507156909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170559523995150865671437939 255839285992726298507156909)
  ·
    refine ⟨95939732247272361940183841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 255839285992726298507156909 95939732247272361940183841)
    ·
      refine ⟨71954799185454271455137881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95939732247272361940183841 71954799185454271455137881)
      ·
        refine ⟨53966099389090703591353411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71954799185454271455137881 53966099389090703591353411)
        ·
          refine ⟨80949149083636055387030117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53966099389090703591353411 80949149083636055387030117)
          ·
            refine ⟨15177965453181760385068147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80949149083636055387030117 15177965453181760385068147)
            ·
              refine ⟨22766948179772640577602221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15177965453181760385068147 22766948179772640577602221)
              ·
                refine ⟨8537605567414740216600833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22766948179772640577602221 8537605567414740216600833)
                ·
                  refine ⟨6403204175561055162450625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8537605567414740216600833 6403204175561055162450625)
                  ·
                    refine ⟨4802403131670791371837969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6403204175561055162450625 4802403131670791371837969)
                    ·
                      refine ⟨3601802348753093528878477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4802403131670791371837969 3601802348753093528878477)
                      ·
                        rfl

theorem cell23_7014485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_7014485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014485 prefixEnd_7014485 := by exact prefixLift 7014485
  have htrace : WordTrace (prefixWord ++ tailWord_7014485) baseStart_7014485 baseEnd_7014485 := by
    simpa [prefixWord, tailWord_7014485, baseEnd_7014485] using wordTrace_append hprefix tailTrace_7014485
  have hstable : (prefixWord ++ tailWord_7014485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014485).length < 2 ^ (prefixWord ++ tailWord_7014485).sum := by decide
  have hdescent : baseEnd_7014485 < baseStart_7014485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014521 : List Nat := [1, 2, 1, 3, 4, 1, 2, 2, 2, 5]
def baseStart_7014521 : Nat := 118140960795 + 7014521 * 2 ^ 59
def prefixEnd_7014521 : Nat := 4983230072969 + 3 ^ 40 * 7014521 * 2
def baseEnd_7014521 : Nat := 1200606944685551796009437

theorem tailTrace_7014521 : CollatzResearch.WordTrace tailWord_7014521 prefixEnd_7014521 1200606944685551796009437 := by
  unfold tailWord_7014521
  simp only [CollatzResearch.WordTrace]
  refine ⟨255840599020595876655467417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170560399347063917770311611 255840599020595876655467417)
  ·
    refine ⟨191880449265446907491600563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255840599020595876655467417 191880449265446907491600563)
    ·
      refine ⟨287820673898170361237400845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191880449265446907491600563 287820673898170361237400845)
      ·
        refine ⟨107932752711813885464025317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287820673898170361237400845 107932752711813885464025317)
        ·
          refine ⟨20237391133465103524504747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107932752711813885464025317 20237391133465103524504747)
          ·
            refine ⟨30356086700197655286757121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20237391133465103524504747 30356086700197655286757121)
            ·
              refine ⟨22767065025148241465067841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30356086700197655286757121 22767065025148241465067841)
              ·
                refine ⟨17075298768861181098800881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22767065025148241465067841 17075298768861181098800881)
                ·
                  refine ⟨12806474076645885824100661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17075298768861181098800881 12806474076645885824100661)
                  ·
                    refine ⟨1200606944685551796009437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12806474076645885824100661 1200606944685551796009437)
                    ·
                      rfl

theorem cell23_7014521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 5].length) (baseStart_7014521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014521 prefixEnd_7014521 := by exact prefixLift 7014521
  have htrace : WordTrace (prefixWord ++ tailWord_7014521) baseStart_7014521 baseEnd_7014521 := by
    simpa [prefixWord, tailWord_7014521, baseEnd_7014521] using wordTrace_append hprefix tailTrace_7014521
  have hstable : (prefixWord ++ tailWord_7014521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014521).length < 2 ^ (prefixWord ++ tailWord_7014521).sum := by decide
  have hdescent : baseEnd_7014521 < baseStart_7014521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014525 : List Nat := [1, 4, 1, 1, 3, 4, 2, 2, 5]
def baseStart_7014525 : Nat := 118140960795 + 7014525 * 2 ^ 59
def prefixEnd_7014525 : Nat := 4983230072969 + 3 ^ 40 * 7014525 * 2
def baseEnd_7014525 : Nat := 400202543108808152486477

theorem tailTrace_7014525 : CollatzResearch.WordTrace tailWord_7014525 prefixEnd_7014525 400202543108808152486477 := by
  unfold tailWord_7014525
  simp only [CollatzResearch.WordTrace]
  refine ⟨255840744912581385338613029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170560496608387590225742019 255840744912581385338613029)
  ·
    refine ⟨47970139671109009750989943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 255840744912581385338613029 47970139671109009750989943)
    ·
      refine ⟨71955209506663514626484915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47970139671109009750989943 71955209506663514626484915)
      ·
        refine ⟨107932814259995271939727373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71955209506663514626484915 107932814259995271939727373)
        ·
          refine ⟨40474805347498226977397765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107932814259995271939727373 40474805347498226977397765)
          ·
            refine ⟨7589026002655917558262081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40474805347498226977397765 7589026002655917558262081)
            ·
              refine ⟨5691769501991938168696561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7589026002655917558262081 5691769501991938168696561)
              ·
                refine ⟨4268827126493953626522421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5691769501991938168696561 4268827126493953626522421)
                ·
                  refine ⟨400202543108808152486477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4268827126493953626522421 400202543108808152486477)
                  ·
                    rfl

theorem cell23_7014525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 2, 5].length) (baseStart_7014525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014525 prefixEnd_7014525 := by exact prefixLift 7014525
  have htrace : WordTrace (prefixWord ++ tailWord_7014525) baseStart_7014525 baseEnd_7014525 := by
    simpa [prefixWord, tailWord_7014525, baseEnd_7014525] using wordTrace_append hprefix tailTrace_7014525
  have hstable : (prefixWord ++ tailWord_7014525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014525).length < 2 ^ (prefixWord ++ tailWord_7014525).sum := by decide
  have hdescent : baseEnd_7014525 < baseStart_7014525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014584 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 1, 1, 8]
def baseStart_7014584 : Nat := 118140960795 + 7014584 * 2 ^ 59
def prefixEnd_7014584 : Nat := 4983230072969 + 3 ^ 40 * 7014584 * 2
def baseEnd_7014584 : Nat := 3601853183337888641540521

theorem tailTrace_7014584 : CollatzResearch.WordTrace tailWord_7014584 prefixEnd_7014584 3601853183337888641540521 := by
  unfold tailWord_7014584
  simp only [CollatzResearch.WordTrace]
  refine ⟨127921448409683819207505403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170561931212911758943340537 127921448409683819207505403)
  ·
    refine ⟨191882172614525728811258105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127921448409683819207505403 191882172614525728811258105)
    ·
      refine ⟨143911629460894296608443579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191882172614525728811258105 143911629460894296608443579)
      ·
        refine ⟨215867444191341444912665369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143911629460894296608443579 215867444191341444912665369)
        ·
          refine ⟨161900583143506083684499027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215867444191341444912665369 161900583143506083684499027)
          ·
            refine ⟨242850874715259125526748541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161900583143506083684499027 242850874715259125526748541)
            ·
              refine ⟨91069078018222172072530703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242850874715259125526748541 91069078018222172072530703)
              ·
                refine ⟨136603617027333258108796055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91069078018222172072530703 136603617027333258108796055)
                ·
                  refine ⟨204905425540999887163194083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 136603617027333258108796055 204905425540999887163194083)
                  ·
                    refine ⟨307358138311499830744791125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 204905425540999887163194083 307358138311499830744791125)
                    ·
                      refine ⟨3601853183337888641540521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 307358138311499830744791125 3601853183337888641540521)
                      ·
                        rfl

theorem cell23_7014584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_7014584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014584 prefixEnd_7014584 := by exact prefixLift 7014584
  have htrace : WordTrace (prefixWord ++ tailWord_7014584) baseStart_7014584 baseEnd_7014584 := by
    simpa [prefixWord, tailWord_7014584, baseEnd_7014584] using wordTrace_append hprefix tailTrace_7014584
  have hstable : (prefixWord ++ tailWord_7014584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014584).length < 2 ^ (prefixWord ++ tailWord_7014584).sum := by decide
  have hdescent : baseEnd_7014584 < baseStart_7014584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014618 : List Nat := [3, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2]
def baseStart_7014618 : Nat := 118140960795 + 7014618 * 2 ^ 59
def prefixEnd_7014618 : Nat := 4983230072969 + 3 ^ 40 * 7014618 * 2
def baseEnd_7014618 : Nat := 3601870641680141508515365

theorem tailTrace_7014618 : CollatzResearch.WordTrace tailWord_7014618 prefixEnd_7014618 3601870641680141508515365 := by
  unfold tailWord_7014618
  simp only [CollatzResearch.WordTrace]
  refine ⟨63961034225311115555437127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170562757934162974814499005 63961034225311115555437127)
  ·
    refine ⟨95941551337966673333155691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63961034225311115555437127 95941551337966673333155691)
    ·
      refine ⟨143912327006950009999733537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95941551337966673333155691 143912327006950009999733537)
      ·
        refine ⟨107934245255212507499800153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143912327006950009999733537 107934245255212507499800153)
        ·
          refine ⟨80950683941409380624850115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107934245255212507499800153 80950683941409380624850115)
          ·
            refine ⟨121426025912114070937275173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80950683941409380624850115 121426025912114070937275173)
            ·
              refine ⟨22767379858521388300739095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121426025912114070937275173 22767379858521388300739095)
              ·
                refine ⟨34151069787782082451108643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22767379858521388300739095 34151069787782082451108643)
                ·
                  refine ⟨51226604681673123676662965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34151069787782082451108643 51226604681673123676662965)
                  ·
                    refine ⟨4802494188906855344687153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51226604681673123676662965 4802494188906855344687153)
                    ·
                      refine ⟨3601870641680141508515365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4802494188906855344687153 3601870641680141508515365)
                      ·
                        rfl

theorem cell23_7014618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2].length) (baseStart_7014618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014618 prefixEnd_7014618 := by exact prefixLift 7014618
  have htrace : WordTrace (prefixWord ++ tailWord_7014618) baseStart_7014618 baseEnd_7014618 := by
    simpa [prefixWord, tailWord_7014618, baseEnd_7014618] using wordTrace_append hprefix tailTrace_7014618
  have hstable : (prefixWord ++ tailWord_7014618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014618).length < 2 ^ (prefixWord ++ tailWord_7014618).sum := by decide
  have hdescent : baseEnd_7014618 < baseStart_7014618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014642 : List Nat := [3, 2, 1, 3, 2, 3, 1, 1, 3, 1, 3]
def baseStart_7014642 : Nat := 118140960795 + 7014642 * 2 ^ 59
def prefixEnd_7014642 : Nat := 4983230072969 + 3 ^ 40 * 7014642 * 2
def baseEnd_7014642 : Nat := 3601882965215849414615255

theorem tailTrace_7014642 : CollatzResearch.WordTrace tailWord_7014642 prefixEnd_7014642 3601882965215849414615255 := by
  unfold tailWord_7014642
  simp only [CollatzResearch.WordTrace]
  refine ⟨63961253063289378580155545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170563341502105009547081453 63961253063289378580155545)
  ·
    refine ⟨47970939797467033935116659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63961253063289378580155545 47970939797467033935116659)
    ·
      refine ⟨71956409696200550902674989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47970939797467033935116659 71956409696200550902674989)
      ·
        refine ⟨26983653636075206588503121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71956409696200550902674989 26983653636075206588503121)
        ·
          refine ⟨20237740227056404941377341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26983653636075206588503121 20237740227056404941377341)
          ·
            refine ⟨7589152585146151853016503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20237740227056404941377341 7589152585146151853016503)
            ·
              refine ⟨11383728877719227779524755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7589152585146151853016503 11383728877719227779524755)
              ·
                refine ⟨17075593316578841669287133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11383728877719227779524755 17075593316578841669287133)
                ·
                  refine ⟨6403347493717065625982675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17075593316578841669287133 6403347493717065625982675)
                  ·
                    refine ⟨9605021240575598438974013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6403347493717065625982675 9605021240575598438974013)
                    ·
                      refine ⟨3601882965215849414615255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9605021240575598438974013 3601882965215849414615255)
                      ·
                        rfl

theorem cell23_7014642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_7014642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014642 prefixEnd_7014642 := by exact prefixLift 7014642
  have htrace : WordTrace (prefixWord ++ tailWord_7014642) baseStart_7014642 baseEnd_7014642 := by
    simpa [prefixWord, tailWord_7014642, baseEnd_7014642] using wordTrace_append hprefix tailTrace_7014642
  have hstable : (prefixWord ++ tailWord_7014642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014642).length < 2 ^ (prefixWord ++ tailWord_7014642).sum := by decide
  have hdescent : baseEnd_7014642 < baseStart_7014642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014665 : List Nat := [1, 2, 1, 1, 3, 6, 1, 2, 1, 1, 4]
def baseStart_7014665 : Nat := 118140960795 + 7014665 * 2 ^ 59
def prefixEnd_7014665 : Nat := 4983230072969 + 3 ^ 40 * 7014665 * 2
def baseEnd_7014665 : Nat := 3601894775270902824627649

theorem tailTrace_7014665 : CollatzResearch.WordTrace tailWord_7014665 prefixEnd_7014665 3601894775270902824627649 := by
  unfold tailWord_7014665
  simp only [CollatzResearch.WordTrace]
  refine ⟨255845851132074189248709449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170563900754716126165806299 255845851132074189248709449)
  ·
    refine ⟨191884388349055641936532087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255845851132074189248709449 191884388349055641936532087)
    ·
      refine ⟨287826582523583462904798131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191884388349055641936532087 287826582523583462904798131)
      ·
        refine ⟨431739873785375194357197197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287826582523583462904798131 431739873785375194357197197)
        ·
          refine ⟨161902452669515697883948949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 431739873785375194357197197 161902452669515697883948949)
          ·
            refine ⟨7589177468883548338310107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 161902452669515697883948949 7589177468883548338310107)
            ·
              refine ⟨11383766203325322507465161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7589177468883548338310107 11383766203325322507465161)
              ·
                refine ⟨8537824652493991880598871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11383766203325322507465161 8537824652493991880598871)
                ·
                  refine ⟨12806736978740987820898307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8537824652493991880598871 12806736978740987820898307)
                  ·
                    refine ⟨19210105468111481731347461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12806736978740987820898307 19210105468111481731347461)
                    ·
                      refine ⟨3601894775270902824627649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19210105468111481731347461 3601894775270902824627649)
                      ·
                        rfl

theorem cell23_7014665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 1, 4].length) (baseStart_7014665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014665 prefixEnd_7014665 := by exact prefixLift 7014665
  have htrace : WordTrace (prefixWord ++ tailWord_7014665) baseStart_7014665 baseEnd_7014665 := by
    simpa [prefixWord, tailWord_7014665, baseEnd_7014665] using wordTrace_append hprefix tailTrace_7014665
  have hstable : (prefixWord ++ tailWord_7014665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014665).length < 2 ^ (prefixWord ++ tailWord_7014665).sum := by decide
  have hdescent : baseEnd_7014665 < baseStart_7014665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014668 : List Nat := [2, 2, 1, 2, 2, 2, 3, 1, 3, 2, 3]
def baseStart_7014668 : Nat := 118140960795 + 7014668 * 2 ^ 59
def prefixEnd_7014668 : Nat := 4983230072969 + 3 ^ 40 * 7014668 * 2
def baseEnd_7014668 : Nat := 3601896315712866312890135

theorem tailTrace_7014668 : CollatzResearch.WordTrace tailWord_7014668 prefixEnd_7014668 3601896315712866312890135 := by
  unfold tailWord_7014668
  simp only [CollatzResearch.WordTrace]
  refine ⟨127922980275531660380534329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 170563973700708880507379105 127922980275531660380534329)
  ·
    refine ⟨95942235206648745285400747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 127922980275531660380534329 95942235206648745285400747)
    ·
      refine ⟨143913352809973117928101121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95942235206648745285400747 143913352809973117928101121)
      ·
        refine ⟨107935014607479838446075841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143913352809973117928101121 107935014607479838446075841)
        ·
          refine ⟨80951260955609878834556881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107935014607479838446075841 80951260955609878834556881)
          ·
            refine ⟨60713445716707409125917661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80951260955609878834556881 60713445716707409125917661)
            ·
              refine ⟨22767542143765278422219123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60713445716707409125917661 22767542143765278422219123)
              ·
                refine ⟨34151313215647917633328685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22767542143765278422219123 34151313215647917633328685)
                ·
                  refine ⟨12806742455867969112498257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34151313215647917633328685 12806742455867969112498257)
                  ·
                    refine ⟨9605056841900976834373693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12806742455867969112498257 9605056841900976834373693)
                    ·
                      refine ⟨3601896315712866312890135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9605056841900976834373693 3601896315712866312890135)
                      ·
                        rfl

theorem cell23_7014668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_7014668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014668 prefixEnd_7014668 := by exact prefixLift 7014668
  have htrace : WordTrace (prefixWord ++ tailWord_7014668) baseStart_7014668 baseEnd_7014668 := by
    simpa [prefixWord, tailWord_7014668, baseEnd_7014668] using wordTrace_append hprefix tailTrace_7014668
  have hstable : (prefixWord ++ tailWord_7014668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014668).length < 2 ^ (prefixWord ++ tailWord_7014668).sum := by decide
  have hdescent : baseEnd_7014668 < baseStart_7014668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014682 : List Nat := [3, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4]
def baseStart_7014682 : Nat := 118140960795 + 7014682 * 2 ^ 59
def prefixEnd_7014682 : Nat := 4983230072969 + 3 ^ 40 * 7014682 * 2
def baseEnd_7014682 : Nat := 3601903504442029258115071

theorem tailTrace_7014682 : CollatzResearch.WordTrace tailWord_7014682 prefixEnd_7014682 3601903504442029258115071 := by
  unfold tailWord_7014682
  simp only [CollatzResearch.WordTrace]
  refine ⟨63961617793253150288019575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 170564314115341734101385533 63961617793253150288019575)
  ·
    refine ⟨95942426689879725432029363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63961617793253150288019575 95942426689879725432029363)
    ·
      refine ⟨143913640034819588148044045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95942426689879725432029363 143913640034819588148044045)
      ·
        refine ⟨53967615013057345555516517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143913640034819588148044045 53967615013057345555516517)
        ·
          refine ⟨10118927814948252291659347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53967615013057345555516517 10118927814948252291659347)
          ·
            refine ⟨15178391722422378437489021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10118927814948252291659347 15178391722422378437489021)
            ·
              refine ⟨5691896895908391914058383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15178391722422378437489021 5691896895908391914058383)
              ·
                refine ⟨8537845343862587871087575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5691896895908391914058383 8537845343862587871087575)
                ·
                  refine ⟨12806768015793881806631363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8537845343862587871087575 12806768015793881806631363)
                  ·
                    refine ⟨19210152023690822709947045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12806768015793881806631363 19210152023690822709947045)
                    ·
                      refine ⟨3601903504442029258115071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19210152023690822709947045 3601903504442029258115071)
                      ·
                        rfl

theorem cell23_7014682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_7014682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014682 prefixEnd_7014682 := by exact prefixLift 7014682
  have htrace : WordTrace (prefixWord ++ tailWord_7014682) baseStart_7014682 baseEnd_7014682 := by
    simpa [prefixWord, tailWord_7014682, baseEnd_7014682] using wordTrace_append hprefix tailTrace_7014682
  have hstable : (prefixWord ++ tailWord_7014682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014682).length < 2 ^ (prefixWord ++ tailWord_7014682).sum := by decide
  have hdescent : baseEnd_7014682 < baseStart_7014682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014705 : List Nat := [1, 2, 2, 3, 5, 1, 1, 8]
def baseStart_7014705 : Nat := 118140960795 + 7014705 * 2 ^ 59
def prefixEnd_7014705 : Nat := 4983230072969 + 3 ^ 40 * 7014705 * 2
def baseEnd_7014705 : Nat := 133404270907299358078795

theorem tailTrace_7014705 : CollatzResearch.WordTrace tailWord_7014705 prefixEnd_7014705 133404270907299358078795 := by
  unfold tailWord_7014705
  simp only [CollatzResearch.WordTrace]
  refine ⟨255847310051929276080165569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 170564873367952850720110379 255847310051929276080165569)
  ·
    refine ⟨191885482538946957060124177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 255847310051929276080165569 191885482538946957060124177)
    ·
      refine ⟨143914111904210217795093133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 191885482538946957060124177 143914111904210217795093133)
      ·
        refine ⟨53967791964078831673159925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 143914111904210217795093133 53967791964078831673159925)
        ·
          refine ⟨5059480496632390469358743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53967791964078831673159925 5059480496632390469358743)
          ·
            refine ⟨7589220744948585704038115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5059480496632390469358743 7589220744948585704038115)
            ·
              refine ⟨11383831117422878556057173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7589220744948585704038115 11383831117422878556057173)
              ·
                refine ⟨133404270907299358078795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11383831117422878556057173 133404270907299358078795)
                ·
                  rfl

theorem cell23_7014705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 8].length) (baseStart_7014705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014705 prefixEnd_7014705 := by exact prefixLift 7014705
  have htrace : WordTrace (prefixWord ++ tailWord_7014705) baseStart_7014705 baseEnd_7014705 := by
    simpa [prefixWord, tailWord_7014705, baseEnd_7014705] using wordTrace_append hprefix tailTrace_7014705
  have hstable : (prefixWord ++ tailWord_7014705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014705).length < 2 ^ (prefixWord ++ tailWord_7014705).sum := by decide
  have hdescent : baseEnd_7014705 < baseStart_7014705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7014750 : List Nat := [4, 4, 2, 1, 1, 1, 2, 1, 3, 2, 2]
def baseStart_7014750 : Nat := 118140960795 + 7014750 * 2 ^ 59
def prefixEnd_7014750 : Nat := 4983230072969 + 3 ^ 40 * 7014750 * 2
def baseEnd_7014750 : Nat := 3601938421126534992064759

theorem tailTrace_7014750 : CollatzResearch.WordTrace tailWord_7014750 prefixEnd_7014750 3601938421126534992064759 := by
  unfold tailWord_7014750
  simp only [CollatzResearch.WordTrace]
  refine ⟨31981118917095781095694213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 170565967557844165843702469 31981118917095781095694213)
  ·
    refine ⟨5996459796955458955442665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31981118917095781095694213 5996459796955458955442665)
    ·
      refine ⟨4497344847716594216581999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5996459796955458955442665 4497344847716594216581999)
      ·
        refine ⟨6746017271574891324872999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4497344847716594216581999 6746017271574891324872999)
        ·
          refine ⟨10119025907362336987309499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6746017271574891324872999 10119025907362336987309499)
          ·
            refine ⟨15178538861043505480964249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10119025907362336987309499 15178538861043505480964249)
            ·
              refine ⟨11383904145782629110723187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15178538861043505480964249 11383904145782629110723187)
              ·
                refine ⟨17075856218673943666084781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11383904145782629110723187 17075856218673943666084781)
                ·
                  refine ⟨6403446082002728874781793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17075856218673943666084781 6403446082002728874781793)
                  ·
                    refine ⟨4802584561502046656086345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6403446082002728874781793 4802584561502046656086345)
                    ·
                      refine ⟨3601938421126534992064759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4802584561502046656086345 3601938421126534992064759)
                      ·
                        rfl

theorem cell23_7014750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_7014750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7014750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7014750 prefixEnd_7014750 := by exact prefixLift 7014750
  have htrace : WordTrace (prefixWord ++ tailWord_7014750) baseStart_7014750 baseEnd_7014750 := by
    simpa [prefixWord, tailWord_7014750, baseEnd_7014750] using wordTrace_append hprefix tailTrace_7014750
  have hstable : (prefixWord ++ tailWord_7014750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7014750).length < 2 ^ (prefixWord ++ tailWord_7014750).sum := by decide
  have hdescent : baseEnd_7014750 < baseStart_7014750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7014750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
