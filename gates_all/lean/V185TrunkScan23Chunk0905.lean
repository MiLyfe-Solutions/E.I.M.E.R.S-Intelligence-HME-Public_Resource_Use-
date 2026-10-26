import V185TrunkScan23Chunk0904

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5356056 : List Nat := [2, 1, 2, 3, 3, 1, 3, 1, 3, 1, 3]
def baseStart_5356056 : Nat := 118140960795 + 5356056 * 2 ^ 59
def prefixEnd_5356056 : Nat := 4983230072969 + 3 ^ 40 * 5356056 * 2
def baseEnd_5356056 : Nat := 2750231140397801639967953

theorem tailTrace_5356056 : CollatzResearch.WordTrace tailWord_5356056 prefixEnd_5356056 2750231140397801639967953 := by
  unfold tailWord_5356056
  simp only [CollatzResearch.WordTrace]
  refine ⟨97675705541965664191808011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130234274055954218922410681 97675705541965664191808011)
  ·
    refine ⟨146513558312948496287712017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97675705541965664191808011 146513558312948496287712017)
    ·
      refine ⟨109885168734711372215784013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146513558312948496287712017 109885168734711372215784013)
      ·
        refine ⟨41206938275516764580919005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109885168734711372215784013 41206938275516764580919005)
        ·
          refine ⟨15452601853318786717844627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41206938275516764580919005 15452601853318786717844627)
          ·
            refine ⟨23178902779978180076766941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15452601853318786717844627 23178902779978180076766941)
            ·
              refine ⟨8692088542491817528787603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23178902779978180076766941 8692088542491817528787603)
              ·
                refine ⟨13038132813737726293181405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8692088542491817528787603 13038132813737726293181405)
                ·
                  refine ⟨4889299805151647359943027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13038132813737726293181405 4889299805151647359943027)
                  ·
                    refine ⟨7333949707727471039914541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4889299805151647359943027 7333949707727471039914541)
                    ·
                      refine ⟨2750231140397801639967953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7333949707727471039914541 2750231140397801639967953)
                      ·
                        rfl

theorem cell23_5356056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_5356056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356056 prefixEnd_5356056 := by exact prefixLift 5356056
  have htrace : WordTrace (prefixWord ++ tailWord_5356056) baseStart_5356056 baseEnd_5356056 := by
    simpa [prefixWord, tailWord_5356056, baseEnd_5356056] using wordTrace_append hprefix tailTrace_5356056
  have hstable : (prefixWord ++ tailWord_5356056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356056).length < 2 ^ (prefixWord ++ tailWord_5356056).sum := by decide
  have hdescent : baseEnd_5356056 < baseStart_5356056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356082 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5]
def baseStart_5356082 : Nat := 118140960795 + 5356082 * 2 ^ 59
def prefixEnd_5356082 : Nat := 4983230072969 + 3 ^ 40 * 5356082 * 2
def baseEnd_5356082 : Nat := 2750244490894818538242833

theorem tailTrace_5356082 : CollatzResearch.WordTrace tailWord_5356082 prefixEnd_5356082 2750244490894818538242833 := by
  unfold tailWord_5356082
  simp only [CollatzResearch.WordTrace]
  refine ⟨48838089845459283706015625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130234906254558089882708333 48838089845459283706015625)
  ·
    refine ⟨36628567384094462779511719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48838089845459283706015625 36628567384094462779511719)
    ·
      refine ⟨54942851076141694169267579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36628567384094462779511719 54942851076141694169267579)
      ·
        refine ⟨82414276614212541253901369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54942851076141694169267579 82414276614212541253901369)
        ·
          refine ⟨61810707460659405940426027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82414276614212541253901369 61810707460659405940426027)
          ·
            refine ⟨92716061190989108910639041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61810707460659405940426027 92716061190989108910639041)
            ·
              refine ⟨69537045893241831682979281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92716061190989108910639041 69537045893241831682979281)
              ·
                refine ⟨52152784419931373762234461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69537045893241831682979281 52152784419931373762234461)
                ·
                  refine ⟨19557294157474265160837923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52152784419931373762234461 19557294157474265160837923)
                  ·
                    refine ⟨29335941236211397741256885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19557294157474265160837923 29335941236211397741256885)
                    ·
                      refine ⟨2750244490894818538242833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29335941236211397741256885 2750244490894818538242833)
                      ·
                        rfl

theorem cell23_5356082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_5356082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356082 prefixEnd_5356082 := by exact prefixLift 5356082
  have htrace : WordTrace (prefixWord ++ tailWord_5356082) baseStart_5356082 baseEnd_5356082 := by
    simpa [prefixWord, tailWord_5356082, baseEnd_5356082] using wordTrace_append hprefix tailTrace_5356082
  have hstable : (prefixWord ++ tailWord_5356082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356082).length < 2 ^ (prefixWord ++ tailWord_5356082).sum := by decide
  have hdescent : baseEnd_5356082 < baseStart_5356082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356099 : List Nat := [1, 1, 1, 3, 1, 2, 1, 7, 1, 2, 3]
def baseStart_5356099 : Nat := 118140960795 + 5356099 * 2 ^ 59
def prefixEnd_5356099 : Nat := 4983230072969 + 3 ^ 40 * 5356099 * 2
def baseEnd_5356099 : Nat := 2750253220065944971730255

theorem tailTrace_5356099 : CollatzResearch.WordTrace tailWord_5356099 prefixEnd_5356099 2750253220065944971730255 := by
  unfold tailWord_5356099
  simp only [CollatzResearch.WordTrace]
  refine ⟨195352979422775546727431351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130235319615183697818287567 195352979422775546727431351)
  ·
    refine ⟨293029469134163320091147027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195352979422775546727431351 293029469134163320091147027)
    ·
      refine ⟨439544203701244980136720541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293029469134163320091147027 439544203701244980136720541)
      ·
        refine ⟨164829076387966867551270203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 439544203701244980136720541 164829076387966867551270203)
        ·
          refine ⟨247243614581950301326905305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164829076387966867551270203 247243614581950301326905305)
          ·
            refine ⟨185432710936462725995178979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247243614581950301326905305 185432710936462725995178979)
            ·
              refine ⟨278149066404694088992768469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185432710936462725995178979 278149066404694088992768469)
              ·
                refine ⟨6519118743860017710768011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 278149066404694088992768469 6519118743860017710768011)
                ·
                  refine ⟨9778678115790026566152017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6519118743860017710768011 9778678115790026566152017)
                  ·
                    refine ⟨7334008586842519924614013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9778678115790026566152017 7334008586842519924614013)
                    ·
                      refine ⟨2750253220065944971730255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7334008586842519924614013 2750253220065944971730255)
                      ·
                        rfl

theorem cell23_5356099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 2, 3].length) (baseStart_5356099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356099 prefixEnd_5356099 := by exact prefixLift 5356099
  have htrace : WordTrace (prefixWord ++ tailWord_5356099) baseStart_5356099 baseEnd_5356099 := by
    simpa [prefixWord, tailWord_5356099, baseEnd_5356099] using wordTrace_append hprefix tailTrace_5356099
  have hstable : (prefixWord ++ tailWord_5356099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356099).length < 2 ^ (prefixWord ++ tailWord_5356099).sum := by decide
  have hdescent : baseEnd_5356099 < baseStart_5356099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356106 : List Nat := [3, 1, 2, 1, 1, 5, 2, 2, 2, 4]
def baseStart_5356106 : Nat := 118140960795 + 5356106 * 2 ^ 59
def prefixEnd_5356106 : Nat := 4983230072969 + 3 ^ 40 * 5356106 * 2
def baseEnd_5356106 : Nat := 916752271476842148114241

theorem tailTrace_5356106 : CollatzResearch.WordTrace tailWord_5356106 prefixEnd_5356106 916752271476842148114241 := by
  unfold tailWord_5356106
  simp only [CollatzResearch.WordTrace]
  refine ⟨48838308683437546730734043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130235489822500124615290781 48838308683437546730734043)
  ·
    refine ⟨73257463025156320096101065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48838308683437546730734043 73257463025156320096101065)
    ·
      refine ⟨54943097268867240072075799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73257463025156320096101065 54943097268867240072075799)
      ·
        refine ⟨82414645903300860108113699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54943097268867240072075799 82414645903300860108113699)
        ·
          refine ⟨123621968854951290162170549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82414645903300860108113699 123621968854951290162170549)
          ·
            refine ⟨11589559580151683452703489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 123621968854951290162170549 11589559580151683452703489)
            ·
              refine ⟨8692169685113762589527617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11589559580151683452703489 8692169685113762589527617)
              ·
                refine ⟨6519127263835321942145713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8692169685113762589527617 6519127263835321942145713)
                ·
                  refine ⟨4889345447876491456609285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6519127263835321942145713 4889345447876491456609285)
                  ·
                    refine ⟨916752271476842148114241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4889345447876491456609285 916752271476842148114241)
                    ·
                      rfl

theorem cell23_5356106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_5356106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356106 prefixEnd_5356106 := by exact prefixLift 5356106
  have htrace : WordTrace (prefixWord ++ tailWord_5356106) baseStart_5356106 baseEnd_5356106 := by
    simpa [prefixWord, tailWord_5356106, baseEnd_5356106] using wordTrace_append hprefix tailTrace_5356106
  have hstable : (prefixWord ++ tailWord_5356106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356106).length < 2 ^ (prefixWord ++ tailWord_5356106).sum := by decide
  have hdescent : baseEnd_5356106 < baseStart_5356106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356129 : List Nat := [1, 2, 3, 1, 1, 4, 1, 3, 1, 3, 3]
def baseStart_5356129 : Nat := 118140960795 + 5356129 * 2 ^ 59
def prefixEnd_5356129 : Nat := 4983230072969 + 3 ^ 40 * 5356129 * 2
def baseEnd_5356129 : Nat := 2750268624485579854355117

theorem tailTrace_5356129 : CollatzResearch.WordTrace tailWord_5356129 prefixEnd_5356129 2750268624485579854355117 := by
  unfold tailWord_5356129
  simp only [CollatzResearch.WordTrace]
  refine ⟨195354073612666861851023441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130236049075111241234015627 195354073612666861851023441)
  ·
    refine ⟨146515555209500146388267581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195354073612666861851023441 146515555209500146388267581)
    ·
      refine ⟨54943333203562554895600343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146515555209500146388267581 54943333203562554895600343)
      ·
        refine ⟨82414999805343832343400515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54943333203562554895600343 82414999805343832343400515)
        ·
          refine ⟨123622499708015748515100773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82414999805343832343400515 123622499708015748515100773)
          ·
            refine ⟨23179218695252952846581395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123622499708015748515100773 23179218695252952846581395)
            ·
              refine ⟨34768828042879429269872093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23179218695252952846581395 34768828042879429269872093)
              ·
                refine ⟨13038310516079785976202035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34768828042879429269872093 13038310516079785976202035)
                ·
                  refine ⟨19557465774119678964303053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13038310516079785976202035 19557465774119678964303053)
                  ·
                    refine ⟨7334049665294879611613645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19557465774119678964303053 7334049665294879611613645)
                    ·
                      refine ⟨2750268624485579854355117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7334049665294879611613645 2750268624485579854355117)
                      ·
                        rfl

theorem cell23_5356129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_5356129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356129 prefixEnd_5356129 := by exact prefixLift 5356129
  have htrace : WordTrace (prefixWord ++ tailWord_5356129) baseStart_5356129 baseEnd_5356129 := by
    simpa [prefixWord, tailWord_5356129, baseEnd_5356129] using wordTrace_append hprefix tailTrace_5356129
  have hstable : (prefixWord ++ tailWord_5356129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356129).length < 2 ^ (prefixWord ++ tailWord_5356129).sum := by decide
  have hdescent : baseEnd_5356129 < baseStart_5356129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356132 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 2, 7]
def baseStart_5356132 : Nat := 118140960795 + 5356132 * 2 ^ 59
def prefixEnd_5356132 : Nat := 4983230072969 + 3 ^ 40 * 5356132 * 2
def baseEnd_5356132 : Nat := 916756721642514447539201

theorem tailTrace_5356132 : CollatzResearch.WordTrace tailWord_5356132 prefixEnd_5356132 916756721642514447539201 := by
  unfold tailWord_5356132
  simp only [CollatzResearch.WordTrace]
  refine ⟨97677091515827996681691325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130236122021103995575588433 97677091515827996681691325)
  ·
    refine ⟨36628909318435498755634247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97677091515827996681691325 36628909318435498755634247)
    ·
      refine ⟨54943363977653248133451371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36628909318435498755634247 54943363977653248133451371)
      ·
        refine ⟨82415045966479872200177057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54943363977653248133451371 82415045966479872200177057)
        ·
          refine ⟨61811284474859904150132793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82415045966479872200177057 61811284474859904150132793)
          ·
            refine ⟨46358463356144928112599595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61811284474859904150132793 46358463356144928112599595)
            ·
              refine ⟨69537695034217392168899393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46358463356144928112599595 69537695034217392168899393)
              ·
                refine ⟨52153271275663044126674545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69537695034217392168899393 52153271275663044126674545)
                ·
                  refine ⟨39114953456747283095005909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52153271275663044126674545 39114953456747283095005909)
                  ·
                    refine ⟨916756721642514447539201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39114953456747283095005909 916756721642514447539201)
                    ·
                      rfl

theorem cell23_5356132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_5356132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356132 prefixEnd_5356132 := by exact prefixLift 5356132
  have htrace : WordTrace (prefixWord ++ tailWord_5356132) baseStart_5356132 baseEnd_5356132 := by
    simpa [prefixWord, tailWord_5356132, baseEnd_5356132] using wordTrace_append hprefix tailTrace_5356132
  have hstable : (prefixWord ++ tailWord_5356132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356132).length < 2 ^ (prefixWord ++ tailWord_5356132).sum := by decide
  have hdescent : baseEnd_5356132 < baseStart_5356132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356136 : List Nat := [2, 1, 4, 3, 2, 1, 3, 7]
def baseStart_5356136 : Nat := 118140960795 + 5356136 * 2 ^ 59
def prefixEnd_5356136 : Nat := 4983230072969 + 3 ^ 40 * 5356136 * 2
def baseEnd_5356136 : Nat := 101861934031487456554355

theorem tailTrace_5356136 : CollatzResearch.WordTrace tailWord_5356136 prefixEnd_5356136 101861934031487456554355 := by
  unfold tailWord_5356136
  simp only [CollatzResearch.WordTrace]
  refine ⟨97677164461820751023264131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130236219282427668031018841 97677164461820751023264131)
  ·
    refine ⟨146515746692731126534896197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97677164461820751023264131 146515746692731126534896197)
    ·
      refine ⟨27471702504887086225293037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146515746692731126534896197 27471702504887086225293037)
      ·
        refine ⟨10301888439332657334484889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27471702504887086225293037 10301888439332657334484889)
        ·
          refine ⟨7726416329499493000863667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10301888439332657334484889 7726416329499493000863667)
          ·
            refine ⟨11589624494249239501295501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7726416329499493000863667 11589624494249239501295501)
            ·
              refine ⟨4346109185343464812985813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11589624494249239501295501 4346109185343464812985813)
              ·
                refine ⟨101861934031487456554355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4346109185343464812985813 101861934031487456554355)
                ·
                  rfl

theorem cell23_5356136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 7].length) (baseStart_5356136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356136 prefixEnd_5356136 := by exact prefixLift 5356136
  have htrace : WordTrace (prefixWord ++ tailWord_5356136) baseStart_5356136 baseEnd_5356136 := by
    simpa [prefixWord, tailWord_5356136, baseEnd_5356136] using wordTrace_append hprefix tailTrace_5356136
  have hstable : (prefixWord ++ tailWord_5356136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356136).length < 2 ^ (prefixWord ++ tailWord_5356136).sum := by decide
  have hdescent : baseEnd_5356136 < baseStart_5356136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356152 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 4, 3, 4]
def baseStart_5356152 : Nat := 118140960795 + 5356152 * 2 ^ 59
def prefixEnd_5356152 : Nat := 4983230072969 + 3 ^ 40 * 5356152 * 2
def baseEnd_5356152 : Nat := 2750280434540633264367511

theorem tailTrace_5356152 : CollatzResearch.WordTrace tailWord_5356152 prefixEnd_5356152 2750280434540633264367511 := by
  unfold tailWord_5356152
  simp only [CollatzResearch.WordTrace]
  refine ⟨97677456245791768389555355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130236608327722357852740473 97677456245791768389555355)
  ·
    refine ⟨146516184368687652584333033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97677456245791768389555355 146516184368687652584333033)
    ·
      refine ⟨109887138276515739438249775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146516184368687652584333033 109887138276515739438249775)
      ·
        refine ⟨164830707414773609157374663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109887138276515739438249775 164830707414773609157374663)
        ·
          refine ⟨247246061122160413736061995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164830707414773609157374663 247246061122160413736061995)
          ·
            refine ⟨370869091683240620604092993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247246061122160413736061995 370869091683240620604092993)
            ·
              refine ⟨278151818762430465453069745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 370869091683240620604092993 278151818762430465453069745)
              ·
                refine ⟨208613864071822849089802309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278151818762430465453069745 208613864071822849089802309)
                ·
                  refine ⟨39115099513466784204337933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 208613864071822849089802309 39115099513466784204337933)
                  ·
                    refine ⟨14668162317550044076626725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39115099513466784204337933 14668162317550044076626725)
                    ·
                      refine ⟨2750280434540633264367511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14668162317550044076626725 2750280434540633264367511)
                      ·
                        rfl

theorem cell23_5356152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_5356152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356152 prefixEnd_5356152 := by exact prefixLift 5356152
  have htrace : WordTrace (prefixWord ++ tailWord_5356152) baseStart_5356152 baseEnd_5356152 := by
    simpa [prefixWord, tailWord_5356152, baseEnd_5356152] using wordTrace_append hprefix tailTrace_5356152
  have hstable : (prefixWord ++ tailWord_5356152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356152).length < 2 ^ (prefixWord ++ tailWord_5356152).sum := by decide
  have hdescent : baseEnd_5356152 < baseStart_5356152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356172 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 3, 3, 5]
def baseStart_5356172 : Nat := 118140960795 + 5356172 * 2 ^ 59
def prefixEnd_5356172 : Nat := 4983230072969 + 3 ^ 40 * 5356172 * 2
def baseEnd_5356172 : Nat := 2750290704153723186117419

theorem tailTrace_5356172 : CollatzResearch.WordTrace tailWord_5356172 prefixEnd_5356172 2750290704153723186117419 := by
  unfold tailWord_5356172
  simp only [CollatzResearch.WordTrace]
  refine ⟨97677820975755540097419385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130237094634340720129892513 97677820975755540097419385)
  ·
    refine ⟨73258365731816655073064539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97677820975755540097419385 73258365731816655073064539)
    ·
      refine ⟨109887548597724982609596809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73258365731816655073064539 109887548597724982609596809)
      ·
        refine ⟨82415661448293736957197607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109887548597724982609596809 82415661448293736957197607)
        ·
          refine ⟨123623492172440605435796411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82415661448293736957197607 123623492172440605435796411)
          ·
            refine ⟨185435238258660908153694617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123623492172440605435796411 185435238258660908153694617)
            ·
              refine ⟨139076428693995681115270963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185435238258660908153694617 139076428693995681115270963)
              ·
                refine ⟨208614643040993521672906445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139076428693995681115270963 208614643040993521672906445)
                ·
                  refine ⟨78230491140372570627339917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 208614643040993521672906445 78230491140372570627339917)
                  ·
                    refine ⟨29336434177639713985252469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78230491140372570627339917 29336434177639713985252469)
                    ·
                      refine ⟨2750290704153723186117419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29336434177639713985252469 2750290704153723186117419)
                      ·
                        rfl

theorem cell23_5356172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_5356172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356172 prefixEnd_5356172 := by exact prefixLift 5356172
  have htrace : WordTrace (prefixWord ++ tailWord_5356172) baseStart_5356172 baseEnd_5356172 := by
    simpa [prefixWord, tailWord_5356172, baseEnd_5356172] using wordTrace_append hprefix tailTrace_5356172
  have hstable : (prefixWord ++ tailWord_5356172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356172).length < 2 ^ (prefixWord ++ tailWord_5356172).sum := by decide
  have hdescent : baseEnd_5356172 < baseStart_5356172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356189 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 2, 4, 3]
def baseStart_5356189 : Nat := 118140960795 + 5356189 * 2 ^ 59
def prefixEnd_5356189 : Nat := 4983230072969 + 3 ^ 40 * 5356189 * 2
def baseEnd_5356189 : Nat := 2750299433324849619604841

theorem tailTrace_5356189 : CollatzResearch.WordTrace tailWord_5356189 prefixEnd_5356189 2750299433324849619604841 := by
  unfold tailWord_5356189
  simp only [CollatzResearch.WordTrace]
  refine ⟨195356261992449492098207621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130237507994966328065471747 195356261992449492098207621)
  ·
    refine ⟨36629299123584279768413929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195356261992449492098207621 36629299123584279768413929)
    ·
      refine ⟨27471974342688209826310447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36629299123584279768413929 27471974342688209826310447)
      ·
        refine ⟨41207961514032314739465671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27471974342688209826310447 41207961514032314739465671)
        ·
          refine ⟨61811942271048472109198507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41207961514032314739465671 61811942271048472109198507)
          ·
            refine ⟨92717913406572708163797761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61811942271048472109198507 92717913406572708163797761)
            ·
              refine ⟨69538435054929531122848321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92717913406572708163797761 69538435054929531122848321)
              ·
                refine ⟨52153826291197148342136241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69538435054929531122848321 52153826291197148342136241)
                ·
                  refine ⟨39115369718397861256602181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52153826291197148342136241 39115369718397861256602181)
                  ·
                    refine ⟨7334131822199598985612909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39115369718397861256602181 7334131822199598985612909)
                    ·
                      refine ⟨2750299433324849619604841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7334131822199598985612909 2750299433324849619604841)
                      ·
                        rfl

theorem cell23_5356189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_5356189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356189 prefixEnd_5356189 := by exact prefixLift 5356189
  have htrace : WordTrace (prefixWord ++ tailWord_5356189) baseStart_5356189 baseEnd_5356189 := by
    simpa [prefixWord, tailWord_5356189, baseEnd_5356189] using wordTrace_append hprefix tailTrace_5356189
  have hstable : (prefixWord ++ tailWord_5356189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356189).length < 2 ^ (prefixWord ++ tailWord_5356189).sum := by decide
  have hdescent : baseEnd_5356189 < baseStart_5356189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356190 : List Nat := [4, 3, 1, 1, 1, 1, 4, 2, 1, 3, 2]
def baseStart_5356190 : Nat := 118140960795 + 5356190 * 2 ^ 59
def prefixEnd_5356190 : Nat := 4983230072969 + 3 ^ 40 * 5356190 * 2
def baseEnd_5356190 : Nat := 2750299946805504115692337

theorem tailTrace_5356190 : CollatzResearch.WordTrace tailWord_5356190 prefixEnd_5356190 2750299946805504115692337 := by
  unfold tailWord_5356190
  simp only [CollatzResearch.WordTrace]
  refine ⟨24419537308180733658624253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130237532310297246179329349 24419537308180733658624253)
  ·
    refine ⟨9157326490567775121984095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24419537308180733658624253 9157326490567775121984095)
    ·
      refine ⟨13735989735851662682976143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9157326490567775121984095 13735989735851662682976143)
      ·
        refine ⟨20603984603777494024464215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13735989735851662682976143 20603984603777494024464215)
        ·
          refine ⟨30905976905666241036696323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20603984603777494024464215 30905976905666241036696323)
          ·
            refine ⟨46358965358499361555044485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30905976905666241036696323 46358965358499361555044485)
            ·
              refine ⟨8692306004718630291570841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46358965358499361555044485 8692306004718630291570841)
              ·
                refine ⟨6519229503538972718678131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8692306004718630291570841 6519229503538972718678131)
                ·
                  refine ⟨9778844255308459078017197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6519229503538972718678131 9778844255308459078017197)
                  ·
                    refine ⟨3667066595740672154256449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9778844255308459078017197 3667066595740672154256449)
                    ·
                      refine ⟨2750299946805504115692337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3667066595740672154256449 2750299946805504115692337)
                      ·
                        rfl

theorem cell23_5356190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_5356190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356190 prefixEnd_5356190 := by exact prefixLift 5356190
  have htrace : WordTrace (prefixWord ++ tailWord_5356190) baseStart_5356190 baseEnd_5356190 := by
    simpa [prefixWord, tailWord_5356190, baseEnd_5356190] using wordTrace_append hprefix tailTrace_5356190
  have hstable : (prefixWord ++ tailWord_5356190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356190).length < 2 ^ (prefixWord ++ tailWord_5356190).sum := by decide
  have hdescent : baseEnd_5356190 < baseStart_5356190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356206 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_5356206 : Nat := 118140960795 + 5356206 * 2 ^ 59
def prefixEnd_5356206 : Nat := 4983230072969 + 3 ^ 40 * 5356206 * 2
def baseEnd_5356206 : Nat := 2750308162495976053092263

theorem tailTrace_5356206 : CollatzResearch.WordTrace tailWord_5356206 prefixEnd_5356206 2750308162495976053092263 := by
  unfold tailWord_5356206
  simp only [CollatzResearch.WordTrace]
  refine ⟨24419610254173488000197059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130237921355591936001050981 24419610254173488000197059)
  ·
    refine ⟨36629415381260232000295589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24419610254173488000197059 36629415381260232000295589)
    ·
      refine ⟨6868015383986293500055423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36629415381260232000295589 6868015383986293500055423)
      ·
        refine ⟨10302023075979440250083135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6868015383986293500055423 10302023075979440250083135)
        ·
          refine ⟨15453034613969160375124703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10302023075979440250083135 15453034613969160375124703)
          ·
            refine ⟨23179551920953740562687055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15453034613969160375124703 23179551920953740562687055)
            ·
              refine ⟨34769327881430610844030583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23179551920953740562687055 34769327881430610844030583)
              ·
                refine ⟨52153991822145916266045875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34769327881430610844030583 52153991822145916266045875)
                ·
                  refine ⟨78230987733218874399068813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52153991822145916266045875 78230987733218874399068813)
                  ·
                    refine ⟨29336620399957077899650805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78230987733218874399068813 29336620399957077899650805)
                    ·
                      refine ⟨2750308162495976053092263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29336620399957077899650805 2750308162495976053092263)
                      ·
                        rfl

theorem cell23_5356206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_5356206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356206 prefixEnd_5356206 := by exact prefixLift 5356206
  have htrace : WordTrace (prefixWord ++ tailWord_5356206) baseStart_5356206 baseEnd_5356206 := by
    simpa [prefixWord, tailWord_5356206, baseEnd_5356206] using wordTrace_append hprefix tailTrace_5356206
  have hstable : (prefixWord ++ tailWord_5356206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356206).length < 2 ^ (prefixWord ++ tailWord_5356206).sum := by decide
  have hdescent : baseEnd_5356206 < baseStart_5356206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356277 : List Nat := [1, 3, 6, 1, 1, 1, 1, 4, 5]
def baseStart_5356277 : Nat := 118140960795 + 5356277 * 2 ^ 59
def prefixEnd_5356277 : Nat := 4983230072969 + 3 ^ 40 * 5356277 * 2
def baseEnd_5356277 : Nat := 305593846624716141700493

theorem tailTrace_5356277 : CollatzResearch.WordTrace tailWord_5356277 prefixEnd_5356277 305593846624716141700493 := by
  unfold tailWord_5356277
  simp only [CollatzResearch.WordTrace]
  refine ⟨195359471616130683127411085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130239647744087122084940723 195359471616130683127411085)
  ·
    refine ⟨73259801856049006172779157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195359471616130683127411085 73259801856049006172779157)
    ·
      refine ⟨3434053212002297164349023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 73259801856049006172779157 3434053212002297164349023)
      ·
        refine ⟨5151079818003445746523535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3434053212002297164349023 5151079818003445746523535)
        ·
          refine ⟨7726619727005168619785303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5151079818003445746523535 7726619727005168619785303)
          ·
            refine ⟨11589929590507752929677955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7726619727005168619785303 11589929590507752929677955)
            ·
              refine ⟨17384894385761629394516933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11589929590507752929677955 17384894385761629394516933)
              ·
                refine ⟨3259667697330305511471925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17384894385761629394516933 3259667697330305511471925)
                ·
                  refine ⟨305593846624716141700493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3259667697330305511471925 305593846624716141700493)
                  ·
                    rfl

theorem cell23_5356277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 4, 5].length) (baseStart_5356277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356277 prefixEnd_5356277 := by exact prefixLift 5356277
  have htrace : WordTrace (prefixWord ++ tailWord_5356277) baseStart_5356277 baseEnd_5356277 := by
    simpa [prefixWord, tailWord_5356277, baseEnd_5356277] using wordTrace_append hprefix tailTrace_5356277
  have hstable : (prefixWord ++ tailWord_5356277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356277).length < 2 ^ (prefixWord ++ tailWord_5356277).sum := by decide
  have hdescent : baseEnd_5356277 < baseStart_5356277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356279 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 3, 4, 3]
def baseStart_5356279 : Nat := 118140960795 + 5356279 * 2 ^ 59
def prefixEnd_5356279 : Nat := 4983230072969 + 3 ^ 40 * 5356279 * 2
def baseEnd_5356279 : Nat := 2750345646583754267479427

theorem tailTrace_5356279 : CollatzResearch.WordTrace tailWord_5356279 prefixEnd_5356279 2750345646583754267479427 := by
  unfold tailWord_5356279
  simp only [CollatzResearch.WordTrace]
  refine ⟨195359544562123437468983891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130239696374748958312655927 195359544562123437468983891)
  ·
    refine ⟨293039316843185156203475837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195359544562123437468983891 293039316843185156203475837)
    ·
      refine ⟨109889743816194433576303439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293039316843185156203475837 109889743816194433576303439)
      ·
        refine ⟨164834615724291650364455159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109889743816194433576303439 164834615724291650364455159)
        ·
          refine ⟨247251923586437475546682739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164834615724291650364455159 247251923586437475546682739)
          ·
            refine ⟨370877885379656213320024109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247251923586437475546682739 370877885379656213320024109)
            ·
              refine ⟨139079207017371079995009041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 370877885379656213320024109 139079207017371079995009041)
              ·
                refine ⟨104309405263028309996256781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139079207017371079995009041 104309405263028309996256781)
                ·
                  refine ⟨39116026973635616248596293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104309405263028309996256781 39116026973635616248596293)
                  ·
                    refine ⟨7334255057556678046611805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39116026973635616248596293 7334255057556678046611805)
                    ·
                      refine ⟨2750345646583754267479427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7334255057556678046611805 2750345646583754267479427)
                      ·
                        rfl

theorem cell23_5356279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 4, 3].length) (baseStart_5356279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356279 prefixEnd_5356279 := by exact prefixLift 5356279
  have htrace : WordTrace (prefixWord ++ tailWord_5356279) baseStart_5356279 baseEnd_5356279 := by
    simpa [prefixWord, tailWord_5356279, baseEnd_5356279] using wordTrace_append hprefix tailTrace_5356279
  have hstable : (prefixWord ++ tailWord_5356279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356279).length < 2 ^ (prefixWord ++ tailWord_5356279).sum := by decide
  have hdescent : baseEnd_5356279 < baseStart_5356279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356289 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_5356289 : Nat := 118140960795 + 5356289 * 2 ^ 59
def prefixEnd_5356289 : Nat := 4983230072969 + 3 ^ 40 * 5356289 * 2
def baseEnd_5356289 : Nat := 2750350781390299228354381

theorem tailTrace_5356289 : CollatzResearch.WordTrace tailWord_5356289 prefixEnd_5356289 2750350781390299228354381 := by
  unfold tailWord_5356289
  simp only [CollatzResearch.WordTrace]
  refine ⟨195359909292087209176847921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130239939528058139451231947 195359909292087209176847921)
  ·
    refine ⟨146519931969065406882635941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195359909292087209176847921 146519931969065406882635941)
    ·
      refine ⟨27472487244199763790494239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146519931969065406882635941 27472487244199763790494239)
      ·
        refine ⟨41208730866299645685741359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27472487244199763790494239 41208730866299645685741359)
        ·
          refine ⟨61813096299449468528612039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41208730866299645685741359 61813096299449468528612039)
          ·
            refine ⟨92719644449174202792918059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61813096299449468528612039 92719644449174202792918059)
            ·
              refine ⟨139079466673761304189377089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92719644449174202792918059 139079466673761304189377089)
              ·
                refine ⟨104309600005320978142032817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139079466673761304189377089 104309600005320978142032817)
                ·
                  refine ⟨78232200003990733606524613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104309600005320978142032817 78232200003990733606524613)
                  ·
                    refine ⟨14668537500748262551223365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78232200003990733606524613 14668537500748262551223365)
                    ·
                      refine ⟨2750350781390299228354381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14668537500748262551223365 2750350781390299228354381)
                      ·
                        rfl

theorem cell23_5356289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_5356289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356289 prefixEnd_5356289 := by exact prefixLift 5356289
  have htrace : WordTrace (prefixWord ++ tailWord_5356289) baseStart_5356289 baseEnd_5356289 := by
    simpa [prefixWord, tailWord_5356289, baseEnd_5356289] using wordTrace_append hprefix tailTrace_5356289
  have hstable : (prefixWord ++ tailWord_5356289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356289).length < 2 ^ (prefixWord ++ tailWord_5356289).sum := by decide
  have hdescent : baseEnd_5356289 < baseStart_5356289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356320 : List Nat := [2, 1, 1, 5, 1, 3, 2, 3, 1, 4]
def baseStart_5356320 : Nat := 118140960795 + 5356320 * 2 ^ 59
def prefixEnd_5356320 : Nat := 4983230072969 + 3 ^ 40 * 5356320 * 2
def baseEnd_5356320 : Nat := 916788899763529535688913

theorem tailTrace_5356320 : CollatzResearch.WordTrace tailWord_5356320 prefixEnd_5356320 916788899763529535688913 := by
  unfold tailWord_5356320
  simp only [CollatzResearch.WordTrace]
  refine ⟨97680519977487450735613207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130240693303316600980817609 97680519977487450735613207)
  ·
    refine ⟨146520779966231176103419811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97680519977487450735613207 146520779966231176103419811)
    ·
      refine ⟨219781169949346764155129717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146520779966231176103419811 219781169949346764155129717)
      ·
        refine ⟨20604484682751259139543411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 219781169949346764155129717 20604484682751259139543411)
        ·
          refine ⟨30906727024126888709315117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20604484682751259139543411 30906727024126888709315117)
          ·
            refine ⟨11590022634047583265993169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30906727024126888709315117 11590022634047583265993169)
            ·
              refine ⟨8692516975535687449494877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11590022634047583265993169 8692516975535687449494877)
              ·
                refine ⟨3259693865825882793560579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8692516975535687449494877 3259693865825882793560579)
                ·
                  refine ⟨4889540798738824190340869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3259693865825882793560579 4889540798738824190340869)
                  ·
                    refine ⟨916788899763529535688913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4889540798738824190340869 916788899763529535688913)
                    ·
                      rfl

theorem cell23_5356320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 3, 1, 4].length) (baseStart_5356320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356320 prefixEnd_5356320 := by exact prefixLift 5356320
  have htrace : WordTrace (prefixWord ++ tailWord_5356320) baseStart_5356320 baseEnd_5356320 := by
    simpa [prefixWord, tailWord_5356320, baseEnd_5356320] using wordTrace_append hprefix tailTrace_5356320
  have hstable : (prefixWord ++ tailWord_5356320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356320).length < 2 ^ (prefixWord ++ tailWord_5356320).sum := by decide
  have hdescent : baseEnd_5356320 < baseStart_5356320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356343 : List Nat := [1, 1, 3, 1, 2, 1, 6, 1, 3, 1, 3]
def baseStart_5356343 : Nat := 118140960795 + 5356343 * 2 ^ 59
def prefixEnd_5356343 : Nat := 4983230072969 + 3 ^ 40 * 5356343 * 2
def baseEnd_5356343 : Nat := 2750378509345642017079133

theorem tailTrace_5356343 : CollatzResearch.WordTrace tailWord_5356343 prefixEnd_5356343 2750378509345642017079133 := by
  unfold tailWord_5356343
  simp only [CollatzResearch.WordTrace]
  refine ⟨195361878833891576399313683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130241252555927717599542455 195361878833891576399313683)
  ·
    refine ⟨293042818250837364598970525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195361878833891576399313683 293042818250837364598970525)
    ·
      refine ⟨109891056844064011724613947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293042818250837364598970525 109891056844064011724613947)
      ·
        refine ⟨164836585266096017586920921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109891056844064011724613947 164836585266096017586920921)
        ·
          refine ⟨123627438949572013190190691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164836585266096017586920921 123627438949572013190190691)
          ·
            refine ⟨185441158424358019785286037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123627438949572013190190691 185441158424358019785286037)
            ·
              refine ⟨8692554301141782177435283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 185441158424358019785286037 8692554301141782177435283)
              ·
                refine ⟨13038831451712673266152925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8692554301141782177435283 13038831451712673266152925)
                ·
                  refine ⟨4889561794392252474807347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13038831451712673266152925 4889561794392252474807347)
                  ·
                    refine ⟨7334342691588378712211021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4889561794392252474807347 7334342691588378712211021)
                    ·
                      refine ⟨2750378509345642017079133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7334342691588378712211021 2750378509345642017079133)
                      ·
                        rfl

theorem cell23_5356343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3, 1, 3].length) (baseStart_5356343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356343 prefixEnd_5356343 := by exact prefixLift 5356343
  have htrace : WordTrace (prefixWord ++ tailWord_5356343) baseStart_5356343 baseEnd_5356343 := by
    simpa [prefixWord, tailWord_5356343, baseEnd_5356343] using wordTrace_append hprefix tailTrace_5356343
  have hstable : (prefixWord ++ tailWord_5356343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356343).length < 2 ^ (prefixWord ++ tailWord_5356343).sum := by decide
  have hdescent : baseEnd_5356343 < baseStart_5356343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356350 : List Nat := [4, 2, 1, 2, 3, 1, 3, 1, 6]
def baseStart_5356350 : Nat := 118140960795 + 5356350 * 2 ^ 59
def prefixEnd_5356350 : Nat := 4983230072969 + 3 ^ 40 * 5356350 * 2
def baseEnd_5356350 : Nat := 305598011523358165521289

theorem tailTrace_5356350 : CollatzResearch.WordTrace tailWord_5356350 prefixEnd_5356350 305598011523358165521289 := by
  unfold tailWord_5356350
  simp only [CollatzResearch.WordTrace]
  refine ⟨24420266768108277074352313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130241422763244144396545669 24420266768108277074352313)
  ·
    refine ⟨18315200076081207805764235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24420266768108277074352313 18315200076081207805764235)
    ·
      refine ⟨27472800114121811708646353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18315200076081207805764235 27472800114121811708646353)
      ·
        refine ⟨20604600085591358781484765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27472800114121811708646353 20604600085591358781484765)
        ·
          refine ⟨7726725032096759543056787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20604600085591358781484765 7726725032096759543056787)
          ·
            refine ⟨11590087548145139314585181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7726725032096759543056787 11590087548145139314585181)
            ·
              refine ⟨4346282830554427242969443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11590087548145139314585181 4346282830554427242969443)
              ·
                refine ⟨6519424245831640864454165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4346282830554427242969443 6519424245831640864454165)
                ·
                  refine ⟨305598011523358165521289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6519424245831640864454165 305598011523358165521289)
                  ·
                    rfl

theorem cell23_5356350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_5356350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356350 prefixEnd_5356350 := by exact prefixLift 5356350
  have htrace : WordTrace (prefixWord ++ tailWord_5356350) baseStart_5356350 baseEnd_5356350 := by
    simpa [prefixWord, tailWord_5356350, baseEnd_5356350] using wordTrace_append hprefix tailTrace_5356350
  have hstable : (prefixWord ++ tailWord_5356350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356350).length < 2 ^ (prefixWord ++ tailWord_5356350).sum := by decide
  have hdescent : baseEnd_5356350 < baseStart_5356350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356366 : List Nat := [4, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4]
def baseStart_5356366 : Nat := 118140960795 + 5356366 * 2 ^ 59
def prefixEnd_5356366 : Nat := 4983230072969 + 3 ^ 40 * 5356366 * 2
def baseEnd_5356366 : Nat := 2750390319400695427091527

theorem tailTrace_5356366 : CollatzResearch.WordTrace tailWord_5356366 prefixEnd_5356366 2750390319400695427091527 := by
  unfold tailWord_5356366
  simp only [CollatzResearch.WordTrace]
  refine ⟨24420339714101031415925119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130241811808538834218267301 24420339714101031415925119)
  ·
    refine ⟨36630509571151547123887679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24420339714101031415925119 36630509571151547123887679)
    ·
      refine ⟨54945764356727320685831519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36630509571151547123887679 54945764356727320685831519)
      ·
        refine ⟨82418646535090981028747279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54945764356727320685831519 82418646535090981028747279)
        ·
          refine ⟨123627969802636471543120919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82418646535090981028747279 123627969802636471543120919)
          ·
            refine ⟨185441954703954707314681379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123627969802636471543120919 185441954703954707314681379)
            ·
              refine ⟨278162932055932060972022069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185441954703954707314681379 278162932055932060972022069)
              ·
                refine ⟨26077774880243630716127069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 278162932055932060972022069 26077774880243630716127069)
                ·
                  refine ⟨9779165580091361518547651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26077774880243630716127069 9779165580091361518547651)
                  ·
                    refine ⟨14668748370137042277821477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9779165580091361518547651 14668748370137042277821477)
                    ·
                      refine ⟨2750390319400695427091527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14668748370137042277821477 2750390319400695427091527)
                      ·
                        rfl

theorem cell23_5356366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_5356366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356366 prefixEnd_5356366 := by exact prefixLift 5356366
  have htrace : WordTrace (prefixWord ++ tailWord_5356366) baseStart_5356366 baseEnd_5356366 := by
    simpa [prefixWord, tailWord_5356366, baseEnd_5356366] using wordTrace_append hprefix tailTrace_5356366
  have hstable : (prefixWord ++ tailWord_5356366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356366).length < 2 ^ (prefixWord ++ tailWord_5356366).sum := by decide
  have hdescent : baseEnd_5356366 < baseStart_5356366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356377 : List Nat := [1, 2, 1, 2, 2, 6, 1, 3, 1, 1, 3]
def baseStart_5356377 : Nat := 118140960795 + 5356377 * 2 ^ 59
def prefixEnd_5356377 : Nat := 4983230072969 + 3 ^ 40 * 5356377 * 2
def baseEnd_5356377 : Nat := 2750395967687894884053977

theorem tailTrace_5356377 : CollatzResearch.WordTrace tailWord_5356377 prefixEnd_5356377 2750395967687894884053977 := by
  unfold tailWord_5356377
  simp only [CollatzResearch.WordTrace]
  refine ⟨195363118915768400206051385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130242079277178933470700923 195363118915768400206051385)
  ·
    refine ⟨146522339186826300154538539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195363118915768400206051385 146522339186826300154538539)
    ·
      refine ⟨219783508780239450231807809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146522339186826300154538539 219783508780239450231807809)
      ·
        refine ⟨164837631585179587673855857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219783508780239450231807809 164837631585179587673855857)
        ·
          refine ⟨123628223688884690755391893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164837631585179587673855857 123628223688884690755391893)
          ·
            refine ⟨5795072985416469879158995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 123628223688884690755391893 5795072985416469879158995)
            ·
              refine ⟨8692609478124704818738493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5795072985416469879158995 8692609478124704818738493)
              ·
                refine ⟨3259728554296764307026935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8692609478124704818738493 3259728554296764307026935)
                ·
                  refine ⟨4889592831445146460540403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3259728554296764307026935 4889592831445146460540403)
                  ·
                    refine ⟨7334389247167719690810605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4889592831445146460540403 7334389247167719690810605)
                    ·
                      refine ⟨2750395967687894884053977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7334389247167719690810605 2750395967687894884053977)
                      ·
                        rfl

theorem cell23_5356377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3, 1, 1, 3].length) (baseStart_5356377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356377 prefixEnd_5356377 := by exact prefixLift 5356377
  have htrace : WordTrace (prefixWord ++ tailWord_5356377) baseStart_5356377 baseEnd_5356377 := by
    simpa [prefixWord, tailWord_5356377, baseEnd_5356377] using wordTrace_append hprefix tailTrace_5356377
  have hstable : (prefixWord ++ tailWord_5356377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356377).length < 2 ^ (prefixWord ++ tailWord_5356377).sum := by decide
  have hdescent : baseEnd_5356377 < baseStart_5356377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356389 : List Nat := [1, 3, 1, 3, 1, 1, 13]
def baseStart_5356389 : Nat := 118140960795 + 5356389 * 2 ^ 59
def prefixEnd_5356389 : Nat := 4983230072969 + 3 ^ 40 * 5356389 * 2
def baseEnd_5356389 : Nat := 33955581845132701692641

theorem tailTrace_5356389 : CollatzResearch.WordTrace tailWord_5356389 prefixEnd_5356389 33955581845132701692641 := by
  unfold tailWord_5356389
  simp only [CollatzResearch.WordTrace]
  refine ⟨195363556591724926255488221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130242371061149950836992147 195363556591724926255488221)
  ·
    refine ⟨73261333721896847345808083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195363556591724926255488221 73261333721896847345808083)
    ·
      refine ⟨109892000582845271018712125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73261333721896847345808083 109892000582845271018712125)
      ·
        refine ⟨41209500218566976632017047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109892000582845271018712125 41209500218566976632017047)
        ·
          refine ⟨61814250327850464948025571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41209500218566976632017047 61814250327850464948025571)
          ·
            refine ⟨92721375491775697422038357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61814250327850464948025571 92721375491775697422038357)
            ·
              refine ⟨33955581845132701692641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 92721375491775697422038357 33955581845132701692641)
              ·
                rfl

theorem cell23_5356389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 13].length) (baseStart_5356389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356389 prefixEnd_5356389 := by exact prefixLift 5356389
  have htrace : WordTrace (prefixWord ++ tailWord_5356389) baseStart_5356389 baseEnd_5356389 := by
    simpa [prefixWord, tailWord_5356389, baseEnd_5356389] using wordTrace_append hprefix tailTrace_5356389
  have hstable : (prefixWord ++ tailWord_5356389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356389).length < 2 ^ (prefixWord ++ tailWord_5356389).sum := by decide
  have hdescent : baseEnd_5356389 < baseStart_5356389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356400 : List Nat := [2, 1, 1, 1, 4, 1, 5, 1, 3, 2, 2]
def baseStart_5356400 : Nat := 118140960795 + 5356400 * 2 ^ 59
def prefixEnd_5356400 : Nat := 4983230072969 + 3 ^ 40 * 5356400 * 2
def baseEnd_5356400 : Nat := 2750407777742948294066371

theorem tailTrace_5356400 : CollatzResearch.WordTrace tailWord_5356400 prefixEnd_5356400 2750407777742948294066371 := by
  unfold tailWord_5356400
  simp only [CollatzResearch.WordTrace]
  refine ⟨97681978897342537567069327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130242638529790050089425769 97681978897342537567069327)
  ·
    refine ⟨146522968346013806350603991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97681978897342537567069327 146522968346013806350603991)
    ·
      refine ⟨219784452519020709525905987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146522968346013806350603991 219784452519020709525905987)
      ·
        refine ⟨329676678778531064288858981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219784452519020709525905987 329676678778531064288858981)
        ·
          refine ⟨61814377270974574554161059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 329676678778531064288858981 61814377270974574554161059)
          ·
            refine ⟨92721565906461861831241589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61814377270974574554161059 92721565906461861831241589)
            ·
              refine ⟨8692646803730799546678899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92721565906461861831241589 8692646803730799546678899)
              ·
                refine ⟨13038970205596199320018349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8692646803730799546678899 13038970205596199320018349)
                ·
                  refine ⟨4889613827098574745006881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13038970205596199320018349 4889613827098574745006881)
                  ·
                    refine ⟨3667210370323931058755161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4889613827098574745006881 3667210370323931058755161)
                    ·
                      refine ⟨2750407777742948294066371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3667210370323931058755161 2750407777742948294066371)
                      ·
                        rfl

theorem cell23_5356400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 3, 2, 2].length) (baseStart_5356400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356400 prefixEnd_5356400 := by exact prefixLift 5356400
  have htrace : WordTrace (prefixWord ++ tailWord_5356400) baseStart_5356400 baseEnd_5356400 := by
    simpa [prefixWord, tailWord_5356400, baseEnd_5356400] using wordTrace_append hprefix tailTrace_5356400
  have hstable : (prefixWord ++ tailWord_5356400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356400).length < 2 ^ (prefixWord ++ tailWord_5356400).sum := by decide
  have hdescent : baseEnd_5356400 < baseStart_5356400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356414 : List Nat := [4, 2, 3, 1, 3, 1, 1, 2, 1, 5]
def baseStart_5356414 : Nat := 118140960795 + 5356414 * 2 ^ 59
def prefixEnd_5356414 : Nat := 4983230072969 + 3 ^ 40 * 5356414 * 2
def baseEnd_5356414 : Nat := 916804988824037079763769

theorem tailTrace_5356414 : CollatzResearch.WordTrace tailWord_5356414 prefixEnd_5356414 916804988824037079763769 := by
  unfold tailWord_5356414
  simp only [CollatzResearch.WordTrace]
  refine ⟨24420558552079294440643537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130242978944422903683432197 24420558552079294440643537)
  ·
    refine ⟨18315418914059470830482653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24420558552079294440643537 18315418914059470830482653)
    ·
      refine ⟨6868282092772301561430995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18315418914059470830482653 6868282092772301561430995)
      ·
        refine ⟨10302423139158452342146493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6868282092772301561430995 10302423139158452342146493)
        ·
          refine ⟨3863408677184419628304935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10302423139158452342146493 3863408677184419628304935)
          ·
            refine ⟨5795113015776629442457403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3863408677184419628304935 5795113015776629442457403)
            ·
              refine ⟨8692669523664944163686105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5795113015776629442457403 8692669523664944163686105)
              ·
                refine ⟨6519502142748708122764579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8692669523664944163686105 6519502142748708122764579)
                ·
                  refine ⟨9779253214123062184146869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6519502142748708122764579 9779253214123062184146869)
                  ·
                    refine ⟨916804988824037079763769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9779253214123062184146869 916804988824037079763769)
                    ·
                      rfl

theorem cell23_5356414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_5356414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356414 prefixEnd_5356414 := by exact prefixLift 5356414
  have htrace : WordTrace (prefixWord ++ tailWord_5356414) baseStart_5356414 baseEnd_5356414 := by
    simpa [prefixWord, tailWord_5356414, baseEnd_5356414] using wordTrace_append hprefix tailTrace_5356414
  have hstable : (prefixWord ++ tailWord_5356414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356414).length < 2 ^ (prefixWord ++ tailWord_5356414).sum := by decide
  have hdescent : baseEnd_5356414 < baseStart_5356414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356490 : List Nat := [3, 1, 2, 1, 2, 1, 1, 4, 4, 2, 2]
def baseStart_5356490 : Nat := 118140960795 + 5356490 * 2 ^ 59
def prefixEnd_5356490 : Nat := 4983230072969 + 3 ^ 40 * 5356490 * 2
def baseEnd_5356490 : Nat := 2750453991001852941940957

theorem tailTrace_5356490 : CollatzResearch.WordTrace tailWord_5356490 prefixEnd_5356490 2750453991001852941940957 := by
  unfold tailWord_5356490
  simp only [CollatzResearch.WordTrace]
  refine ⟨48841810091089755126228731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130244826909572680336609949 48841810091089755126228731)
  ·
    refine ⟨73262715136634632689343097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48841810091089755126228731 73262715136634632689343097)
    ·
      refine ⟨54947036352475974517007323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73262715136634632689343097 54947036352475974517007323)
      ·
        refine ⟨82420554528713961775510985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54947036352475974517007323 82420554528713961775510985)
        ·
          refine ⟨61815415896535471331633239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82420554528713961775510985 61815415896535471331633239)
          ·
            refine ⟨92723123844803206997449859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61815415896535471331633239 92723123844803206997449859)
            ·
              refine ⟨139084685767204810496174789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92723123844803206997449859 139084685767204810496174789)
              ·
                refine ⟨26078378581350901968032773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139084685767204810496174789 26078378581350901968032773)
                ·
                  refine ⟨4889695984003294119006145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26078378581350901968032773 4889695984003294119006145)
                  ·
                    refine ⟨3667271988002470589254609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4889695984003294119006145 3667271988002470589254609)
                    ·
                      refine ⟨2750453991001852941940957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3667271988002470589254609 2750453991001852941940957)
                      ·
                        rfl

theorem cell23_5356490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 4, 2, 2].length) (baseStart_5356490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356490 prefixEnd_5356490 := by exact prefixLift 5356490
  have htrace : WordTrace (prefixWord ++ tailWord_5356490) baseStart_5356490 baseEnd_5356490 := by
    simpa [prefixWord, tailWord_5356490, baseEnd_5356490] using wordTrace_append hprefix tailTrace_5356490
  have hstable : (prefixWord ++ tailWord_5356490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356490).length < 2 ^ (prefixWord ++ tailWord_5356490).sum := by decide
  have hdescent : baseEnd_5356490 < baseStart_5356490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356494 : List Nat := [4, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2]
def baseStart_5356494 : Nat := 118140960795 + 5356494 * 2 ^ 59
def prefixEnd_5356494 : Nat := 4983230072969 + 3 ^ 40 * 5356494 * 2
def baseEnd_5356494 : Nat := 2750456044924470926290939

theorem tailTrace_5356494 : CollatzResearch.WordTrace tailWord_5356494 prefixEnd_5356494 2750456044924470926290939 := by
  unfold tailWord_5356494
  simp only [CollatzResearch.WordTrace]
  refine ⟨24420923282043066148507567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130244924170896352792040357 24420923282043066148507567)
  ·
    refine ⟨36631384923064599222761351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24420923282043066148507567 36631384923064599222761351)
    ·
      refine ⟨54947077384596898834142027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36631384923064599222761351 54947077384596898834142027)
      ·
        refine ⟨82420616076895348251213041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54947077384596898834142027 82420616076895348251213041)
        ·
          refine ⟨61815462057671511188409781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82420616076895348251213041 61815462057671511188409781)
          ·
            refine ⟨5795199567906704173913417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61815462057671511188409781 5795199567906704173913417)
            ·
              refine ⟨4346399675930028130435063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5795199567906704173913417 4346399675930028130435063)
              ·
                refine ⟨6519599513895042195652595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4346399675930028130435063 6519599513895042195652595)
                ·
                  refine ⟨9779399270842563293478893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6519599513895042195652595 9779399270842563293478893)
                  ·
                    refine ⟨3667274726565961235054585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9779399270842563293478893 3667274726565961235054585)
                    ·
                      refine ⟨2750456044924470926290939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3667274726565961235054585 2750456044924470926290939)
                      ·
                        rfl

theorem cell23_5356494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2].length) (baseStart_5356494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356494 prefixEnd_5356494 := by exact prefixLift 5356494
  have htrace : WordTrace (prefixWord ++ tailWord_5356494) baseStart_5356494 baseEnd_5356494 := by
    simpa [prefixWord, tailWord_5356494, baseEnd_5356494] using wordTrace_append hprefix tailTrace_5356494
  have hstable : (prefixWord ++ tailWord_5356494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356494).length < 2 ^ (prefixWord ++ tailWord_5356494).sum := by decide
  have hdescent : baseEnd_5356494 < baseStart_5356494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356536 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 3, 2, 5]
def baseStart_5356536 : Nat := 118140960795 + 5356536 * 2 ^ 59
def prefixEnd_5356536 : Nat := 4983230072969 + 3 ^ 40 * 5356536 * 2
def baseEnd_5356536 : Nat := 2750477611111959761965745

theorem tailTrace_5356536 : CollatzResearch.WordTrace tailWord_5356536 prefixEnd_5356536 2750477611111959761965745 := by
  unfold tailWord_5356536
  simp only [CollatzResearch.WordTrace]
  refine ⟨97684459061096185180544731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130245945414794913574059641 97684459061096185180544731)
  ·
    refine ⟨146526688591644277770817097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97684459061096185180544731 146526688591644277770817097)
    ·
      refine ⟨109895016443733208328112823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146526688591644277770817097 109895016443733208328112823)
      ·
        refine ⟨164842524665599812492169235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109895016443733208328112823 164842524665599812492169235)
        ·
          refine ⟨247263786998399718738253853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164842524665599812492169235 247263786998399718738253853)
          ·
            refine ⟨92723920124399894526845195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 247263786998399718738253853 92723920124399894526845195)
            ·
              refine ⟨139085880186599841790267793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92723920124399894526845195 139085880186599841790267793)
              ·
                refine ⟨104314410139949881342700845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139085880186599841790267793 104314410139949881342700845)
                ·
                  refine ⟨39117903802481205503512817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104314410139949881342700845 39117903802481205503512817)
                  ·
                    refine ⟨29338427851860904127634613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39117903802481205503512817 29338427851860904127634613)
                    ·
                      refine ⟨2750477611111959761965745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29338427851860904127634613 2750477611111959761965745)
                      ·
                        rfl

theorem cell23_5356536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_5356536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356536 prefixEnd_5356536 := by exact prefixLift 5356536
  have htrace : WordTrace (prefixWord ++ tailWord_5356536) baseStart_5356536 baseEnd_5356536 := by
    simpa [prefixWord, tailWord_5356536, baseEnd_5356536] using wordTrace_append hprefix tailTrace_5356536
  have hstable : (prefixWord ++ tailWord_5356536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356536).length < 2 ^ (prefixWord ++ tailWord_5356536).sum := by decide
  have hdescent : baseEnd_5356536 < baseStart_5356536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356590 : List Nat := [4, 1, 3, 1, 1, 1, 2, 1, 5, 4]
def baseStart_5356590 : Nat := 118140960795 + 5356590 * 2 ^ 59
def prefixEnd_5356590 : Nat := 4983230072969 + 3 ^ 40 * 5356590 * 2
def baseEnd_5356590 : Nat := 916835113022434183563499

theorem tailTrace_5356590 : CollatzResearch.WordTrace tailWord_5356590 prefixEnd_5356590 916835113022434183563499 := by
  unfold tailWord_5356590
  simp only [CollatzResearch.WordTrace]
  refine ⟨24421360957999592197944403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130247258442664491722370149 24421360957999592197944403)
  ·
    refine ⟨36632041436999388296916605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24421360957999592197944403 36632041436999388296916605)
    ·
      refine ⟨13737015538874770611343727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36632041436999388296916605 13737015538874770611343727)
      ·
        refine ⟨20605523308312155917015591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13737015538874770611343727 20605523308312155917015591)
        ·
          refine ⟨30908284962468233875523387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20605523308312155917015591 30908284962468233875523387)
          ·
            refine ⟨46362427443702350813285081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30908284962468233875523387 46362427443702350813285081)
            ·
              refine ⟨34771820582776763109963811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46362427443702350813285081 34771820582776763109963811)
              ·
                refine ⟨52157730874165144664945717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34771820582776763109963811 52157730874165144664945717)
                ·
                  refine ⟨4889787269452982312338661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52157730874165144664945717 4889787269452982312338661)
                  ·
                    refine ⟨916835113022434183563499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4889787269452982312338661 916835113022434183563499)
                    ·
                      rfl

theorem cell23_5356590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_5356590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356590 prefixEnd_5356590 := by exact prefixLift 5356590
  have htrace : WordTrace (prefixWord ++ tailWord_5356590) baseStart_5356590 baseEnd_5356590 := by
    simpa [prefixWord, tailWord_5356590, baseEnd_5356590] using wordTrace_append hprefix tailTrace_5356590
  have hstable : (prefixWord ++ tailWord_5356590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356590).length < 2 ^ (prefixWord ++ tailWord_5356590).sum := by decide
  have hdescent : baseEnd_5356590 < baseStart_5356590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356600 : List Nat := [2, 1, 2, 1, 5, 1, 1, 3, 2, 2, 3]
def baseStart_5356600 : Nat := 118140960795 + 5356600 * 2 ^ 59
def prefixEnd_5356600 : Nat := 4983230072969 + 3 ^ 40 * 5356600 * 2
def baseEnd_5356600 : Nat := 2750510473873847511565451

theorem tailTrace_5356600 : CollatzResearch.WordTrace tailWord_5356600 prefixEnd_5356600 2750510473873847511565451 := by
  unfold tailWord_5356600
  simp only [CollatzResearch.WordTrace]
  refine ⟨97685626196980254645709627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130247501595973672860946169 97685626196980254645709627)
  ·
    refine ⟨146528439295470381968564441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97685626196980254645709627 146528439295470381968564441)
    ·
      refine ⟨109896329471602786476423331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146528439295470381968564441 109896329471602786476423331)
      ·
        refine ⟨164844494207404179714634997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109896329471602786476423331 164844494207404179714634997)
        ·
          refine ⟨15454171331944141848247031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 164844494207404179714634997 15454171331944141848247031)
          ·
            refine ⟨23181256997916212772370547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15454171331944141848247031 23181256997916212772370547)
            ·
              refine ⟨34771885496874319158555821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23181256997916212772370547 34771885496874319158555821)
              ·
                refine ⟨13039457061327869684458433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34771885496874319158555821 13039457061327869684458433)
                ·
                  refine ⟨9779592795995902263343825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13039457061327869684458433 9779592795995902263343825)
                  ·
                    refine ⟨7334694596996926697507869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9779592795995902263343825 7334694596996926697507869)
                    ·
                      refine ⟨2750510473873847511565451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7334694596996926697507869 2750510473873847511565451)
                      ·
                        rfl

theorem cell23_5356600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 2, 2, 3].length) (baseStart_5356600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356600 prefixEnd_5356600 := by exact prefixLift 5356600
  have htrace : WordTrace (prefixWord ++ tailWord_5356600) baseStart_5356600 baseEnd_5356600 := by
    simpa [prefixWord, tailWord_5356600, baseEnd_5356600] using wordTrace_append hprefix tailTrace_5356600
  have hstable : (prefixWord ++ tailWord_5356600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356600).length < 2 ^ (prefixWord ++ tailWord_5356600).sum := by decide
  have hdescent : baseEnd_5356600 < baseStart_5356600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356640 : List Nat := [2, 1, 1, 3, 2, 2, 2, 2, 1, 5, 2]
def baseStart_5356640 : Nat := 118140960795 + 5356640 * 2 ^ 59
def prefixEnd_5356640 : Nat := 4983230072969 + 3 ^ 40 * 5356640 * 2
def baseEnd_5356640 : Nat := 2750531013100027355065267

theorem tailTrace_5356640 : CollatzResearch.WordTrace tailWord_5356640 prefixEnd_5356640 2750531013100027355065267 := by
  unfold tailWord_5356640
  simp only [CollatzResearch.WordTrace]
  refine ⟨97686355656907798061437687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130248474209210397415250249 97686355656907798061437687)
  ·
    refine ⟨146529533485361697092156531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97686355656907798061437687 146529533485361697092156531)
    ·
      refine ⟨219794300228042545638234797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146529533485361697092156531 219794300228042545638234797)
      ·
        refine ⟨82422862585515954614338049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219794300228042545638234797 82422862585515954614338049)
        ·
          refine ⟨61817146939136965960753537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82422862585515954614338049 61817146939136965960753537)
          ·
            refine ⟨46362860204352724470565153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61817146939136965960753537 46362860204352724470565153)
            ·
              refine ⟨34772145153264543352923865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46362860204352724470565153 34772145153264543352923865)
              ·
                refine ⟨26079108864948407514692899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34772145153264543352923865 26079108864948407514692899)
                ·
                  refine ⟨39118663297422611272039349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26079108864948407514692899 39118663297422611272039349)
                  ·
                    refine ⟨3667374684133369806753689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39118663297422611272039349 3667374684133369806753689)
                    ·
                      refine ⟨2750531013100027355065267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3667374684133369806753689 2750531013100027355065267)
                      ·
                        rfl

theorem cell23_5356640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 1, 5, 2].length) (baseStart_5356640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356640 prefixEnd_5356640 := by exact prefixLift 5356640
  have htrace : WordTrace (prefixWord ++ tailWord_5356640) baseStart_5356640 baseEnd_5356640 := by
    simpa [prefixWord, tailWord_5356640, baseEnd_5356640] using wordTrace_append hprefix tailTrace_5356640
  have hstable : (prefixWord ++ tailWord_5356640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356640).length < 2 ^ (prefixWord ++ tailWord_5356640).sum := by decide
  have hdescent : baseEnd_5356640 < baseStart_5356640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356647 : List Nat := [1, 1, 5, 1, 1, 4, 1, 2, 3, 1, 3]
def baseStart_5356647 : Nat := 118140960795 + 5356647 * 2 ^ 59
def prefixEnd_5356647 : Nat := 4983230072969 + 3 ^ 40 * 5356647 * 2
def baseEnd_5356647 : Nat := 2750534607464608827677735

theorem tailTrace_5356647 : CollatzResearch.WordTrace tailWord_5356647 prefixEnd_5356647 2750534607464608827677735 := by
  unfold tailWord_5356647
  simp only [CollatzResearch.WordTrace]
  refine ⟨195372966624790236318380195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130248644416526824212253463 195372966624790236318380195)
  ·
    refine ⟨293059449937185354477570293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195372966624790236318380195 293059449937185354477570293)
    ·
      refine ⟨27474323431611126982272215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 293059449937185354477570293 27474323431611126982272215)
      ·
        refine ⟨41211485147416690473408323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27474323431611126982272215 41211485147416690473408323)
        ·
          refine ⟨61817227721125035710112485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41211485147416690473408323 61817227721125035710112485)
          ·
            refine ⟨11590730197710944195646091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61817227721125035710112485 11590730197710944195646091)
            ·
              refine ⟨17386095296566416293469137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11590730197710944195646091 17386095296566416293469137)
              ·
                refine ⟨13039571472424812220101853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17386095296566416293469137 13039571472424812220101853)
                ·
                  refine ⟨4889839302159304582538195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13039571472424812220101853 4889839302159304582538195)
                  ·
                    refine ⟨7334758953238956873807293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4889839302159304582538195 7334758953238956873807293)
                    ·
                      refine ⟨2750534607464608827677735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7334758953238956873807293 2750534607464608827677735)
                      ·
                        rfl

theorem cell23_5356647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_5356647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356647 prefixEnd_5356647 := by exact prefixLift 5356647
  have htrace : WordTrace (prefixWord ++ tailWord_5356647) baseStart_5356647 baseEnd_5356647 := by
    simpa [prefixWord, tailWord_5356647, baseEnd_5356647] using wordTrace_append hprefix tailTrace_5356647
  have hstable : (prefixWord ++ tailWord_5356647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356647).length < 2 ^ (prefixWord ++ tailWord_5356647).sum := by decide
  have hdescent : baseEnd_5356647 < baseStart_5356647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356650 : List Nat := [3, 1, 3, 2, 2, 1, 2, 1, 3, 5]
def baseStart_5356650 : Nat := 118140960795 + 5356650 * 2 ^ 59
def prefixEnd_5356650 : Nat := 4983230072969 + 3 ^ 40 * 5356650 * 2
def baseEnd_5356650 : Nat := 916845382635524105313407

theorem tailTrace_5356650 : CollatzResearch.WordTrace tailWord_5356650 prefixEnd_5356650 916845382635524105313407 := by
  unfold tailWord_5356650
  simp only [CollatzResearch.WordTrace]
  refine ⟨48843269010944841957684851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130248717362519578553826269 48843269010944841957684851)
  ·
    refine ⟨73264903516417262936527277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48843269010944841957684851 73264903516417262936527277)
    ·
      refine ⟨27474338818656473601197729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73264903516417262936527277 27474338818656473601197729)
      ·
        refine ⟨20605754113992355200898297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27474338818656473601197729 20605754113992355200898297)
        ·
          refine ⟨15454315585494266400673723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20605754113992355200898297 15454315585494266400673723)
          ·
            refine ⟨23181473378241399601010585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15454315585494266400673723 23181473378241399601010585)
            ·
              refine ⟨17386105033681049700757939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23181473378241399601010585 17386105033681049700757939)
              ·
                refine ⟨26079157550521574551136909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17386105033681049700757939 26079157550521574551136909)
                ·
                  refine ⟨9779684081445590456676341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26079157550521574551136909 9779684081445590456676341)
                  ·
                    refine ⟨916845382635524105313407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9779684081445590456676341 916845382635524105313407)
                    ·
                      rfl

theorem cell23_5356650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_5356650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356650 prefixEnd_5356650 := by exact prefixLift 5356650
  have htrace : WordTrace (prefixWord ++ tailWord_5356650) baseStart_5356650 baseEnd_5356650 := by
    simpa [prefixWord, tailWord_5356650, baseEnd_5356650] using wordTrace_append hprefix tailTrace_5356650
  have hstable : (prefixWord ++ tailWord_5356650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356650).length < 2 ^ (prefixWord ++ tailWord_5356650).sum := by decide
  have hdescent : baseEnd_5356650 < baseStart_5356650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356663 : List Nat := [1, 1, 3, 1, 1, 4, 1, 4, 1, 6]
def baseStart_5356663 : Nat := 118140960795 + 5356663 * 2 ^ 59
def prefixEnd_5356663 : Nat := 4983230072969 + 3 ^ 40 * 5356663 * 2
def baseEnd_5356663 : Nat := 916847607718360255025887

theorem tailTrace_5356663 : CollatzResearch.WordTrace tailWord_5356663 prefixEnd_5356663 916847607718360255025887 := by
  unfold tailWord_5356663
  simp only [CollatzResearch.WordTrace]
  refine ⟨195373550192732271050962643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130249033461821514033975095 195373550192732271050962643)
  ·
    refine ⟨293060325289098406576443965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195373550192732271050962643 293060325289098406576443965)
    ·
      refine ⟨109897621983411902466166487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293060325289098406576443965 109897621983411902466166487)
      ·
        refine ⟨164846432975117853699249731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109897621983411902466166487 164846432975117853699249731)
        ·
          refine ⟨247269649462676780548874597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164846432975117853699249731 247269649462676780548874597)
          ·
            refine ⟨46363059274251896352913987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 247269649462676780548874597 46363059274251896352913987)
            ·
              refine ⟨69544588911377844529370981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46363059274251896352913987 69544588911377844529370981)
              ·
                refine ⟨13039610420883345849257059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69544588911377844529370981 13039610420883345849257059)
                ·
                  refine ⟨19559415631325018773885589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13039610420883345849257059 19559415631325018773885589)
                  ·
                    refine ⟨916847607718360255025887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19559415631325018773885589 916847607718360255025887)
                    ·
                      rfl

theorem cell23_5356663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 6].length) (baseStart_5356663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356663 prefixEnd_5356663 := by exact prefixLift 5356663
  have htrace : WordTrace (prefixWord ++ tailWord_5356663) baseStart_5356663 baseEnd_5356663 := by
    simpa [prefixWord, tailWord_5356663, baseEnd_5356663] using wordTrace_append hprefix tailTrace_5356663
  have hstable : (prefixWord ++ tailWord_5356663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356663).length < 2 ^ (prefixWord ++ tailWord_5356663).sum := by decide
  have hdescent : baseEnd_5356663 < baseStart_5356663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356683 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 4]
def baseStart_5356683 : Nat := 118140960795 + 5356683 * 2 ^ 59
def prefixEnd_5356683 : Nat := 4983230072969 + 3 ^ 40 * 5356683 * 2
def baseEnd_5356683 : Nat := 2750553092768170686827569

theorem tailTrace_5356683 : CollatzResearch.WordTrace tailWord_5356683 prefixEnd_5356683 2750553092768170686827569 := by
  unfold tailWord_5356683
  simp only [CollatzResearch.WordTrace]
  refine ⟨195374279652659814466690703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130249519768439876311127135 195374279652659814466690703)
  ·
    refine ⟨293061419478989721700036055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195374279652659814466690703 293061419478989721700036055)
    ·
      refine ⟨439592129218484582550054083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293061419478989721700036055 439592129218484582550054083)
      ·
        refine ⟨659388193827726873825081125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439592129218484582550054083 659388193827726873825081125)
        ·
          refine ⟨123635286342698788842202711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 659388193827726873825081125 123635286342698788842202711)
          ·
            refine ⟨185452929514048183263304067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123635286342698788842202711 185452929514048183263304067)
            ·
              refine ⟨278179394271072274894956101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185452929514048183263304067 278179394271072274894956101)
              ·
                refine ⟨52158636425826051542804269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 278179394271072274894956101 52158636425826051542804269)
                ·
                  refine ⟨19559488659684769328551601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52158636425826051542804269 19559488659684769328551601)
                  ·
                    refine ⟨14669616494763576996413701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19559488659684769328551601 14669616494763576996413701)
                    ·
                      refine ⟨2750553092768170686827569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14669616494763576996413701 2750553092768170686827569)
                      ·
                        rfl

theorem cell23_5356683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 4].length) (baseStart_5356683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356683 prefixEnd_5356683 := by exact prefixLift 5356683
  have htrace : WordTrace (prefixWord ++ tailWord_5356683) baseStart_5356683 baseEnd_5356683 := by
    simpa [prefixWord, tailWord_5356683, baseEnd_5356683] using wordTrace_append hprefix tailTrace_5356683
  have hstable : (prefixWord ++ tailWord_5356683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356683).length < 2 ^ (prefixWord ++ tailWord_5356683).sum := by decide
  have hdescent : baseEnd_5356683 < baseStart_5356683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356690 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_5356690 : Nat := 118140960795 + 5356690 * 2 ^ 59
def prefixEnd_5356690 : Nat := 4983230072969 + 3 ^ 40 * 5356690 * 2
def baseEnd_5356690 : Nat := 2750556687132752159440037

theorem tailTrace_5356690 : CollatzResearch.WordTrace tailWord_5356690 prefixEnd_5356690 2750556687132752159440037 := by
  unfold tailWord_5356690
  simp only [CollatzResearch.WordTrace]
  refine ⟨48843633740908613665548881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130249689975756303108130349 48843633740908613665548881)
  ·
    refine ⟨36632725305681460249161661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48843633740908613665548881 36632725305681460249161661)
    ·
      refine ⟨13737271989630547593435623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36632725305681460249161661 13737271989630547593435623)
      ·
        refine ⟨20605907984445821390153435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13737271989630547593435623 20605907984445821390153435)
        ·
          refine ⟨30908861976668732085230153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20605907984445821390153435 30908861976668732085230153)
          ·
            refine ⟨23181646482501549063922615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30908861976668732085230153 23181646482501549063922615)
            ·
              refine ⟨34772469723752323595883923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23181646482501549063922615 34772469723752323595883923)
              ·
                refine ⟨52158704585628485393825885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34772469723752323595883923 52158704585628485393825885)
                ·
                  refine ⟨19559514219610682022684707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52158704585628485393825885 19559514219610682022684707)
                  ·
                    refine ⟨29339271329416023034027061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19559514219610682022684707 29339271329416023034027061)
                    ·
                      refine ⟨2750556687132752159440037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29339271329416023034027061 2750556687132752159440037)
                      ·
                        rfl

theorem cell23_5356690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_5356690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356690 prefixEnd_5356690 := by exact prefixLift 5356690
  have htrace : WordTrace (prefixWord ++ tailWord_5356690) baseStart_5356690 baseEnd_5356690 := by
    simpa [prefixWord, tailWord_5356690, baseEnd_5356690] using wordTrace_append hprefix tailTrace_5356690
  have hstable : (prefixWord ++ tailWord_5356690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356690).length < 2 ^ (prefixWord ++ tailWord_5356690).sum := by decide
  have hdescent : baseEnd_5356690 < baseStart_5356690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356700 : List Nat := [2, 2, 3, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_5356700 : Nat := 118140960795 + 5356700 * 2 ^ 59
def prefixEnd_5356700 : Nat := 4983230072969 + 3 ^ 40 * 5356700 * 2
def baseEnd_5356700 : Nat := 2750561821939297120314991

theorem tailTrace_5356700 : CollatzResearch.WordTrace tailWord_5356700 prefixEnd_5356700 2750561821939297120314991 := by
  unfold tailWord_5356700
  simp only [CollatzResearch.WordTrace]
  refine ⟨97687449846799113185029777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130249933129065484246706369 97687449846799113185029777)
  ·
    refine ⟨73265587385099334888772333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97687449846799113185029777 73265587385099334888772333)
    ·
      refine ⟨27474595269412250583289625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73265587385099334888772333 27474595269412250583289625)
      ·
        refine ⟨20605946452059187937467219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27474595269412250583289625 20605946452059187937467219)
        ·
          refine ⟨30908919678088781906200829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20605946452059187937467219 30908919678088781906200829)
          ·
            refine ⟨11590844879283293214825311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30908919678088781906200829 11590844879283293214825311)
            ·
              refine ⟨17386267318924939822237967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11590844879283293214825311 17386267318924939822237967)
              ·
                refine ⟨26079400978387409733356951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17386267318924939822237967 26079400978387409733356951)
                ·
                  refine ⟨39119101467581114600035427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26079400978387409733356951 39119101467581114600035427)
                  ·
                    refine ⟨58678652201371671900053141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39119101467581114600035427 58678652201371671900053141)
                    ·
                      refine ⟨2750561821939297120314991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58678652201371671900053141 2750561821939297120314991)
                      ·
                        rfl

theorem cell23_5356700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_5356700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356700 prefixEnd_5356700 := by exact prefixLift 5356700
  have htrace : WordTrace (prefixWord ++ tailWord_5356700) baseStart_5356700 baseEnd_5356700 := by
    simpa [prefixWord, tailWord_5356700, baseEnd_5356700] using wordTrace_append hprefix tailTrace_5356700
  have hstable : (prefixWord ++ tailWord_5356700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356700).length < 2 ^ (prefixWord ++ tailWord_5356700).sum := by decide
  have hdescent : baseEnd_5356700 < baseStart_5356700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356753 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 1, 8]
def baseStart_5356753 : Nat := 118140960795 + 5356753 * 2 ^ 59
def prefixEnd_5356753 : Nat := 4983230072969 + 3 ^ 40 * 5356753 * 2
def baseEnd_5356753 : Nat := 916863012137995137650749

theorem tailTrace_5356753 : CollatzResearch.WordTrace tailWord_5356753 prefixEnd_5356753 916863012137995137650749 := by
  unfold tailWord_5356753
  simp only [CollatzResearch.WordTrace]
  refine ⟨195376832762406216421738913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130251221841604144281159275 195376832762406216421738913)
  ·
    refine ⟨146532624571804662316304185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195376832762406216421738913 146532624571804662316304185)
    ·
      refine ⟨109899468428853496737228139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146532624571804662316304185 109899468428853496737228139)
      ·
        refine ⟨164849202643280245105842209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109899468428853496737228139 164849202643280245105842209)
        ·
          refine ⟨123636901982460183829381657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164849202643280245105842209 123636901982460183829381657)
          ·
            refine ⟨92727676486845137872036243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123636901982460183829381657 92727676486845137872036243)
            ·
              refine ⟨139091514730267706808054365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92727676486845137872036243 139091514730267706808054365)
              ·
                refine ⟨52159318023850390053020387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139091514730267706808054365 52159318023850390053020387)
                ·
                  refine ⟨78238977035775585079530581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52159318023850390053020387 78238977035775585079530581)
                  ·
                    refine ⟨916863012137995137650749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78238977035775585079530581 916863012137995137650749)
                    ·
                      rfl

theorem cell23_5356753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_5356753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356753 prefixEnd_5356753 := by exact prefixLift 5356753
  have htrace : WordTrace (prefixWord ++ tailWord_5356753) baseStart_5356753 baseEnd_5356753 := by
    simpa [prefixWord, tailWord_5356753, baseEnd_5356753] using wordTrace_append hprefix tailTrace_5356753
  have hstable : (prefixWord ++ tailWord_5356753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356753).length < 2 ^ (prefixWord ++ tailWord_5356753).sum := by decide
  have hdescent : baseEnd_5356753 < baseStart_5356753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356754 : List Nat := [3, 2, 2, 2, 1, 1, 3, 3, 2, 1, 3]
def baseStart_5356754 : Nat := 118140960795 + 5356754 * 2 ^ 59
def prefixEnd_5356754 : Nat := 4983230072969 + 3 ^ 40 * 5356754 * 2
def baseEnd_5356754 : Nat := 2750589549894639909039743

theorem tailTrace_5356754 : CollatzResearch.WordTrace tailWord_5356754 prefixEnd_5356754 2750589549894639909039743 := by
  unfold tailWord_5356754
  simp only [CollatzResearch.WordTrace]
  refine ⟨48844217308850648398131329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130251246156935062395016877 48844217308850648398131329)
  ·
    refine ⟨36633162981637986298598497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48844217308850648398131329 36633162981637986298598497)
    ·
      refine ⟨27474872236228489723948873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36633162981637986298598497 27474872236228489723948873)
      ·
        refine ⟨20606154177171367292961655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27474872236228489723948873 20606154177171367292961655)
        ·
          refine ⟨30909231265757050939442483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20606154177171367292961655 30909231265757050939442483)
          ·
            refine ⟨46363846898635576409163725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30909231265757050939442483 46363846898635576409163725)
            ·
              refine ⟨17386442586988341153436397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46363846898635576409163725 17386442586988341153436397)
              ·
                refine ⟨6519915970120627932538649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17386442586988341153436397 6519915970120627932538649)
                ·
                  refine ⟨4889936977590470949403987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6519915970120627932538649 4889936977590470949403987)
                  ·
                    refine ⟨7334905466385706424105981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4889936977590470949403987 7334905466385706424105981)
                    ·
                      refine ⟨2750589549894639909039743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7334905466385706424105981 2750589549894639909039743)
                      ·
                        rfl

theorem cell23_5356754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_5356754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356754 prefixEnd_5356754 := by exact prefixLift 5356754
  have htrace : WordTrace (prefixWord ++ tailWord_5356754) baseStart_5356754 baseEnd_5356754 := by
    simpa [prefixWord, tailWord_5356754, baseEnd_5356754] using wordTrace_append hprefix tailTrace_5356754
  have hstable : (prefixWord ++ tailWord_5356754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356754).length < 2 ^ (prefixWord ++ tailWord_5356754).sum := by decide
  have hdescent : baseEnd_5356754 < baseStart_5356754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356758 : List Nat := [5, 2, 1, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_5356758 : Nat := 118140960795 + 5356758 * 2 ^ 59
def prefixEnd_5356758 : Nat := 4983230072969 + 3 ^ 40 * 5356758 * 2
def baseEnd_5356758 : Nat := 2750591603817257893389725

theorem tailTrace_5356758 : CollatzResearch.WordTrace tailWord_5356758 prefixEnd_5356758 2750591603817257893389725 := by
  unfold tailWord_5356758
  simp only [CollatzResearch.WordTrace]
  refine ⟨12211063445461756392229433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130251343418258734850447285 12211063445461756392229433)
  ·
    refine ⟨9158297584096317294172075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12211063445461756392229433 9158297584096317294172075)
    ·
      refine ⟨13737446376144475941258113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9158297584096317294172075 13737446376144475941258113)
      ·
        refine ⟨10303084782108356955943585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13737446376144475941258113 10303084782108356955943585)
        ·
          refine ⟨7727313586581267716957689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10303084782108356955943585 7727313586581267716957689)
          ·
            refine ⟨5795485189935950787718267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7727313586581267716957689 5795485189935950787718267)
            ·
              refine ⟨8693227784903926181577401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5795485189935950787718267 8693227784903926181577401)
              ·
                refine ⟨6519920838677944636183051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8693227784903926181577401 6519920838677944636183051)
                ·
                  refine ⟨9779881258016916954274577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6519920838677944636183051 9779881258016916954274577)
                  ·
                    refine ⟨7334910943512687715705933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9779881258016916954274577 7334910943512687715705933)
                    ·
                      refine ⟨2750591603817257893389725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7334910943512687715705933 2750591603817257893389725)
                      ·
                        rfl

theorem cell23_5356758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_5356758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356758 prefixEnd_5356758 := by exact prefixLift 5356758
  have htrace : WordTrace (prefixWord ++ tailWord_5356758) baseStart_5356758 baseEnd_5356758 := by
    simpa [prefixWord, tailWord_5356758, baseEnd_5356758] using wordTrace_append hprefix tailTrace_5356758
  have hstable : (prefixWord ++ tailWord_5356758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356758).length < 2 ^ (prefixWord ++ tailWord_5356758).sum := by decide
  have hdescent : baseEnd_5356758 < baseStart_5356758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356780 : List Nat := [2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 5]
def baseStart_5356780 : Nat := 118140960795 + 5356780 * 2 ^ 59
def prefixEnd_5356780 : Nat := 4983230072969 + 3 ^ 40 * 5356780 * 2
def baseEnd_5356780 : Nat := 2750602900391656807314623

theorem tailTrace_5356780 : CollatzResearch.WordTrace tailWord_5356780 prefixEnd_5356780 2750602900391656807314623 := by
  unfold tailWord_5356780
  simp only [CollatzResearch.WordTrace]
  refine ⟨97688908766654200016485897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130251878355538933355314529 97688908766654200016485897)
  ·
    refine ⟨73266681574990650012364423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97688908766654200016485897 73266681574990650012364423)
    ·
      refine ⟨109900022362485975018546635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73266681574990650012364423 109900022362485975018546635)
      ·
        refine ⟨164850033543728962527819953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109900022362485975018546635 164850033543728962527819953)
        ·
          refine ⟨123637525157796721895864965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164850033543728962527819953 123637525157796721895864965)
          ·
            refine ⟨23182035967086885355474681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123637525157796721895864965 23182035967086885355474681)
            ·
              refine ⟨17386526975315164016606011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23182035967086885355474681 17386526975315164016606011)
              ·
                refine ⟨26079790462972746024909017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17386526975315164016606011 26079790462972746024909017)
                ·
                  refine ⟨19559842847229559518681763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26079790462972746024909017 19559842847229559518681763)
                  ·
                    refine ⟨29339764270844339278022645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19559842847229559518681763 29339764270844339278022645)
                    ·
                      refine ⟨2750602900391656807314623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29339764270844339278022645 2750602900391656807314623)
                      ·
                        rfl

theorem cell23_5356780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_5356780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356780 prefixEnd_5356780 := by exact prefixLift 5356780
  have htrace : WordTrace (prefixWord ++ tailWord_5356780) baseStart_5356780 baseEnd_5356780 := by
    simpa [prefixWord, tailWord_5356780, baseEnd_5356780] using wordTrace_append hprefix tailTrace_5356780
  have hstable : (prefixWord ++ tailWord_5356780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356780).length < 2 ^ (prefixWord ++ tailWord_5356780).sum := by decide
  have hdescent : baseEnd_5356780 < baseStart_5356780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356790 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_5356790 : Nat := 118140960795 + 5356790 * 2 ^ 59
def prefixEnd_5356790 : Nat := 4983230072969 + 3 ^ 40 * 5356790 * 2
def baseEnd_5356790 : Nat := 2750608035198201768189577

theorem tailTrace_5356790 : CollatzResearch.WordTrace tailWord_5356790 prefixEnd_5356790 2750608035198201768189577 := by
  unfold tailWord_5356790
  simp only [CollatzResearch.WordTrace]
  refine ⟨12211136391454510733802239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130252121508848114493890549 12211136391454510733802239)
  ·
    refine ⟨18316704587181766100703359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12211136391454510733802239 18316704587181766100703359)
    ·
      refine ⟨27475056880772649151055039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18316704587181766100703359 27475056880772649151055039)
      ·
        refine ⟨41212585321158973726582559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27475056880772649151055039 41212585321158973726582559)
        ·
          refine ⟨61818877981738460589873839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41212585321158973726582559 61818877981738460589873839)
          ·
            refine ⟨92728316972607690884810759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61818877981738460589873839 92728316972607690884810759)
            ·
              refine ⟨139092475458911536327216139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92728316972607690884810759 139092475458911536327216139)
              ·
                refine ⟨208638713188367304490824209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139092475458911536327216139 208638713188367304490824209)
                ·
                  refine ⟨156479034891275478368118157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208638713188367304490824209 156479034891275478368118157)
                  ·
                    refine ⟨58679638084228304388044309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 156479034891275478368118157 58679638084228304388044309)
                    ·
                      refine ⟨2750608035198201768189577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58679638084228304388044309 2750608035198201768189577)
                      ·
                        rfl

theorem cell23_5356790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_5356790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356790 prefixEnd_5356790 := by exact prefixLift 5356790
  have htrace : WordTrace (prefixWord ++ tailWord_5356790) baseStart_5356790 baseEnd_5356790 := by
    simpa [prefixWord, tailWord_5356790, baseEnd_5356790] using wordTrace_append hprefix tailTrace_5356790
  have hstable : (prefixWord ++ tailWord_5356790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356790).length < 2 ^ (prefixWord ++ tailWord_5356790).sum := by decide
  have hdescent : baseEnd_5356790 < baseStart_5356790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356845 : List Nat := [1, 5, 3, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_5356845 : Nat := 118140960795 + 5356845 * 2 ^ 59
def prefixEnd_5356845 : Nat := 4983230072969 + 3 ^ 40 * 5356845 * 2
def baseEnd_5356845 : Nat := 2750636276634199053001825

theorem tailTrace_5356845 : CollatzResearch.WordTrace tailWord_5356845 prefixEnd_5356845 2750636276634199053001825 := by
  unfold tailWord_5356845
  simp only [CollatzResearch.WordTrace]
  refine ⟨195380188278072916134087989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130253458852048610756058659 195380188278072916134087989)
  ·
    refine ⟨18316892651069335887570749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 195380188278072916134087989 18316892651069335887570749)
    ·
      refine ⟨6868834744151000957839031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18316892651069335887570749 6868834744151000957839031)
      ·
        refine ⟨10303252116226501436758547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6868834744151000957839031 10303252116226501436758547)
        ·
          refine ⟨15454878174339752155137821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10303252116226501436758547 15454878174339752155137821)
          ·
            refine ⟨5795579315377407058176683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15454878174339752155137821 5795579315377407058176683)
            ·
              refine ⟨8693368973066110587265025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5795579315377407058176683 8693368973066110587265025)
              ·
                refine ⟨6520026729799582940448769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8693368973066110587265025 6520026729799582940448769)
                ·
                  refine ⟨4890020047349687205336577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6520026729799582940448769 4890020047349687205336577)
                  ·
                    refine ⟨3667515035512265404002433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4890020047349687205336577 3667515035512265404002433)
                    ·
                      refine ⟨2750636276634199053001825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3667515035512265404002433 2750636276634199053001825)
                      ·
                        rfl

theorem cell23_5356845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_5356845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356845 prefixEnd_5356845 := by exact prefixLift 5356845
  have htrace : WordTrace (prefixWord ++ tailWord_5356845) baseStart_5356845 baseEnd_5356845 := by
    simpa [prefixWord, tailWord_5356845, baseEnd_5356845] using wordTrace_append hprefix tailTrace_5356845
  have hstable : (prefixWord ++ tailWord_5356845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356845).length < 2 ^ (prefixWord ++ tailWord_5356845).sum := by decide
  have hdescent : baseEnd_5356845 < baseStart_5356845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356880 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 4]
def baseStart_5356880 : Nat := 118140960795 + 5356880 * 2 ^ 59
def prefixEnd_5356880 : Nat := 4983230072969 + 3 ^ 40 * 5356880 * 2
def baseEnd_5356880 : Nat := 2750654248457106416064163

theorem tailTrace_5356880 : CollatzResearch.WordTrace tailWord_5356880 prefixEnd_5356880 2750654248457106416064163 := by
  unfold tailWord_5356880
  simp only [CollatzResearch.WordTrace]
  refine ⟨97690732416473058555806047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130254309888630744741074729 97690732416473058555806047)
  ·
    refine ⟨146536098624709587833709071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97690732416473058555806047 146536098624709587833709071)
    ·
      refine ⟨219804147937064381750563607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146536098624709587833709071 219804147937064381750563607)
      ·
        refine ⟨329706221905596572625845411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219804147937064381750563607 329706221905596572625845411)
        ·
          refine ⟨494559332858394858938768117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329706221905596572625845411 494559332858394858938768117)
          ·
            refine ⟨46364937455474518025509511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 494559332858394858938768117 46364937455474518025509511)
            ·
              refine ⟨69547406183211777038264267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46364937455474518025509511 69547406183211777038264267)
              ·
                refine ⟨104321109274817665557396401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69547406183211777038264267 104321109274817665557396401)
                ·
                  refine ⟨78240831956113249168047301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104321109274817665557396401 78240831956113249168047301)
                  ·
                    refine ⟨14670155991771234219008869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78240831956113249168047301 14670155991771234219008869)
                    ·
                      refine ⟨2750654248457106416064163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14670155991771234219008869 2750654248457106416064163)
                      ·
                        rfl

theorem cell23_5356880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 4].length) (baseStart_5356880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356880 prefixEnd_5356880 := by exact prefixLift 5356880
  have htrace : WordTrace (prefixWord ++ tailWord_5356880) baseStart_5356880 baseEnd_5356880 := by
    simpa [prefixWord, tailWord_5356880, baseEnd_5356880] using wordTrace_append hprefix tailTrace_5356880
  have hstable : (prefixWord ++ tailWord_5356880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356880).length < 2 ^ (prefixWord ++ tailWord_5356880).sum := by decide
  have hdescent : baseEnd_5356880 < baseStart_5356880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356887 : List Nat := [1, 1, 3, 2, 3, 2, 2, 1, 1, 4, 3]
def baseStart_5356887 : Nat := 118140960795 + 5356887 * 2 ^ 59
def prefixEnd_5356887 : Nat := 4983230072969 + 3 ^ 40 * 5356887 * 2
def baseEnd_5356887 : Nat := 2750657842821687888676631

theorem tailTrace_5356887 : CollatzResearch.WordTrace tailWord_5356887 prefixEnd_5356887 2750657842821687888676631 := by
  unfold tailWord_5356887
  simp only [CollatzResearch.WordTrace]
  refine ⟨195381720143920757307116915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130254480095947171538077943 195381720143920757307116915)
  ·
    refine ⟨293072580215881135960675373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195381720143920757307116915 293072580215881135960675373)
    ·
      refine ⟨109902217580955425985253265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293072580215881135960675373 109902217580955425985253265)
      ·
        refine ⟨82426663185716569488939949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109902217580955425985253265 82426663185716569488939949)
        ·
          refine ⟨30909998694643713558352481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82426663185716569488939949 30909998694643713558352481)
          ·
            refine ⟨23182499020982785168764361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30909998694643713558352481 23182499020982785168764361)
            ·
              refine ⟨17386874265737088876573271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23182499020982785168764361 17386874265737088876573271)
              ·
                refine ⟨26080311398605633314859907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17386874265737088876573271 26080311398605633314859907)
                ·
                  refine ⟨39120467097908449972289861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26080311398605633314859907 39120467097908449972289861)
                  ·
                    refine ⟨7335087580857834369804349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39120467097908449972289861 7335087580857834369804349)
                    ·
                      refine ⟨2750657842821687888676631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7335087580857834369804349 2750657842821687888676631)
                      ·
                        rfl

theorem cell23_5356887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_5356887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356887 prefixEnd_5356887 := by exact prefixLift 5356887
  have htrace : WordTrace (prefixWord ++ tailWord_5356887) baseStart_5356887 baseEnd_5356887 := by
    simpa [prefixWord, tailWord_5356887, baseEnd_5356887] using wordTrace_append hprefix tailTrace_5356887
  have hstable : (prefixWord ++ tailWord_5356887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356887).length < 2 ^ (prefixWord ++ tailWord_5356887).sum := by decide
  have hdescent : baseEnd_5356887 < baseStart_5356887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356890 : List Nat := [3, 1, 1, 2, 1, 2, 3, 2, 8]
def baseStart_5356890 : Nat := 118140960795 + 5356890 * 2 ^ 59
def prefixEnd_5356890 : Nat := 4983230072969 + 3 ^ 40 * 5356890 * 2
def baseEnd_5356890 : Nat := 305628820362627930771013

theorem tailTrace_5356890 : CollatzResearch.WordTrace tailWord_5356890 prefixEnd_5356890 305628820362627930771013 := by
  unfold tailWord_5356890
  simp only [CollatzResearch.WordTrace]
  refine ⟨48845457390727472204869031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130254553041939925879650749 48845457390727472204869031)
  ·
    refine ⟨73268186086091208307303547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48845457390727472204869031 73268186086091208307303547)
    ·
      refine ⟨109902279129136812460955321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73268186086091208307303547 109902279129136812460955321)
      ·
        refine ⟨82426709346852609345716491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109902279129136812460955321 82426709346852609345716491)
        ·
          refine ⟨123640064020278914018574737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82426709346852609345716491 123640064020278914018574737)
          ·
            refine ⟨92730048015209185513931053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123640064020278914018574737 92730048015209185513931053)
            ·
              refine ⟨34773768005703444567724145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92730048015209185513931053 34773768005703444567724145)
              ·
                refine ⟨26080326004277583425793109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34773768005703444567724145 26080326004277583425793109)
                ·
                  refine ⟨305628820362627930771013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26080326004277583425793109 305628820362627930771013)
                  ·
                    rfl

theorem cell23_5356890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 8].length) (baseStart_5356890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356890 prefixEnd_5356890 := by exact prefixLift 5356890
  have htrace : WordTrace (prefixWord ++ tailWord_5356890) baseStart_5356890 baseEnd_5356890 := by
    simpa [prefixWord, tailWord_5356890, baseEnd_5356890] using wordTrace_append hprefix tailTrace_5356890
  have hstable : (prefixWord ++ tailWord_5356890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356890).length < 2 ^ (prefixWord ++ tailWord_5356890).sum := by decide
  have hdescent : baseEnd_5356890 < baseStart_5356890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356911 : List Nat := [1, 1, 2, 1, 3, 1, 7, 2, 1, 4]
def baseStart_5356911 : Nat := 118140960795 + 5356911 * 2 ^ 59
def prefixEnd_5356911 : Nat := 4983230072969 + 3 ^ 40 * 5356911 * 2
def baseEnd_5356911 : Nat := 916890055452465264925507

theorem tailTrace_5356911 : CollatzResearch.WordTrace tailWord_5356911 prefixEnd_5356911 916890055452465264925507 := by
  unfold tailWord_5356911
  simp only [CollatzResearch.WordTrace]
  refine ⟨195382595495833809405990587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130255063663889206270660391 195382595495833809405990587)
  ·
    refine ⟨293073893243750714108985881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195382595495833809405990587 293073893243750714108985881)
    ·
      refine ⟨219805419932813035581739411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293073893243750714108985881 219805419932813035581739411)
      ·
        refine ⟨329708129899219553372609117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219805419932813035581739411 329708129899219553372609117)
        ·
          refine ⟨123640548712207332514728419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 329708129899219553372609117 123640548712207332514728419)
          ·
            refine ⟨185460823068310998772092629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123640548712207332514728419 185460823068310998772092629)
            ·
              refine ⟨4346738040663539033720921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 185460823068310998772092629 4346738040663539033720921)
              ·
                refine ⟨3260053530497654275290691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4346738040663539033720921 3260053530497654275290691)
                ·
                  refine ⟨4890080295746481412936037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3260053530497654275290691 4890080295746481412936037)
                  ·
                    refine ⟨916890055452465264925507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4890080295746481412936037 916890055452465264925507)
                    ·
                      rfl

theorem cell23_5356911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2, 1, 4].length) (baseStart_5356911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356911 prefixEnd_5356911 := by exact prefixLift 5356911
  have htrace : WordTrace (prefixWord ++ tailWord_5356911) baseStart_5356911 baseEnd_5356911 := by
    simpa [prefixWord, tailWord_5356911, baseEnd_5356911] using wordTrace_append hprefix tailTrace_5356911
  have hstable : (prefixWord ++ tailWord_5356911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356911).length < 2 ^ (prefixWord ++ tailWord_5356911).sum := by decide
  have hdescent : baseEnd_5356911 < baseStart_5356911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356951 : List Nat := [1, 1, 3, 3, 1, 1, 1, 7, 1, 1, 3]
def baseStart_5356951 : Nat := 118140960795 + 5356951 * 2 ^ 59
def prefixEnd_5356951 : Nat := 4983230072969 + 3 ^ 40 * 5356951 * 2
def baseEnd_5356951 : Nat := 2750690705583575638276337

theorem tailTrace_5356951 : CollatzResearch.WordTrace tailWord_5356951 prefixEnd_5356951 2750690705583575638276337 := by
  unfold tailWord_5356951
  simp only [CollatzResearch.WordTrace]
  refine ⟨195384054415688896237446707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130256036277125930824964471 195384054415688896237446707)
  ·
    refine ⟨293076081623533344356170061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195384054415688896237446707 293076081623533344356170061)
    ·
      refine ⟨109903530608825004133563773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293076081623533344356170061 109903530608825004133563773)
      ·
        refine ⟨41213823978309376550086415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109903530608825004133563773 41213823978309376550086415)
        ·
          refine ⟨61820735967464064825129623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41213823978309376550086415 61820735967464064825129623)
          ·
            refine ⟨92731103951196097237694435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61820735967464064825129623 92731103951196097237694435)
            ·
              refine ⟨139096655926794145856541653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92731103951196097237694435 139096655926794145856541653)
              ·
                refine ⟨3260077873284237793512695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 139096655926794145856541653 3260077873284237793512695)
                ·
                  refine ⟨4890116809926356690269043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3260077873284237793512695 4890116809926356690269043)
                  ·
                    refine ⟨7335175214889535035403565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4890116809926356690269043 7335175214889535035403565)
                    ·
                      refine ⟨2750690705583575638276337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7335175214889535035403565 2750690705583575638276337)
                      ·
                        rfl

theorem cell23_5356951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_5356951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356951 prefixEnd_5356951 := by exact prefixLift 5356951
  have htrace : WordTrace (prefixWord ++ tailWord_5356951) baseStart_5356951 baseEnd_5356951 := by
    simpa [prefixWord, tailWord_5356951, baseEnd_5356951] using wordTrace_append hprefix tailTrace_5356951
  have hstable : (prefixWord ++ tailWord_5356951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356951).length < 2 ^ (prefixWord ++ tailWord_5356951).sum := by decide
  have hdescent : baseEnd_5356951 < baseStart_5356951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356967 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 3, 6]
def baseStart_5356967 : Nat := 118140960795 + 5356967 * 2 ^ 59
def prefixEnd_5356967 : Nat := 4983230072969 + 3 ^ 40 * 5356967 * 2
def baseEnd_5356967 : Nat := 916899640424682525225421

theorem tailTrace_5356967 : CollatzResearch.WordTrace tailWord_5356967 prefixEnd_5356967 916899640424682525225421 := by
  unfold tailWord_5356967
  simp only [CollatzResearch.WordTrace]
  refine ⟨195384637983630930970029155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130256425322420620646686103 195384637983630930970029155)
  ·
    refine ⟨293076956975446396455043733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195384637983630930970029155 293076956975446396455043733)
    ·
      refine ⟨13737982358224049833830175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 293076956975446396455043733 13737982358224049833830175)
      ·
        refine ⟨20606973537336074750745263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13737982358224049833830175 20606973537336074750745263)
        ·
          refine ⟨30910460306004112126117895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20606973537336074750745263 30910460306004112126117895)
          ·
            refine ⟨46365690459006168189176843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30910460306004112126117895 46365690459006168189176843)
            ·
              refine ⟨69548535688509252283765265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46365690459006168189176843 69548535688509252283765265)
              ·
                refine ⟨52161401766381939212823949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69548535688509252283765265 52161401766381939212823949)
                ·
                  refine ⟨19560525662393227204808981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52161401766381939212823949 19560525662393227204808981)
                  ·
                    refine ⟨916899640424682525225421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19560525662393227204808981 916899640424682525225421)
                    ·
                      rfl

theorem cell23_5356967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_5356967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356967 prefixEnd_5356967 := by exact prefixLift 5356967
  have htrace : WordTrace (prefixWord ++ tailWord_5356967) baseStart_5356967 baseEnd_5356967 := by
    simpa [prefixWord, tailWord_5356967, baseEnd_5356967] using wordTrace_append hprefix tailTrace_5356967
  have hstable : (prefixWord ++ tailWord_5356967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356967).length < 2 ^ (prefixWord ++ tailWord_5356967).sum := by decide
  have hdescent : baseEnd_5356967 < baseStart_5356967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356977 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 3, 1, 5]
def baseStart_5356977 : Nat := 118140960795 + 5356977 * 2 ^ 59
def prefixEnd_5356977 : Nat := 4983230072969 + 3 ^ 40 * 5356977 * 2
def baseEnd_5356977 : Nat := 2750704056080592536551217

theorem tailTrace_5356977 : CollatzResearch.WordTrace tailWord_5356977 prefixEnd_5356977 2750704056080592536551217 := by
  unfold tailWord_5356977
  simp only [CollatzResearch.WordTrace]
  refine ⟨195385002713594702677893185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130256668475729801785262123 195385002713594702677893185)
  ·
    refine ⟨146538752035196027008419889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195385002713594702677893185 146538752035196027008419889)
    ·
      refine ⟨109904064026397020256314917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146538752035196027008419889 109904064026397020256314917)
      ·
        refine ⟨20607012004949441298059047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109904064026397020256314917 20607012004949441298059047)
        ·
          refine ⟨30910518007424161947088571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20607012004949441298059047 30910518007424161947088571)
          ·
            refine ⟨46365777011136242920632857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30910518007424161947088571 46365777011136242920632857)
            ·
              refine ⟨34774332758352182190474643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46365777011136242920632857 34774332758352182190474643)
              ·
                refine ⟨52161499137528273285711965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34774332758352182190474643 52161499137528273285711965)
                ·
                  refine ⟨19560562176573102482141987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52161499137528273285711965 19560562176573102482141987)
                  ·
                    refine ⟨29340843264859653723212981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19560562176573102482141987 29340843264859653723212981)
                    ·
                      refine ⟨2750704056080592536551217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29340843264859653723212981 2750704056080592536551217)
                      ·
                        rfl

theorem cell23_5356977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_5356977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356977 prefixEnd_5356977 := by exact prefixLift 5356977
  have htrace : WordTrace (prefixWord ++ tailWord_5356977) baseStart_5356977 baseEnd_5356977 := by
    simpa [prefixWord, tailWord_5356977, baseEnd_5356977] using wordTrace_append hprefix tailTrace_5356977
  have hstable : (prefixWord ++ tailWord_5356977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356977).length < 2 ^ (prefixWord ++ tailWord_5356977).sum := by decide
  have hdescent : baseEnd_5356977 < baseStart_5356977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5356984 : List Nat := [2, 1, 2, 1, 2, 2, 4, 3, 2, 4]
def baseStart_5356984 : Nat := 118140960795 + 5356984 * 2 ^ 59
def prefixEnd_5356984 : Nat := 4983230072969 + 3 ^ 40 * 5356984 * 2
def baseEnd_5356984 : Nat := 916902550148391336387895

theorem tailTrace_5356984 : CollatzResearch.WordTrace tailWord_5356984 prefixEnd_5356984 916902550148391336387895 := by
  unfold tailWord_5356984
  simp only [CollatzResearch.WordTrace]
  refine ⟨97692629012284671436699003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130256838683046228582265337 97692629012284671436699003)
  ·
    refine ⟨146538943518427007155048505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97692629012284671436699003 146538943518427007155048505)
    ·
      refine ⟨109904207638820255366286379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146538943518427007155048505 109904207638820255366286379)
      ·
        refine ⟨164856311458230383049429569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109904207638820255366286379 164856311458230383049429569)
        ·
          refine ⟨123642233593672787287072177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164856311458230383049429569 123642233593672787287072177)
          ·
            refine ⟨92731675195254590465304133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123642233593672787287072177 92731675195254590465304133)
            ·
              refine ⟨17387189099110235712244525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92731675195254590465304133 17387189099110235712244525)
              ·
                refine ⟨6520195912166338392091697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17387189099110235712244525 6520195912166338392091697)
                ·
                  refine ⟨4890146934124753794068773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6520195912166338392091697 4890146934124753794068773)
                  ·
                    refine ⟨916902550148391336387895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4890146934124753794068773 916902550148391336387895)
                    ·
                      rfl

theorem cell23_5356984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 2, 4].length) (baseStart_5356984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5356984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5356984 prefixEnd_5356984 := by exact prefixLift 5356984
  have htrace : WordTrace (prefixWord ++ tailWord_5356984) baseStart_5356984 baseEnd_5356984 := by
    simpa [prefixWord, tailWord_5356984, baseEnd_5356984] using wordTrace_append hprefix tailTrace_5356984
  have hstable : (prefixWord ++ tailWord_5356984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5356984).length < 2 ^ (prefixWord ++ tailWord_5356984).sum := by decide
  have hdescent : baseEnd_5356984 < baseStart_5356984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5356984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357004 : List Nat := [2, 2, 1, 4, 2, 1, 2, 2, 1, 2, 4]
def baseStart_5357004 : Nat := 118140960795 + 5357004 * 2 ^ 59
def prefixEnd_5357004 : Nat := 4983230072969 + 3 ^ 40 * 5357004 * 2
def baseEnd_5357004 : Nat := 2750717920058263930913593

theorem tailTrace_5357004 : CollatzResearch.WordTrace tailWord_5357004 prefixEnd_5357004 2750717920058263930913593 := by
  unfold tailWord_5357004
  simp only [CollatzResearch.WordTrace]
  refine ⟨97692993742248443144563033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130257324989664590859417377 97692993742248443144563033)
  ·
    refine ⟨73269745306686332358422275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97692993742248443144563033 73269745306686332358422275)
    ·
      refine ⟨109904617960029498537633413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73269745306686332358422275 109904617960029498537633413)
      ·
        refine ⟨20607115867505530975806265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109904617960029498537633413 20607115867505530975806265)
        ·
          refine ⟨15455336900629148231854699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20607115867505530975806265 15455336900629148231854699)
          ·
            refine ⟨23183005350943722347782049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15455336900629148231854699 23183005350943722347782049)
            ·
              refine ⟨17387254013207791760836537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23183005350943722347782049 17387254013207791760836537)
              ·
                refine ⟨13040440509905843820627403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17387254013207791760836537 13040440509905843820627403)
                ·
                  refine ⟨19560660764858765730941105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13040440509905843820627403 19560660764858765730941105)
                  ·
                    refine ⟨14670495573644074298205829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19560660764858765730941105 14670495573644074298205829)
                    ·
                      refine ⟨2750717920058263930913593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14670495573644074298205829 2750717920058263930913593)
                      ·
                        rfl

theorem cell23_5357004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_5357004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357004 prefixEnd_5357004 := by exact prefixLift 5357004
  have htrace : WordTrace (prefixWord ++ tailWord_5357004) baseStart_5357004 baseEnd_5357004 := by
    simpa [prefixWord, tailWord_5357004, baseEnd_5357004] using wordTrace_append hprefix tailTrace_5357004
  have hstable : (prefixWord ++ tailWord_5357004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357004).length < 2 ^ (prefixWord ++ tailWord_5357004).sum := by decide
  have hdescent : baseEnd_5357004 < baseStart_5357004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357014 : List Nat := [5, 2, 1, 1, 1, 3, 10]
def baseStart_5357014 : Nat := 118140960795 + 5357014 * 2 ^ 59
def prefixEnd_5357014 : Nat := 4983230072969 + 3 ^ 40 * 5357014 * 2
def baseEnd_5357014 : Nat := 33959543887219862861587

theorem tailTrace_5357014 : CollatzResearch.WordTrace tailWord_5357014 prefixEnd_5357014 33959543887219862861587 := by
  unfold tailWord_5357014
  simp only [CollatzResearch.WordTrace]
  refine ⟨12211647013403791124811881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130257568142973771997993397 12211647013403791124811881)
  ·
    refine ⟨9158735260052843343608911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12211647013403791124811881 9158735260052843343608911)
    ·
      refine ⟨13738102890079265015413367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9158735260052843343608911 13738102890079265015413367)
      ·
        refine ⟨20607154335118897523120051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13738102890079265015413367 20607154335118897523120051)
        ·
          refine ⟨30910731502678346284680077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20607154335118897523120051 30910731502678346284680077)
          ·
            refine ⟨11591524313504379856755029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30910731502678346284680077 11591524313504379856755029)
            ·
              refine ⟨33959543887219862861587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11591524313504379856755029 33959543887219862861587)
              ·
                rfl

theorem cell23_5357014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 10].length) (baseStart_5357014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357014 prefixEnd_5357014 := by exact prefixLift 5357014
  have htrace : WordTrace (prefixWord ++ tailWord_5357014) baseStart_5357014 baseEnd_5357014 := by
    simpa [prefixWord, tailWord_5357014, baseEnd_5357014] using wordTrace_append hprefix tailTrace_5357014
  have hstable : (prefixWord ++ tailWord_5357014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357014).length < 2 ^ (prefixWord ++ tailWord_5357014).sum := by decide
  have hdescent : baseEnd_5357014 < baseStart_5357014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357041 : List Nat := [1, 2, 2, 2, 3, 4, 1, 1, 1, 3, 3]
def baseStart_5357041 : Nat := 118140960795 + 5357041 * 2 ^ 59
def prefixEnd_5357041 : Nat := 4983230072969 + 3 ^ 40 * 5357041 * 2
def baseEnd_5357041 : Nat := 2750736918842480286150923

theorem tailTrace_5357041 : CollatzResearch.WordTrace tailWord_5357041 prefixEnd_5357041 2750736918842480286150923 := by
  unfold tailWord_5357041
  simp only [CollatzResearch.WordTrace]
  refine ⟨195387336985362841608222977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130258224656908561072148651 195387336985362841608222977)
  ·
    refine ⟨146540502739022131206167233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195387336985362841608222977 146540502739022131206167233)
    ·
      refine ⟨109905377054266598404625425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146540502739022131206167233 109905377054266598404625425)
      ·
        refine ⟨82429032790699948803469069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109905377054266598404625425 82429032790699948803469069)
        ·
          refine ⟨30910887296512480801300901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82429032790699948803469069 30910887296512480801300901)
          ·
            refine ⟨5795791368096090150243919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30910887296512480801300901 5795791368096090150243919)
            ·
              refine ⟨8693687052144135225365879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5795791368096090150243919 8693687052144135225365879)
              ·
                refine ⟨13040530578216202838048819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8693687052144135225365879 13040530578216202838048819)
                ·
                  refine ⟨19560795867324304257073229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13040530578216202838048819 19560795867324304257073229)
                  ·
                    refine ⟨7335298450246614096402461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19560795867324304257073229 7335298450246614096402461)
                    ·
                      refine ⟨2750736918842480286150923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7335298450246614096402461 2750736918842480286150923)
                      ·
                        rfl

theorem cell23_5357041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_5357041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357041 prefixEnd_5357041 := by exact prefixLift 5357041
  have htrace : WordTrace (prefixWord ++ tailWord_5357041) baseStart_5357041 baseEnd_5357041 := by
    simpa [prefixWord, tailWord_5357041, baseEnd_5357041] using wordTrace_append hprefix tailTrace_5357041
  have hstable : (prefixWord ++ tailWord_5357041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357041).length < 2 ^ (prefixWord ++ tailWord_5357041).sum := by decide
  have hdescent : baseEnd_5357041 < baseStart_5357041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357058 : List Nat := [3, 4, 1, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_5357058 : Nat := 118140960795 + 5357058 * 2 ^ 59
def prefixEnd_5357058 : Nat := 4983230072969 + 3 ^ 40 * 5357058 * 2
def baseEnd_5357058 : Nat := 2750745648013606719638345

theorem tailTrace_5357058 : CollatzResearch.WordTrace tailWord_5357058 prefixEnd_5357058 2750745648013606719638345 := by
  unfold tailWord_5357058
  simp only [CollatzResearch.WordTrace]
  refine ⟨48846989256575313377897957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130258638017534169007727885 48846989256575313377897957)
  ·
    refine ⟨9158810485607871258355867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48846989256575313377897957 9158810485607871258355867)
    ·
      refine ⟨13738215728411806887533801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9158810485607871258355867 13738215728411806887533801)
      ·
        refine ⟨10303661796308855165650351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13738215728411806887533801 10303661796308855165650351)
        ·
          refine ⟨15455492694463282748475527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10303661796308855165650351 15455492694463282748475527)
          ·
            refine ⟨23183239041694924122713291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15455492694463282748475527 23183239041694924122713291)
            ·
              refine ⟨34774858562542386184069937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23183239041694924122713291 34774858562542386184069937)
              ·
                refine ⟨26081143921906789638052453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34774858562542386184069937 26081143921906789638052453)
                ·
                  refine ⟨4890214485357523057134835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26081143921906789638052453 4890214485357523057134835)
                  ·
                    refine ⟨7335321728036284585702253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4890214485357523057134835 7335321728036284585702253)
                    ·
                      refine ⟨2750745648013606719638345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7335321728036284585702253 2750745648013606719638345)
                      ·
                        rfl

theorem cell23_5357058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_5357058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357058 prefixEnd_5357058 := by exact prefixLift 5357058
  have htrace : WordTrace (prefixWord ++ tailWord_5357058) baseStart_5357058 baseEnd_5357058 := by
    simpa [prefixWord, tailWord_5357058, baseEnd_5357058] using wordTrace_append hprefix tailTrace_5357058
  have hstable : (prefixWord ++ tailWord_5357058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357058).length < 2 ^ (prefixWord ++ tailWord_5357058).sum := by decide
  have hdescent : baseEnd_5357058 < baseStart_5357058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357084 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 2, 4, 3]
def baseStart_5357084 : Nat := 118140960795 + 5357084 * 2 ^ 59
def prefixEnd_5357084 : Nat := 4983230072969 + 3 ^ 40 * 5357084 * 2
def baseEnd_5357084 : Nat := 2750758998510623617913225

theorem tailTrace_5357084 : CollatzResearch.WordTrace tailWord_5357084 prefixEnd_5357084 2750758998510623617913225 := by
  unfold tailWord_5357084
  simp only [CollatzResearch.WordTrace]
  refine ⟨97694452662103529976019153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130259270216138039968025537 97694452662103529976019153)
  ·
    refine ⟨73270839496577647482014365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97694452662103529976019153 73270839496577647482014365)
    ·
      refine ⟨27476564811216617805755387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73270839496577647482014365 27476564811216617805755387)
      ·
        refine ⟨41214847216824926708633081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27476564811216617805755387 41214847216824926708633081)
        ·
          refine ⟨30911135412618695031474811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41214847216824926708633081 30911135412618695031474811)
          ·
            refine ⟨46366703118928042547212217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30911135412618695031474811 46366703118928042547212217)
            ·
              refine ⟨34775027339196031910409163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46366703118928042547212217 34775027339196031910409163)
              ·
                refine ⟨52162541008794047865613745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34775027339196031910409163 52162541008794047865613745)
                ·
                  refine ⟨39121905756595535899210309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52162541008794047865613745 39121905756595535899210309)
                  ·
                    refine ⟨7335357329361662981101933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39121905756595535899210309 7335357329361662981101933)
                    ·
                      refine ⟨2750758998510623617913225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7335357329361662981101933 2750758998510623617913225)
                      ·
                        rfl

theorem cell23_5357084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_5357084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357084 prefixEnd_5357084 := by exact prefixLift 5357084
  have htrace : WordTrace (prefixWord ++ tailWord_5357084) baseStart_5357084 baseEnd_5357084 := by
    simpa [prefixWord, tailWord_5357084, baseEnd_5357084] using wordTrace_append hprefix tailTrace_5357084
  have hstable : (prefixWord ++ tailWord_5357084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357084).length < 2 ^ (prefixWord ++ tailWord_5357084).sum := by decide
  have hdescent : baseEnd_5357084 < baseStart_5357084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357086 : List Nat := [4, 3, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_5357086 : Nat := 118140960795 + 5357086 * 2 ^ 59
def prefixEnd_5357086 : Nat := 4983230072969 + 3 ^ 40 * 5357086 * 2
def baseEnd_5357086 : Nat := 916920008490644203362739

theorem tailTrace_5357086 : CollatzResearch.WordTrace tailWord_5357086 prefixEnd_5357086 916920008490644203362739 := by
  unfold tailWord_5357086
  simp only [CollatzResearch.WordTrace]
  refine ⟨24423622283774976786701389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130259318846799876195740741 24423622283774976786701389)
  ·
    refine ⟨9158858356415616295013021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24423622283774976786701389 9158858356415616295013021)
    ·
      refine ⟨3434571883655856110629883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9158858356415616295013021 3434571883655856110629883)
      ·
        refine ⟨5151857825483784165944825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3434571883655856110629883 5151857825483784165944825)
        ·
          refine ⟨3863893369112838124458619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5151857825483784165944825 3863893369112838124458619)
          ·
            refine ⟨5795840053669257186687929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3863893369112838124458619 5795840053669257186687929)
            ·
              refine ⟨4346880040251942890015947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5795840053669257186687929 4346880040251942890015947)
              ·
                refine ⟨6520320060377914335023921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4346880040251942890015947 6520320060377914335023921)
                ·
                  refine ⟨4890240045283435751267941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6520320060377914335023921 4890240045283435751267941)
                  ·
                    refine ⟨916920008490644203362739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4890240045283435751267941 916920008490644203362739)
                    ·
                      rfl

theorem cell23_5357086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_5357086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357086 prefixEnd_5357086 := by exact prefixLift 5357086
  have htrace : WordTrace (prefixWord ++ tailWord_5357086) baseStart_5357086 baseEnd_5357086 := by
    simpa [prefixWord, tailWord_5357086, baseEnd_5357086] using wordTrace_append hprefix tailTrace_5357086
  have hstable : (prefixWord ++ tailWord_5357086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357086).length < 2 ^ (prefixWord ++ tailWord_5357086).sum := by decide
  have hdescent : baseEnd_5357086 < baseStart_5357086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357121 : List Nat := [1, 2, 5, 1, 1, 1, 2, 5, 5]
def baseStart_5357121 : Nat := 118140960795 + 5357121 * 2 ^ 59
def prefixEnd_5357121 : Nat := 4983230072969 + 3 ^ 40 * 5357121 * 2
def baseEnd_5357121 : Nat := 305641999699426663683395

theorem tailTrace_5357121 : CollatzResearch.WordTrace tailWord_5357121 prefixEnd_5357121 305641999699426663683395 := by
  unfold tailWord_5357121
  simp only [CollatzResearch.WordTrace]
  refine ⟨195390254825073015271135217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130260169883382010180756811 195390254825073015271135217)
  ·
    refine ⟨146542691118804761453351413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195390254825073015271135217 146542691118804761453351413)
    ·
      refine ⟨13738377292387946386251695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 146542691118804761453351413 13738377292387946386251695)
      ·
        refine ⟨20607565938581919579377543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13738377292387946386251695 20607565938581919579377543)
        ·
          refine ⟨30911348907872879369066315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20607565938581919579377543 30911348907872879369066315)
          ·
            refine ⟨46367023361809319053599473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30911348907872879369066315 46367023361809319053599473)
            ·
              refine ⟨34775267521356989290199605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46367023361809319053599473 34775267521356989290199605)
              ·
                refine ⟨3260181330127217745956213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34775267521356989290199605 3260181330127217745956213)
                ·
                  refine ⟨305641999699426663683395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3260181330127217745956213 305641999699426663683395)
                  ·
                    rfl

theorem cell23_5357121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5, 5].length) (baseStart_5357121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357121 prefixEnd_5357121 := by exact prefixLift 5357121
  have htrace : WordTrace (prefixWord ++ tailWord_5357121) baseStart_5357121 baseEnd_5357121 := by
    simpa [prefixWord, tailWord_5357121, baseEnd_5357121] using wordTrace_append hprefix tailTrace_5357121
  have hstable : (prefixWord ++ tailWord_5357121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357121).length < 2 ^ (prefixWord ++ tailWord_5357121).sum := by decide
  have hdescent : baseEnd_5357121 < baseStart_5357121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357138 : List Nat := [3, 2, 2, 1, 2, 2, 4, 2, 5]
def baseStart_5357138 : Nat := 118140960795 + 5357138 * 2 ^ 59
def prefixEnd_5357138 : Nat := 4983230072969 + 3 ^ 40 * 5357138 * 2
def baseEnd_5357138 : Nat := 305642969607329600737553

theorem tailTrace_5357138 : CollatzResearch.WordTrace tailWord_5357138 prefixEnd_5357138 305642969607329600737553 := by
  unfold tailWord_5357138
  simp only [CollatzResearch.WordTrace]
  refine ⟨48847718716502856793626017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130260583244007618116336045 48847718716502856793626017)
  ·
    refine ⟨36635789037377142595219513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48847718716502856793626017 36635789037377142595219513)
    ·
      refine ⟨27476841778032856946414635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36635789037377142595219513 27476841778032856946414635)
      ·
        refine ⟨41215262667049285419621953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27476841778032856946414635 41215262667049285419621953)
        ·
          refine ⟨30911447000286964064716465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41215262667049285419621953 30911447000286964064716465)
          ·
            refine ⟨23183585250215223048537349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30911447000286964064716465 23183585250215223048537349)
            ·
              refine ⟨4346922234415354321600753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23183585250215223048537349 4346922234415354321600753)
              ·
                refine ⟨3260191675811515741200565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4346922234415354321600753 3260191675811515741200565)
                ·
                  refine ⟨305642969607329600737553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3260191675811515741200565 305642969607329600737553)
                  ·
                    rfl

theorem cell23_5357138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2, 5].length) (baseStart_5357138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357138 prefixEnd_5357138 := by exact prefixLift 5357138
  have htrace : WordTrace (prefixWord ++ tailWord_5357138) baseStart_5357138 baseEnd_5357138 := by
    simpa [prefixWord, tailWord_5357138, baseEnd_5357138] using wordTrace_append hprefix tailTrace_5357138
  have hstable : (prefixWord ++ tailWord_5357138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357138).length < 2 ^ (prefixWord ++ tailWord_5357138).sum := by decide
  have hdescent : baseEnd_5357138 < baseStart_5357138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357198 : List Nat := [4, 1, 1, 3, 1, 3, 2, 1, 3, 4]
def baseStart_5357198 : Nat := 118140960795 + 5357198 * 2 ^ 59
def prefixEnd_5357198 : Nat := 4983230072969 + 3 ^ 40 * 5357198 * 2
def baseEnd_5357198 : Nat := 916939178435078723962567

theorem tailTrace_5357198 : CollatzResearch.WordTrace tailWord_5357198 prefixEnd_5357198 916939178435078723962567 := by
  unfold tailWord_5357198
  simp only [CollatzResearch.WordTrace]
  refine ⟨24424132905724257177711031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130262042163862704947792165 24424132905724257177711031)
  ·
    refine ⟨36636199358586385766566547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24424132905724257177711031 36636199358586385766566547)
    ·
      refine ⟨54954299037879578649849821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36636199358586385766566547 54954299037879578649849821)
      ·
        refine ⟨20607862139204841993693683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54954299037879578649849821 20607862139204841993693683)
        ·
          refine ⟨30911793208807262990540525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20607862139204841993693683 30911793208807262990540525)
          ·
            refine ⟨11591922453302723621452697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30911793208807262990540525 11591922453302723621452697)
            ·
              refine ⟨8693941839977042716089523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11591922453302723621452697 8693941839977042716089523)
              ·
                refine ⟨13040912759965564074134285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8693941839977042716089523 13040912759965564074134285)
                ·
                  refine ⟨4890342284987086527800357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13040912759965564074134285 4890342284987086527800357)
                  ·
                    refine ⟨916939178435078723962567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4890342284987086527800357 916939178435078723962567)
                    ·
                      rfl

theorem cell23_5357198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_5357198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357198 prefixEnd_5357198 := by exact prefixLift 5357198
  have htrace : WordTrace (prefixWord ++ tailWord_5357198) baseStart_5357198 baseEnd_5357198 := by
    simpa [prefixWord, tailWord_5357198, baseEnd_5357198] using wordTrace_append hprefix tailTrace_5357198
  have hstable : (prefixWord ++ tailWord_5357198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357198).length < 2 ^ (prefixWord ++ tailWord_5357198).sum := by decide
  have hdescent : baseEnd_5357198 < baseStart_5357198 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357231 : List Nat := [1, 1, 2, 1, 2, 4, 1, 3, 1, 5, 2]
def baseStart_5357231 : Nat := 118140960795 + 5357231 * 2 ^ 59
def prefixEnd_5357231 : Nat := 4983230072969 + 3 ^ 40 * 5357231 * 2
def baseEnd_5357231 : Nat := 2750834480166834542775049

theorem tailTrace_5357231 : CollatzResearch.WordTrace tailWord_5357231 prefixEnd_5357231 2750834480166834542775049 := by
  unfold tailWord_5357231
  simp only [CollatzResearch.WordTrace]
  refine ⟨195394266854674504057639547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130262844569783002705093031 195394266854674504057639547)
  ·
    refine ⟨293091400282011756086459321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195394266854674504057639547 293091400282011756086459321)
    ·
      refine ⟨219818550211508817064844491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293091400282011756086459321 219818550211508817064844491)
      ·
        refine ⟨329727825317263225597266737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219818550211508817064844491 329727825317263225597266737)
        ·
          refine ⟨247295868987947419197950053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329727825317263225597266737 247295868987947419197950053)
          ·
            refine ⟨46367975435240141099615635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 247295868987947419197950053 46367975435240141099615635)
            ·
              refine ⟨69551963152860211649423453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46367975435240141099615635 69551963152860211649423453)
              ·
                refine ⟨26081986182322579368533795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69551963152860211649423453 26081986182322579368533795)
                ·
                  refine ⟨39122979273483869052800693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26081986182322579368533795 39122979273483869052800693)
                  ·
                    refine ⟨3667779306889112723700065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39122979273483869052800693 3667779306889112723700065)
                    ·
                      refine ⟨2750834480166834542775049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3667779306889112723700065 2750834480166834542775049)
                      ·
                        rfl

theorem cell23_5357231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 5, 2].length) (baseStart_5357231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357231 prefixEnd_5357231 := by exact prefixLift 5357231
  have htrace : WordTrace (prefixWord ++ tailWord_5357231) baseStart_5357231 baseEnd_5357231 := by
    simpa [prefixWord, tailWord_5357231, baseEnd_5357231] using wordTrace_append hprefix tailTrace_5357231
  have hstable : (prefixWord ++ tailWord_5357231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357231).length < 2 ^ (prefixWord ++ tailWord_5357231).sum := by decide
  have hdescent : baseEnd_5357231 < baseStart_5357231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357241 : List Nat := [1, 2, 1, 4, 1, 1, 4, 3, 1, 5]
def baseStart_5357241 : Nat := 118140960795 + 5357241 * 2 ^ 59
def prefixEnd_5357241 : Nat := 4983230072969 + 3 ^ 40 * 5357241 * 2
def baseEnd_5357241 : Nat := 916946538324459834550001

theorem tailTrace_5357241 : CollatzResearch.WordTrace tailWord_5357241 prefixEnd_5357241 916946538324459834550001 := by
  unfold tailWord_5357241
  simp only [CollatzResearch.WordTrace]
  refine ⟨195394631584638275765503577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130263087723092183843669051 195394631584638275765503577)
  ·
    refine ⟨146545973688478706824127683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195394631584638275765503577 146545973688478706824127683)
    ·
      refine ⟨219818960532718060236191525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146545973688478706824127683 219818960532718060236191525)
      ·
        refine ⟨41216055099884636294285911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219818960532718060236191525 41216055099884636294285911)
        ·
          refine ⟨61824082649826954441428867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41216055099884636294285911 61824082649826954441428867)
          ·
            refine ⟨92736123974740431662143301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61824082649826954441428867 92736123974740431662143301)
            ·
              refine ⟨17388023245263830936651869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92736123974740431662143301 17388023245263830936651869)
              ·
                refine ⟨6520508716973936601244451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17388023245263830936651869 6520508716973936601244451)
                ·
                  refine ⟨9780763075460904901866677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6520508716973936601244451 9780763075460904901866677)
                  ·
                    refine ⟨916946538324459834550001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9780763075460904901866677 916946538324459834550001)
                    ·
                      rfl

theorem cell23_5357241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 5].length) (baseStart_5357241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357241 prefixEnd_5357241 := by exact prefixLift 5357241
  have htrace : WordTrace (prefixWord ++ tailWord_5357241) baseStart_5357241 baseEnd_5357241 := by
    simpa [prefixWord, tailWord_5357241, baseEnd_5357241] using wordTrace_append hprefix tailTrace_5357241
  have hstable : (prefixWord ++ tailWord_5357241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357241).length < 2 ^ (prefixWord ++ tailWord_5357241).sum := by decide
  have hdescent : baseEnd_5357241 < baseStart_5357241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357248 : List Nat := [2, 1, 1, 2, 4, 1, 3, 2, 2, 3, 2]
def baseStart_5357248 : Nat := 118140960795 + 5357248 * 2 ^ 59
def prefixEnd_5357248 : Nat := 4983230072969 + 3 ^ 40 * 5357248 * 2
def baseEnd_5357248 : Nat := 2750843209337960976262471

theorem tailTrace_5357248 : CollatzResearch.WordTrace tailWord_5357248 prefixEnd_5357248 2750843209337960976262471 := by
  unfold tailWord_5357248
  simp only [CollatzResearch.WordTrace]
  refine ⟨97697443447806457980504199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130263257930408610640672265 97697443447806457980504199)
  ·
    refine ⟨146546165171709686970756299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97697443447806457980504199 146546165171709686970756299)
    ·
      refine ⟨219819247757564530456134449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146546165171709686970756299 219819247757564530456134449)
      ·
        refine ⟨164864435818173397842100837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219819247757564530456134449 164864435818173397842100837)
        ·
          refine ⟨30912081715907512095393907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164864435818173397842100837 30912081715907512095393907)
          ·
            refine ⟨46368122573861268143090861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30912081715907512095393907 46368122573861268143090861)
            ·
              refine ⟨17388045965197975553659073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46368122573861268143090861 17388045965197975553659073)
              ·
                refine ⟨13041034473898481665244305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17388045965197975553659073 13041034473898481665244305)
                ·
                  refine ⟨9780775855423861248933229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13041034473898481665244305 9780775855423861248933229)
                  ·
                    refine ⟨3667790945783947968349961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9780775855423861248933229 3667790945783947968349961)
                    ·
                      refine ⟨2750843209337960976262471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3667790945783947968349961 2750843209337960976262471)
                      ·
                        rfl

theorem cell23_5357248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 2, 3, 2].length) (baseStart_5357248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357248 prefixEnd_5357248 := by exact prefixLift 5357248
  have htrace : WordTrace (prefixWord ++ tailWord_5357248) baseStart_5357248 baseEnd_5357248 := by
    simpa [prefixWord, tailWord_5357248, baseEnd_5357248] using wordTrace_append hprefix tailTrace_5357248
  have hstable : (prefixWord ++ tailWord_5357248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357248).length < 2 ^ (prefixWord ++ tailWord_5357248).sum := by decide
  have hdescent : baseEnd_5357248 < baseStart_5357248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357264 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 5]
def baseStart_5357264 : Nat := 118140960795 + 5357264 * 2 ^ 59
def prefixEnd_5357264 : Nat := 4983230072969 + 3 ^ 40 * 5357264 * 2
def baseEnd_5357264 : Nat := 2750851425028432913662397

theorem tailTrace_5357264 : CollatzResearch.WordTrace tailWord_5357264 prefixEnd_5357264 2750851425028432913662397 := by
  unfold tailWord_5357264
  simp only [CollatzResearch.WordTrace]
  refine ⟨97697735231777475346795423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130263646975703300462393897 97697735231777475346795423)
  ·
    refine ⟨146546602847666213020193135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97697735231777475346795423 146546602847666213020193135)
    ·
      refine ⟨219819904271499319530289703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146546602847666213020193135 219819904271499319530289703)
      ·
        refine ⟨329729856407248979295434555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219819904271499319530289703 329729856407248979295434555)
        ·
          refine ⟨494594784610873468943151833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329729856407248979295434555 494594784610873468943151833)
          ·
            refine ⟨370946088458155101707363875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 494594784610873468943151833 370946088458155101707363875)
            ·
              refine ⟨556419132687232652561045813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370946088458155101707363875 556419132687232652561045813)
              ·
                refine ⟨52164293689428061177598045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 556419132687232652561045813 52164293689428061177598045)
                ·
                  refine ⟨19561610133535522941599267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52164293689428061177598045 19561610133535522941599267)
                  ·
                    refine ⟨29342415200303284412398901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19561610133535522941599267 29342415200303284412398901)
                    ·
                      refine ⟨2750851425028432913662397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29342415200303284412398901 2750851425028432913662397)
                      ·
                        rfl

theorem cell23_5357264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 5].length) (baseStart_5357264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357264 prefixEnd_5357264 := by exact prefixLift 5357264
  have htrace : WordTrace (prefixWord ++ tailWord_5357264) baseStart_5357264 baseEnd_5357264 := by
    simpa [prefixWord, tailWord_5357264, baseEnd_5357264] using wordTrace_append hprefix tailTrace_5357264
  have hstable : (prefixWord ++ tailWord_5357264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357264).length < 2 ^ (prefixWord ++ tailWord_5357264).sum := by decide
  have hdescent : baseEnd_5357264 < baseStart_5357264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357284 : List Nat := [2, 3, 1, 1, 1, 3, 1, 11]
def baseStart_5357284 : Nat := 118140960795 + 5357284 * 2 ^ 59
def prefixEnd_5357284 : Nat := 4983230072969 + 3 ^ 40 * 5357284 * 2
def baseEnd_5357284 : Nat := 101883766468204549459715

theorem tailTrace_5357284 : CollatzResearch.WordTrace tailWord_5357284 prefixEnd_5357284 101883766468204549459715 := by
  unfold tailWord_5357284
  simp only [CollatzResearch.WordTrace]
  refine ⟨97698099961741247054659453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130264133282321662739545937 97698099961741247054659453)
  ·
    refine ⟨36636787485652967645497295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97698099961741247054659453 36636787485652967645497295)
    ·
      refine ⟨54955181228479451468245943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36636787485652967645497295 54955181228479451468245943)
      ·
        refine ⟨82432771842719177202368915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54955181228479451468245943 82432771842719177202368915)
        ·
          refine ⟨123649157764078765803553373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82432771842719177202368915 123649157764078765803553373)
          ·
            refine ⟨46368434161529537176332515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123649157764078765803553373 46368434161529537176332515)
            ·
              refine ⟨69552651242294305764498773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46368434161529537176332515 69552651242294305764498773)
              ·
                refine ⟨101883766468204549459715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 69552651242294305764498773 101883766468204549459715)
                ·
                  rfl

theorem cell23_5357284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 11].length) (baseStart_5357284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357284 prefixEnd_5357284 := by exact prefixLift 5357284
  have htrace : WordTrace (prefixWord ++ tailWord_5357284) baseStart_5357284 baseEnd_5357284 := by
    simpa [prefixWord, tailWord_5357284, baseEnd_5357284] using wordTrace_append hprefix tailTrace_5357284
  have hstable : (prefixWord ++ tailWord_5357284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357284).length < 2 ^ (prefixWord ++ tailWord_5357284).sum := by decide
  have hdescent : baseEnd_5357284 < baseStart_5357284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357301 : List Nat := [1, 3, 6, 13]
def baseStart_5357301 : Nat := 118140960795 + 5357301 * 2 ^ 59
def prefixEnd_5357301 : Nat := 4983230072969 + 3 ^ 40 * 5357301 * 2
def baseEnd_5357301 : Nat := 1257828268775788417421

theorem tailTrace_5357301 : CollatzResearch.WordTrace tailWord_5357301 prefixEnd_5357301 1257828268775788417421 := by
  unfold tailWord_5357301
  simp only [CollatzResearch.WordTrace]
  refine ⟨195396819964420906012687757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130264546642947270675125171 195396819964420906012687757)
  ·
    refine ⟨73273807486657839754757909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195396819964420906012687757 73273807486657839754757909)
    ·
      refine ⟨3434709725937086238504277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 73273807486657839754757909 3434709725937086238504277)
      ·
        refine ⟨1257828268775788417421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 3434709725937086238504277 1257828268775788417421)
        ·
          rfl

theorem cell23_5357301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 13].length) (baseStart_5357301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357301 prefixEnd_5357301 := by exact prefixLift 5357301
  have htrace : WordTrace (prefixWord ++ tailWord_5357301) baseStart_5357301 baseEnd_5357301 := by
    simpa [prefixWord, tailWord_5357301, baseEnd_5357301] using wordTrace_append hprefix tailTrace_5357301
  have hstable : (prefixWord ++ tailWord_5357301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357301).length < 2 ^ (prefixWord ++ tailWord_5357301).sum := by decide
  have hdescent : baseEnd_5357301 < baseStart_5357301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357304 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 2, 2, 6]
def baseStart_5357304 : Nat := 118140960795 + 5357304 * 2 ^ 59
def prefixEnd_5357304 : Nat := 4983230072969 + 3 ^ 40 * 5357304 * 2
def baseEnd_5357304 : Nat := 2750871964254612757162213

theorem tailTrace_5357304 : CollatzResearch.WordTrace tailWord_5357304 prefixEnd_5357304 2750871964254612757162213 := by
  unfold tailWord_5357304
  simp only [CollatzResearch.WordTrace]
  refine ⟨97698464691705018762523483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130264619588940025016697977 97698464691705018762523483)
  ·
    refine ⟨146547697037557528143785225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97698464691705018762523483 146547697037557528143785225)
    ·
      refine ⟨109910772778168146107838919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146547697037557528143785225 109910772778168146107838919)
      ·
        refine ⟨164866159167252219161758379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109910772778168146107838919 164866159167252219161758379)
        ·
          refine ⟨247299238750878328742637569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164866159167252219161758379 247299238750878328742637569)
          ·
            refine ⟨185474429063158746556978177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247299238750878328742637569 185474429063158746556978177)
            ·
              refine ⟨139105821797369059917733633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185474429063158746556978177 139105821797369059917733633)
              ·
                refine ⟨104329366348026794938300225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139105821797369059917733633 104329366348026794938300225)
                ·
                  refine ⟨78247024761020096203725169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104329366348026794938300225 78247024761020096203725169)
                  ·
                    refine ⟨58685268570765072152793877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78247024761020096203725169 58685268570765072152793877)
                    ·
                      refine ⟨2750871964254612757162213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58685268570765072152793877 2750871964254612757162213)
                      ·
                        rfl

theorem cell23_5357304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_5357304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357304 prefixEnd_5357304 := by exact prefixLift 5357304
  have htrace : WordTrace (prefixWord ++ tailWord_5357304) baseStart_5357304 baseEnd_5357304 := by
    simpa [prefixWord, tailWord_5357304, baseEnd_5357304] using wordTrace_append hprefix tailTrace_5357304
  have hstable : (prefixWord ++ tailWord_5357304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357304).length < 2 ^ (prefixWord ++ tailWord_5357304).sum := by decide
  have hdescent : baseEnd_5357304 < baseStart_5357304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357361 : List Nat := [1, 2, 2, 3, 2, 2, 1, 2, 2, 6]
def baseStart_5357361 : Nat := 118140960795 + 5357361 * 2 ^ 59
def prefixEnd_5357361 : Nat := 4983230072969 + 3 ^ 40 * 5357361 * 2
def baseEnd_5357361 : Nat := 916967077550639678049817

theorem tailTrace_5357361 : CollatzResearch.WordTrace tailWord_5357361 prefixEnd_5357361 916967077550639678049817 := by
  unfold tailWord_5357361
  simp only [CollatzResearch.WordTrace]
  refine ⟨195399008344203536259871937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130266005562802357506581291 195399008344203536259871937)
  ·
    refine ⟨146549256258152652194903953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195399008344203536259871937 146549256258152652194903953)
    ·
      refine ⟨109911942193614489146177965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146549256258152652194903953 109911942193614489146177965)
      ·
        refine ⟨41216978322605433429816737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109911942193614489146177965 41216978322605433429816737)
        ·
          refine ⟨30912733741954075072362553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41216978322605433429816737 30912733741954075072362553)
          ·
            refine ⟨23184550306465556304271915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30912733741954075072362553 23184550306465556304271915)
            ·
              refine ⟨34776825459698334456407873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23184550306465556304271915 34776825459698334456407873)
              ·
                refine ⟨26082619094773750842305905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34776825459698334456407873 26082619094773750842305905)
                ·
                  refine ⟨19561964321080313131729429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26082619094773750842305905 19561964321080313131729429)
                  ·
                    refine ⟨916967077550639678049817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19561964321080313131729429 916967077550639678049817)
                    ·
                      rfl

theorem cell23_5357361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 6].length) (baseStart_5357361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357361 prefixEnd_5357361 := by exact prefixLift 5357361
  have htrace : WordTrace (prefixWord ++ tailWord_5357361) baseStart_5357361 baseEnd_5357361 := by
    simpa [prefixWord, tailWord_5357361, baseEnd_5357361] using wordTrace_append hprefix tailTrace_5357361
  have hstable : (prefixWord ++ tailWord_5357361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357361).length < 2 ^ (prefixWord ++ tailWord_5357361).sum := by decide
  have hdescent : baseEnd_5357361 < baseStart_5357361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357362 : List Nat := [3, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3]
def baseStart_5357362 : Nat := 118140960795 + 5357362 * 2 ^ 59
def prefixEnd_5357362 : Nat := 4983230072969 + 3 ^ 40 * 5357362 * 2
def baseEnd_5357362 : Nat := 2750901746132573530236947

theorem tailTrace_5357362 : CollatzResearch.WordTrace tailWord_5357362 prefixEnd_5357362 2750901746132573530236947 := by
  unfold tailWord_5357362
  simp only [CollatzResearch.WordTrace]
  refine ⟨48849761204299978357664585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130266029878133275620438893 48849761204299978357664585)
  ·
    refine ⟨36637320903224983768248439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48849761204299978357664585 36637320903224983768248439)
    ·
      refine ⟨54955981354837475652372659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36637320903224983768248439 54955981354837475652372659)
      ·
        refine ⟨82433972032256213478558989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54955981354837475652372659 82433972032256213478558989)
        ·
          refine ⟨30912739512096080054459621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82433972032256213478558989 30912739512096080054459621)
          ·
            refine ⟨5796138658518015010211179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30912739512096080054459621 5796138658518015010211179)
            ·
              refine ⟨8694207987777022515316769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5796138658518015010211179 8694207987777022515316769)
              ·
                refine ⟨6520655990832766886487577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8694207987777022515316769 6520655990832766886487577)
                ·
                  refine ⟨4890491993124575164865683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6520655990832766886487577 4890491993124575164865683)
                  ·
                    refine ⟨7335737989686862747298525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4890491993124575164865683 7335737989686862747298525)
                    ·
                      refine ⟨2750901746132573530236947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7335737989686862747298525 2750901746132573530236947)
                      ·
                        rfl

theorem cell23_5357362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_5357362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357362 prefixEnd_5357362 := by exact prefixLift 5357362
  have htrace : WordTrace (prefixWord ++ tailWord_5357362) baseStart_5357362 baseEnd_5357362 := by
    simpa [prefixWord, tailWord_5357362, baseEnd_5357362] using wordTrace_append hprefix tailTrace_5357362
  have hstable : (prefixWord ++ tailWord_5357362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357362).length < 2 ^ (prefixWord ++ tailWord_5357362).sum := by decide
  have hdescent : baseEnd_5357362 < baseStart_5357362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357381 : List Nat := [1, 3, 1, 1, 1, 2, 3, 3, 2, 2, 4]
def baseStart_5357381 : Nat := 118140960795 + 5357381 * 2 ^ 59
def prefixEnd_5357381 : Nat := 4983230072969 + 3 ^ 40 * 5357381 * 2
def baseEnd_5357381 : Nat := 2750911502265008955899359

theorem tailTrace_5357381 : CollatzResearch.WordTrace tailWord_5357381 prefixEnd_5357381 2750911502265008955899359 := by
  unfold tailWord_5357381
  simp only [CollatzResearch.WordTrace]
  refine ⟨195399737804131079675599997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130266491869420719783733331 195399737804131079675599997)
  ·
    refine ⟨73274901676549154878349999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195399737804131079675599997 73274901676549154878349999)
    ·
      refine ⟨109912352514823732317524999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73274901676549154878349999 109912352514823732317524999)
      ·
        refine ⟨164868528772235598476287499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109912352514823732317524999 164868528772235598476287499)
        ·
          refine ⟨247302793158353397714431249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164868528772235598476287499 247302793158353397714431249)
          ·
            refine ⟨185477094868765048285823437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247302793158353397714431249 185477094868765048285823437)
            ·
              refine ⟨69553910575786893107183789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185477094868765048285823437 69553910575786893107183789)
              ·
                refine ⟨26082716465920084915193921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69553910575786893107183789 26082716465920084915193921)
                ·
                  refine ⟨19562037349440063686395441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26082716465920084915193921 19562037349440063686395441)
                  ·
                    refine ⟨14671528012080047764796581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19562037349440063686395441 14671528012080047764796581)
                    ·
                      refine ⟨2750911502265008955899359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14671528012080047764796581 2750911502265008955899359)
                      ·
                        rfl

theorem cell23_5357381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_5357381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357381 prefixEnd_5357381 := by exact prefixLift 5357381
  have htrace : WordTrace (prefixWord ++ tailWord_5357381) baseStart_5357381 baseEnd_5357381 := by
    simpa [prefixWord, tailWord_5357381, baseEnd_5357381] using wordTrace_append hprefix tailTrace_5357381
  have hstable : (prefixWord ++ tailWord_5357381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357381).length < 2 ^ (prefixWord ++ tailWord_5357381).sum := by decide
  have hdescent : baseEnd_5357381 < baseStart_5357381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357389 : List Nat := [1, 6, 1, 2, 1, 2, 2, 2, 1, 3, 2]
def baseStart_5357389 : Nat := 118140960795 + 5357389 * 2 ^ 59
def prefixEnd_5357389 : Nat := 4983230072969 + 3 ^ 40 * 5357389 * 2
def baseEnd_5357389 : Nat := 2750915610110244924599323

theorem tailTrace_5357389 : CollatzResearch.WordTrace tailWord_5357389 prefixEnd_5357389 2750915610110244924599323 := by
  unfold tailWord_5357389
  simp only [CollatzResearch.WordTrace]
  refine ⟨195400029588102097041891221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130266686392068064694594147 195400029588102097041891221)
  ·
    refine ⟨9159376386942285798838651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 195400029588102097041891221 9159376386942285798838651)
    ·
      refine ⟨13739064580413428698257977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9159376386942285798838651 13739064580413428698257977)
      ·
        refine ⟨10304298435310071523693483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13739064580413428698257977 10304298435310071523693483)
        ·
          refine ⟨15456447652965107285540225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10304298435310071523693483 15456447652965107285540225)
          ·
            refine ⟨11592335739723830464155169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15456447652965107285540225 11592335739723830464155169)
            ·
              refine ⟨8694251804792872848116377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11592335739723830464155169 8694251804792872848116377)
              ·
                refine ⟨6520688853594654636087283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8694251804792872848116377 6520688853594654636087283)
                ·
                  refine ⟨9781033280391981954130925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6520688853594654636087283 9781033280391981954130925)
                  ·
                    refine ⟨3667887480146993232799097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9781033280391981954130925 3667887480146993232799097)
                    ·
                      refine ⟨2750915610110244924599323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3667887480146993232799097 2750915610110244924599323)
                      ·
                        rfl

theorem cell23_5357389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_5357389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357389 prefixEnd_5357389 := by exact prefixLift 5357389
  have htrace : WordTrace (prefixWord ++ tailWord_5357389) baseStart_5357389 baseEnd_5357389 := by
    simpa [prefixWord, tailWord_5357389, baseEnd_5357389] using wordTrace_append hprefix tailTrace_5357389
  have hstable : (prefixWord ++ tailWord_5357389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357389).length < 2 ^ (prefixWord ++ tailWord_5357389).sum := by decide
  have hdescent : baseEnd_5357389 < baseStart_5357389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357425 : List Nat := [1, 2, 2, 2, 1, 3, 5, 2, 5]
def baseStart_5357425 : Nat := 118140960795 + 5357425 * 2 ^ 59
def prefixEnd_5357425 : Nat := 4983230072969 + 3 ^ 40 * 5357425 * 2
def baseEnd_5357425 : Nat := 305659343934867420416573

theorem tailTrace_5357425 : CollatzResearch.WordTrace tailWord_5357425 prefixEnd_5357425 305659343934867420416573 := by
  unfold tailWord_5357425
  simp only [CollatzResearch.WordTrace]
  refine ⟨195401342615971675190201729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130267561743981116793467819 195401342615971675190201729)
  ·
    refine ⟨146551006961978756392651297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195401342615971675190201729 146551006961978756392651297)
    ·
      refine ⟨109913255221484067294488473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146551006961978756392651297 109913255221484067294488473)
      ·
        refine ⟨82434941416113050470866355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109913255221484067294488473 82434941416113050470866355)
        ·
          refine ⟨123652412124169575706299533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82434941416113050470866355 123652412124169575706299533)
          ·
            refine ⟨46369654546563590889862325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123652412124169575706299533 46369654546563590889862325)
            ·
              refine ⟨4347155113740336645924593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46369654546563590889862325 4347155113740336645924593)
              ·
                refine ⟨3260366335305252484443445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4347155113740336645924593 3260366335305252484443445)
                ·
                  refine ⟨305659343934867420416573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3260366335305252484443445 305659343934867420416573)
                  ·
                    rfl

theorem cell23_5357425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2, 5].length) (baseStart_5357425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357425 prefixEnd_5357425 := by exact prefixLift 5357425
  have htrace : WordTrace (prefixWord ++ tailWord_5357425) baseStart_5357425 baseEnd_5357425 := by
    simpa [prefixWord, tailWord_5357425, baseEnd_5357425] using wordTrace_append hprefix tailTrace_5357425
  have hstable : (prefixWord ++ tailWord_5357425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357425).length < 2 ^ (prefixWord ++ tailWord_5357425).sum := by decide
  have hdescent : baseEnd_5357425 < baseStart_5357425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357512 : List Nat := [2, 1, 3, 1, 4, 3, 1, 1, 2, 2, 3]
def baseStart_5357512 : Nat := 118140960795 + 5357512 * 2 ^ 59
def prefixEnd_5357512 : Nat := 4983230072969 + 3 ^ 40 * 5357512 * 2
def baseEnd_5357512 : Nat := 2750978768230747943361257

theorem tailTrace_5357512 : CollatzResearch.WordTrace tailWord_5357512 prefixEnd_5357512 2750978768230747943361257 := by
  unfold tailWord_5357512
  simp only [CollatzResearch.WordTrace]
  refine ⟨97702257883328244524309395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130269677177770992699079193 97702257883328244524309395)
  ·
    refine ⟨146553386824992366786464093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97702257883328244524309395 146553386824992366786464093)
    ·
      refine ⟨54957520059372137544924035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146553386824992366786464093 54957520059372137544924035)
      ·
        refine ⟨82436280089058206317386053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54957520059372137544924035 82436280089058206317386053)
        ·
          refine ⟨15456802516698413684509885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82436280089058206317386053 15456802516698413684509885)
          ·
            refine ⟨5796300943761905131691207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15456802516698413684509885 5796300943761905131691207)
            ·
              refine ⟨8694451415642857697536811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5796300943761905131691207 8694451415642857697536811)
              ·
                refine ⟨13041677123464286546305217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8694451415642857697536811 13041677123464286546305217)
                ·
                  refine ⟨9781257842598214909728913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13041677123464286546305217 9781257842598214909728913)
                  ·
                    refine ⟨7335943381948661182296685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9781257842598214909728913 7335943381948661182296685)
                    ·
                      refine ⟨2750978768230747943361257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7335943381948661182296685 2750978768230747943361257)
                      ·
                        rfl

theorem cell23_5357512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_5357512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357512 prefixEnd_5357512 := by exact prefixLift 5357512
  have htrace : WordTrace (prefixWord ++ tailWord_5357512) baseStart_5357512 baseEnd_5357512 := by
    simpa [prefixWord, tailWord_5357512, baseEnd_5357512] using wordTrace_append hprefix tailTrace_5357512
  have hstable : (prefixWord ++ tailWord_5357512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357512).length < 2 ^ (prefixWord ++ tailWord_5357512).sum := by decide
  have hdescent : baseEnd_5357512 < baseStart_5357512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357548 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 4]
def baseStart_5357548 : Nat := 118140960795 + 5357548 * 2 ^ 59
def prefixEnd_5357548 : Nat := 4983230072969 + 3 ^ 40 * 5357548 * 2
def baseEnd_5357548 : Nat := 2750997253534309802511091

theorem tailTrace_5357548 : CollatzResearch.WordTrace tailWord_5357548 prefixEnd_5357548 2750997253534309802511091 := by
  unfold tailWord_5357548
  simp only [CollatzResearch.WordTrace]
  refine ⟨97702914397263033598464649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130270552529684044797952865 97702914397263033598464649)
  ·
    refine ⟨73277185797947275198848487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97702914397263033598464649 73277185797947275198848487)
    ·
      refine ⟨109915778696920912798272731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73277185797947275198848487 109915778696920912798272731)
      ·
        refine ⟨164873668045381369197409097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109915778696920912798272731 164873668045381369197409097)
        ·
          refine ⟨123655251034036026898056823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164873668045381369197409097 123655251034036026898056823)
          ·
            refine ⟨185482876551054040347085235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123655251034036026898056823 185482876551054040347085235)
            ·
              refine ⟨278224314826581060520627853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185482876551054040347085235 278224314826581060520627853)
              ·
                refine ⟨104334118059967897695235445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 278224314826581060520627853 104334118059967897695235445)
                ·
                  refine ⟨9781323568121990408928323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104334118059967897695235445 9781323568121990408928323)
                  ·
                    refine ⟨14671985352182985613392485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9781323568121990408928323 14671985352182985613392485)
                    ·
                      refine ⟨2750997253534309802511091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14671985352182985613392485 2750997253534309802511091)
                      ·
                        rfl

theorem cell23_5357548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_5357548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357548 prefixEnd_5357548 := by exact prefixLift 5357548
  have htrace : WordTrace (prefixWord ++ tailWord_5357548) baseStart_5357548 baseEnd_5357548 := by
    simpa [prefixWord, tailWord_5357548, baseEnd_5357548] using wordTrace_append hprefix tailTrace_5357548
  have hstable : (prefixWord ++ tailWord_5357548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357548).length < 2 ^ (prefixWord ++ tailWord_5357548).sum := by decide
  have hdescent : baseEnd_5357548 < baseStart_5357548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357549 : List Nat := [1, 5, 1, 4, 1, 1, 3, 1, 6]
def baseStart_5357549 : Nat := 118140960795 + 5357549 * 2 ^ 59
def prefixEnd_5357549 : Nat := 4983230072969 + 3 ^ 40 * 5357549 * 2
def baseEnd_5357549 : Nat := 305666418557218255399843

theorem tailTrace_5357549 : CollatzResearch.WordTrace tailWord_5357549 prefixEnd_5357549 305666418557218255399843 := by
  unfold tailWord_5357549
  simp only [CollatzResearch.WordTrace]
  refine ⟨195405865267522444367715701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130270576845014962911810467 195405865267522444367715701)
  ·
    refine ⟨18319299868830229159473347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 195405865267522444367715701 18319299868830229159473347)
    ·
      refine ⟨27478949803245343739210021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18319299868830229159473347 27478949803245343739210021)
      ·
        refine ⟨5152303088108501951101879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27478949803245343739210021 5152303088108501951101879)
        ·
          refine ⟨7728454632162752926652819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5152303088108501951101879 7728454632162752926652819)
          ·
            refine ⟨11592681948244129389979229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7728454632162752926652819 11592681948244129389979229)
            ·
              refine ⟨4347255730591548521242211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11592681948244129389979229 4347255730591548521242211)
              ·
                refine ⟨6520883595887322781863317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4347255730591548521242211 6520883595887322781863317)
                ·
                  refine ⟨305666418557218255399843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6520883595887322781863317 305666418557218255399843)
                  ·
                    rfl

theorem cell23_5357549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_5357549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357549 prefixEnd_5357549 := by exact prefixLift 5357549
  have htrace : WordTrace (prefixWord ++ tailWord_5357549) baseStart_5357549 baseEnd_5357549 := by
    simpa [prefixWord, tailWord_5357549, baseEnd_5357549] using wordTrace_append hprefix tailTrace_5357549
  have hstable : (prefixWord ++ tailWord_5357549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357549).length < 2 ^ (prefixWord ++ tailWord_5357549).sum := by decide
  have hdescent : baseEnd_5357549 < baseStart_5357549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357565 : List Nat := [1, 4, 1, 1, 1, 2, 3, 4, 1, 1, 4]
def baseStart_5357565 : Nat := 118140960795 + 5357565 * 2 ^ 59
def prefixEnd_5357565 : Nat := 4983230072969 + 3 ^ 40 * 5357565 * 2
def baseEnd_5357565 : Nat := 2751005982705436235998513

theorem tailTrace_5357565 : CollatzResearch.WordTrace tailWord_5357565 prefixEnd_5357565 2751005982705436235998513 := by
  unfold tailWord_5357565
  simp only [CollatzResearch.WordTrace]
  refine ⟨195406448835464479100298149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130270965890309652733532099 195406448835464479100298149)
  ·
    refine ⟨36638709156649589831305903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195406448835464479100298149 36638709156649589831305903)
    ·
      refine ⟨54958063734974384746958855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36638709156649589831305903 54958063734974384746958855)
      ·
        refine ⟨82437095602461577120438283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54958063734974384746958855 82437095602461577120438283)
        ·
          refine ⟨123655643403692365680657425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82437095602461577120438283 123655643403692365680657425)
          ·
            refine ⟨92741732552769274260493069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123655643403692365680657425 92741732552769274260493069)
            ·
              refine ⟨34778149707288477847684901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92741732552769274260493069 34778149707288477847684901)
              ·
                refine ⟨6520903070116589596440919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34778149707288477847684901 6520903070116589596440919)
                ·
                  refine ⟨9781354605174884394661379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6520903070116589596440919 9781354605174884394661379)
                  ·
                    refine ⟨14672031907762326591992069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9781354605174884394661379 14672031907762326591992069)
                    ·
                      refine ⟨2751005982705436235998513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14672031907762326591992069 2751005982705436235998513)
                      ·
                        rfl

theorem cell23_5357565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_5357565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357565 prefixEnd_5357565 := by exact prefixLift 5357565
  have htrace : WordTrace (prefixWord ++ tailWord_5357565) baseStart_5357565 baseEnd_5357565 := by
    simpa [prefixWord, tailWord_5357565, baseEnd_5357565] using wordTrace_append hprefix tailTrace_5357565
  have hstable : (prefixWord ++ tailWord_5357565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357565).length < 2 ^ (prefixWord ++ tailWord_5357565).sum := by decide
  have hdescent : baseEnd_5357565 < baseStart_5357565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357575 : List Nat := [1, 1, 4, 3, 1, 2, 1, 2, 4, 4]
def baseStart_5357575 : Nat := 118140960795 + 5357575 * 2 ^ 59
def prefixEnd_5357575 : Nat := 4983230072969 + 3 ^ 40 * 5357575 * 2
def baseEnd_5357575 : Nat := 917003705837327065624489

theorem tailTrace_5357575 : CollatzResearch.WordTrace tailWord_5357575 prefixEnd_5357575 917003705837327065624489 := by
  unfold tailWord_5357575
  simp only [CollatzResearch.WordTrace]
  refine ⟨195406813565428250808162179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130271209043618833872108119 195406813565428250808162179)
  ·
    refine ⟨293110220348142376212243269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195406813565428250808162179 293110220348142376212243269)
    ·
      refine ⟨54958166315276695539795613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 293110220348142376212243269 54958166315276695539795613)
      ·
        refine ⟨20609312368228760827423355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54958166315276695539795613 20609312368228760827423355)
        ·
          refine ⟨30913968552343141241135033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20609312368228760827423355 30913968552343141241135033)
          ·
            refine ⟨23185476414257355930851275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30913968552343141241135033 23185476414257355930851275)
            ·
              refine ⟨34778214621386033896276913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23185476414257355930851275 34778214621386033896276913)
              ·
                refine ⟨26083660966039525422207685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34778214621386033896276913 26083660966039525422207685)
                ·
                  refine ⟨4890686431132411016663941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26083660966039525422207685 4890686431132411016663941)
                  ·
                    refine ⟨917003705837327065624489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4890686431132411016663941 917003705837327065624489)
                    ·
                      rfl

theorem cell23_5357575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_5357575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357575 prefixEnd_5357575 := by exact prefixLift 5357575
  have htrace : WordTrace (prefixWord ++ tailWord_5357575) baseStart_5357575 baseEnd_5357575 := by
    simpa [prefixWord, tailWord_5357575, baseEnd_5357575] using wordTrace_append hprefix tailTrace_5357575
  have hstable : (prefixWord ++ tailWord_5357575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357575).length < 2 ^ (prefixWord ++ tailWord_5357575).sum := by decide
  have hdescent : baseEnd_5357575 < baseStart_5357575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357615 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 6, 1, 3]
def baseStart_5357615 : Nat := 118140960795 + 5357615 * 2 ^ 59
def prefixEnd_5357615 : Nat := 4983230072969 + 3 ^ 40 * 5357615 * 2
def baseEnd_5357615 : Nat := 2751031656738161040373283

theorem tailTrace_5357615 : CollatzResearch.WordTrace tailWord_5357615 prefixEnd_5357615 2751031656738161040373283 := by
  unfold tailWord_5357615
  simp only [CollatzResearch.WordTrace]
  refine ⟨195408272485283337639618299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130272181656855558426412199 195408272485283337639618299)
  ·
    refine ⟨293112408727925006459427449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195408272485283337639618299 293112408727925006459427449)
    ·
      refine ⟨219834306545943754844570587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293112408727925006459427449 219834306545943754844570587)
      ·
        refine ⟨329751459818915632266855881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219834306545943754844570587 329751459818915632266855881)
        ·
          refine ⟨247313594864186724200141911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329751459818915632266855881 247313594864186724200141911)
          ·
            refine ⟨370970392296280086300212867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247313594864186724200141911 370970392296280086300212867)
            ·
              refine ⟨556455588444420129450319301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370970392296280086300212867 556455588444420129450319301)
              ·
                refine ⟨104335422833328774271934869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 556455588444420129450319301 104335422833328774271934869)
                ·
                  refine ⟨4890722945312286293996947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 104335422833328774271934869 4890722945312286293996947)
                  ·
                    refine ⟨7336084417968429440995421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4890722945312286293996947 7336084417968429440995421)
                    ·
                      refine ⟨2751031656738161040373283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7336084417968429440995421 2751031656738161040373283)
                      ·
                        rfl

theorem cell23_5357615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6, 1, 3].length) (baseStart_5357615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357615 prefixEnd_5357615 := by exact prefixLift 5357615
  have htrace : WordTrace (prefixWord ++ tailWord_5357615) baseStart_5357615 baseEnd_5357615 := by
    simpa [prefixWord, tailWord_5357615, baseEnd_5357615] using wordTrace_append hprefix tailTrace_5357615
  have hstable : (prefixWord ++ tailWord_5357615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357615).length < 2 ^ (prefixWord ++ tailWord_5357615).sum := by decide
  have hdescent : baseEnd_5357615 < baseStart_5357615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357650 : List Nat := [3, 2, 2, 1, 4, 2, 2, 2, 1, 2, 2]
def baseStart_5357650 : Nat := 118140960795 + 5357650 * 2 ^ 59
def prefixEnd_5357650 : Nat := 4983230072969 + 3 ^ 40 * 5357650 * 2
def baseEnd_5357650 : Nat := 2751049628561068403435623

theorem tailTrace_5357650 : CollatzResearch.WordTrace tailWord_5357650 prefixEnd_5357650 2751049628561068403435623 := by
  unfold tailWord_5357650
  simp only [CollatzResearch.WordTrace]
  refine ⟨48852387260039134654285601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130273032693437692411428269 48852387260039134654285601)
  ·
    refine ⟨36639290445029350990714201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48852387260039134654285601 36639290445029350990714201)
    ·
      refine ⟨27479467833772013243035651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36639290445029350990714201 27479467833772013243035651)
      ·
        refine ⟨41219201750658019864553477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27479467833772013243035651 41219201750658019864553477)
        ·
          refine ⟨7728600328248378724603777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41219201750658019864553477 7728600328248378724603777)
          ·
            refine ⟨5796450246186284043452833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7728600328248378724603777 5796450246186284043452833)
            ·
              refine ⟨4347337684639713032589625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5796450246186284043452833 4347337684639713032589625)
              ·
                refine ⟨3260503263479784774442219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4347337684639713032589625 3260503263479784774442219)
                ·
                  refine ⟨4890754895219677161663329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3260503263479784774442219 4890754895219677161663329)
                  ·
                    refine ⟨3668066171414757871247497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4890754895219677161663329 3668066171414757871247497)
                    ·
                      refine ⟨2751049628561068403435623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3668066171414757871247497 2751049628561068403435623)
                      ·
                        rfl

theorem cell23_5357650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_5357650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357650 prefixEnd_5357650 := by exact prefixLift 5357650
  have htrace : WordTrace (prefixWord ++ tailWord_5357650) baseStart_5357650 baseEnd_5357650 := by
    simpa [prefixWord, tailWord_5357650, baseEnd_5357650] using wordTrace_append hprefix tailTrace_5357650
  have hstable : (prefixWord ++ tailWord_5357650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357650).length < 2 ^ (prefixWord ++ tailWord_5357650).sum := by decide
  have hdescent : baseEnd_5357650 < baseStart_5357650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357688 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 1, 2, 7]
def baseStart_5357688 : Nat := 118140960795 + 5357688 * 2 ^ 59
def prefixEnd_5357688 : Nat := 4983230072969 + 3 ^ 40 * 5357688 * 2
def baseEnd_5357688 : Nat := 2751069140825939254760447

theorem tailTrace_5357688 : CollatzResearch.WordTrace tailWord_5357688 prefixEnd_5357688 2751069140825939254760447 := by
  unfold tailWord_5357688
  simp only [CollatzResearch.WordTrace]
  refine ⟨97705467507009435553512859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130273956676012580738017145 97705467507009435553512859)
  ·
    refine ⟨146558201260514153330269289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97705467507009435553512859 146558201260514153330269289)
    ·
      refine ⟨109918650945385614997701967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146558201260514153330269289 109918650945385614997701967)
      ·
        refine ⟨164877976418078422496552951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109918650945385614997701967 164877976418078422496552951)
        ·
          refine ⟨247316964627117633744829427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164877976418078422496552951 247316964627117633744829427)
          ·
            refine ⟨370975446940676450617244141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247316964627117633744829427 370975446940676450617244141)
            ·
              refine ⟨139115792602753668981466553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 370975446940676450617244141 139115792602753668981466553)
              ·
                refine ⟨104336844452065251736099915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139115792602753668981466553 104336844452065251736099915)
                ·
                  refine ⟨156505266678097877604149873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104336844452065251736099915 156505266678097877604149873)
                  ·
                    refine ⟨117378950008573408203112405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 156505266678097877604149873 117378950008573408203112405)
                    ·
                      refine ⟨2751069140825939254760447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 117378950008573408203112405 2751069140825939254760447)
                      ·
                        rfl

theorem cell23_5357688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_5357688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357688 prefixEnd_5357688 := by exact prefixLift 5357688
  have htrace : WordTrace (prefixWord ++ tailWord_5357688) baseStart_5357688 baseEnd_5357688 := by
    simpa [prefixWord, tailWord_5357688, baseEnd_5357688] using wordTrace_append hprefix tailTrace_5357688
  have hstable : (prefixWord ++ tailWord_5357688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357688).length < 2 ^ (prefixWord ++ tailWord_5357688).sum := by decide
  have hdescent : baseEnd_5357688 < baseStart_5357688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357705 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 4, 3, 3]
def baseStart_5357705 : Nat := 118140960795 + 5357705 * 2 ^ 59
def prefixEnd_5357705 : Nat := 4983230072969 + 3 ^ 40 * 5357705 * 2
def baseEnd_5357705 : Nat := 2751077869997065688247869

theorem tailTrace_5357705 : CollatzResearch.WordTrace tailWord_5357705 prefixEnd_5357705 2751077869997065688247869 := by
  unfold tailWord_5357705
  simp only [CollatzResearch.WordTrace]
  refine ⟨195411555054957283010394569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130274370036638188673596379 195411555054957283010394569)
  ·
    refine ⟨146558666291217962257795927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195411555054957283010394569 146558666291217962257795927)
    ·
      refine ⟨219837999436826943386693891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146558666291217962257795927 219837999436826943386693891)
      ·
        refine ⟨329756999155240415080040837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219837999436826943386693891 329756999155240415080040837)
        ·
          refine ⟨61829437341607577827507657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 329756999155240415080040837 61829437341607577827507657)
          ·
            refine ⟨46372078006205683370630743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61829437341607577827507657 46372078006205683370630743)
            ·
              refine ⟨69558117009308525055946115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46372078006205683370630743 69558117009308525055946115)
              ·
                refine ⟨104337175513962787583919173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69558117009308525055946115 104337175513962787583919173)
                ·
                  refine ⟨19563220408868022671984845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104337175513962787583919173 19563220408868022671984845)
                  ·
                    refine ⟨7336207653325508501994317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19563220408868022671984845 7336207653325508501994317)
                    ·
                      refine ⟨2751077869997065688247869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7336207653325508501994317 2751077869997065688247869)
                      ·
                        rfl

theorem cell23_5357705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 3, 3].length) (baseStart_5357705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357705 prefixEnd_5357705 := by exact prefixLift 5357705
  have htrace : WordTrace (prefixWord ++ tailWord_5357705) baseStart_5357705 baseEnd_5357705 := by
    simpa [prefixWord, tailWord_5357705, baseEnd_5357705] using wordTrace_append hprefix tailTrace_5357705
  have hstable : (prefixWord ++ tailWord_5357705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357705).length < 2 ^ (prefixWord ++ tailWord_5357705).sum := by decide
  have hdescent : baseEnd_5357705 < baseStart_5357705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357706 : List Nat := [3, 1, 2, 3, 1, 2, 3, 2, 2, 2, 2]
def baseStart_5357706 : Nat := 118140960795 + 5357706 * 2 ^ 59
def prefixEnd_5357706 : Nat := 4983230072969 + 3 ^ 40 * 5357706 * 2
def baseEnd_5357706 : Nat := 2751078383477720184335365

theorem tailTrace_5357706 : CollatzResearch.WordTrace tailWord_5357706 prefixEnd_5357706 2751078383477720184335365 := by
  unfold tailWord_5357706
  simp only [CollatzResearch.WordTrace]
  refine ⟨48852897881988415045295243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130274394351969106787453981 48852897881988415045295243)
  ·
    refine ⟨73279346822982622567942865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48852897881988415045295243 73279346822982622567942865)
    ·
      refine ⟨54959510117236966925957149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73279346822982622567942865 54959510117236966925957149)
      ·
        refine ⟨20609816293963862597233931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54959510117236966925957149 20609816293963862597233931)
        ·
          refine ⟨30914724440945793895850897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20609816293963862597233931 30914724440945793895850897)
          ·
            refine ⟨23186043330709345421888173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30914724440945793895850897 23186043330709345421888173)
            ·
              refine ⟨8694766249016004533208065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23186043330709345421888173 8694766249016004533208065)
              ·
                refine ⟨6521074686762003399906049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8694766249016004533208065 6521074686762003399906049)
                ·
                  refine ⟨4890806015071502549929537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6521074686762003399906049 4890806015071502549929537)
                  ·
                    refine ⟨3668104511303626912447153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4890806015071502549929537 3668104511303626912447153)
                    ·
                      refine ⟨2751078383477720184335365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3668104511303626912447153 2751078383477720184335365)
                      ·
                        rfl

theorem cell23_5357706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_5357706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357706 prefixEnd_5357706 := by exact prefixLift 5357706
  have htrace : WordTrace (prefixWord ++ tailWord_5357706) baseStart_5357706 baseEnd_5357706 := by
    simpa [prefixWord, tailWord_5357706, baseEnd_5357706] using wordTrace_append hprefix tailTrace_5357706
  have hstable : (prefixWord ++ tailWord_5357706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357706).length < 2 ^ (prefixWord ++ tailWord_5357706).sum := by decide
  have hdescent : baseEnd_5357706 < baseStart_5357706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357725 : List Nat := [1, 4, 2, 1, 1, 3, 1, 2, 1, 7]
def baseStart_5357725 : Nat := 118140960795 + 5357725 * 2 ^ 59
def prefixEnd_5357725 : Nat := 4983230072969 + 3 ^ 40 * 5357725 * 2
def baseEnd_5357725 : Nat := 917029379870051869999259

theorem tailTrace_5357725 : CollatzResearch.WordTrace tailWord_5357725 prefixEnd_5357725 917029379870051869999259 := by
  unfold tailWord_5357725
  simp only [CollatzResearch.WordTrace]
  refine ⟨195412284514884826426122629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130274856343256550950748419 195412284514884826426122629)
  ·
    refine ⟨36639803346540904954897993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195412284514884826426122629 36639803346540904954897993)
    ·
      refine ⟨27479852509905678716173495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36639803346540904954897993 27479852509905678716173495)
      ·
        refine ⟨41219778764858518074260243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27479852509905678716173495 41219778764858518074260243)
        ·
          refine ⟨61829668147287777111390365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41219778764858518074260243 61829668147287777111390365)
          ·
            refine ⟨23186125555232916416771387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61829668147287777111390365 23186125555232916416771387)
            ·
              refine ⟨34779188332849374625157081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23186125555232916416771387 34779188332849374625157081)
              ·
                refine ⟨26084391249637030968867811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34779188332849374625157081 26084391249637030968867811)
                ·
                  refine ⟨39126586874455546453301717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26084391249637030968867811 39126586874455546453301717)
                  ·
                    refine ⟨917029379870051869999259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39126586874455546453301717 917029379870051869999259)
                    ·
                      rfl

theorem cell23_5357725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_5357725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357725 prefixEnd_5357725 := by exact prefixLift 5357725
  have htrace : WordTrace (prefixWord ++ tailWord_5357725) baseStart_5357725 baseEnd_5357725 := by
    simpa [prefixWord, tailWord_5357725, baseEnd_5357725] using wordTrace_append hprefix tailTrace_5357725
  have hstable : (prefixWord ++ tailWord_5357725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357725).length < 2 ^ (prefixWord ++ tailWord_5357725).sum := by decide
  have hdescent : baseEnd_5357725 < baseStart_5357725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357799 : List Nat := [1, 1, 5, 3, 1, 1, 1, 3, 2, 2, 3]
def baseStart_5357799 : Nat := 118140960795 + 5357799 * 2 ^ 59
def prefixEnd_5357799 : Nat := 4983230072969 + 3 ^ 40 * 5357799 * 2
def baseEnd_5357799 : Nat := 2751126137178588320472437

theorem tailTrace_5357799 : CollatzResearch.WordTrace tailWord_5357799 prefixEnd_5357799 2751126137178588320472437 := by
  unfold tailWord_5357799
  simp only [CollatzResearch.WordTrace]
  refine ⟨195414983516616737064316451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130276655677744491376210967 195414983516616737064316451)
  ·
    refine ⟨293122475274925105596474677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195414983516616737064316451 293122475274925105596474677)
    ·
      refine ⟨27480232057024228649669501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 293122475274925105596474677 27480232057024228649669501)
      ·
        refine ⟨10305087021384085743626063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27480232057024228649669501 10305087021384085743626063)
        ·
          refine ⟨15457630532076128615439095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10305087021384085743626063 15457630532076128615439095)
          ·
            refine ⟨23186445798114192923158643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15457630532076128615439095 23186445798114192923158643)
            ·
              refine ⟨34779668697171289384737965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23186445798114192923158643 34779668697171289384737965)
              ·
                refine ⟨13042375761439233519276737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34779668697171289384737965 13042375761439233519276737)
                ·
                  refine ⟨9781781821079425139457553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13042375761439233519276737 9781781821079425139457553)
                  ·
                    refine ⟨7336336365809568854593165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9781781821079425139457553 7336336365809568854593165)
                    ·
                      refine ⟨2751126137178588320472437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7336336365809568854593165 2751126137178588320472437)
                      ·
                        rfl

theorem cell23_5357799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_5357799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357799 prefixEnd_5357799 := by exact prefixLift 5357799
  have htrace : WordTrace (prefixWord ++ tailWord_5357799) baseStart_5357799 baseEnd_5357799 := by
    simpa [prefixWord, tailWord_5357799, baseEnd_5357799] using wordTrace_append hprefix tailTrace_5357799
  have hstable : (prefixWord ++ tailWord_5357799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357799).length < 2 ^ (prefixWord ++ tailWord_5357799).sum := by decide
  have hdescent : baseEnd_5357799 < baseStart_5357799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357815 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 7, 5]
def baseStart_5357815 : Nat := 118140960795 + 5357815 * 2 ^ 59
def prefixEnd_5357815 : Nat := 4983230072969 + 3 ^ 40 * 5357815 * 2
def baseEnd_5357815 : Nat := 917044784289686752624121

theorem tailTrace_5357815 : CollatzResearch.WordTrace tailWord_5357815 prefixEnd_5357815 917044784289686752624121 := by
  unfold tailWord_5357815
  simp only [CollatzResearch.WordTrace]
  refine ⟨195415567084558771796898899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130277044723039181197932599 195415567084558771796898899)
  ·
    refine ⟨293123350626838157695348349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195415567084558771796898899 293123350626838157695348349)
    ·
      refine ⟨109921256485064309135755631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293123350626838157695348349 109921256485064309135755631)
      ·
        refine ⟨164881884727596463703633447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109921256485064309135755631 164881884727596463703633447)
        ·
          refine ⟨247322827091394695555450171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164881884727596463703633447 247322827091394695555450171)
          ·
            refine ⟨370984240637092043333175257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247322827091394695555450171 370984240637092043333175257)
            ·
              refine ⟨278238180477819032499881443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 370984240637092043333175257 278238180477819032499881443)
              ·
                refine ⟨417357270716728548749822165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278238180477819032499881443 417357270716728548749822165)
                ·
                  refine ⟨9781811032423325361323957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 417357270716728548749822165 9781811032423325361323957)
                  ·
                    refine ⟨917044784289686752624121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9781811032423325361323957 917044784289686752624121)
                    ·
                      rfl

theorem cell23_5357815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 5].length) (baseStart_5357815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357815 prefixEnd_5357815 := by exact prefixLift 5357815
  have htrace : WordTrace (prefixWord ++ tailWord_5357815) baseStart_5357815 baseEnd_5357815 := by
    simpa [prefixWord, tailWord_5357815, baseEnd_5357815] using wordTrace_append hprefix tailTrace_5357815
  have hstable : (prefixWord ++ tailWord_5357815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357815).length < 2 ^ (prefixWord ++ tailWord_5357815).sum := by decide
  have hdescent : baseEnd_5357815 < baseStart_5357815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357822 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_5357822 : Nat := 118140960795 + 5357822 * 2 ^ 59
def prefixEnd_5357822 : Nat := 4983230072969 + 3 ^ 40 * 5357822 * 2
def baseEnd_5357822 : Nat := 2751137947233641730484831

theorem tailTrace_5357822 : CollatzResearch.WordTrace tailWord_5357822 prefixEnd_5357822 2751137947233641730484831 := by
  unfold tailWord_5357822
  simp only [CollatzResearch.WordTrace]
  refine ⟨24426977799441676499050465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130277214930355607994935813 24426977799441676499050465)
  ·
    refine ⟨18320233349581257374287849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24426977799441676499050465 18320233349581257374287849)
    ·
      refine ⟨13740175012185943030715887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18320233349581257374287849 13740175012185943030715887)
      ·
        refine ⟨20610262518278914546073831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13740175012185943030715887 20610262518278914546073831)
        ·
          refine ⟨30915393777418371819110747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20610262518278914546073831 30915393777418371819110747)
          ·
            refine ⟨46373090666127557728666121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30915393777418371819110747 46373090666127557728666121)
            ·
              refine ⟨34779817999595668296499591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46373090666127557728666121 34779817999595668296499591)
              ·
                refine ⟨52169726999393502444749387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34779817999595668296499591 52169726999393502444749387)
                ·
                  refine ⟨78254590499090253667124081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52169726999393502444749387 78254590499090253667124081)
                  ·
                    refine ⟨58690942874317690250343061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78254590499090253667124081 58690942874317690250343061)
                    ·
                      refine ⟨2751137947233641730484831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58690942874317690250343061 2751137947233641730484831)
                      ·
                        rfl

theorem cell23_5357822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_5357822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357822 prefixEnd_5357822 := by exact prefixLift 5357822
  have htrace : WordTrace (prefixWord ++ tailWord_5357822) baseStart_5357822 baseEnd_5357822 := by
    simpa [prefixWord, tailWord_5357822, baseEnd_5357822] using wordTrace_append hprefix tailTrace_5357822
  have hstable : (prefixWord ++ tailWord_5357822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357822).length < 2 ^ (prefixWord ++ tailWord_5357822).sum := by decide
  have hdescent : baseEnd_5357822 < baseStart_5357822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357832 : List Nat := [2, 1, 3, 2, 3, 1, 1, 2, 3, 5]
def baseStart_5357832 : Nat := 118140960795 + 5357832 * 2 ^ 59
def prefixEnd_5357832 : Nat := 4983230072969 + 3 ^ 40 * 5357832 * 2
def baseEnd_5357832 : Nat := 917047694013395563786595

theorem tailTrace_5357832 : CollatzResearch.WordTrace tailWord_5357832 prefixEnd_5357832 917047694013395563786595 := by
  unfold tailWord_5357832
  simp only [CollatzResearch.WordTrace]
  refine ⟨97708093562748591850133875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130277458083664789133511833 97708093562748591850133875)
  ·
    refine ⟨146562140344122887775200813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97708093562748591850133875 146562140344122887775200813)
    ·
      refine ⟨54960802629046082915700305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146562140344122887775200813 54960802629046082915700305)
      ·
        refine ⟨41220601971784562186775229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54960802629046082915700305 41220601971784562186775229)
        ·
          refine ⟨15457725739419210820040711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41220601971784562186775229 15457725739419210820040711)
          ·
            refine ⟨23186588609128816230061067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15457725739419210820040711 23186588609128816230061067)
            ·
              refine ⟨34779882913693224345091601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23186588609128816230061067 34779882913693224345091601)
              ·
                refine ⟨26084912185269918258818701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34779882913693224345091601 26084912185269918258818701)
                ·
                  refine ⟨9781842069476219347057013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26084912185269918258818701 9781842069476219347057013)
                  ·
                    refine ⟨917047694013395563786595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9781842069476219347057013 917047694013395563786595)
                    ·
                      rfl

theorem cell23_5357832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_5357832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357832 prefixEnd_5357832 := by exact prefixLift 5357832
  have htrace : WordTrace (prefixWord ++ tailWord_5357832) baseStart_5357832 baseEnd_5357832 := by
    simpa [prefixWord, tailWord_5357832, baseEnd_5357832] using wordTrace_append hprefix tailTrace_5357832
  have hstable : (prefixWord ++ tailWord_5357832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357832).length < 2 ^ (prefixWord ++ tailWord_5357832).sum := by decide
  have hdescent : baseEnd_5357832 < baseStart_5357832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357856 : List Nat := [2, 1, 1, 5, 2, 1, 3, 1, 2, 3, 2]
def baseStart_5357856 : Nat := 118140960795 + 5357856 * 2 ^ 59
def prefixEnd_5357856 : Nat := 4983230072969 + 3 ^ 40 * 5357856 * 2
def baseEnd_5357856 : Nat := 2751155405575894597459675

theorem tailTrace_5357856 : CollatzResearch.WordTrace tailWord_5357856 prefixEnd_5357856 2751155405575894597459675 := by
  unfold tailWord_5357856
  simp only [CollatzResearch.WordTrace]
  refine ⟨97708531238705117899570711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130278041651606823866094281 97708531238705117899570711)
  ·
    refine ⟨146562796858057676849356067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97708531238705117899570711 146562796858057676849356067)
    ·
      refine ⟨219844195287086515274034101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146562796858057676849356067 219844195287086515274034101)
      ·
        refine ⟨20610393308164360806940697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 219844195287086515274034101 20610393308164360806940697)
        ·
          refine ⟨15457794981123270605205523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20610393308164360806940697 15457794981123270605205523)
          ·
            refine ⟨23186692471684905907808285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15457794981123270605205523 23186692471684905907808285)
            ·
              refine ⟨8695009676881839715428107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23186692471684905907808285 8695009676881839715428107)
              ·
                refine ⟨13042514515322759573142161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8695009676881839715428107 13042514515322759573142161)
                ·
                  refine ⟨9781885886492069679856621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13042514515322759573142161 9781885886492069679856621)
                  ·
                    refine ⟨3668207207434526129946233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9781885886492069679856621 3668207207434526129946233)
                    ·
                      refine ⟨2751155405575894597459675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3668207207434526129946233 2751155405575894597459675)
                      ·
                        rfl

theorem cell23_5357856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_5357856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357856 prefixEnd_5357856 := by exact prefixLift 5357856
  have htrace : WordTrace (prefixWord ++ tailWord_5357856) baseStart_5357856 baseEnd_5357856 := by
    simpa [prefixWord, tailWord_5357856, baseEnd_5357856] using wordTrace_append hprefix tailTrace_5357856
  have hstable : (prefixWord ++ tailWord_5357856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357856).length < 2 ^ (prefixWord ++ tailWord_5357856).sum := by decide
  have hdescent : baseEnd_5357856 < baseStart_5357856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357866 : List Nat := [3, 1, 4, 2, 2, 1, 1, 3, 1, 5]
def baseStart_5357866 : Nat := 118140960795 + 5357866 * 2 ^ 59
def prefixEnd_5357866 : Nat := 4983230072969 + 3 ^ 40 * 5357866 * 2
def baseEnd_5357866 : Nat := 917053513460813186111543

theorem tailTrace_5357866 : CollatzResearch.WordTrace tailWord_5357866 prefixEnd_5357866 917053513460813186111543 := by
  unfold tailWord_5357866
  simp only [CollatzResearch.WordTrace]
  refine ⟨48854356801843501876751363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130278284804916005004670301 48854356801843501876751363)
  ·
    refine ⟨73281535202765252815127045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48854356801843501876751363 73281535202765252815127045)
    ·
      refine ⟨13740287850518484902836321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73281535202765252815127045 13740287850518484902836321)
      ·
        refine ⟨10305215887888863677127241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13740287850518484902836321 10305215887888863677127241)
        ·
          refine ⟨7728911915916647757845431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10305215887888863677127241 7728911915916647757845431)
          ·
            refine ⟨11593367873874971636768147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7728911915916647757845431 11593367873874971636768147)
            ·
              refine ⟨17390051810812457455152221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11593367873874971636768147 17390051810812457455152221)
              ·
                refine ⟨6521269429054671545682083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17390051810812457455152221 6521269429054671545682083)
                ·
                  refine ⟨9781904143582007318523125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6521269429054671545682083 9781904143582007318523125)
                  ·
                    refine ⟨917053513460813186111543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9781904143582007318523125 917053513460813186111543)
                    ·
                      rfl

theorem cell23_5357866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_5357866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357866 prefixEnd_5357866 := by exact prefixLift 5357866
  have htrace : WordTrace (prefixWord ++ tailWord_5357866) baseStart_5357866 baseEnd_5357866 := by
    simpa [prefixWord, tailWord_5357866, baseEnd_5357866] using wordTrace_append hprefix tailTrace_5357866
  have hstable : (prefixWord ++ tailWord_5357866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357866).length < 2 ^ (prefixWord ++ tailWord_5357866).sum := by decide
  have hdescent : baseEnd_5357866 < baseStart_5357866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357872 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 3]
def baseStart_5357872 : Nat := 118140960795 + 5357872 * 2 ^ 59
def prefixEnd_5357872 : Nat := 4983230072969 + 3 ^ 40 * 5357872 * 2
def baseEnd_5357872 : Nat := 2751163621266366534859601

theorem tailTrace_5357872 : CollatzResearch.WordTrace tailWord_5357872 prefixEnd_5357872 2751163621266366534859601 := by
  unfold tailWord_5357872
  simp only [CollatzResearch.WordTrace]
  refine ⟨97708823022676135265861935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130278430696901513687815913 97708823022676135265861935)
  ·
    refine ⟨146563234534014202898792903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97708823022676135265861935 146563234534014202898792903)
    ·
      refine ⟨219844851801021304348189355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146563234534014202898792903 219844851801021304348189355)
      ·
        refine ⟨329767277701531956522284033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219844851801021304348189355 329767277701531956522284033)
        ·
          refine ⟨247325458276148967391713025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329767277701531956522284033 247325458276148967391713025)
          ·
            refine ⟨185494093707111725543784769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247325458276148967391713025 185494093707111725543784769)
            ·
              refine ⟨139120570280333794157838577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185494093707111725543784769 139120570280333794157838577)
              ·
                refine ⟨104340427710250345618378933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139120570280333794157838577 104340427710250345618378933)
                ·
                  refine ⟨9781915097835969901723025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104340427710250345618378933 9781915097835969901723025)
                  ·
                    refine ⟨7336436323376977426292269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9781915097835969901723025 7336436323376977426292269)
                    ·
                      refine ⟨2751163621266366534859601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7336436323376977426292269 2751163621266366534859601)
                      ·
                        rfl

theorem cell23_5357872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 3].length) (baseStart_5357872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357872 prefixEnd_5357872 := by exact prefixLift 5357872
  have htrace : WordTrace (prefixWord ++ tailWord_5357872) baseStart_5357872 baseEnd_5357872 := by
    simpa [prefixWord, tailWord_5357872, baseEnd_5357872] using wordTrace_append hprefix tailTrace_5357872
  have hstable : (prefixWord ++ tailWord_5357872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357872).length < 2 ^ (prefixWord ++ tailWord_5357872).sum := by decide
  have hdescent : baseEnd_5357872 < baseStart_5357872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357875 : List Nat := [1, 1, 1, 2, 5, 1, 12]
def baseStart_5357875 : Nat := 118140960795 + 5357875 * 2 ^ 59
def prefixEnd_5357875 : Nat := 4983230072969 + 3 ^ 40 * 5357875 * 2
def baseEnd_5357875 : Nat := 33965001996399136087927

theorem tailTrace_5357875 : CollatzResearch.WordTrace tailWord_5357875 prefixEnd_5357875 33965001996399136087927 := by
  unfold tailWord_5357875
  simp only [CollatzResearch.WordTrace]
  refine ⟨195417755464341402044083079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130278503642894268029388719 195417755464341402044083079)
  ·
    refine ⟨293126633196512103066124619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195417755464341402044083079 293126633196512103066124619)
    ·
      refine ⟨439689949794768154599186929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293126633196512103066124619 439689949794768154599186929)
      ·
        refine ⟨329767462346076115949390197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 439689949794768154599186929 329767462346076115949390197)
        ·
          refine ⟨30915699594944635870255331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 329767462346076115949390197 30915699594944635870255331)
          ·
            refine ⟨46373549392416953805382997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30915699594944635870255331 46373549392416953805382997)
            ·
              refine ⟨33965001996399136087927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 46373549392416953805382997 33965001996399136087927)
              ·
                rfl

theorem cell23_5357875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 12].length) (baseStart_5357875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357875 prefixEnd_5357875 := by exact prefixLift 5357875
  have htrace : WordTrace (prefixWord ++ tailWord_5357875) baseStart_5357875 baseEnd_5357875 := by
    simpa [prefixWord, tailWord_5357875, baseEnd_5357875] using wordTrace_append hprefix tailTrace_5357875
  have hstable : (prefixWord ++ tailWord_5357875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357875).length < 2 ^ (prefixWord ++ tailWord_5357875).sum := by decide
  have hdescent : baseEnd_5357875 < baseStart_5357875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357919 : List Nat := [1, 1, 2, 3, 1, 2, 3, 2, 4, 1, 3]
def baseStart_5357919 : Nat := 118140960795 + 5357919 * 2 ^ 59
def prefixEnd_5357919 : Nat := 4983230072969 + 3 ^ 40 * 5357919 * 2
def baseEnd_5357919 : Nat := 2751187754857127850971885

theorem tailTrace_5357919 : CollatzResearch.WordTrace tailWord_5357919 prefixEnd_5357919 2751187754857127850971885 := by
  unfold tailWord_5357919
  simp only [CollatzResearch.WordTrace]
  refine ⟨195419360276181997558684811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130279573517454665039123207 195419360276181997558684811)
  ·
    refine ⟨293129040414272996338027217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195419360276181997558684811 293129040414272996338027217)
    ·
      refine ⟨219846780310704747253520413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293129040414272996338027217 219846780310704747253520413)
      ·
        refine ⟨82442542616514280220070155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219846780310704747253520413 82442542616514280220070155)
        ·
          refine ⟨123663813924771420330105233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82442542616514280220070155 123663813924771420330105233)
          ·
            refine ⟨92747860443578565247578925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123663813924771420330105233 92747860443578565247578925)
            ·
              refine ⟨34780447666341961967842097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92747860443578565247578925 34780447666341961967842097)
              ·
                refine ⟨26085335749756471475881573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34780447666341961967842097 26085335749756471475881573)
                ·
                  refine ⟨4891000453079338401727795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26085335749756471475881573 4891000453079338401727795)
                  ·
                    refine ⟨7336500679619007602591693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4891000453079338401727795 7336500679619007602591693)
                    ·
                      refine ⟨2751187754857127850971885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7336500679619007602591693 2751187754857127850971885)
                      ·
                        rfl

theorem cell23_5357919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_5357919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357919 prefixEnd_5357919 := by exact prefixLift 5357919
  have htrace : WordTrace (prefixWord ++ tailWord_5357919) baseStart_5357919 baseEnd_5357919 := by
    simpa [prefixWord, tailWord_5357919, baseEnd_5357919] using wordTrace_append hprefix tailTrace_5357919
  have hstable : (prefixWord ++ tailWord_5357919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357919).length < 2 ^ (prefixWord ++ tailWord_5357919).sum := by decide
  have hdescent : baseEnd_5357919 < baseStart_5357919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357953 : List Nat := [1, 2, 4, 3, 1, 2, 1, 3, 2, 1, 3]
def baseStart_5357953 : Nat := 118140960795 + 5357953 * 2 ^ 59
def prefixEnd_5357953 : Nat := 4983230072969 + 3 ^ 40 * 5357953 * 2
def baseEnd_5357953 : Nat := 2751205213199380717946729

theorem tailTrace_5357953 : CollatzResearch.WordTrace tailWord_5357953 prefixEnd_5357953 2751205213199380717946729 := by
  unfold tailWord_5357953
  simp only [CollatzResearch.WordTrace]
  refine ⟨195420600358058821365422513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130280400238705880910281675 195420600358058821365422513)
  ·
    refine ⟨146565450268544116024066885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195420600358058821365422513 146565450268544116024066885)
    ·
      refine ⟨27481021925352021754512541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146565450268544116024066885 27481021925352021754512541)
      ·
        refine ⟨10305383222007008157942203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27481021925352021754512541 10305383222007008157942203)
        ·
          refine ⟨15458074833010512236913305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10305383222007008157942203 15458074833010512236913305)
          ·
            refine ⟨11593556124757884177684979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15458074833010512236913305 11593556124757884177684979)
            ·
              refine ⟨17390334187136826266527469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11593556124757884177684979 17390334187136826266527469)
              ·
                refine ⟨6521375320176309849947801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17390334187136826266527469 6521375320176309849947801)
                ·
                  refine ⟨4891031490132232387460851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6521375320176309849947801 4891031490132232387460851)
                  ·
                    refine ⟨7336547235198348581191277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4891031490132232387460851 7336547235198348581191277)
                    ·
                      refine ⟨2751205213199380717946729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7336547235198348581191277 2751205213199380717946729)
                      ·
                        rfl

theorem cell23_5357953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_5357953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357953 prefixEnd_5357953 := by exact prefixLift 5357953
  have htrace : WordTrace (prefixWord ++ tailWord_5357953) baseStart_5357953 baseEnd_5357953 := by
    simpa [prefixWord, tailWord_5357953, baseEnd_5357953] using wordTrace_append hprefix tailTrace_5357953
  have hstable : (prefixWord ++ tailWord_5357953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357953).length < 2 ^ (prefixWord ++ tailWord_5357953).sum := by decide
  have hdescent : baseEnd_5357953 < baseStart_5357953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357963 : List Nat := [1, 1, 1, 1, 4, 6, 1, 2, 1, 3, 2]
def baseStart_5357963 : Nat := 118140960795 + 5357963 * 2 ^ 59
def prefixEnd_5357963 : Nat := 4983230072969 + 3 ^ 40 * 5357963 * 2
def baseEnd_5357963 : Nat := 2751210348005925678821683

theorem tailTrace_5357963 : CollatzResearch.WordTrace tailWord_5357963 prefixEnd_5357963 2751210348005925678821683 := by
  unfold tailWord_5357963
  simp only [CollatzResearch.WordTrace]
  refine ⟨195420965088022593073286543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130280643392015062048857695 195420965088022593073286543)
  ·
    refine ⟨293131447632033889609929815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195420965088022593073286543 293131447632033889609929815)
    ·
      refine ⟨439697171448050834414894723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293131447632033889609929815 439697171448050834414894723)
      ·
        refine ⟨659545757172076251622342085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439697171448050834414894723 659545757172076251622342085)
        ·
          refine ⟨123664829469764297179189141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 659545757172076251622342085 123664829469764297179189141)
          ·
            refine ⟨5796788881395201430274491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 123664829469764297179189141 5796788881395201430274491)
            ·
              refine ⟨8695183322092802145411737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5796788881395201430274491 8695183322092802145411737)
              ·
                refine ⟨6521387491569601609058803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8695183322092802145411737 6521387491569601609058803)
                ·
                  refine ⟨9782081237354402413588205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6521387491569601609058803 9782081237354402413588205)
                  ·
                    refine ⟨3668280464007900905095577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9782081237354402413588205 3668280464007900905095577)
                    ·
                      refine ⟨2751210348005925678821683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3668280464007900905095577 2751210348005925678821683)
                      ·
                        rfl

theorem cell23_5357963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 3, 2].length) (baseStart_5357963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357963 prefixEnd_5357963 := by exact prefixLift 5357963
  have htrace : WordTrace (prefixWord ++ tailWord_5357963) baseStart_5357963 baseEnd_5357963 := by
    simpa [prefixWord, tailWord_5357963, baseEnd_5357963] using wordTrace_append hprefix tailTrace_5357963
  have hstable : (prefixWord ++ tailWord_5357963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357963).length < 2 ^ (prefixWord ++ tailWord_5357963).sum := by decide
  have hdescent : baseEnd_5357963 < baseStart_5357963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357974 : List Nat := [5, 3, 1, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_5357974 : Nat := 118140960795 + 5357974 * 2 ^ 59
def prefixEnd_5357974 : Nat := 4983230072969 + 3 ^ 40 * 5357974 * 2
def baseEnd_5357974 : Nat := 2751215996293125135784133

theorem tailTrace_5357974 : CollatzResearch.WordTrace tailWord_5357974 prefixEnd_5357974 2751215996293125135784133 := by
  unfold tailWord_5357974
  simp only [CollatzResearch.WordTrace]
  refine ⟨12213835393186421371996061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130280910860655161301291317 12213835393186421371996061)
  ·
    refine ⟨4580188272444908014498523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12213835393186421371996061 4580188272444908014498523)
    ·
      refine ⟨6870282408667362021747785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4580188272444908014498523 6870282408667362021747785)
      ·
        refine ⟨5152711806500521516310839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6870282408667362021747785 5152711806500521516310839)
        ·
          refine ⟨7729067709750782274466259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5152711806500521516310839 7729067709750782274466259)
          ·
            refine ⟨11593601564626173411699389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7729067709750782274466259 11593601564626173411699389)
            ·
              refine ⟨4347600586734815029387271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11593601564626173411699389 4347600586734815029387271)
              ·
                refine ⟨6521400880102222544080907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4347600586734815029387271 6521400880102222544080907)
                ·
                  refine ⟨9782101320153333816121361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6521400880102222544080907 9782101320153333816121361)
                  ·
                    refine ⟨7336575990115000362091021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9782101320153333816121361 7336575990115000362091021)
                    ·
                      refine ⟨2751215996293125135784133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7336575990115000362091021 2751215996293125135784133)
                      ·
                        rfl

theorem cell23_5357974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_5357974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357974 prefixEnd_5357974 := by exact prefixLift 5357974
  have htrace : WordTrace (prefixWord ++ tailWord_5357974) baseStart_5357974 baseEnd_5357974 := by
    simpa [prefixWord, tailWord_5357974, baseEnd_5357974] using wordTrace_append hprefix tailTrace_5357974
  have hstable : (prefixWord ++ tailWord_5357974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357974).length < 2 ^ (prefixWord ++ tailWord_5357974).sum := by decide
  have hdescent : baseEnd_5357974 < baseStart_5357974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5357976 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 3, 4, 2]
def baseStart_5357976 : Nat := 118140960795 + 5357976 * 2 ^ 59
def prefixEnd_5357976 : Nat := 4983230072969 + 3 ^ 40 * 5357976 * 2
def baseEnd_5357976 : Nat := 2751217023254434127959123

theorem tailTrace_5357976 : CollatzResearch.WordTrace tailWord_5357976 prefixEnd_5357976 2751217023254434127959123 := by
  unfold tailWord_5357976
  simp only [CollatzResearch.WordTrace]
  refine ⟨97710719618487748146754891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130280959491316997529006521 97710719618487748146754891)
  ·
    refine ⟨146566079427731622220132337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97710719618487748146754891 146566079427731622220132337)
    ·
      refine ⟨109924559570798716665099253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146566079427731622220132337 109924559570798716665099253)
      ·
        refine ⟨10305427459762379687353055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109924559570798716665099253 10305427459762379687353055)
        ·
          refine ⟨15458141189643569531029583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10305427459762379687353055 15458141189643569531029583)
          ·
            refine ⟨23187211784465354296544375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15458141189643569531029583 23187211784465354296544375)
            ·
              refine ⟨34780817676698031444816563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23187211784465354296544375 34780817676698031444816563)
              ·
                refine ⟨52171226515047047167224845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34780817676698031444816563 52171226515047047167224845)
                ·
                  refine ⟨19564209943142642687709317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52171226515047047167224845 19564209943142642687709317)
                  ·
                    refine ⟨3668289364339245503945497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19564209943142642687709317 3668289364339245503945497)
                    ·
                      refine ⟨2751217023254434127959123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3668289364339245503945497 2751217023254434127959123)
                      ·
                        rfl

theorem cell23_5357976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_5357976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5357976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5357976 prefixEnd_5357976 := by exact prefixLift 5357976
  have htrace : WordTrace (prefixWord ++ tailWord_5357976) baseStart_5357976 baseEnd_5357976 := by
    simpa [prefixWord, tailWord_5357976, baseEnd_5357976] using wordTrace_append hprefix tailTrace_5357976
  have hstable : (prefixWord ++ tailWord_5357976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5357976).length < 2 ^ (prefixWord ++ tailWord_5357976).sum := by decide
  have hdescent : baseEnd_5357976 < baseStart_5357976 := by decide
  rcases family_descends (prefixWord ++ tailWord_5357976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358009 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 1, 5, 3]
def baseStart_5358009 : Nat := 118140960795 + 5358009 * 2 ^ 59
def prefixEnd_5358009 : Nat := 4983230072969 + 3 ^ 40 * 5358009 * 2
def baseEnd_5358009 : Nat := 2751233968116032498846471

theorem tailTrace_5358009 : CollatzResearch.WordTrace tailWord_5358009 prefixEnd_5358009 2751233968116032498846471 := by
  unfold tailWord_5358009
  simp only [CollatzResearch.WordTrace]
  refine ⟨195422642845855942929461081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130281761897237295286307387 195422642845855942929461081)
  ·
    refine ⟨146566982134391957197095811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195422642845855942929461081 146566982134391957197095811)
    ·
      refine ⟨219850473201587935795643717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146566982134391957197095811 219850473201587935795643717)
      ·
        refine ⟨41221963725297737961683197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219850473201587935795643717 41221963725297737961683197)
        ·
          refine ⟨15458236396986651735631199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41221963725297737961683197 15458236396986651735631199)
          ·
            refine ⟨23187354595479977603446799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15458236396986651735631199 23187354595479977603446799)
            ·
              refine ⟨34781031893219966405170199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23187354595479977603446799 34781031893219966405170199)
              ·
                refine ⟨52171547839829949607755299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34781031893219966405170199 52171547839829949607755299)
                ·
                  refine ⟨78257321759744924411632949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52171547839829949607755299 78257321759744924411632949)
                  ·
                    refine ⟨7336623914976086663590589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78257321759744924411632949 7336623914976086663590589)
                    ·
                      refine ⟨2751233968116032498846471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7336623914976086663590589 2751233968116032498846471)
                      ·
                        rfl

theorem cell23_5358009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_5358009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358009 prefixEnd_5358009 := by exact prefixLift 5358009
  have htrace : WordTrace (prefixWord ++ tailWord_5358009) baseStart_5358009 baseEnd_5358009 := by
    simpa [prefixWord, tailWord_5358009, baseEnd_5358009] using wordTrace_append hprefix tailTrace_5358009
  have hstable : (prefixWord ++ tailWord_5358009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358009).length < 2 ^ (prefixWord ++ tailWord_5358009).sum := by decide
  have hdescent : baseEnd_5358009 < baseStart_5358009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358019 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 4, 5, 2]
def baseStart_5358019 : Nat := 118140960795 + 5358019 * 2 ^ 59
def prefixEnd_5358019 : Nat := 4983230072969 + 3 ^ 40 * 5358019 * 2
def baseEnd_5358019 : Nat := 2751239102922577459721425

theorem tailTrace_5358019 : CollatzResearch.WordTrace tailWord_5358019 prefixEnd_5358019 2751239102922577459721425 := by
  unfold tailWord_5358019
  simp only [CollatzResearch.WordTrace]
  refine ⟨195423007575819714637325111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130282005050546476424883407 195423007575819714637325111)
  ·
    refine ⟨293134511363729571955987667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195423007575819714637325111 293134511363729571955987667)
    ·
      refine ⟨439701767045594357933981501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293134511363729571955987667 439701767045594357933981501)
      ·
        refine ⟨164888162642097884225243063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 439701767045594357933981501 164888162642097884225243063)
        ·
          refine ⟨247332243963146826337864595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164888162642097884225243063 247332243963146826337864595)
          ·
            refine ⟨370998365944720239506796893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247332243963146826337864595 370998365944720239506796893)
            ·
              refine ⟨139124387229270089815048835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 370998365944720239506796893 139124387229270089815048835)
              ·
                refine ⟨208686580843905134722573253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139124387229270089815048835 208686580843905134722573253)
                ·
                  refine ⟨39128733908232212760482485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 208686580843905134722573253 39128733908232212760482485)
                  ·
                    refine ⟨3668318803896769946295233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39128733908232212760482485 3668318803896769946295233)
                    ·
                      refine ⟨2751239102922577459721425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3668318803896769946295233 2751239102922577459721425)
                      ·
                        rfl

theorem cell23_5358019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 5, 2].length) (baseStart_5358019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358019 prefixEnd_5358019 := by exact prefixLift 5358019
  have htrace : WordTrace (prefixWord ++ tailWord_5358019) baseStart_5358019 baseEnd_5358019 := by
    simpa [prefixWord, tailWord_5358019, baseEnd_5358019] using wordTrace_append hprefix tailTrace_5358019
  have hstable : (prefixWord ++ tailWord_5358019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358019).length < 2 ^ (prefixWord ++ tailWord_5358019).sum := by decide
  have hdescent : baseEnd_5358019 < baseStart_5358019 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358049 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 4, 1, 4]
def baseStart_5358049 : Nat := 118140960795 + 5358049 * 2 ^ 59
def prefixEnd_5358049 : Nat := 4983230072969 + 3 ^ 40 * 5358049 * 2
def baseEnd_5358049 : Nat := 2751254507342212342346287

theorem tailTrace_5358049 : CollatzResearch.WordTrace tailWord_5358049 prefixEnd_5358049 2751254507342212342346287 := by
  unfold tailWord_5358049
  simp only [CollatzResearch.WordTrace]
  refine ⟨195424101765711029760917201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130282734510474019840611467 195424101765711029760917201)
  ·
    refine ⟨146568076324283272320687901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195424101765711029760917201 146568076324283272320687901)
    ·
      refine ⟨54963028621606227120257963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146568076324283272320687901 54963028621606227120257963)
      ·
        refine ⟨82444542932409340680386945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54963028621606227120257963 82444542932409340680386945)
        ·
          refine ⟨61833407199307005510290209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82444542932409340680386945 61833407199307005510290209)
          ·
            refine ⟨46375055399480254132717657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61833407199307005510290209 46375055399480254132717657)
            ·
              refine ⟨34781291549610190599538243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46375055399480254132717657 34781291549610190599538243)
              ·
                refine ⟨52171937324415285899307365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34781291549610190599538243 52171937324415285899307365)
                ·
                  refine ⟨9782238248327866106120131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52171937324415285899307365 9782238248327866106120131)
                  ·
                    refine ⟨14673357372491799159180197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9782238248327866106120131 14673357372491799159180197)
                    ·
                      refine ⟨2751254507342212342346287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14673357372491799159180197 2751254507342212342346287)
                      ·
                        rfl

theorem cell23_5358049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_5358049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358049 prefixEnd_5358049 := by exact prefixLift 5358049
  have htrace : WordTrace (prefixWord ++ tailWord_5358049) baseStart_5358049 baseEnd_5358049 := by
    simpa [prefixWord, tailWord_5358049, baseEnd_5358049] using wordTrace_append hprefix tailTrace_5358049
  have hstable : (prefixWord ++ tailWord_5358049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358049).length < 2 ^ (prefixWord ++ tailWord_5358049).sum := by decide
  have hdescent : baseEnd_5358049 < baseStart_5358049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358143 : List Nat := [1, 1, 2, 2, 3, 2, 4, 1, 2, 3, 2]
def baseStart_5358143 : Nat := 118140960795 + 5358143 * 2 ^ 59
def prefixEnd_5358143 : Nat := 4983230072969 + 3 ^ 40 * 5358143 * 2
def baseEnd_5358143 : Nat := 2751302774523734974570855

theorem tailTrace_5358143 : CollatzResearch.WordTrace tailWord_5358143 prefixEnd_5358143 2751302774523734974570855 := by
  unfold tailWord_5358143
  simp only [CollatzResearch.WordTrace]
  refine ⟨195427530227370483814839083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130285020151580322543226055 195427530227370483814839083)
  ·
    refine ⟨293141295341055725722258625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195427530227370483814839083 293141295341055725722258625)
    ·
      refine ⟨219855971505791794291693969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293141295341055725722258625 219855971505791794291693969)
      ·
        refine ⟨164891978629343845718770477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219855971505791794291693969 164891978629343845718770477)
        ·
          refine ⟨61834491986003942144538929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164891978629343845718770477 61834491986003942144538929)
          ·
            refine ⟨46375868989502956608404197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61834491986003942144538929 46375868989502956608404197)
            ·
              refine ⟨8695475435531804364075787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46375868989502956608404197 8695475435531804364075787)
              ·
                refine ⟨13043213153297706546113681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8695475435531804364075787 13043213153297706546113681)
                ·
                  refine ⟨9782409864973279909585261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13043213153297706546113681 9782409864973279909585261)
                  ·
                    refine ⟨3668403699364979966094473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9782409864973279909585261 3668403699364979966094473)
                    ·
                      refine ⟨2751302774523734974570855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3668403699364979966094473 2751302774523734974570855)
                      ·
                        rfl

theorem cell23_5358143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 3, 2].length) (baseStart_5358143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358143 prefixEnd_5358143 := by exact prefixLift 5358143
  have htrace : WordTrace (prefixWord ++ tailWord_5358143) baseStart_5358143 baseEnd_5358143 := by
    simpa [prefixWord, tailWord_5358143, baseEnd_5358143] using wordTrace_append hprefix tailTrace_5358143
  have hstable : (prefixWord ++ tailWord_5358143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358143).length < 2 ^ (prefixWord ++ tailWord_5358143).sum := by decide
  have hdescent : baseEnd_5358143 < baseStart_5358143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358149 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 3, 6]
def baseStart_5358149 : Nat := 118140960795 + 5358149 * 2 ^ 59
def prefixEnd_5358149 : Nat := 4983230072969 + 3 ^ 40 * 5358149 * 2
def baseEnd_5358149 : Nat := 917101951802553983698609

theorem tailTrace_5358149 : CollatzResearch.WordTrace tailWord_5358149 prefixEnd_5358149 917101951802553983698609 := by
  unfold tailWord_5358149
  simp only [CollatzResearch.WordTrace]
  refine ⟨195427749065348746839557501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130285166043565831226371667 195427749065348746839557501)
  ·
    refine ⟨73285405899505780064834063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195427749065348746839557501 73285405899505780064834063)
    ·
      refine ⟨109928108849258670097251095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73285405899505780064834063 109928108849258670097251095)
      ·
        refine ⟨164892163273888005145876643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109928108849258670097251095 164892163273888005145876643)
        ·
          refine ⟨247338244910832007718814965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164892163273888005145876643 247338244910832007718814965)
          ·
            refine ⟨23187960460390500723638903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 247338244910832007718814965 23187960460390500723638903)
            ·
              refine ⟨34781940690585751085458355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23187960460390500723638903 34781940690585751085458355)
              ·
                refine ⟨52172911035878626628187533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34781940690585751085458355 52172911035878626628187533)
                ·
                  refine ⟨19564841638454484985570325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52172911035878626628187533 19564841638454484985570325)
                  ·
                    refine ⟨917101951802553983698609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19564841638454484985570325 917101951802553983698609)
                    ·
                      rfl

theorem cell23_5358149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 6].length) (baseStart_5358149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358149 prefixEnd_5358149 := by exact prefixLift 5358149
  have htrace : WordTrace (prefixWord ++ tailWord_5358149) baseStart_5358149 baseEnd_5358149 := by
    simpa [prefixWord, tailWord_5358149, baseEnd_5358149] using wordTrace_append hprefix tailTrace_5358149
  have hstable : (prefixWord ++ tailWord_5358149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358149).length < 2 ^ (prefixWord ++ tailWord_5358149).sum := by decide
  have hdescent : baseEnd_5358149 < baseStart_5358149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358176 : List Nat := [2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 3]
def baseStart_5358176 : Nat := 118140960795 + 5358176 * 2 ^ 59
def prefixEnd_5358176 : Nat := 4983230072969 + 3 ^ 40 * 5358176 * 2
def baseEnd_5358176 : Nat := 2751319719385333345458203

theorem tailTrace_5358176 : CollatzResearch.WordTrace tailWord_5358176 prefixEnd_5358176 2751319719385333345458203 := by
  unfold tailWord_5358176
  simp only [CollatzResearch.WordTrace]
  refine ⟨97714366918125465225395191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130285822557500620300526921 97714366918125465225395191)
  ·
    refine ⟨146571550377188197838092787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97714366918125465225395191 146571550377188197838092787)
    ·
      refine ⟨219857325565782296757139181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146571550377188197838092787 219857325565782296757139181)
      ·
        refine ⟨82446497087168361283927193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219857325565782296757139181 82446497087168361283927193)
        ·
          refine ⟨61834872815376270962945395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82446497087168361283927193 61834872815376270962945395)
          ·
            refine ⟨92752309223064406444418093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61834872815376270962945395 92752309223064406444418093)
            ·
              refine ⟨34782115958649152416656785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92752309223064406444418093 34782115958649152416656785)
              ·
                refine ⟨26086586968986864312492589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34782115958649152416656785 26086586968986864312492589)
                ·
                  refine ⟨9782470113370074117184721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26086586968986864312492589 9782470113370074117184721)
                  ·
                    refine ⟨7336852585027555587888541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9782470113370074117184721 7336852585027555587888541)
                    ·
                      refine ⟨2751319719385333345458203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7336852585027555587888541 2751319719385333345458203)
                      ·
                        rfl

theorem cell23_5358176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_5358176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358176 prefixEnd_5358176 := by exact prefixLift 5358176
  have htrace : WordTrace (prefixWord ++ tailWord_5358176) baseStart_5358176 baseEnd_5358176 := by
    simpa [prefixWord, tailWord_5358176, baseEnd_5358176] using wordTrace_append hprefix tailTrace_5358176
  have hstable : (prefixWord ++ tailWord_5358176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358176).length < 2 ^ (prefixWord ++ tailWord_5358176).sum := by decide
  have hdescent : baseEnd_5358176 < baseStart_5358176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358190 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 5, 2, 2]
def baseStart_5358190 : Nat := 118140960795 + 5358190 * 2 ^ 59
def prefixEnd_5358190 : Nat := 4983230072969 + 3 ^ 40 * 5358190 * 2
def baseEnd_5358190 : Nat := 2751326908114496290683139

theorem tailTrace_5358190 : CollatzResearch.WordTrace tailWord_5358190 prefixEnd_5358190 2751326908114496290683139 := by
  unfold tailWord_5358190
  simp only [CollatzResearch.WordTrace]
  refine ⟨24428655557275026355225003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130286162972133473894533349 24428655557275026355225003)
  ·
    refine ⟨36642983335912539532837505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24428655557275026355225003 36642983335912539532837505)
    ·
      refine ⟨27482237501934404649628129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36642983335912539532837505 27482237501934404649628129)
      ·
        refine ⟨20611678126450803487221097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27482237501934404649628129 20611678126450803487221097)
        ·
          refine ⟨15458758594838102615415823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20611678126450803487221097 15458758594838102615415823)
          ·
            refine ⟨23188137892257153923123735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15458758594838102615415823 23188137892257153923123735)
            ·
              refine ⟨34782206838385730884685603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23188137892257153923123735 34782206838385730884685603)
              ·
                refine ⟨52173310257578596327028405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34782206838385730884685603 52173310257578596327028405)
                ·
                  refine ⟨4891247836647993405658913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52173310257578596327028405 4891247836647993405658913)
                  ·
                    refine ⟨3668435877485995054244185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4891247836647993405658913 3668435877485995054244185)
                    ·
                      refine ⟨2751326908114496290683139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3668435877485995054244185 2751326908114496290683139)
                      ·
                        rfl

theorem cell23_5358190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_5358190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358190 prefixEnd_5358190 := by exact prefixLift 5358190
  have htrace : WordTrace (prefixWord ++ tailWord_5358190) baseStart_5358190 baseEnd_5358190 := by
    simpa [prefixWord, tailWord_5358190, baseEnd_5358190] using wordTrace_append hprefix tailTrace_5358190
  have hstable : (prefixWord ++ tailWord_5358190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358190).length < 2 ^ (prefixWord ++ tailWord_5358190).sum := by decide
  have hdescent : baseEnd_5358190 < baseStart_5358190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358219 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 5]
def baseStart_5358219 : Nat := 118140960795 + 5358219 * 2 ^ 59
def prefixEnd_5358219 : Nat := 4983230072969 + 3 ^ 40 * 5358219 * 2
def baseEnd_5358219 : Nat := 2751341799053476677220505

theorem tailTrace_5358219 : CollatzResearch.WordTrace tailWord_5358219 prefixEnd_5358219 2751341799053476677220505 := by
  unfold tailWord_5358219
  simp only [CollatzResearch.WordTrace]
  refine ⟨195430302175095148794605711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130286868116730099196403807 195430302175095148794605711)
  ·
    refine ⟨293145453262642723191908567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195430302175095148794605711 293145453262642723191908567)
    ·
      refine ⟨439718179893964084787862851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293145453262642723191908567 439718179893964084787862851)
      ·
        refine ⟨659577269840946127181794277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439718179893964084787862851 659577269840946127181794277)
        ·
          refine ⟨123670738095177398846586427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 659577269840946127181794277 123670738095177398846586427)
          ·
            refine ⟨185506107142766098269879641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123670738095177398846586427 185506107142766098269879641)
            ·
              refine ⟨139129580357074573702409731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185506107142766098269879641 139129580357074573702409731)
              ·
                refine ⟨208694370535611860553614597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139129580357074573702409731 208694370535611860553614597)
                ·
                  refine ⟨39130194475427223853802737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 208694370535611860553614597 39130194475427223853802737)
                  ·
                    refine ⟨29347645856570417890352053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39130194475427223853802737 29347645856570417890352053)
                    ·
                      refine ⟨2751341799053476677220505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29347645856570417890352053 2751341799053476677220505)
                      ·
                        rfl

theorem cell23_5358219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 5].length) (baseStart_5358219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358219 prefixEnd_5358219 := by exact prefixLift 5358219
  have htrace : WordTrace (prefixWord ++ tailWord_5358219) baseStart_5358219 baseEnd_5358219 := by
    simpa [prefixWord, tailWord_5358219, baseEnd_5358219] using wordTrace_append hprefix tailTrace_5358219
  have hstable : (prefixWord ++ tailWord_5358219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358219).length < 2 ^ (prefixWord ++ tailWord_5358219).sum := by decide
  have hdescent : baseEnd_5358219 < baseStart_5358219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358240 : List Nat := [2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 3]
def baseStart_5358240 : Nat := 118140960795 + 5358240 * 2 ^ 59
def prefixEnd_5358240 : Nat := 4983230072969 + 3 ^ 40 * 5358240 * 2
def baseEnd_5358240 : Nat := 2751352582147221095057909

theorem tailTrace_5358240 : CollatzResearch.WordTrace tailWord_5358240 prefixEnd_5358240 2751352582147221095057909 := by
  unfold tailWord_5358240
  simp only [CollatzResearch.WordTrace]
  refine ⟨97715534054009534690560087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130287378738679379587413449 97715534054009534690560087)
  ·
    refine ⟨146573301081014302035840131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97715534054009534690560087 146573301081014302035840131)
    ·
      refine ⟨219859951621521453053760197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146573301081014302035840131 219859951621521453053760197)
      ·
        refine ⟨41223740929035272447580037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219859951621521453053760197 41223740929035272447580037)
        ·
          refine ⟨7729451424194113583921257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41223740929035272447580037 7729451424194113583921257)
          ·
            refine ⟨5797088568145585187940943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7729451424194113583921257 5797088568145585187940943)
            ·
              refine ⟨8695632852218377781911415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5797088568145585187940943 8695632852218377781911415)
              ·
                refine ⟨13043449278327566672867123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8695632852218377781911415 13043449278327566672867123)
                ·
                  refine ⟨19565173917491350009300685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13043449278327566672867123 19565173917491350009300685)
                  ·
                    refine ⟨7336940219059256253487757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19565173917491350009300685 7336940219059256253487757)
                    ·
                      refine ⟨2751352582147221095057909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7336940219059256253487757 2751352582147221095057909)
                      ·
                        rfl

theorem cell23_5358240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_5358240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358240 prefixEnd_5358240 := by exact prefixLift 5358240
  have htrace : WordTrace (prefixWord ++ tailWord_5358240) baseStart_5358240 baseEnd_5358240 := by
    simpa [prefixWord, tailWord_5358240, baseEnd_5358240] using wordTrace_append hprefix tailTrace_5358240
  have hstable : (prefixWord ++ tailWord_5358240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358240).length < 2 ^ (prefixWord ++ tailWord_5358240).sum := by decide
  have hdescent : baseEnd_5358240 < baseStart_5358240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358247 : List Nat := [1, 1, 6, 3, 2, 1, 2, 7]
def baseStart_5358247 : Nat := 118140960795 + 5358247 * 2 ^ 59
def prefixEnd_5358247 : Nat := 4983230072969 + 3 ^ 40 * 5358247 * 2
def baseEnd_5358247 : Nat := 101902080611548243247051

theorem tailTrace_5358247 : CollatzResearch.WordTrace tailWord_5358247 prefixEnd_5358247 101902080611548243247051 := by
  unfold tailWord_5358247
  simp only [CollatzResearch.WordTrace]
  refine ⟨195431323418993709576624995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130287548945995806384416663 195431323418993709576624995)
  ·
    refine ⟨293146985128490564364937493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195431323418993709576624995 293146985128490564364937493)
    ·
      refine ⟨13741264927897995204606445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 293146985128490564364937493 13741264927897995204606445)
      ·
        refine ⟨5152974347961748201727417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13741264927897995204606445 5152974347961748201727417)
        ·
          refine ⟨3864730760971311151295563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5152974347961748201727417 3864730760971311151295563)
          ·
            refine ⟨5797096141456966726943345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3864730760971311151295563 5797096141456966726943345)
            ·
              refine ⟨4347822106092725045207509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5797096141456966726943345 4347822106092725045207509)
              ·
                refine ⟨101902080611548243247051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4347822106092725045207509 101902080611548243247051)
                ·
                  rfl

theorem cell23_5358247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 7].length) (baseStart_5358247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358247 prefixEnd_5358247 := by exact prefixLift 5358247
  have htrace : WordTrace (prefixWord ++ tailWord_5358247) baseStart_5358247 baseEnd_5358247 := by
    simpa [prefixWord, tailWord_5358247, baseEnd_5358247] using wordTrace_append hprefix tailTrace_5358247
  have hstable : (prefixWord ++ tailWord_5358247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358247).length < 2 ^ (prefixWord ++ tailWord_5358247).sum := by decide
  have hdescent : baseEnd_5358247 < baseStart_5358247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358266 : List Nat := [3, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5]
def baseStart_5358266 : Nat := 118140960795 + 5358266 * 2 ^ 59
def prefixEnd_5358266 : Nat := 4983230072969 + 3 ^ 40 * 5358266 * 2
def baseEnd_5358266 : Nat := 2751365932644237993332789

theorem tailTrace_5358266 : CollatzResearch.WordTrace tailWord_5358266 prefixEnd_5358266 2751365932644237993332789 := by
  unfold tailWord_5358266
  simp only [CollatzResearch.WordTrace]
  refine ⟨48858004101481218955391663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130288010937283250547711101 48858004101481218955391663)
  ·
    refine ⟨73287006152221828433087495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48858004101481218955391663 73287006152221828433087495)
    ·
      refine ⟨109930509228332742649631243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73287006152221828433087495 109930509228332742649631243)
      ·
        refine ⟨164895763842499113974446865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109930509228332742649631243 164895763842499113974446865)
        ·
          refine ⟨123671822881874335480835149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164895763842499113974446865 123671822881874335480835149)
          ·
            refine ⟨46376933580702875805313181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123671822881874335480835149 46376933580702875805313181)
            ·
              refine ⟨17391350092763578426992443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46376933580702875805313181 17391350092763578426992443)
              ·
                refine ⟨26087025139145367640488665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17391350092763578426992443 26087025139145367640488665)
                ·
                  refine ⟨19565268854359025730366499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26087025139145367640488665 19565268854359025730366499)
                  ·
                    refine ⟨29347903281538538595549749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19565268854359025730366499 29347903281538538595549749)
                    ·
                      refine ⟨2751365932644237993332789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29347903281538538595549749 2751365932644237993332789)
                      ·
                        rfl

theorem cell23_5358266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_5358266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358266 prefixEnd_5358266 := by exact prefixLift 5358266
  have htrace : WordTrace (prefixWord ++ tailWord_5358266) baseStart_5358266 baseEnd_5358266 := by
    simpa [prefixWord, tailWord_5358266, baseEnd_5358266] using wordTrace_append hprefix tailTrace_5358266
  have hstable : (prefixWord ++ tailWord_5358266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358266).length < 2 ^ (prefixWord ++ tailWord_5358266).sum := by decide
  have hdescent : baseEnd_5358266 < baseStart_5358266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358280 : List Nat := [2, 1, 3, 1, 2, 3, 2, 1, 4, 2, 2]
def baseStart_5358280 : Nat := 118140960795 + 5358280 * 2 ^ 59
def prefixEnd_5358280 : Nat := 4983230072969 + 3 ^ 40 * 5358280 * 2
def baseEnd_5358280 : Nat := 2751373121373400938557725

theorem tailTrace_5358280 : CollatzResearch.WordTrace tailWord_5358280 prefixEnd_5358280 2751373121373400938557725 := by
  unfold tailWord_5358280
  simp only [CollatzResearch.WordTrace]
  refine ⟨97716263513937078106288147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130288351351916104141717529 97716263513937078106288147)
  ·
    refine ⟨146574395270905617159432221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97716263513937078106288147 146574395270905617159432221)
    ·
      refine ⟨54965398226589606434787083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146574395270905617159432221 54965398226589606434787083)
      ·
        refine ⟨82448097339884409652180625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54965398226589606434787083 82448097339884409652180625)
        ·
          refine ⟨61836073004913307239135469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82448097339884409652180625 61836073004913307239135469)
          ·
            refine ⟨23188527376842490214675801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61836073004913307239135469 23188527376842490214675801)
            ·
              refine ⟨17391395532631867661006851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23188527376842490214675801 17391395532631867661006851)
              ·
                refine ⟨26087093298947801491510277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17391395532631867661006851 26087093298947801491510277)
                ·
                  refine ⟨4891329993552712779658177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26087093298947801491510277 4891329993552712779658177)
                  ·
                    refine ⟨3668497495164534584743633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4891329993552712779658177 3668497495164534584743633)
                    ·
                      refine ⟨2751373121373400938557725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3668497495164534584743633 2751373121373400938557725)
                      ·
                        rfl

theorem cell23_5358280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 4, 2, 2].length) (baseStart_5358280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358280 prefixEnd_5358280 := by exact prefixLift 5358280
  have htrace : WordTrace (prefixWord ++ tailWord_5358280) baseStart_5358280 baseEnd_5358280 := by
    simpa [prefixWord, tailWord_5358280, baseEnd_5358280] using wordTrace_append hprefix tailTrace_5358280
  have hstable : (prefixWord ++ tailWord_5358280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358280).length < 2 ^ (prefixWord ++ tailWord_5358280).sum := by decide
  have hdescent : baseEnd_5358280 < baseStart_5358280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358343 : List Nat := [1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 5]
def baseStart_5358343 : Nat := 118140960795 + 5358343 * 2 ^ 59
def prefixEnd_5358343 : Nat := 4983230072969 + 3 ^ 40 * 5358343 * 2
def baseEnd_5358343 : Nat := 2751405470654634192069935

theorem tailTrace_5358343 : CollatzResearch.WordTrace tailWord_5358343 prefixEnd_5358343 2751405470654634192069935 := by
  unfold tailWord_5358343
  simp only [CollatzResearch.WordTrace]
  refine ⟨195434824826645917972119683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130289883217763945314746455 195434824826645917972119683)
  ·
    refine ⟨293152237239968876958179525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195434824826645917972119683 293152237239968876958179525)
    ·
      refine ⟨54966044482494164429658661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 293152237239968876958179525 54966044482494164429658661)
      ·
        refine ⟨10306133340467655830560999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54966044482494164429658661 10306133340467655830560999)
        ·
          refine ⟨15459200010701483745841499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10306133340467655830560999 15459200010701483745841499)
          ·
            refine ⟨23188800016052225618762249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15459200010701483745841499 23188800016052225618762249)
            ·
              refine ⟨17391600012039169214071687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23188800016052225618762249 17391600012039169214071687)
              ·
                refine ⟨26087400018058753821107531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17391600012039169214071687 26087400018058753821107531)
                ·
                  refine ⟨39131100027088130731661297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26087400018058753821107531 39131100027088130731661297)
                  ·
                    refine ⟨29348325020316098048745973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39131100027088130731661297 29348325020316098048745973)
                    ·
                      refine ⟨2751405470654634192069935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29348325020316098048745973 2751405470654634192069935)
                      ·
                        rfl

theorem cell23_5358343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_5358343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358343 prefixEnd_5358343 := by exact prefixLift 5358343
  have htrace : WordTrace (prefixWord ++ tailWord_5358343) baseStart_5358343 baseEnd_5358343 := by
    simpa [prefixWord, tailWord_5358343, baseEnd_5358343] using wordTrace_append hprefix tailTrace_5358343
  have hstable : (prefixWord ++ tailWord_5358343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358343).length < 2 ^ (prefixWord ++ tailWord_5358343).sum := by decide
  have hdescent : baseEnd_5358343 < baseStart_5358343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358353 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 1, 6, 2]
def baseStart_5358353 : Nat := 118140960795 + 5358353 * 2 ^ 59
def prefixEnd_5358353 : Nat := 4983230072969 + 3 ^ 40 * 5358353 * 2
def baseEnd_5358353 : Nat := 2751410605461179152944889

theorem tailTrace_5358353 : CollatzResearch.WordTrace tailWord_5358353 prefixEnd_5358353 2751410605461179152944889 := by
  unfold tailWord_5358353
  simp only [CollatzResearch.WordTrace]
  refine ⟨195435189556609689679983713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130290126371073126453322475 195435189556609689679983713)
  ·
    refine ⟨146576392167457267259987785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195435189556609689679983713 146576392167457267259987785)
    ·
      refine ⟨109932294125592950444990839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146576392167457267259987785 109932294125592950444990839)
      ·
        refine ⟨164898441188389425667486259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109932294125592950444990839 164898441188389425667486259)
        ·
          refine ⟨247347661782584138501229389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164898441188389425667486259 247347661782584138501229389)
          ·
            refine ⟨92755373168469051937961021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 247347661782584138501229389 92755373168469051937961021)
            ·
              refine ⟨34783264938175894476735383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92755373168469051937961021 34783264938175894476735383)
              ·
                refine ⟨52174897407263841715103075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34783264938175894476735383 52174897407263841715103075)
                ·
                  refine ⟨78262346110895762572654613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52174897407263841715103075 78262346110895762572654613)
                  ·
                    refine ⟨3668547473948238870593185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78262346110895762572654613 3668547473948238870593185)
                    ·
                      refine ⟨2751410605461179152944889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3668547473948238870593185 2751410605461179152944889)
                      ·
                        rfl

theorem cell23_5358353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 6, 2].length) (baseStart_5358353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358353 prefixEnd_5358353 := by exact prefixLift 5358353
  have htrace : WordTrace (prefixWord ++ tailWord_5358353) baseStart_5358353 baseEnd_5358353 := by
    simpa [prefixWord, tailWord_5358353, baseEnd_5358353] using wordTrace_append hprefix tailTrace_5358353
  have hstable : (prefixWord ++ tailWord_5358353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358353).length < 2 ^ (prefixWord ++ tailWord_5358353).sum := by decide
  have hdescent : baseEnd_5358353 < baseStart_5358353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358370 : List Nat := [3, 3, 1, 1, 2, 2, 3, 1, 2, 1, 4]
def baseStart_5358370 : Nat := 118140960795 + 5358370 * 2 ^ 59
def prefixEnd_5358370 : Nat := 4983230072969 + 3 ^ 40 * 5358370 * 2
def baseEnd_5358370 : Nat := 2751419334632305586432311

theorem tailTrace_5358370 : CollatzResearch.WordTrace tailWord_5358370 prefixEnd_5358370 2751419334632305586432311 := by
  unfold tailWord_5358370
  simp only [CollatzResearch.WordTrace]
  refine ⟨48858952399387025395838141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130290539731698734388901709 48858952399387025395838141)
  ·
    refine ⟨18322107149770134523439303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48858952399387025395838141 18322107149770134523439303)
    ·
      refine ⟨27483160724655201785158955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18322107149770134523439303 27483160724655201785158955)
      ·
        refine ⟨41224741086982802677738433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27483160724655201785158955 41224741086982802677738433)
        ·
          refine ⟨30918555815237102008303825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41224741086982802677738433 30918555815237102008303825)
          ·
            refine ⟨23188916861427826506227869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30918555815237102008303825 23188916861427826506227869)
            ·
              refine ⟨8695843823035434939835451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23188916861427826506227869 8695843823035434939835451)
              ·
                refine ⟨13043765734553152409753177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8695843823035434939835451 13043765734553152409753177)
                ·
                  refine ⟨9782824300914864307314883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13043765734553152409753177 9782824300914864307314883)
                  ·
                    refine ⟨14674236451372296460972325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9782824300914864307314883 14674236451372296460972325)
                    ·
                      refine ⟨2751419334632305586432311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14674236451372296460972325 2751419334632305586432311)
                      ·
                        rfl

theorem cell23_5358370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_5358370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358370 prefixEnd_5358370 := by exact prefixLift 5358370
  have htrace : WordTrace (prefixWord ++ tailWord_5358370) baseStart_5358370 baseEnd_5358370 := by
    simpa [prefixWord, tailWord_5358370, baseEnd_5358370] using wordTrace_append hprefix tailTrace_5358370
  have hstable : (prefixWord ++ tailWord_5358370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358370).length < 2 ^ (prefixWord ++ tailWord_5358370).sum := by decide
  have hdescent : baseEnd_5358370 < baseStart_5358370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358373 : List Nat := [1, 3, 1, 2, 3, 1, 3, 1, 1, 4, 3]
def baseStart_5358373 : Nat := 118140960795 + 5358373 * 2 ^ 59
def prefixEnd_5358373 : Nat := 4983230072969 + 3 ^ 40 * 5358373 * 2
def baseEnd_5358373 : Nat := 2751420875074269074694797

theorem tailTrace_5358373 : CollatzResearch.WordTrace tailWord_5358373 prefixEnd_5358373 2751420875074269074694797 := by
  unfold tailWord_5358373
  simp only [CollatzResearch.WordTrace]
  refine ⟨195435919016537233095711773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130290612677691488730474515 195435919016537233095711773)
  ·
    refine ⟨73288469631201462410891915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195435919016537233095711773 73288469631201462410891915)
    ·
      refine ⟨109932704446802193616337873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73288469631201462410891915 109932704446802193616337873)
      ·
        refine ⟨82449528335101645212253405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109932704446802193616337873 82449528335101645212253405)
        ·
          refine ⟨30918573125663116954595027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82449528335101645212253405 30918573125663116954595027)
          ·
            refine ⟨46377859688494675431892541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30918573125663116954595027 46377859688494675431892541)
            ·
              refine ⟨17391697383185503286959703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46377859688494675431892541 17391697383185503286959703)
              ·
                refine ⟨26087546074778254930439555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17391697383185503286959703 26087546074778254930439555)
                ·
                  refine ⟨39131319112167382395659333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26087546074778254930439555 39131319112167382395659333)
                  ·
                    refine ⟨7337122333531384199186125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39131319112167382395659333 7337122333531384199186125)
                    ·
                      refine ⟨2751420875074269074694797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7337122333531384199186125 2751420875074269074694797)
                      ·
                        rfl

theorem cell23_5358373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_5358373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358373 prefixEnd_5358373 := by exact prefixLift 5358373
  have htrace : WordTrace (prefixWord ++ tailWord_5358373) baseStart_5358373 baseEnd_5358373 := by
    simpa [prefixWord, tailWord_5358373, baseEnd_5358373] using wordTrace_append hprefix tailTrace_5358373
  have hstable : (prefixWord ++ tailWord_5358373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358373).length < 2 ^ (prefixWord ++ tailWord_5358373).sum := by decide
  have hdescent : baseEnd_5358373 < baseStart_5358373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358397 : List Nat := [1, 4, 1, 4, 2, 1, 2, 1, 3, 4]
def baseStart_5358397 : Nat := 118140960795 + 5358397 * 2 ^ 59
def prefixEnd_5358397 : Nat := 4983230072969 + 3 ^ 40 * 5358397 * 2
def baseEnd_5358397 : Nat := 917144399536658993598229

theorem tailTrace_5358397 : CollatzResearch.WordTrace tailWord_5358397 prefixEnd_5358397 917144399536658993598229 := by
  unfold tailWord_5358397
  simp only [CollatzResearch.WordTrace]
  refine ⟨195436794368450285194585445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130291196245633523463056963 195436794368450285194585445)
  ·
    refine ⟨36644398944084428473984771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195436794368450285194585445 36644398944084428473984771)
    ·
      refine ⟨54966598416126642710977157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36644398944084428473984771 54966598416126642710977157)
      ·
        refine ⟨10306237203023745508308217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54966598416126642710977157 10306237203023745508308217)
        ·
          refine ⟨7729677902267809131231163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10306237203023745508308217 7729677902267809131231163)
          ·
            refine ⟨11594516853401713696846745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7729677902267809131231163 11594516853401713696846745)
            ·
              refine ⟨8695887640051285272635059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11594516853401713696846745 8695887640051285272635059)
              ·
                refine ⟨13043831460076927908952589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8695887640051285272635059 13043831460076927908952589)
                ·
                  refine ⟨4891436797528847965857221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13043831460076927908952589 4891436797528847965857221)
                  ·
                    refine ⟨917144399536658993598229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4891436797528847965857221 917144399536658993598229)
                    ·
                      rfl

theorem cell23_5358397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_5358397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358397 prefixEnd_5358397 := by exact prefixLift 5358397
  have htrace : WordTrace (prefixWord ++ tailWord_5358397) baseStart_5358397 baseEnd_5358397 := by
    simpa [prefixWord, tailWord_5358397, baseEnd_5358397] using wordTrace_append hprefix tailTrace_5358397
  have hstable : (prefixWord ++ tailWord_5358397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358397).length < 2 ^ (prefixWord ++ tailWord_5358397).sum := by decide
  have hdescent : baseEnd_5358397 < baseStart_5358397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358416 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 7]
def baseStart_5358416 : Nat := 118140960795 + 5358416 * 2 ^ 59
def prefixEnd_5358416 : Nat := 4983230072969 + 3 ^ 40 * 5358416 * 2
def baseEnd_5358416 : Nat := 2751442954742412406457099

theorem tailTrace_5358416 : CollatzResearch.WordTrace tailWord_5358416 prefixEnd_5358416 2751442954742412406457099 := by
  unfold tailWord_5358416
  simp only [CollatzResearch.WordTrace]
  refine ⟨97718743677690725719763551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130291658236920967626351401 97718743677690725719763551)
  ·
    refine ⟨146578115516536088579645327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97718743677690725719763551 146578115516536088579645327)
    ·
      refine ⟨219867173274804132869467991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146578115516536088579645327 219867173274804132869467991)
      ·
        refine ⟨329800759912206199304201987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219867173274804132869467991 329800759912206199304201987)
        ·
          refine ⟨494701139868309298956302981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329800759912206199304201987 494701139868309298956302981)
          ·
            refine ⟨92756463725307993554306809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 494701139868309298956302981 92756463725307993554306809)
            ·
              refine ⟨69567347793980995165730107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92756463725307993554306809 69567347793980995165730107)
              ·
                refine ⟨104351021690971492748595161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69567347793980995165730107 104351021690971492748595161)
                ·
                  refine ⟨78263266268228619561446371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104351021690971492748595161 78263266268228619561446371)
                  ·
                    refine ⟨117394899402342929342169557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78263266268228619561446371 117394899402342929342169557)
                    ·
                      refine ⟨2751442954742412406457099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 117394899402342929342169557 2751442954742412406457099)
                      ·
                        rfl

theorem cell23_5358416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 7].length) (baseStart_5358416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358416 prefixEnd_5358416 := by exact prefixLift 5358416
  have htrace : WordTrace (prefixWord ++ tailWord_5358416) baseStart_5358416 baseEnd_5358416 := by
    simpa [prefixWord, tailWord_5358416, baseEnd_5358416] using wordTrace_append hprefix tailTrace_5358416
  have hstable : (prefixWord ++ tailWord_5358416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358416).length < 2 ^ (prefixWord ++ tailWord_5358416).sum := by decide
  have hdescent : baseEnd_5358416 < baseStart_5358416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358440 : List Nat := [2, 1, 4, 2, 1, 2, 2, 3, 1, 5]
def baseStart_5358440 : Nat := 118140960795 + 5358440 * 2 ^ 59
def prefixEnd_5358440 : Nat := 4983230072969 + 3 ^ 40 * 5358440 * 2
def baseEnd_5358440 : Nat := 917151759426040104185663

theorem tailTrace_5358440 : CollatzResearch.WordTrace tailWord_5358440 prefixEnd_5358440 917151759426040104185663 := by
  unfold tailWord_5358440
  simp only [CollatzResearch.WordTrace]
  refine ⟨97719181353647251769200387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130292241804863002358933849 97719181353647251769200387)
  ·
    refine ⟨146578772030470877653800581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97719181353647251769200387 146578772030470877653800581)
    ·
      refine ⟨27483519755713289560087609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146578772030470877653800581 27483519755713289560087609)
      ·
        refine ⟨20612639816784967170065707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27483519755713289560087609 20612639816784967170065707)
        ·
          refine ⟨30918959725177450755098561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20612639816784967170065707 30918959725177450755098561)
          ·
            refine ⟨23189219793883088066323921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30918959725177450755098561 23189219793883088066323921)
            ·
              refine ⟨17391914845412316049742941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23189219793883088066323921 17391914845412316049742941)
              ·
                refine ⟨6521968067029618518653603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17391914845412316049742941 6521968067029618518653603)
                ·
                  refine ⟨9782952100544427777980405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6521968067029618518653603 9782952100544427777980405)
                  ·
                    refine ⟨917151759426040104185663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9782952100544427777980405 917151759426040104185663)
                    ·
                      rfl

theorem cell23_5358440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_5358440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358440 prefixEnd_5358440 := by exact prefixLift 5358440
  have htrace : WordTrace (prefixWord ++ tailWord_5358440) baseStart_5358440 baseEnd_5358440 := by
    simpa [prefixWord, tailWord_5358440, baseEnd_5358440] using wordTrace_append hprefix tailTrace_5358440
  have hstable : (prefixWord ++ tailWord_5358440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358440).length < 2 ^ (prefixWord ++ tailWord_5358440).sum := by decide
  have hdescent : baseEnd_5358440 < baseStart_5358440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358454 : List Nat := [5, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3]
def baseStart_5358454 : Nat := 118140960795 + 5358454 * 2 ^ 59
def prefixEnd_5358454 : Nat := 4983230072969 + 3 ^ 40 * 5358454 * 2
def baseEnd_5358454 : Nat := 2751462467007283257781925

theorem tailTrace_5358454 : CollatzResearch.WordTrace tailWord_5358454 prefixEnd_5358454 2751462467007283257781925 := by
  unfold tailWord_5358454
  simp only [CollatzResearch.WordTrace]
  refine ⟨12214929583077736495588151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130292582219495855952940277 12214929583077736495588151)
  ·
    refine ⟨18322394374616604743382227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12214929583077736495588151 18322394374616604743382227)
    ·
      refine ⟨27483591561924907115073341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18322394374616604743382227 27483591561924907115073341)
      ·
        refine ⟨10306346835721840168152503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27483591561924907115073341 10306346835721840168152503)
        ·
          refine ⟨15459520253582760252228755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10306346835721840168152503 15459520253582760252228755)
          ·
            refine ⟨23189280380374140378343133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15459520253582760252228755 23189280380374140378343133)
            ·
              refine ⟨8695980142640302641878675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23189280380374140378343133 8695980142640302641878675)
              ·
                refine ⟨13043970213960453962818013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8695980142640302641878675 13043970213960453962818013)
                ·
                  refine ⟨4891488830235170236056755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13043970213960453962818013 4891488830235170236056755)
                  ·
                    refine ⟨7337233245352755354085133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4891488830235170236056755 7337233245352755354085133)
                    ·
                      refine ⟨2751462467007283257781925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7337233245352755354085133 2751462467007283257781925)
                      ·
                        rfl

theorem cell23_5358454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_5358454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358454 prefixEnd_5358454 := by exact prefixLift 5358454
  have htrace : WordTrace (prefixWord ++ tailWord_5358454) baseStart_5358454 baseEnd_5358454 := by
    simpa [prefixWord, tailWord_5358454, baseEnd_5358454] using wordTrace_append hprefix tailTrace_5358454
  have hstable : (prefixWord ++ tailWord_5358454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358454).length < 2 ^ (prefixWord ++ tailWord_5358454).sum := by decide
  have hdescent : baseEnd_5358454 < baseStart_5358454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358463 : List Nat := [1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 5]
def baseStart_5358463 : Nat := 118140960795 + 5358463 * 2 ^ 59
def prefixEnd_5358463 : Nat := 4983230072969 + 3 ^ 40 * 5358463 * 2
def baseEnd_5358463 : Nat := 2751467088333173722569383

theorem tailTrace_5358463 : CollatzResearch.WordTrace tailWord_5358463 prefixEnd_5358463 2751467088333173722569383 := by
  unfold tailWord_5358463
  simp only [CollatzResearch.WordTrace]
  refine ⟨195439201586211178466488043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130292801057474118977658695 195439201586211178466488043)
  ·
    refine ⟨293158802379316767699732065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195439201586211178466488043 293158802379316767699732065)
    ·
      refine ⟨219869101784487575774799049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293158802379316767699732065 219869101784487575774799049)
      ·
        refine ⟨164901826338365681831099287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219869101784487575774799049 164901826338365681831099287)
        ·
          refine ⟨247352739507548522746648931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164901826338365681831099287 247352739507548522746648931)
          ·
            refine ⟨371029109261322784119973397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247352739507548522746648931 371029109261322784119973397)
            ·
              refine ⟨17391989496624505505623753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 371029109261322784119973397 17391989496624505505623753)
              ·
                refine ⟨13043992122468379129217815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17391989496624505505623753 13043992122468379129217815)
                ·
                  refine ⟨19565988183702568693826723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13043992122468379129217815 19565988183702568693826723)
                  ·
                    refine ⟨29348982275553853040740085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19565988183702568693826723 29348982275553853040740085)
                    ·
                      refine ⟨2751467088333173722569383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29348982275553853040740085 2751467088333173722569383)
                      ·
                        rfl

theorem cell23_5358463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_5358463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358463 prefixEnd_5358463 := by exact prefixLift 5358463
  have htrace : WordTrace (prefixWord ++ tailWord_5358463) baseStart_5358463 baseEnd_5358463 := by
    simpa [prefixWord, tailWord_5358463, baseEnd_5358463] using wordTrace_append hprefix tailTrace_5358463
  have hstable : (prefixWord ++ tailWord_5358463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358463).length < 2 ^ (prefixWord ++ tailWord_5358463).sum := by decide
  have hdescent : baseEnd_5358463 < baseStart_5358463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358473 : List Nat := [1, 2, 1, 1, 5, 2, 2, 1, 1, 1, 6]
def baseStart_5358473 : Nat := 118140960795 + 5358473 * 2 ^ 59
def prefixEnd_5358473 : Nat := 4983230072969 + 3 ^ 40 * 5358473 * 2
def baseEnd_5358473 : Nat := 2751472223139718683444337

theorem tailTrace_5358473 : CollatzResearch.WordTrace tailWord_5358473 prefixEnd_5358473 2751472223139718683444337 := by
  unfold tailWord_5358473
  simp only [CollatzResearch.WordTrace]
  refine ⟨195439566316174950174352073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130293044210783300116234715 195439566316174950174352073)
  ·
    refine ⟨146579674737131212630764055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195439566316174950174352073 146579674737131212630764055)
    ·
      refine ⟨219869512105696818946146083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146579674737131212630764055 219869512105696818946146083)
      ·
        refine ⟨329804268158545228419219125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219869512105696818946146083 329804268158545228419219125)
        ·
          refine ⟨30919150139863615164301793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 329804268158545228419219125 30919150139863615164301793)
          ·
            refine ⟨23189362604897711373226345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30919150139863615164301793 23189362604897711373226345)
            ·
              refine ⟨17392021953673283529919759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23189362604897711373226345 17392021953673283529919759)
              ·
                refine ⟨26088032930509925294879639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17392021953673283529919759 26088032930509925294879639)
                ·
                  refine ⟨39132049395764887942319459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26088032930509925294879639 39132049395764887942319459)
                  ·
                    refine ⟨58698074093647331913479189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39132049395764887942319459 58698074093647331913479189)
                    ·
                      refine ⟨2751472223139718683444337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58698074093647331913479189 2751472223139718683444337)
                      ·
                        rfl

theorem cell23_5358473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 1, 6].length) (baseStart_5358473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358473 prefixEnd_5358473 := by exact prefixLift 5358473
  have htrace : WordTrace (prefixWord ++ tailWord_5358473) baseStart_5358473 baseEnd_5358473 := by
    simpa [prefixWord, tailWord_5358473, baseEnd_5358473] using wordTrace_append hprefix tailTrace_5358473
  have hstable : (prefixWord ++ tailWord_5358473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358473).length < 2 ^ (prefixWord ++ tailWord_5358473).sum := by decide
  have hdescent : baseEnd_5358473 < baseStart_5358473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358497 : List Nat := [1, 2, 3, 4, 1, 3, 1, 1, 1, 1, 5]
def baseStart_5358497 : Nat := 118140960795 + 5358497 * 2 ^ 59
def prefixEnd_5358497 : Nat := 4983230072969 + 3 ^ 40 * 5358497 * 2
def baseEnd_5358497 : Nat := 2751484546675426589544227

theorem tailTrace_5358497 : CollatzResearch.WordTrace tailWord_5358497 prefixEnd_5358497 2751484546675426589544227 := by
  unfold tailWord_5358497
  simp only [CollatzResearch.WordTrace]
  refine ⟨195440441668088002273225745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130293627778725334848817163 195440441668088002273225745)
  ·
    refine ⟨146580331251066001704919309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195440441668088002273225745 146580331251066001704919309)
    ·
      refine ⟨54967624219149750639344741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146580331251066001704919309 54967624219149750639344741)
      ·
        refine ⟨10306429541090578244877139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54967624219149750639344741 10306429541090578244877139)
        ·
          refine ⟨15459644311635867367315709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10306429541090578244877139 15459644311635867367315709)
          ·
            refine ⟨5797366616863450262743391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15459644311635867367315709 5797366616863450262743391)
            ·
              refine ⟨8696049925295175394115087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5797366616863450262743391 8696049925295175394115087)
              ·
                refine ⟨13044074887942763091172631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8696049925295175394115087 13044074887942763091172631)
                ·
                  refine ⟨19566112331914144636758947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13044074887942763091172631 19566112331914144636758947)
                  ·
                    refine ⟨29349168497871216955138421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19566112331914144636758947 29349168497871216955138421)
                    ·
                      refine ⟨2751484546675426589544227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29349168497871216955138421 2751484546675426589544227)
                      ·
                        rfl

theorem cell23_5358497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_5358497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358497 prefixEnd_5358497 := by exact prefixLift 5358497
  have htrace : WordTrace (prefixWord ++ tailWord_5358497) baseStart_5358497 baseEnd_5358497 := by
    simpa [prefixWord, tailWord_5358497, baseEnd_5358497] using wordTrace_append hprefix tailTrace_5358497
  have hstable : (prefixWord ++ tailWord_5358497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358497).length < 2 ^ (prefixWord ++ tailWord_5358497).sum := by decide
  have hdescent : baseEnd_5358497 < baseStart_5358497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358554 : List Nat := [3, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2]
def baseStart_5358554 : Nat := 118140960795 + 5358554 * 2 ^ 59
def prefixEnd_5358554 : Nat := 4983230072969 + 3 ^ 40 * 5358554 * 2
def baseEnd_5358554 : Nat := 2751513815072732866531465

theorem tailTrace_5358554 : CollatzResearch.WordTrace tailWord_5358554 prefixEnd_5358554 2751513815072732866531465 := by
  unfold tailWord_5358554
  simp only [CollatzResearch.WordTrace]
  refine ⟨48860630157220375252012679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130295013752587667338700477 48860630157220375252012679)
  ·
    refine ⟨73290945235830562878019019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48860630157220375252012679 73290945235830562878019019)
    ·
      refine ⟨109936417853745844317028529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73290945235830562878019019 109936417853745844317028529)
      ·
        refine ⟨82452313390309383237771397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109936417853745844317028529 82452313390309383237771397)
        ·
          refine ⟨15459808760683009357082137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82452313390309383237771397 15459808760683009357082137)
          ·
            refine ⟨11594856570512257017811603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15459808760683009357082137 11594856570512257017811603)
            ·
              refine ⟨17392284855768385526717405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11594856570512257017811603 17392284855768385526717405)
              ·
                refine ⟨6522106820913144572519027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17392284855768385526717405 6522106820913144572519027)
                ·
                  refine ⟨9783160231369716858778541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6522106820913144572519027 9783160231369716858778541)
                  ·
                    refine ⟨3668685086763643822041953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9783160231369716858778541 3668685086763643822041953)
                    ·
                      refine ⟨2751513815072732866531465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3668685086763643822041953 2751513815072732866531465)
                      ·
                        rfl

theorem cell23_5358554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2].length) (baseStart_5358554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358554 prefixEnd_5358554 := by exact prefixLift 5358554
  have htrace : WordTrace (prefixWord ++ tailWord_5358554) baseStart_5358554 baseEnd_5358554 := by
    simpa [prefixWord, tailWord_5358554, baseEnd_5358554] using wordTrace_append hprefix tailTrace_5358554
  have hstable : (prefixWord ++ tailWord_5358554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358554).length < 2 ^ (prefixWord ++ tailWord_5358554).sum := by decide
  have hdescent : baseEnd_5358554 < baseStart_5358554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358578 : List Nat := [3, 2, 1, 5, 1, 1, 3, 1, 2, 1, 3]
def baseStart_5358578 : Nat := 118140960795 + 5358578 * 2 ^ 59
def prefixEnd_5358578 : Nat := 4983230072969 + 3 ^ 40 * 5358578 * 2
def baseEnd_5358578 : Nat := 2751526138608440772631355

theorem tailTrace_5358578 : CollatzResearch.WordTrace tailWord_5358578 prefixEnd_5358578 2751526138608440772631355 := by
  unfold tailWord_5358578
  simp only [CollatzResearch.WordTrace]
  refine ⟨48860848995198638276731097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130295597320529702071282925 48860848995198638276731097)
  ·
    refine ⟨36645636746398978707548323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48860848995198638276731097 36645636746398978707548323)
    ·
      refine ⟨54968455119598468061322485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36645636746398978707548323 54968455119598468061322485)
      ·
        refine ⟨5153292667462356380748983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54968455119598468061322485 5153292667462356380748983)
        ·
          refine ⟨7729939001193534571123475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5153292667462356380748983 7729939001193534571123475)
          ·
            refine ⟨11594908501790301856685213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7729939001193534571123475 11594908501790301856685213)
            ·
              refine ⟨4348090688171363196256955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11594908501790301856685213 4348090688171363196256955)
              ·
                refine ⟨6522136032257044794385433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4348090688171363196256955 6522136032257044794385433)
                ·
                  refine ⟨4891602024192783595789075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6522136032257044794385433 4891602024192783595789075)
                  ·
                    refine ⟨7337403036289175393683613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4891602024192783595789075 7337403036289175393683613)
                    ·
                      refine ⟨2751526138608440772631355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7337403036289175393683613 2751526138608440772631355)
                      ·
                        rfl

theorem cell23_5358578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_5358578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358578 prefixEnd_5358578 := by exact prefixLift 5358578
  have htrace : WordTrace (prefixWord ++ tailWord_5358578) baseStart_5358578 baseEnd_5358578 := by
    simpa [prefixWord, tailWord_5358578, baseEnd_5358578] using wordTrace_append hprefix tailTrace_5358578
  have hstable : (prefixWord ++ tailWord_5358578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358578).length < 2 ^ (prefixWord ++ tailWord_5358578).sum := by decide
  have hdescent : baseEnd_5358578 < baseStart_5358578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358624 : List Nat := [2, 1, 1, 7, 1, 2, 1, 1, 7]
def baseStart_5358624 : Nat := 118140960795 + 5358624 * 2 ^ 59
def prefixEnd_5358624 : Nat := 4983230072969 + 3 ^ 40 * 5358624 * 2
def baseEnd_5358624 : Nat := 305727750968727510295127

theorem tailTrace_5358624 : CollatzResearch.WordTrace tailWord_5358624 prefixEnd_5358624 305727750968727510295127 := by
  unfold tailWord_5358624
  simp only [CollatzResearch.WordTrace]
  refine ⟨97722536869313951481549463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130296715825751935308732617 97722536869313951481549463)
  ·
    refine ⟨146583805303970927222324195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97722536869313951481549463 146583805303970927222324195)
    ·
      refine ⟨219875707955956390833486293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146583805303970927222324195 219875707955956390833486293)
      ·
        refine ⟨5153336905217727910159835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 219875707955956390833486293 5153336905217727910159835)
        ·
          refine ⟨7730005357826591865239753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5153336905217727910159835 7730005357826591865239753)
          ·
            refine ⟨5797504018369943898929815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7730005357826591865239753 5797504018369943898929815)
            ·
              refine ⟨8696256027554915848394723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5797504018369943898929815 8696256027554915848394723)
              ·
                refine ⟨13044384041332373772592085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8696256027554915848394723 13044384041332373772592085)
                ·
                  refine ⟨305727750968727510295127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13044384041332373772592085 305727750968727510295127)
                  ·
                    rfl

theorem cell23_5358624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 7].length) (baseStart_5358624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358624 prefixEnd_5358624 := by exact prefixLift 5358624
  have htrace : WordTrace (prefixWord ++ tailWord_5358624) baseStart_5358624 baseEnd_5358624 := by
    simpa [prefixWord, tailWord_5358624, baseEnd_5358624] using wordTrace_append hprefix tailTrace_5358624
  have hstable : (prefixWord ++ tailWord_5358624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358624).length < 2 ^ (prefixWord ++ tailWord_5358624).sum := by decide
  have hdescent : baseEnd_5358624 < baseStart_5358624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358640 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 4]
def baseStart_5358640 : Nat := 118140960795 + 5358640 * 2 ^ 59
def prefixEnd_5358640 : Nat := 4983230072969 + 3 ^ 40 * 5358640 * 2
def baseEnd_5358640 : Nat := 2751557974409019530056069

theorem tailTrace_5358640 : CollatzResearch.WordTrace tailWord_5358640 prefixEnd_5358640 2751557974409019530056069 := by
  unfold tailWord_5358640
  simp only [CollatzResearch.WordTrace]
  refine ⟨97722828653284968847840687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130297104871046625130454249 97722828653284968847840687)
  ·
    refine ⟨146584242979927453271761031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97722828653284968847840687 146584242979927453271761031)
    ·
      refine ⟨219876364469891179907641547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146584242979927453271761031 219876364469891179907641547)
      ·
        refine ⟨329814546704836769861462321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219876364469891179907641547 329814546704836769861462321)
        ·
          refine ⟨247360910028627577396096741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329814546704836769861462321 247360910028627577396096741)
          ·
            refine ⟨46380170630367670761768139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 247360910028627577396096741 46380170630367670761768139)
            ·
              refine ⟨69570255945551506142652209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46380170630367670761768139 69570255945551506142652209)
              ·
                refine ⟨52177691959163629606989157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69570255945551506142652209 52177691959163629606989157)
                ·
                  refine ⟨9783317242343180551310467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52177691959163629606989157 9783317242343180551310467)
                  ·
                    refine ⟨14674975863514770826965701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9783317242343180551310467 14674975863514770826965701)
                    ·
                      refine ⟨2751557974409019530056069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14674975863514770826965701 2751557974409019530056069)
                      ·
                        rfl

theorem cell23_5358640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 4].length) (baseStart_5358640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358640 prefixEnd_5358640 := by exact prefixLift 5358640
  have htrace : WordTrace (prefixWord ++ tailWord_5358640) baseStart_5358640 baseEnd_5358640 := by
    simpa [prefixWord, tailWord_5358640, baseEnd_5358640] using wordTrace_append hprefix tailTrace_5358640
  have hstable : (prefixWord ++ tailWord_5358640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358640).length < 2 ^ (prefixWord ++ tailWord_5358640).sum := by decide
  have hdescent : baseEnd_5358640 < baseStart_5358640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358654 : List Nat := [4, 2, 1, 3, 1, 2, 2, 1, 2, 5]
def baseStart_5358654 : Nat := 118140960795 + 5358654 * 2 ^ 59
def prefixEnd_5358654 : Nat := 4983230072969 + 3 ^ 40 * 5358654 * 2
def baseEnd_5358654 : Nat := 917188387712727491760335

theorem tailTrace_5358654 : CollatzResearch.WordTrace tailWord_5358654 prefixEnd_5358654 917188387712727491760335 := by
  unfold tailWord_5358654
  simp only [CollatzResearch.WordTrace]
  refine ⟨24430770991064902260836377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130297445285679478724460677 24430770991064902260836377)
  ·
    refine ⟨18323078243298676695627283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24430770991064902260836377 18323078243298676695627283)
    ·
      refine ⟨27484617364948015043440925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18323078243298676695627283 27484617364948015043440925)
      ·
        refine ⟨10306731511855505641290347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27484617364948015043440925 10306731511855505641290347)
        ·
          refine ⟨15460097267783258461935521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10306731511855505641290347 15460097267783258461935521)
          ·
            refine ⟨11595072950837443846451641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15460097267783258461935521 11595072950837443846451641)
            ·
              refine ⟨8696304713128082884838731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11595072950837443846451641 8696304713128082884838731)
              ·
                refine ⟨13044457069692124327258097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8696304713128082884838731 13044457069692124327258097)
                ·
                  refine ⟨9783342802269093245443573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13044457069692124327258097 9783342802269093245443573)
                  ·
                    refine ⟨917188387712727491760335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9783342802269093245443573 917188387712727491760335)
                    ·
                      rfl

theorem cell23_5358654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_5358654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358654 prefixEnd_5358654 := by exact prefixLift 5358654
  have htrace : WordTrace (prefixWord ++ tailWord_5358654) baseStart_5358654 baseEnd_5358654 := by
    simpa [prefixWord, tailWord_5358654, baseEnd_5358654] using wordTrace_append hprefix tailTrace_5358654
  have hstable : (prefixWord ++ tailWord_5358654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358654).length < 2 ^ (prefixWord ++ tailWord_5358654).sum := by decide
  have hdescent : baseEnd_5358654 < baseStart_5358654 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358670 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6]
def baseStart_5358670 : Nat := 118140960795 + 5358670 * 2 ^ 59
def prefixEnd_5358670 : Nat := 4983230072969 + 3 ^ 40 * 5358670 * 2
def baseEnd_5358670 : Nat := 2751573378828654412680931

theorem tailTrace_5358670 : CollatzResearch.WordTrace tailWord_5358670 prefixEnd_5358670 2751573378828654412680931 := by
  unfold tailWord_5358670
  simp only [CollatzResearch.WordTrace]
  refine ⟨24430843937057656602409183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130297834330974168546182309 24430843937057656602409183)
  ·
    refine ⟨36646265905586484903613775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24430843937057656602409183 36646265905586484903613775)
    ·
      refine ⟨54969398858379727355420663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36646265905586484903613775 54969398858379727355420663)
      ·
        refine ⟨82454098287569591033130995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54969398858379727355420663 82454098287569591033130995)
        ·
          refine ⟨123681147431354386549696493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82454098287569591033130995 123681147431354386549696493)
          ·
            refine ⟨46380430286757894956136185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123681147431354386549696493 46380430286757894956136185)
            ·
              refine ⟨34785322715068421217102139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46380430286757894956136185 34785322715068421217102139)
              ·
                refine ⟨52177984072602631825653209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34785322715068421217102139 52177984072602631825653209)
                ·
                  refine ⟨39133488054451973869239907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52177984072602631825653209 39133488054451973869239907)
                  ·
                    refine ⟨58700232081677960803859861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39133488054451973869239907 58700232081677960803859861)
                    ·
                      refine ⟨2751573378828654412680931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58700232081677960803859861 2751573378828654412680931)
                      ·
                        rfl

theorem cell23_5358670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_5358670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358670 prefixEnd_5358670 := by exact prefixLift 5358670
  have htrace : WordTrace (prefixWord ++ tailWord_5358670) baseStart_5358670 baseEnd_5358670 := by
    simpa [prefixWord, tailWord_5358670, baseEnd_5358670] using wordTrace_append hprefix tailTrace_5358670
  have hstable : (prefixWord ++ tailWord_5358670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358670).length < 2 ^ (prefixWord ++ tailWord_5358670).sum := by decide
  have hdescent : baseEnd_5358670 < baseStart_5358670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358677 : List Nat := [1, 3, 2, 2, 1, 2, 1, 4, 2, 2, 3]
def baseStart_5358677 : Nat := 118140960795 + 5358677 * 2 ^ 59
def prefixEnd_5358677 : Nat := 4983230072969 + 3 ^ 40 * 5358677 * 2
def baseEnd_5358677 : Nat := 2751576973193235885293399

theorem tailTrace_5358677 : CollatzResearch.WordTrace tailWord_5358677 prefixEnd_5358677 2751576973193235885293399 := by
  unfold tailWord_5358677
  simp only [CollatzResearch.WordTrace]
  refine ⟨195447006807435893014778285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130298004538290595343185523 195447006807435893014778285)
  ·
    refine ⟨73292627552788459880541857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195447006807435893014778285 73292627552788459880541857)
    ·
      refine ⟨54969470664591344910406393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73292627552788459880541857 54969470664591344910406393)
      ·
        refine ⟨41227102998443508682804795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54969470664591344910406393 41227102998443508682804795)
        ·
          refine ⟨61840654497665263024207193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41227102998443508682804795 61840654497665263024207193)
          ·
            refine ⟨46380490873248947268155395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61840654497665263024207193 46380490873248947268155395)
            ·
              refine ⟨69570736309873420902233093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46380490873248947268155395 69570736309873420902233093)
              ·
                refine ⟨13044513058101266419168705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69570736309873420902233093 13044513058101266419168705)
                ·
                  refine ⟨9783384793575949814376529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13044513058101266419168705 9783384793575949814376529)
                  ·
                    refine ⟨7337538595181962360782397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9783384793575949814376529 7337538595181962360782397)
                    ·
                      refine ⟨2751576973193235885293399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7337538595181962360782397 2751576973193235885293399)
                      ·
                        rfl

theorem cell23_5358677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_5358677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358677 prefixEnd_5358677 := by exact prefixLift 5358677
  have htrace : WordTrace (prefixWord ++ tailWord_5358677) baseStart_5358677 baseEnd_5358677 := by
    simpa [prefixWord, tailWord_5358677, baseEnd_5358677] using wordTrace_append hprefix tailTrace_5358677
  have hstable : (prefixWord ++ tailWord_5358677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358677).length < 2 ^ (prefixWord ++ tailWord_5358677).sum := by decide
  have hdescent : baseEnd_5358677 < baseStart_5358677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358757 : List Nat := [1, 3, 1, 2, 1, 4, 3, 1, 1, 6]
def baseStart_5358757 : Nat := 118140960795 + 5358757 * 2 ^ 59
def prefixEnd_5358757 : Nat := 4983230072969 + 3 ^ 40 * 5358757 * 2
def baseEnd_5358757 : Nat := 917206017215198524097677

theorem tailTrace_5358757 : CollatzResearch.WordTrace tailWord_5358757 prefixEnd_5358757 917206017215198524097677 := by
  unfold tailWord_5358757
  simp only [CollatzResearch.WordTrace]
  refine ⟨195449924647146066677690525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130299949764764044451793683 195449924647146066677690525)
  ·
    refine ⟨73293721742679775004133947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195449924647146066677690525 73293721742679775004133947)
    ·
      refine ⟨109940582614019662506200921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73293721742679775004133947 109940582614019662506200921)
      ·
        refine ⟨82455436960514746879650691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109940582614019662506200921 82455436960514746879650691)
        ·
          refine ⟨123683155440772120319476037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82455436960514746879650691 123683155440772120319476037)
          ·
            refine ⟨23190591645144772559901757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123683155440772120319476037 23190591645144772559901757)
            ·
              refine ⟨8696471866929289709963159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23190591645144772559901757 8696471866929289709963159)
              ·
                refine ⟨13044707800393934564944739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8696471866929289709963159 13044707800393934564944739)
                ·
                  refine ⟨19567061700590901847417109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13044707800393934564944739 19567061700590901847417109)
                  ·
                    refine ⟨917206017215198524097677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19567061700590901847417109 917206017215198524097677)
                    ·
                      rfl

theorem cell23_5358757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 6].length) (baseStart_5358757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358757 prefixEnd_5358757 := by exact prefixLift 5358757
  have htrace : WordTrace (prefixWord ++ tailWord_5358757) baseStart_5358757 baseEnd_5358757 := by
    simpa [prefixWord, tailWord_5358757, baseEnd_5358757] using wordTrace_append hprefix tailTrace_5358757
  have hstable : (prefixWord ++ tailWord_5358757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358757).length < 2 ^ (prefixWord ++ tailWord_5358757).sum := by decide
  have hdescent : baseEnd_5358757 < baseStart_5358757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358764 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 5, 2, 2]
def baseStart_5358764 : Nat := 118140960795 + 5358764 * 2 ^ 59
def prefixEnd_5358764 : Nat := 4983230072969 + 3 ^ 40 * 5358764 * 2
def baseEnd_5358764 : Nat := 2751621646010177044905499

theorem tailTrace_5358764 : CollatzResearch.WordTrace tailWord_5358764 prefixEnd_5358764 2751621646010177044905499 := by
  unfold tailWord_5358764
  simp only [CollatzResearch.WordTrace]
  refine ⟨97725089979060353436597673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130300119972080471248796897 97725089979060353436597673)
  ·
    refine ⟨73293817484295265077448255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97725089979060353436597673 73293817484295265077448255)
    ·
      refine ⟨109940726226442897616172383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73293817484295265077448255 109940726226442897616172383)
      ·
        refine ⟨164911089339664346424258575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109940726226442897616172383 164911089339664346424258575)
        ·
          refine ⟨247366634009496519636387863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164911089339664346424258575 247366634009496519636387863)
          ·
            refine ⟨371049951014244779454581795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247366634009496519636387863 371049951014244779454581795)
            ·
              refine ⟨556574926521367169181872693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371049951014244779454581795 556574926521367169181872693)
              ·
                refine ⟨52178899361378172110800565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 556574926521367169181872693 52178899361378172110800565)
                ·
                  refine ⟨4891771815129203635387553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52178899361378172110800565 4891771815129203635387553)
                  ·
                    refine ⟨3668828861346902726540665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4891771815129203635387553 3668828861346902726540665)
                    ·
                      refine ⟨2751621646010177044905499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3668828861346902726540665 2751621646010177044905499)
                      ·
                        rfl

theorem cell23_5358764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 2, 2].length) (baseStart_5358764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358764 prefixEnd_5358764 := by exact prefixLift 5358764
  have htrace : WordTrace (prefixWord ++ tailWord_5358764) baseStart_5358764 baseEnd_5358764 := by
    simpa [prefixWord, tailWord_5358764, baseEnd_5358764] using wordTrace_append hprefix tailTrace_5358764
  have hstable : (prefixWord ++ tailWord_5358764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358764).length < 2 ^ (prefixWord ++ tailWord_5358764).sum := by decide
  have hdescent : baseEnd_5358764 < baseStart_5358764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358767 : List Nat := [1, 1, 2, 1, 2, 3, 2, 3, 3, 2, 3]
def baseStart_5358767 : Nat := 118140960795 + 5358767 * 2 ^ 59
def prefixEnd_5358767 : Nat := 4983230072969 + 3 ^ 40 * 5358767 * 2
def baseEnd_5358767 : Nat := 2751623186452140533167985

theorem tailTrace_5358767 : CollatzResearch.WordTrace tailWord_5358767 prefixEnd_5358767 2751623186452140533167985 := by
  unfold tailWord_5358767
  simp only [CollatzResearch.WordTrace]
  refine ⟨195450289377109838385554555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130300192918073225590369703 195450289377109838385554555)
  ·
    refine ⟨293175434065664757578331833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195450289377109838385554555 293175434065664757578331833)
    ·
      refine ⟨219881575549248568183748875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293175434065664757578331833 219881575549248568183748875)
      ·
        refine ⟨329822363323872852275623313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219881575549248568183748875 329822363323872852275623313)
        ·
          refine ⟨247366772492904639206717485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329822363323872852275623313 247366772492904639206717485)
          ·
            refine ⟨92762539684839239702519057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 247366772492904639206717485 92762539684839239702519057)
            ·
              refine ⟨69571904763629429776889293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92762539684839239702519057 69571904763629429776889293)
              ·
                refine ⟨26089464286361036166333485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69571904763629429776889293 26089464286361036166333485)
                ·
                  refine ⟨9783549107385388562375057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26089464286361036166333485 9783549107385388562375057)
                  ·
                    refine ⟨7337661830539041421781293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9783549107385388562375057 7337661830539041421781293)
                    ·
                      refine ⟨2751623186452140533167985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7337661830539041421781293 2751623186452140533167985)
                      ·
                        rfl

theorem cell23_5358767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2, 3].length) (baseStart_5358767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358767 prefixEnd_5358767 := by exact prefixLift 5358767
  have htrace : WordTrace (prefixWord ++ tailWord_5358767) baseStart_5358767 baseEnd_5358767 := by
    simpa [prefixWord, tailWord_5358767, baseEnd_5358767] using wordTrace_append hprefix tailTrace_5358767
  have hstable : (prefixWord ++ tailWord_5358767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358767).length < 2 ^ (prefixWord ++ tailWord_5358767).sum := by decide
  have hdescent : baseEnd_5358767 < baseStart_5358767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358784 : List Nat := [2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 5]
def baseStart_5358784 : Nat := 118140960795 + 5358784 * 2 ^ 59
def prefixEnd_5358784 : Nat := 4983230072969 + 3 ^ 40 * 5358784 * 2
def baseEnd_5358784 : Nat := 2751631915623266966655407

theorem tailTrace_5358784 : CollatzResearch.WordTrace tailWord_5358784 prefixEnd_5358784 2751631915623266966655407 := by
  unfold tailWord_5358784
  simp only [CollatzResearch.WordTrace]
  refine ⟨97725454709024125144461703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130300606278698833525948937 97725454709024125144461703)
  ·
    refine ⟨146588182063536187716692555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97725454709024125144461703 146588182063536187716692555)
    ·
      refine ⟨219882273095304281575038833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146588182063536187716692555 219882273095304281575038833)
      ·
        refine ⟨164911704821478211181279125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219882273095304281575038833 164911704821478211181279125)
        ·
          refine ⟨7730236163506791149122459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 164911704821478211181279125 7730236163506791149122459)
          ·
            refine ⟨11595354245260186723683689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7730236163506791149122459 11595354245260186723683689)
            ·
              refine ⟨8696515683945140042762767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11595354245260186723683689 8696515683945140042762767)
              ·
                refine ⟨13044773525917710064144151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8696515683945140042762767 13044773525917710064144151)
                ·
                  refine ⟨19567160288876565096216227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13044773525917710064144151 19567160288876565096216227)
                  ·
                    refine ⟨29350740433314847644324341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19567160288876565096216227 29350740433314847644324341)
                    ·
                      refine ⟨2751631915623266966655407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29350740433314847644324341 2751631915623266966655407)
                      ·
                        rfl

theorem cell23_5358784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 5].length) (baseStart_5358784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358784 prefixEnd_5358784 := by exact prefixLift 5358784
  have htrace : WordTrace (prefixWord ++ tailWord_5358784) baseStart_5358784 baseEnd_5358784 := by
    simpa [prefixWord, tailWord_5358784, baseEnd_5358784] using wordTrace_append hprefix tailTrace_5358784
  have hstable : (prefixWord ++ tailWord_5358784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358784).length < 2 ^ (prefixWord ++ tailWord_5358784).sum := by decide
  have hdescent : baseEnd_5358784 < baseStart_5358784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358808 : List Nat := [2, 1, 2, 2, 5, 2, 2, 1, 2, 4]
def baseStart_5358808 : Nat := 118140960795 + 5358808 * 2 ^ 59
def prefixEnd_5358808 : Nat := 4983230072969 + 3 ^ 40 * 5358808 * 2
def baseEnd_5358808 : Nat := 917214746386324957585099

theorem tailTrace_5358808 : CollatzResearch.WordTrace tailWord_5358808 prefixEnd_5358808 917214746386324957585099 := by
  unfold tailWord_5358808
  simp only [CollatzResearch.WordTrace]
  refine ⟨97725892384980651193898539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130301189846640868258531385 97725892384980651193898539)
  ·
    refine ⟨146588838577470976790847809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97725892384980651193898539 146588838577470976790847809)
    ·
      refine ⟨109941628933103232593135857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146588838577470976790847809 109941628933103232593135857)
      ·
        refine ⟨82456221699827424444851893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109941628933103232593135857 82456221699827424444851893)
        ·
          refine ⟨7730270784358821041704865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82456221699827424444851893 7730270784358821041704865)
          ·
            refine ⟨5797703088269115781278649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7730270784358821041704865 5797703088269115781278649)
            ·
              refine ⟨4348277316201836835958987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5797703088269115781278649 4348277316201836835958987)
              ·
                refine ⟨6522415974302755253938481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4348277316201836835958987 6522415974302755253938481)
                ·
                  refine ⟨4891811980727066440453861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6522415974302755253938481 4891811980727066440453861)
                  ·
                    refine ⟨917214746386324957585099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4891811980727066440453861 917214746386324957585099)
                    ·
                      rfl

theorem cell23_5358808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 2, 4].length) (baseStart_5358808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358808 prefixEnd_5358808 := by exact prefixLift 5358808
  have htrace : WordTrace (prefixWord ++ tailWord_5358808) baseStart_5358808 baseEnd_5358808 := by
    simpa [prefixWord, tailWord_5358808, baseEnd_5358808] using wordTrace_append hprefix tailTrace_5358808
  have hstable : (prefixWord ++ tailWord_5358808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358808).length < 2 ^ (prefixWord ++ tailWord_5358808).sum := by decide
  have hdescent : baseEnd_5358808 < baseStart_5358808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358857 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 1, 6, 3]
def baseStart_5358857 : Nat := 118140960795 + 5358857 * 2 ^ 59
def prefixEnd_5358857 : Nat := 4983230072969 + 3 ^ 40 * 5358857 * 2
def baseEnd_5358857 : Nat := 2751669399711045181042571

theorem tailTrace_5358857 : CollatzResearch.WordTrace tailWord_5358857 prefixEnd_5358857 2751669399711045181042571 := by
  unfold tailWord_5358857
  simp only [CollatzResearch.WordTrace]
  refine ⟨195453571946783783756330825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130302381297855855837553883 195453571946783783756330825)
  ·
    refine ⟨146590178960087837817248119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195453571946783783756330825 146590178960087837817248119)
    ·
      refine ⟨219885268440131756725872179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146590178960087837817248119 219885268440131756725872179)
      ·
        refine ⟨329827902660197635088808269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219885268440131756725872179 329827902660197635088808269)
        ·
          refine ⟨123685463497574113158303101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 329827902660197635088808269 123685463497574113158303101)
          ·
            refine ⟨46382048811590292434363663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123685463497574113158303101 46382048811590292434363663)
            ·
              refine ⟨69573073217385438651545495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46382048811590292434363663 69573073217385438651545495)
              ·
                refine ⟨104359609826078157977318243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69573073217385438651545495 104359609826078157977318243)
                ·
                  refine ⟨156539414739117236965977365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104359609826078157977318243 156539414739117236965977365)
                  ·
                    refine ⟨7337785065896120482780189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 156539414739117236965977365 7337785065896120482780189)
                    ·
                      refine ⟨2751669399711045181042571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7337785065896120482780189 2751669399711045181042571)
                      ·
                        rfl

theorem cell23_5358857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 6, 3].length) (baseStart_5358857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358857 prefixEnd_5358857 := by exact prefixLift 5358857
  have htrace : WordTrace (prefixWord ++ tailWord_5358857) baseStart_5358857 baseEnd_5358857 := by
    simpa [prefixWord, tailWord_5358857, baseEnd_5358857] using wordTrace_append hprefix tailTrace_5358857
  have hstable : (prefixWord ++ tailWord_5358857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358857).length < 2 ^ (prefixWord ++ tailWord_5358857).sum := by decide
  have hdescent : baseEnd_5358857 < baseStart_5358857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358871 : List Nat := [1, 1, 3, 4, 1, 1, 4, 1, 1, 4, 2]
def baseStart_5358871 : Nat := 118140960795 + 5358871 * 2 ^ 59
def prefixEnd_5358871 : Nat := 4983230072969 + 3 ^ 40 * 5358871 * 2
def baseEnd_5358871 : Nat := 2751676588440208126267507

theorem tailTrace_5358871 : CollatzResearch.WordTrace tailWord_5358871 prefixEnd_5358871 2751676588440208126267507 := by
  unfold tailWord_5358871
  simp only [CollatzResearch.WordTrace]
  refine ⟨195454082568733064147340467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130302721712488709431560311 195454082568733064147340467)
  ·
    refine ⟨293181123853099596221010701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195454082568733064147340467 293181123853099596221010701)
    ·
      refine ⟨109942921444912348582879013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293181123853099596221010701 109942921444912348582879013)
      ·
        refine ⟨20614297770921065359289815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109942921444912348582879013 20614297770921065359289815)
        ·
          refine ⟨30921446656381598038934723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20614297770921065359289815 30921446656381598038934723)
          ·
            refine ⟨46382169984572397058402085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30921446656381598038934723 46382169984572397058402085)
            ·
              refine ⟨8696656872107324448450391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46382169984572397058402085 8696656872107324448450391)
              ·
                refine ⟨13044985308160986672675587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8696656872107324448450391 13044985308160986672675587)
                ·
                  refine ⟨19567477962241480009013381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13044985308160986672675587 19567477962241480009013381)
                  ·
                    refine ⟨3668902117920277501690009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19567477962241480009013381 3668902117920277501690009)
                    ·
                      refine ⟨2751676588440208126267507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3668902117920277501690009 2751676588440208126267507)
                      ·
                        rfl

theorem cell23_5358871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_5358871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358871 prefixEnd_5358871 := by exact prefixLift 5358871
  have htrace : WordTrace (prefixWord ++ tailWord_5358871) baseStart_5358871 baseEnd_5358871 := by
    simpa [prefixWord, tailWord_5358871, baseEnd_5358871] using wordTrace_append hprefix tailTrace_5358871
  have hstable : (prefixWord ++ tailWord_5358871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358871).length < 2 ^ (prefixWord ++ tailWord_5358871).sum := by decide
  have hdescent : baseEnd_5358871 < baseStart_5358871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358917 : List Nat := [1, 3, 1, 1, 1, 2, 1, 5, 1, 2, 5]
def baseStart_5358917 : Nat := 118140960795 + 5358917 * 2 ^ 59
def prefixEnd_5358917 : Nat := 4983230072969 + 3 ^ 40 * 5358917 * 2
def baseEnd_5358917 : Nat := 2751700208550314946292295

theorem tailTrace_5358917 : CollatzResearch.WordTrace tailWord_5358917 prefixEnd_5358917 2751700208550314946292295 := by
  unfold tailWord_5358917
  simp only [CollatzResearch.WordTrace]
  refine ⟨195455760326566414003515005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130303840217710942669010003 195455760326566414003515005)
  ·
    refine ⟨73295910122462405251318127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195455760326566414003515005 73295910122462405251318127)
    ·
      refine ⟨109943865183693607876977191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73295910122462405251318127 109943865183693607876977191)
      ·
        refine ⟨164915797775540411815465787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109943865183693607876977191 164915797775540411815465787)
        ·
          refine ⟨247373696663310617723198681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164915797775540411815465787 247373696663310617723198681)
          ·
            refine ⟨185530272497482963292399011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247373696663310617723198681 185530272497482963292399011)
            ·
              refine ⟨278295408746224444938598517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185530272497482963292399011 278295408746224444938598517)
              ·
                refine ⟨26090194569958541712993611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 278295408746224444938598517 26090194569958541712993611)
                ·
                  refine ⟨39135291854937812569490417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26090194569958541712993611 39135291854937812569490417)
                  ·
                    refine ⟨29351468891203359427117813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39135291854937812569490417 29351468891203359427117813)
                    ·
                      refine ⟨2751700208550314946292295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29351468891203359427117813 2751700208550314946292295)
                      ·
                        rfl

theorem cell23_5358917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_5358917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358917 prefixEnd_5358917 := by exact prefixLift 5358917
  have htrace : WordTrace (prefixWord ++ tailWord_5358917) baseStart_5358917 baseEnd_5358917 := by
    simpa [prefixWord, tailWord_5358917, baseEnd_5358917] using wordTrace_append hprefix tailTrace_5358917
  have hstable : (prefixWord ++ tailWord_5358917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358917).length < 2 ^ (prefixWord ++ tailWord_5358917).sum := by decide
  have hdescent : baseEnd_5358917 < baseStart_5358917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358944 : List Nat := [2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 4]
def baseStart_5358944 : Nat := 118140960795 + 5358944 * 2 ^ 59
def prefixEnd_5358944 : Nat := 4983230072969 + 3 ^ 40 * 5358944 * 2
def baseEnd_5358944 : Nat := 2751714072527986340654671

theorem tailTrace_5358944 : CollatzResearch.WordTrace tailWord_5358944 prefixEnd_5358944 2751714072527986340654671 := by
  unfold tailWord_5358944
  simp only [CollatzResearch.WordTrace]
  refine ⟨97728372548734298807373943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130304496731645731743165257 97728372548734298807373943)
  ·
    refine ⟨146592558823101448211060915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97728372548734298807373943 146592558823101448211060915)
    ·
      refine ⟨219888838234652172316591373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146592558823101448211060915 219888838234652172316591373)
      ·
        refine ⟨82458314337994564618721765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219888838234652172316591373 82458314337994564618721765)
        ·
          refine ⟨15460933938373980866010331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82458314337994564618721765 15460933938373980866010331)
          ·
            refine ⟨23191400907560971299015497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15460933938373980866010331 23191400907560971299015497)
            ·
              refine ⟨17393550680670728474261623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23191400907560971299015497 17393550680670728474261623)
              ·
                refine ⟨26090326021006092711392435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17393550680670728474261623 26090326021006092711392435)
                ·
                  refine ⟨39135489031509139067088653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26090326021006092711392435 39135489031509139067088653)
                  ·
                    refine ⟨14675808386815927150158245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39135489031509139067088653 14675808386815927150158245)
                    ·
                      refine ⟨2751714072527986340654671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14675808386815927150158245 2751714072527986340654671)
                      ·
                        rfl

theorem cell23_5358944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_5358944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358944 prefixEnd_5358944 := by exact prefixLift 5358944
  have htrace : WordTrace (prefixWord ++ tailWord_5358944) baseStart_5358944 baseEnd_5358944 := by
    simpa [prefixWord, tailWord_5358944, baseEnd_5358944] using wordTrace_append hprefix tailTrace_5358944
  have hstable : (prefixWord ++ tailWord_5358944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358944).length < 2 ^ (prefixWord ++ tailWord_5358944).sum := by decide
  have hdescent : baseEnd_5358944 < baseStart_5358944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358958 : List Nat := [4, 1, 2, 4, 1, 1, 1, 2, 2, 5]
def baseStart_5358958 : Nat := 118140960795 + 5358958 * 2 ^ 59
def prefixEnd_5358958 : Nat := 4983230072969 + 3 ^ 40 * 5358958 * 2
def baseEnd_5358958 : Nat := 917240420419049761959869

theorem tailTrace_5358958 : CollatzResearch.WordTrace tailWord_5358958 prefixEnd_5358958 917240420419049761959869 := by
  unfold tailWord_5358958
  simp only [CollatzResearch.WordTrace]
  refine ⟨24432156964927234750719691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130304837146278585337171685 24432156964927234750719691)
  ·
    refine ⟨36648235447390852126079537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24432156964927234750719691 36648235447390852126079537)
    ·
      refine ⟨27486176585543139094559653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36648235447390852126079537 27486176585543139094559653)
      ·
        refine ⟨5153658109789338580229935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27486176585543139094559653 5153658109789338580229935)
        ·
          refine ⟨7730487164684007870344903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5153658109789338580229935 7730487164684007870344903)
          ·
            refine ⟨11595730747026011805517355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7730487164684007870344903 11595730747026011805517355)
            ·
              refine ⟨17393596120539017708276033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11595730747026011805517355 17393596120539017708276033)
              ·
                refine ⟨13045197090404263281207025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17393596120539017708276033 13045197090404263281207025)
                ·
                  refine ⟨9783897817803197460905269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13045197090404263281207025 9783897817803197460905269)
                  ·
                    refine ⟨917240420419049761959869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9783897817803197460905269 917240420419049761959869)
                    ·
                      rfl

theorem cell23_5358958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_5358958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358958 prefixEnd_5358958 := by exact prefixLift 5358958
  have htrace : WordTrace (prefixWord ++ tailWord_5358958) baseStart_5358958 baseEnd_5358958 := by
    simpa [prefixWord, tailWord_5358958, baseEnd_5358958] using wordTrace_append hprefix tailTrace_5358958
  have hstable : (prefixWord ++ tailWord_5358958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358958).length < 2 ^ (prefixWord ++ tailWord_5358958).sum := by decide
  have hdescent : baseEnd_5358958 < baseStart_5358958 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5358967 : List Nat := [1, 1, 3, 1, 1, 2, 3, 3, 8]
def baseStart_5358967 : Nat := 118140960795 + 5358967 * 2 ^ 59
def prefixEnd_5358967 : Nat := 4983230072969 + 3 ^ 40 * 5358967 * 2
def baseEnd_5358967 : Nat := 305747320287004416740785

theorem tailTrace_5358967 : CollatzResearch.WordTrace tailWord_5358967 prefixEnd_5358967 305747320287004416740785 := by
  unfold tailWord_5358967
  simp only [CollatzResearch.WordTrace]
  refine ⟨195457583976385272542835155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130305055984256848361890103 195457583976385272542835155)
  ·
    refine ⟨293186375964577908814252733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195457583976385272542835155 293186375964577908814252733)
    ·
      refine ⟨109944890986716715805344775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293186375964577908814252733 109944890986716715805344775)
      ·
        refine ⟨164917336480075073708017163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109944890986716715805344775 164917336480075073708017163)
        ·
          refine ⟨247376004720112610562025745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164917336480075073708017163 247376004720112610562025745)
          ·
            refine ⟨185532003540084457921519309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247376004720112610562025745 185532003540084457921519309)
            ·
              refine ⟨69574501327531671720569741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185532003540084457921519309 69574501327531671720569741)
              ·
                refine ⟨26090437997824376895213653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69574501327531671720569741 26090437997824376895213653)
                ·
                  refine ⟨305747320287004416740785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26090437997824376895213653 305747320287004416740785)
                  ·
                    rfl

theorem cell23_5358967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 8].length) (baseStart_5358967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5358967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5358967 prefixEnd_5358967 := by exact prefixLift 5358967
  have htrace : WordTrace (prefixWord ++ tailWord_5358967) baseStart_5358967 baseEnd_5358967 := by
    simpa [prefixWord, tailWord_5358967, baseEnd_5358967] using wordTrace_append hprefix tailTrace_5358967
  have hstable : (prefixWord ++ tailWord_5358967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5358967).length < 2 ^ (prefixWord ++ tailWord_5358967).sum := by decide
  have hdescent : baseEnd_5358967 < baseStart_5358967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5358967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359061 : List Nat := [1, 3, 2, 3, 1, 1, 2, 2, 4, 4]
def baseStart_5359061 : Nat := 118140960795 + 5359061 * 2 ^ 59
def prefixEnd_5359061 : Nat := 4983230072969 + 3 ^ 40 * 5359061 * 2
def baseEnd_5359061 : Nat := 917258049921520794297211

theorem tailTrace_5359061 : CollatzResearch.WordTrace tailWord_5359061 prefixEnd_5359061 917258049921520794297211 := by
  unfold tailWord_5359061
  simp only [CollatzResearch.WordTrace]
  refine ⟨195461012438044726596757037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130307341625363151064504691 195461012438044726596757037)
  ·
    refine ⟨73297879664266772473783889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195461012438044726596757037 73297879664266772473783889)
    ·
      refine ⟨54973409748200079355337917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73297879664266772473783889 54973409748200079355337917)
      ·
        refine ⟨20615028655575029758251719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54973409748200079355337917 20615028655575029758251719)
        ·
          refine ⟨30922542983362544637377579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20615028655575029758251719 30922542983362544637377579)
          ·
            refine ⟨46383814475043816956066369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30922542983362544637377579 46383814475043816956066369)
            ·
              refine ⟨34787860856282862717049777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46383814475043816956066369 34787860856282862717049777)
              ·
                refine ⟨26090895642212147037787333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34787860856282862717049777 26090895642212147037787333)
                ·
                  refine ⟨4892042932914777569585125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26090895642212147037787333 4892042932914777569585125)
                  ·
                    refine ⟨917258049921520794297211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4892042932914777569585125 917258049921520794297211)
                    ·
                      rfl

theorem cell23_5359061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_5359061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359061 prefixEnd_5359061 := by exact prefixLift 5359061
  have htrace : WordTrace (prefixWord ++ tailWord_5359061) baseStart_5359061 baseEnd_5359061 := by
    simpa [prefixWord, tailWord_5359061, baseEnd_5359061] using wordTrace_append hprefix tailTrace_5359061
  have hstable : (prefixWord ++ tailWord_5359061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359061).length < 2 ^ (prefixWord ++ tailWord_5359061).sum := by decide
  have hdescent : baseEnd_5359061 < baseStart_5359061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359062 : List Nat := [5, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3]
def baseStart_5359062 : Nat := 118140960795 + 5359062 * 2 ^ 59
def prefixEnd_5359062 : Nat := 4983230072969 + 3 ^ 40 * 5359062 * 2
def baseEnd_5359062 : Nat := 2751774663245216878979129

theorem tailTrace_5359062 : CollatzResearch.WordTrace tailWord_5359062 prefixEnd_5359062 2751774663245216878979129 := by
  unfold tailWord_5359062
  simp only [CollatzResearch.WordTrace]
  refine ⟨12216315556940068985471465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130307365940694069178362293 12216315556940068985471465)
  ·
    refine ⟨9162236667705051739103599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12216315556940068985471465 9162236667705051739103599)
    ·
      refine ⟨13743355001557577608655399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9162236667705051739103599 13743355001557577608655399)
      ·
        refine ⟨20615032502336366412983099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13743355001557577608655399 20615032502336366412983099)
        ·
          refine ⟨30922548753504549619474649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20615032502336366412983099 30922548753504549619474649)
          ·
            refine ⟨23191911565128412214605987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30922548753504549619474649 23191911565128412214605987)
            ·
              refine ⟨34787867347692618321908981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23191911565128412214605987 34787867347692618321908981)
              ·
                refine ⟨3261362563846182967678967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34787867347692618321908981 3261362563846182967678967)
                ·
                  refine ⟨4892043845769274451518451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3261362563846182967678967 4892043845769274451518451)
                  ·
                    refine ⟨7338065768653911677277677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4892043845769274451518451 7338065768653911677277677)
                    ·
                      refine ⟨2751774663245216878979129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7338065768653911677277677 2751774663245216878979129)
                      ·
                        rfl

theorem cell23_5359062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_5359062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359062 prefixEnd_5359062 := by exact prefixLift 5359062
  have htrace : WordTrace (prefixWord ++ tailWord_5359062) baseStart_5359062 baseEnd_5359062 := by
    simpa [prefixWord, tailWord_5359062, baseEnd_5359062] using wordTrace_append hprefix tailTrace_5359062
  have hstable : (prefixWord ++ tailWord_5359062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359062).length < 2 ^ (prefixWord ++ tailWord_5359062).sum := by decide
  have hdescent : baseEnd_5359062 < baseStart_5359062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359102 : List Nat := [4, 2, 2, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_5359102 : Nat := 118140960795 + 5359102 * 2 ^ 59
def prefixEnd_5359102 : Nat := 4983230072969 + 3 ^ 40 * 5359102 * 2
def baseEnd_5359102 : Nat := 2751795202471396722478945

theorem tailTrace_5359102 : CollatzResearch.WordTrace tailWord_5359102 prefixEnd_5359102 2751795202471396722478945 := by
  unfold tailWord_5359102
  simp only [CollatzResearch.WordTrace]
  refine ⟨24432813478862023824874945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130308338553930793732666373 24432813478862023824874945)
  ·
    refine ⟨18324610109146517868656209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24432813478862023824874945 18324610109146517868656209)
    ·
      refine ⟨13743457581859888401492157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18324610109146517868656209 13743457581859888401492157)
      ·
        refine ⟨5153796593197458150559559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13743457581859888401492157 5153796593197458150559559)
        ·
          refine ⟨7730694889796187225839339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5153796593197458150559559 7730694889796187225839339)
          ·
            refine ⟨11596042334694280838759009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7730694889796187225839339 11596042334694280838759009)
            ·
              refine ⟨8697031751020710629069257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11596042334694280838759009 8697031751020710629069257)
              ·
                refine ⟨6522773813265532971801943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8697031751020710629069257 6522773813265532971801943)
                ·
                  refine ⟨9784160719898299457702915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6522773813265532971801943 9784160719898299457702915)
                  ·
                    refine ⟨14676241079847449186554373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9784160719898299457702915 14676241079847449186554373)
                    ·
                      refine ⟨2751795202471396722478945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14676241079847449186554373 2751795202471396722478945)
                      ·
                        rfl

theorem cell23_5359102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_5359102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359102 prefixEnd_5359102 := by exact prefixLift 5359102
  have htrace : WordTrace (prefixWord ++ tailWord_5359102) baseStart_5359102 baseEnd_5359102 := by
    simpa [prefixWord, tailWord_5359102, baseEnd_5359102] using wordTrace_append hprefix tailTrace_5359102
  have hstable : (prefixWord ++ tailWord_5359102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359102).length < 2 ^ (prefixWord ++ tailWord_5359102).sum := by decide
  have hdescent : baseEnd_5359102 < baseStart_5359102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359105 : List Nat := [1, 2, 4, 1, 4, 1, 2, 2, 1, 2, 3]
def baseStart_5359105 : Nat := 118140960795 + 5359105 * 2 ^ 59
def prefixEnd_5359105 : Nat := 4983230072969 + 3 ^ 40 * 5359105 * 2
def baseEnd_5359105 : Nat := 2751796742913360210741431

theorem tailTrace_5359105 : CollatzResearch.WordTrace tailWord_5359105 prefixEnd_5359105 2751796742913360210741431 := by
  unfold tailWord_5359105
  simp only [CollatzResearch.WordTrace]
  refine ⟨195462617249885322111358769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130308411499923548074239179 195462617249885322111358769)
  ·
    refine ⟨146596962937413991583519077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195462617249885322111358769 146596962937413991583519077)
    ·
      refine ⟨27486930550765123421909827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146596962937413991583519077 27486930550765123421909827)
      ·
        refine ⟨41230395826147685132864741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27486930550765123421909827 41230395826147685132864741)
        ·
          refine ⟨7730699217402690962412139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41230395826147685132864741 7730699217402690962412139)
          ·
            refine ⟨11596048826104036443618209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7730699217402690962412139 11596048826104036443618209)
            ·
              refine ⟨8697036619578027332713657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11596048826104036443618209 8697036619578027332713657)
              ·
                refine ⟨6522777464683520499535243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8697036619578027332713657 6522777464683520499535243)
                ·
                  refine ⟨9784166197025280749302865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6522777464683520499535243 9784166197025280749302865)
                  ·
                    refine ⟨7338124647768960561977149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9784166197025280749302865 7338124647768960561977149)
                    ·
                      refine ⟨2751796742913360210741431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7338124647768960561977149 2751796742913360210741431)
                      ·
                        rfl

theorem cell23_5359105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_5359105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359105 prefixEnd_5359105 := by exact prefixLift 5359105
  have htrace : WordTrace (prefixWord ++ tailWord_5359105) baseStart_5359105 baseEnd_5359105 := by
    simpa [prefixWord, tailWord_5359105, baseEnd_5359105] using wordTrace_append hprefix tailTrace_5359105
  have hstable : (prefixWord ++ tailWord_5359105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359105).length < 2 ^ (prefixWord ++ tailWord_5359105).sum := by decide
  have hdescent : baseEnd_5359105 < baseStart_5359105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359161 : List Nat := [1, 2, 1, 5, 1, 2, 1, 2, 2, 1, 5]
def baseStart_5359161 : Nat := 118140960795 + 5359161 * 2 ^ 59
def prefixEnd_5359161 : Nat := 4983230072969 + 3 ^ 40 * 5359161 * 2
def baseEnd_5359161 : Nat := 2751825497830011991641173

theorem tailTrace_5359161 : CollatzResearch.WordTrace tailWord_5359161 prefixEnd_5359161 2751825497830011991641173 := by
  unfold tailWord_5359161
  simp only [CollatzResearch.WordTrace]
  refine ⟨195464659737682443675397337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130309773158454962450264891 195464659737682443675397337)
  ·
    refine ⟨146598494803261832756548003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195464659737682443675397337 146598494803261832756548003)
    ·
      refine ⟨219897742204892749134822005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146598494803261832756548003 219897742204892749134822005)
      ·
        refine ⟨20615413331708695231389563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 219897742204892749134822005 20615413331708695231389563)
        ·
          refine ⟨30923119997563042847084345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20615413331708695231389563 30923119997563042847084345)
          ·
            refine ⟨23192339998172282135313259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30923119997563042847084345 23192339998172282135313259)
            ·
              refine ⟨34788509997258423202969889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23192339998172282135313259 34788509997258423202969889)
              ·
                refine ⟨26091382497943817402227417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34788509997258423202969889 26091382497943817402227417)
                ·
                  refine ⟨19568536873457863051670563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26091382497943817402227417 19568536873457863051670563)
                  ·
                    refine ⟨29352805310186794577505845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19568536873457863051670563 29352805310186794577505845)
                    ·
                      refine ⟨2751825497830011991641173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29352805310186794577505845 2751825497830011991641173)
                      ·
                        rfl

theorem cell23_5359161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_5359161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359161 prefixEnd_5359161 := by exact prefixLift 5359161
  have htrace : WordTrace (prefixWord ++ tailWord_5359161) baseStart_5359161 baseEnd_5359161 := by
    simpa [prefixWord, tailWord_5359161, baseEnd_5359161] using wordTrace_append hprefix tailTrace_5359161
  have hstable : (prefixWord ++ tailWord_5359161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359161).length < 2 ^ (prefixWord ++ tailWord_5359161).sum := by decide
  have hdescent : baseEnd_5359161 < baseStart_5359161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359175 : List Nat := [1, 1, 4, 1, 5, 1, 1, 2, 1, 4, 2]
def baseStart_5359175 : Nat := 118140960795 + 5359175 * 2 ^ 59
def prefixEnd_5359175 : Nat := 4983230072969 + 3 ^ 40 * 5359175 * 2
def baseEnd_5359175 : Nat := 2751832686559174936866109

theorem tailTrace_5359175 : CollatzResearch.WordTrace tailWord_5359175 prefixEnd_5359175 2751832686559174936866109 := by
  unfold tailWord_5359175
  simp only [CollatzResearch.WordTrace]
  refine ⟨195465170359631724066406979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130310113573087816044271319 195465170359631724066406979)
  ·
    refine ⟨293197755539447586099610469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195465170359631724066406979 293197755539447586099610469)
    ·
      refine ⟨54974579163646422393676963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 293197755539447586099610469 54974579163646422393676963)
      ·
        refine ⟨82461868745469633590515445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54974579163646422393676963 82461868745469633590515445)
        ·
          refine ⟨7730800194887778149110823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82461868745469633590515445 7730800194887778149110823)
          ·
            refine ⟨11596200292331667223666235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7730800194887778149110823 11596200292331667223666235)
            ·
              refine ⟨17394300438497500835499353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11596200292331667223666235 17394300438497500835499353)
              ·
                refine ⟨13045725328873125626624515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17394300438497500835499353 13045725328873125626624515)
                ·
                  refine ⟨19568587993309688439936773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13045725328873125626624515 19568587993309688439936773)
                  ·
                    refine ⟨3669110248745566582488145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19568587993309688439936773 3669110248745566582488145)
                    ·
                      refine ⟨2751832686559174936866109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3669110248745566582488145 2751832686559174936866109)
                      ·
                        rfl

theorem cell23_5359175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 4, 2].length) (baseStart_5359175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359175 prefixEnd_5359175 := by exact prefixLift 5359175
  have htrace : WordTrace (prefixWord ++ tailWord_5359175) baseStart_5359175 baseEnd_5359175 := by
    simpa [prefixWord, tailWord_5359175, baseEnd_5359175] using wordTrace_append hprefix tailTrace_5359175
  have hstable : (prefixWord ++ tailWord_5359175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359175).length < 2 ^ (prefixWord ++ tailWord_5359175).sum := by decide
  have hdescent : baseEnd_5359175 < baseStart_5359175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359208 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 1, 5, 3]
def baseStart_5359208 : Nat := 118140960795 + 5359208 * 2 ^ 59
def prefixEnd_5359208 : Nat := 4983230072969 + 3 ^ 40 * 5359208 * 2
def baseEnd_5359208 : Nat := 2751849631420773307753457

theorem tailTrace_5359208 : CollatzResearch.WordTrace tailWord_5359208 prefixEnd_5359208 2751849631420773307753457 := by
  unfold tailWord_5359208
  simp only [CollatzResearch.WordTrace]
  refine ⟨97733186984256085351179139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130310915979008113801572185 97733186984256085351179139)
  ·
    refine ⟨146599780476384128026768709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97733186984256085351179139 146599780476384128026768709)
    ·
      refine ⟨27487458839322024005019133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146599780476384128026768709 27487458839322024005019133)
      ·
        refine ⟨10307797064745759001882175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27487458839322024005019133 10307797064745759001882175)
        ·
          refine ⟨15461695597118638502823263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10307797064745759001882175 15461695597118638502823263)
          ·
            refine ⟨23192543395677957754234895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15461695597118638502823263 23192543395677957754234895)
            ·
              refine ⟨34788815093516936631352343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23192543395677957754234895 34788815093516936631352343)
              ·
                refine ⟨52183222640275404947028515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34788815093516936631352343 52183222640275404947028515)
                ·
                  refine ⟨78274833960413107420542773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52183222640275404947028515 78274833960413107420542773)
                  ·
                    refine ⟨7338265683788728820675885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78274833960413107420542773 7338265683788728820675885)
                    ·
                      refine ⟨2751849631420773307753457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7338265683788728820675885 2751849631420773307753457)
                      ·
                        rfl

theorem cell23_5359208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_5359208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359208 prefixEnd_5359208 := by exact prefixLift 5359208
  have htrace : WordTrace (prefixWord ++ tailWord_5359208) baseStart_5359208 baseEnd_5359208 := by
    simpa [prefixWord, tailWord_5359208, baseEnd_5359208] using wordTrace_append hprefix tailTrace_5359208
  have hstable : (prefixWord ++ tailWord_5359208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359208).length < 2 ^ (prefixWord ++ tailWord_5359208).sum := by decide
  have hdescent : baseEnd_5359208 < baseStart_5359208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359251 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 5, 4, 3]
def baseStart_5359251 : Nat := 118140960795 + 5359251 * 2 ^ 59
def prefixEnd_5359251 : Nat := 4983230072969 + 3 ^ 40 * 5359251 * 2
def baseEnd_5359251 : Nat := 2751871711088916639515759

theorem tailTrace_5359251 : CollatzResearch.WordTrace tailWord_5359251 prefixEnd_5359251 2751871711088916639515759 := by
  unfold tailWord_5359251
  simp only [CollatzResearch.WordTrace]
  refine ⟨195467942307356389046173607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130311961538237592697449071 195467942307356389046173607)
  ·
    refine ⟨293201913461034583569260411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195467942307356389046173607 293201913461034583569260411)
    ·
      refine ⟨439802870191551875353890617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293201913461034583569260411 439802870191551875353890617)
      ·
        refine ⟨329852152643663906515417963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 439802870191551875353890617 329852152643663906515417963)
        ·
          refine ⟨494778228965495859773126945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329852152643663906515417963 494778228965495859773126945)
          ·
            refine ⟨371083671724121894829845209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 494778228965495859773126945 371083671724121894829845209)
            ·
              refine ⟨278312753793091421122383907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 371083671724121894829845209 278312753793091421122383907)
              ·
                refine ⟨417469130689637131683575861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278312753793091421122383907 417469130689637131683575861)
                ·
                  refine ⟨39137731002153481095335237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 417469130689637131683575861 39137731002153481095335237)
                  ·
                    refine ⟨7338324562903777705375357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39137731002153481095335237 7338324562903777705375357)
                    ·
                      refine ⟨2751871711088916639515759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7338324562903777705375357 2751871711088916639515759)
                      ·
                        rfl

theorem cell23_5359251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4, 3].length) (baseStart_5359251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359251 prefixEnd_5359251 := by exact prefixLift 5359251
  have htrace : WordTrace (prefixWord ++ tailWord_5359251) baseStart_5359251 baseEnd_5359251 := by
    simpa [prefixWord, tailWord_5359251, baseEnd_5359251] using wordTrace_append hprefix tailTrace_5359251
  have hstable : (prefixWord ++ tailWord_5359251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359251).length < 2 ^ (prefixWord ++ tailWord_5359251).sum := by decide
  have hdescent : baseEnd_5359251 < baseStart_5359251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359261 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_5359261 : Nat := 118140960795 + 5359261 * 2 ^ 59
def prefixEnd_5359261 : Nat := 4983230072969 + 3 ^ 40 * 5359261 * 2
def baseEnd_5359261 : Nat := 2751876845895461600390713

theorem tailTrace_5359261 : CollatzResearch.WordTrace tailWord_5359261 prefixEnd_5359261 2751876845895461600390713 := by
  unfold tailWord_5359261
  simp only [CollatzResearch.WordTrace]
  refine ⟨195468307037320160754037637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130312204691546773836025091 195468307037320160754037637)
  ·
    refine ⟨36650307569497530141382057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195468307037320160754037637 36650307569497530141382057)
    ·
      refine ⟨27487730677123147606036543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36650307569497530141382057 27487730677123147606036543)
      ·
        refine ⟨41231596015684721409054815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27487730677123147606036543 41231596015684721409054815)
        ·
          refine ⟨61847394023527082113582223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41231596015684721409054815 61847394023527082113582223)
          ·
            refine ⟨92771091035290623170373335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61847394023527082113582223 92771091035290623170373335)
            ·
              refine ⟨139156636552935934755560003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92771091035290623170373335 139156636552935934755560003)
              ·
                refine ⟨208734954829403902133340005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139156636552935934755560003 208734954829403902133340005)
                ·
                  refine ⟨39137804030513231650001251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 208734954829403902133340005 39137804030513231650001251)
                  ·
                    refine ⟨58706706045769847475001877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39137804030513231650001251 58706706045769847475001877)
                    ·
                      refine ⟨2751876845895461600390713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58706706045769847475001877 2751876845895461600390713)
                      ·
                        rfl

theorem cell23_5359261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_5359261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359261 prefixEnd_5359261 := by exact prefixLift 5359261
  have htrace : WordTrace (prefixWord ++ tailWord_5359261) baseStart_5359261 baseEnd_5359261 := by
    simpa [prefixWord, tailWord_5359261, baseEnd_5359261] using wordTrace_append hprefix tailTrace_5359261
  have hstable : (prefixWord ++ tailWord_5359261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359261).length < 2 ^ (prefixWord ++ tailWord_5359261).sum := by decide
  have hdescent : baseEnd_5359261 < baseStart_5359261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359265 : List Nat := [1, 2, 3, 3, 2, 1, 2, 1, 2, 4, 2]
def baseStart_5359265 : Nat := 118140960795 + 5359265 * 2 ^ 59
def prefixEnd_5359265 : Nat := 4983230072969 + 3 ^ 40 * 5359265 * 2
def baseEnd_5359265 : Nat := 2751878899818079584740695

theorem tailTrace_5359265 : CollatzResearch.WordTrace tailWord_5359265 prefixEnd_5359265 2751878899818079584740695 := by
  unfold tailWord_5359265
  simp only [CollatzResearch.WordTrace]
  refine ⟨195468452929305669437183249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130312301952870446291455499 195468452929305669437183249)
  ·
    refine ⟨146601339696979252077887437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195468452929305669437183249 146601339696979252077887437)
    ·
      refine ⟨54975502386367219529207789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146601339696979252077887437 54975502386367219529207789)
      ·
        refine ⟨20615813394887707323452921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54975502386367219529207789 20615813394887707323452921)
        ·
          refine ⟨15461860046165780492589691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20615813394887707323452921 15461860046165780492589691)
          ·
            refine ⟨23192790069248670738884537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15461860046165780492589691 23192790069248670738884537)
            ·
              refine ⟨17394592551936503054163403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23192790069248670738884537 17394592551936503054163403)
              ·
                refine ⟨26091888827904754581245105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17394592551936503054163403 26091888827904754581245105)
                ·
                  refine ⟨19568916620928565935933829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26091888827904754581245105 19568916620928565935933829)
                  ·
                    refine ⟨3669171866424106112987593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19568916620928565935933829 3669171866424106112987593)
                    ·
                      refine ⟨2751878899818079584740695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3669171866424106112987593 2751878899818079584740695)
                      ·
                        rfl

theorem cell23_5359265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_5359265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359265 prefixEnd_5359265 := by exact prefixLift 5359265
  have htrace : WordTrace (prefixWord ++ tailWord_5359265) baseStart_5359265 baseEnd_5359265 := by
    simpa [prefixWord, tailWord_5359265, baseEnd_5359265] using wordTrace_append hprefix tailTrace_5359265
  have hstable : (prefixWord ++ tailWord_5359265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359265).length < 2 ^ (prefixWord ++ tailWord_5359265).sum := by decide
  have hdescent : baseEnd_5359265 < baseStart_5359265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359268 : List Nat := [2, 3, 1, 2, 2, 2, 1, 2, 1, 4, 3]
def baseStart_5359268 : Nat := 118140960795 + 5359268 * 2 ^ 59
def prefixEnd_5359268 : Nat := 4983230072969 + 3 ^ 40 * 5359268 * 2
def baseEnd_5359268 : Nat := 2751880440260043073003181

theorem tailTrace_5359268 : CollatzResearch.WordTrace tailWord_5359268 prefixEnd_5359268 2751880440260043073003181 := by
  unfold tailWord_5359268
  simp only [CollatzResearch.WordTrace]
  refine ⟨97734281174147400474771229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130312374898863200633028305 97734281174147400474771229)
  ·
    refine ⟨36650355440305275178039211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97734281174147400474771229 36650355440305275178039211)
    ·
      refine ⟨54975533160457912767058817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36650355440305275178039211 54975533160457912767058817)
      ·
        refine ⟨41231649870343434575294113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54975533160457912767058817 41231649870343434575294113)
        ·
          refine ⟨30923737402757575931470585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41231649870343434575294113 30923737402757575931470585)
          ·
            refine ⟨23192803052068181948602939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30923737402757575931470585 23192803052068181948602939)
            ·
              refine ⟨34789204578102272922904409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23192803052068181948602939 34789204578102272922904409)
              ·
                refine ⟨26091903433576704692178307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34789204578102272922904409 26091903433576704692178307)
                ·
                  refine ⟨39137855150365057038267461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26091903433576704692178307 39137855150365057038267461)
                  ·
                    refine ⟨7338347840693448194675149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39137855150365057038267461 7338347840693448194675149)
                    ·
                      refine ⟨2751880440260043073003181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7338347840693448194675149 2751880440260043073003181)
                      ·
                        rfl

theorem cell23_5359268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_5359268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359268 prefixEnd_5359268 := by exact prefixLift 5359268
  have htrace : WordTrace (prefixWord ++ tailWord_5359268) baseStart_5359268 baseEnd_5359268 := by
    simpa [prefixWord, tailWord_5359268, baseEnd_5359268] using wordTrace_append hprefix tailTrace_5359268
  have hstable : (prefixWord ++ tailWord_5359268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359268).length < 2 ^ (prefixWord ++ tailWord_5359268).sum := by decide
  have hdescent : baseEnd_5359268 < baseStart_5359268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359292 : List Nat := [2, 2, 2, 3, 1, 2, 3, 3, 1, 4]
def baseStart_5359292 : Nat := 118140960795 + 5359292 * 2 ^ 59
def prefixEnd_5359292 : Nat := 4983230072969 + 3 ^ 40 * 5359292 * 2
def baseEnd_5359292 : Nat := 917297587931916993034357

theorem tailTrace_5359292 : CollatzResearch.WordTrace tailWord_5359292 prefixEnd_5359292 917297587931916993034357 := by
  unfold tailWord_5359292
  simp only [CollatzResearch.WordTrace]
  refine ⟨97734718850103926524208065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130312958466805235365610753 97734718850103926524208065)
  ·
    refine ⟨73301039137577944893156049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97734718850103926524208065 73301039137577944893156049)
    ·
      refine ⟨54975779353183458669867037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73301039137577944893156049 54975779353183458669867037)
      ·
        refine ⟨20615917257443797001200139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54975779353183458669867037 20615917257443797001200139)
        ·
          refine ⟨30923875886165695501800209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20615917257443797001200139 30923875886165695501800209)
          ·
            refine ⟨23192906914624271626350157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30923875886165695501800209 23192906914624271626350157)
            ·
              refine ⟨8697340092984101859881309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23192906914624271626350157 8697340092984101859881309)
              ·
                refine ⟨3261502534869038197455491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8697340092984101859881309 3261502534869038197455491)
                ·
                  refine ⟨4892253802303557296183237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3261502534869038197455491 4892253802303557296183237)
                  ·
                    refine ⟨917297587931916993034357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4892253802303557296183237 917297587931916993034357)
                    ·
                      rfl

theorem cell23_5359292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_5359292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359292 prefixEnd_5359292 := by exact prefixLift 5359292
  have htrace : WordTrace (prefixWord ++ tailWord_5359292) baseStart_5359292 baseEnd_5359292 := by
    simpa [prefixWord, tailWord_5359292, baseEnd_5359292] using wordTrace_append hprefix tailTrace_5359292
  have hstable : (prefixWord ++ tailWord_5359292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359292).length < 2 ^ (prefixWord ++ tailWord_5359292).sum := by decide
  have hdescent : baseEnd_5359292 < baseStart_5359292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359309 : List Nat := [1, 6, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_5359309 : Nat := 118140960795 + 5359309 * 2 ^ 59
def prefixEnd_5359309 : Nat := 4983230072969 + 3 ^ 40 * 5359309 * 2
def baseEnd_5359309 : Nat := 917300497655625804196831

theorem tailTrace_5359309 : CollatzResearch.WordTrace tailWord_5359309 prefixEnd_5359309 917300497655625804196831 := by
  unfold tailWord_5359309
  simp only [CollatzResearch.WordTrace]
  refine ⟨195470057741146264951784981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130313371827430843301189987 195470057741146264951784981)
  ·
    refine ⟨9162658956616231169614921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 195470057741146264951784981 9162658956616231169614921)
    ·
      refine ⟨6871994217462173377211191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9162658956616231169614921 6871994217462173377211191)
      ·
        refine ⟨10307991326193260065816787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6871994217462173377211191 10307991326193260065816787)
        ·
          refine ⟨15461986989289890098725181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10307991326193260065816787 15461986989289890098725181)
          ·
            refine ⟨5798245120983708787021943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15461986989289890098725181 5798245120983708787021943)
            ·
              refine ⟨8697367681475563180532915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5798245120983708787021943 8697367681475563180532915)
              ·
                refine ⟨13046051522213344770799373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8697367681475563180532915 13046051522213344770799373)
                ·
                  refine ⟨4892269320830004289049765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13046051522213344770799373 4892269320830004289049765)
                  ·
                    refine ⟨917300497655625804196831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4892269320830004289049765 917300497655625804196831)
                    ·
                      rfl

theorem cell23_5359309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_5359309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359309 prefixEnd_5359309 := by exact prefixLift 5359309
  have htrace : WordTrace (prefixWord ++ tailWord_5359309) baseStart_5359309 baseEnd_5359309 := by
    simpa [prefixWord, tailWord_5359309, baseEnd_5359309] using wordTrace_append hprefix tailTrace_5359309
  have hstable : (prefixWord ++ tailWord_5359309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359309).length < 2 ^ (prefixWord ++ tailWord_5359309).sum := by decide
  have hdescent : baseEnd_5359309 < baseStart_5359309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359342 : List Nat := [4, 1, 2, 1, 1, 2, 4, 1, 2, 3, 2]
def baseStart_5359342 : Nat := 118140960795 + 5359342 * 2 ^ 59
def prefixEnd_5359342 : Nat := 4983230072969 + 3 ^ 40 * 5359342 * 2
def baseEnd_5359342 : Nat := 2751918437828475783477841

theorem tailTrace_5359342 : CollatzResearch.WordTrace tailWord_5359342 prefixEnd_5359342 2751918437828475783477841 := by
  unfold tailWord_5359342
  simp only [CollatzResearch.WordTrace]
  refine ⟨24433907668753338948467035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130314174233351141058490853 24433907668753338948467035)
  ·
    refine ⟨36650861503130008422700553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24433907668753338948467035 36650861503130008422700553)
    ·
      refine ⟨27488146127347506317025415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36650861503130008422700553 27488146127347506317025415)
      ·
        refine ⟨41232219191021259475538123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27488146127347506317025415 41232219191021259475538123)
        ·
          refine ⟨61848328786531889213307185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41232219191021259475538123 61848328786531889213307185)
          ·
            refine ⟨46386246589898916909980389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61848328786531889213307185 46386246589898916909980389)
            ·
              refine ⟨8697421235606046920621323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46386246589898916909980389 8697421235606046920621323)
              ·
                refine ⟨13046131853409070380931985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8697421235606046920621323 13046131853409070380931985)
                ·
                  refine ⟨9784598890056802785698989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13046131853409070380931985 9784598890056802785698989)
                  ·
                    refine ⟨3669224583771301044637121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9784598890056802785698989 3669224583771301044637121)
                    ·
                      refine ⟨2751918437828475783477841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3669224583771301044637121 2751918437828475783477841)
                      ·
                        rfl

theorem cell23_5359342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_5359342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359342 prefixEnd_5359342 := by exact prefixLift 5359342
  have htrace : WordTrace (prefixWord ++ tailWord_5359342) baseStart_5359342 baseEnd_5359342 := by
    simpa [prefixWord, tailWord_5359342, baseEnd_5359342] using wordTrace_append hprefix tailTrace_5359342
  have hstable : (prefixWord ++ tailWord_5359342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359342).length < 2 ^ (prefixWord ++ tailWord_5359342).sum := by decide
  have hdescent : baseEnd_5359342 < baseStart_5359342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359355 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 7, 2, 2]
def baseStart_5359355 : Nat := 118140960795 + 5359355 * 2 ^ 59
def prefixEnd_5359355 : Nat := 4983230072969 + 3 ^ 40 * 5359355 * 2
def baseEnd_5359355 : Nat := 2751925113076984232615281

theorem tailTrace_5359355 : CollatzResearch.WordTrace tailWord_5359355 prefixEnd_5359355 2751925113076984232615281 := by
  unfold tailWord_5359355
  simp only [CollatzResearch.WordTrace]
  refine ⟨195471735498979614807959519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130314490332653076538639679 195471735498979614807959519)
  ·
    refine ⟨293207603248469422211939279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195471735498979614807959519 293207603248469422211939279)
    ·
      refine ⟨439811404872704133317908919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293207603248469422211939279 439811404872704133317908919)
      ·
        refine ⟨659717107309056199976863379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439811404872704133317908919 659717107309056199976863379)
        ·
          refine ⟨989575660963584299965295069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 659717107309056199976863379 989575660963584299965295069)
          ·
            refine ⟨371090872861344112486985651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 989575660963584299965295069 371090872861344112486985651)
            ·
              refine ⟨556636309292016168730478477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371090872861344112486985651 556636309292016168730478477)
              ·
                refine ⟨208738615984506063273929429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 556636309292016168730478477 208738615984506063273929429)
                ·
                  refine ⟨4892311312136860857982721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 208738615984506063273929429 4892311312136860857982721)
                  ·
                    refine ⟨3669233484102645643487041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4892311312136860857982721 3669233484102645643487041)
                    ·
                      refine ⟨2751925113076984232615281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3669233484102645643487041 2751925113076984232615281)
                      ·
                        rfl

theorem cell23_5359355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7, 2, 2].length) (baseStart_5359355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359355 prefixEnd_5359355 := by exact prefixLift 5359355
  have htrace : WordTrace (prefixWord ++ tailWord_5359355) baseStart_5359355 baseEnd_5359355 := by
    simpa [prefixWord, tailWord_5359355, baseEnd_5359355] using wordTrace_append hprefix tailTrace_5359355
  have hstable : (prefixWord ++ tailWord_5359355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359355).length < 2 ^ (prefixWord ++ tailWord_5359355).sum := by decide
  have hdescent : baseEnd_5359355 < baseStart_5359355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359368 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 3, 2, 4]
def baseStart_5359368 : Nat := 118140960795 + 5359368 * 2 ^ 59
def prefixEnd_5359368 : Nat := 4983230072969 + 3 ^ 40 * 5359368 * 2
def baseEnd_5359368 : Nat := 2751931788325492681752721

theorem tailTrace_5359368 : CollatzResearch.WordTrace tailWord_5359368 prefixEnd_5359368 2751931788325492681752721 := by
  unfold tailWord_5359368
  simp only [CollatzResearch.WordTrace]
  refine ⟨97736104823966259014091379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130314806431955012018788505 97736104823966259014091379)
  ·
    refine ⟨146604157235949388521137069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97736104823966259014091379 146604157235949388521137069)
    ·
      refine ⟨54976558963481020695426401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146604157235949388521137069 54976558963481020695426401)
      ·
        refine ⟨41232419222610765521569801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54976558963481020695426401 41232419222610765521569801)
        ·
          refine ⟨30924314416958074141177351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41232419222610765521569801 30924314416958074141177351)
          ·
            refine ⟨46386471625437111211766027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30924314416958074141177351 46386471625437111211766027)
            ·
              refine ⟨69579707438155666817649041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46386471625437111211766027 69579707438155666817649041)
              ·
                refine ⟨52184780578616750113236781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69579707438155666817649041 52184780578616750113236781)
                ·
                  refine ⟨19569292716981281292463793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52184780578616750113236781 19569292716981281292463793)
                  ·
                    refine ⟨14676969537735960969347845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19569292716981281292463793 14676969537735960969347845)
                    ·
                      refine ⟨2751931788325492681752721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14676969537735960969347845 2751931788325492681752721)
                      ·
                        rfl

theorem cell23_5359368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_5359368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359368 prefixEnd_5359368 := by exact prefixLift 5359368
  have htrace : WordTrace (prefixWord ++ tailWord_5359368) baseStart_5359368 baseEnd_5359368 := by
    simpa [prefixWord, tailWord_5359368, baseEnd_5359368] using wordTrace_append hprefix tailTrace_5359368
  have hstable : (prefixWord ++ tailWord_5359368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359368).length < 2 ^ (prefixWord ++ tailWord_5359368).sum := by decide
  have hdescent : baseEnd_5359368 < baseStart_5359368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359406 : List Nat := [4, 1, 3, 2, 2, 2, 2, 1, 1, 1, 4]
def baseStart_5359406 : Nat := 118140960795 + 5359406 * 2 ^ 59
def prefixEnd_5359406 : Nat := 4983230072969 + 3 ^ 40 * 5359406 * 2
def baseEnd_5359406 : Nat := 2751951300590363533077547

theorem tailTrace_5359406 : CollatzResearch.WordTrace tailWord_5359406 prefixEnd_5359406 2751951300590363533077547 := by
  unfold tailWord_5359406
  simp only [CollatzResearch.WordTrace]
  refine ⟨24434199452724356314758259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130315730414529900345377381 24434199452724356314758259)
  ·
    refine ⟨36651299179086534472137389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24434199452724356314758259 36651299179086534472137389)
    ·
      refine ⟨13744237192157450427051521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36651299179086534472137389 13744237192157450427051521)
      ·
        refine ⟨10308177894118087820288641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13744237192157450427051521 10308177894118087820288641)
        ·
          refine ⟨7731133420588565865216481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10308177894118087820288641 7731133420588565865216481)
          ·
            refine ⟨5798350065441424398912361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7731133420588565865216481 5798350065441424398912361)
            ·
              refine ⟨4348762549081068299184271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5798350065441424398912361 4348762549081068299184271)
              ·
                refine ⟨6523143823621602448776407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4348762549081068299184271 6523143823621602448776407)
                ·
                  refine ⟨9784715735432403673164611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6523143823621602448776407 9784715735432403673164611)
                  ·
                    refine ⟨14677073603148605509746917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9784715735432403673164611 14677073603148605509746917)
                    ·
                      refine ⟨2751951300590363533077547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14677073603148605509746917 2751951300590363533077547)
                      ·
                        rfl

theorem cell23_5359406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_5359406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359406 prefixEnd_5359406 := by exact prefixLift 5359406
  have htrace : WordTrace (prefixWord ++ tailWord_5359406) baseStart_5359406 baseEnd_5359406 := by
    simpa [prefixWord, tailWord_5359406, baseEnd_5359406] using wordTrace_append hprefix tailTrace_5359406
  have hstable : (prefixWord ++ tailWord_5359406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359406).length < 2 ^ (prefixWord ++ tailWord_5359406).sum := by decide
  have hdescent : baseEnd_5359406 < baseStart_5359406 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359409 : List Nat := [1, 2, 2, 3, 2, 4, 2, 1, 1, 2, 3]
def baseStart_5359409 : Nat := 118140960795 + 5359409 * 2 ^ 59
def prefixEnd_5359409 : Nat := 4983230072969 + 3 ^ 40 * 5359409 * 2
def baseEnd_5359409 : Nat := 2751952841032327021340033

theorem tailTrace_5359409 : CollatzResearch.WordTrace tailWord_5359409 prefixEnd_5359409 2751952841032327021340033 := by
  unfold tailWord_5359409
  simp only [CollatzResearch.WordTrace]
  refine ⟨195473705040783982030425281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130315803360522654686950187 195473705040783982030425281)
  ·
    refine ⟨146605278780587986522818961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195473705040783982030425281 146605278780587986522818961)
    ·
      refine ⟨109953959085440989892114221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146605278780587986522818961 109953959085440989892114221)
      ·
        refine ⟨41232734657040371209542833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109953959085440989892114221 41232734657040371209542833)
        ·
          refine ⟨30924550992780278407157125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41232734657040371209542833 30924550992780278407157125)
          ·
            refine ⟨5798353311146302201341961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30924550992780278407157125 5798353311146302201341961)
            ·
              refine ⟨4348764983359726651006471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5798353311146302201341961 4348764983359726651006471)
              ·
                refine ⟨6523147475039589976509707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4348764983359726651006471 6523147475039589976509707)
                ·
                  refine ⟨9784721212559384964764561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6523147475039589976509707 9784721212559384964764561)
                  ·
                    refine ⟨7338540909419538723573421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9784721212559384964764561 7338540909419538723573421)
                    ·
                      refine ⟨2751952841032327021340033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7338540909419538723573421 2751952841032327021340033)
                      ·
                        rfl

theorem cell23_5359409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_5359409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359409 prefixEnd_5359409 := by exact prefixLift 5359409
  have htrace : WordTrace (prefixWord ++ tailWord_5359409) baseStart_5359409 baseEnd_5359409 := by
    simpa [prefixWord, tailWord_5359409, baseEnd_5359409] using wordTrace_append hprefix tailTrace_5359409
  have hstable : (prefixWord ++ tailWord_5359409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359409).length < 2 ^ (prefixWord ++ tailWord_5359409).sum := by decide
  have hdescent : baseEnd_5359409 < baseStart_5359409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359415 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 5, 3, 2]
def baseStart_5359415 : Nat := 118140960795 + 5359415 * 2 ^ 59
def prefixEnd_5359415 : Nat := 4983230072969 + 3 ^ 40 * 5359415 * 2
def baseEnd_5359415 : Nat := 2751955921916253997865005

theorem tailTrace_5359415 : CollatzResearch.WordTrace tailWord_5359415 prefixEnd_5359415 2751955921916253997865005 := by
  unfold tailWord_5359415
  simp only [CollatzResearch.WordTrace]
  refine ⟨195473923878762245055143699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130315949252508163370095799 195473923878762245055143699)
  ·
    refine ⟨293210885818143367582715549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195473923878762245055143699 293210885818143367582715549)
    ·
      refine ⟨109954082181803762843518331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293210885818143367582715549 109954082181803762843518331)
      ·
        refine ⟨164931123272705644265277497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109954082181803762843518331 164931123272705644265277497)
        ·
          refine ⟨123698342454529233198958123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164931123272705644265277497 123698342454529233198958123)
          ·
            refine ⟨185547513681793849798437185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123698342454529233198958123 185547513681793849798437185)
            ·
              refine ⟨139160635261345387348827889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185547513681793849798437185 139160635261345387348827889)
              ·
                refine ⟨104370476446009040511620917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139160635261345387348827889 104370476446009040511620917)
                ·
                  refine ⟨9784732166813347547964461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104370476446009040511620917 9784732166813347547964461)
                  ·
                    refine ⟨3669274562555005330486673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9784732166813347547964461 3669274562555005330486673)
                    ·
                      refine ⟨2751955921916253997865005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3669274562555005330486673 2751955921916253997865005)
                      ·
                        rfl

theorem cell23_5359415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 3, 2].length) (baseStart_5359415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359415 prefixEnd_5359415 := by exact prefixLift 5359415
  have htrace : WordTrace (prefixWord ++ tailWord_5359415) baseStart_5359415 baseEnd_5359415 := by
    simpa [prefixWord, tailWord_5359415, baseEnd_5359415] using wordTrace_append hprefix tailTrace_5359415
  have hstable : (prefixWord ++ tailWord_5359415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359415).length < 2 ^ (prefixWord ++ tailWord_5359415).sum := by decide
  have hdescent : baseEnd_5359415 < baseStart_5359415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359496 : List Nat := [2, 1, 3, 3, 3, 1, 1, 3, 2, 2, 2]
def baseStart_5359496 : Nat := 118140960795 + 5359496 * 2 ^ 59
def prefixEnd_5359496 : Nat := 4983230072969 + 3 ^ 40 * 5359496 * 2
def baseEnd_5359496 : Nat := 2751997513849268180952133

theorem tailTrace_5359496 : CollatzResearch.WordTrace tailWord_5359496 prefixEnd_5359496 2751997513849268180952133 := by
  unfold tailWord_5359496
  simp only [CollatzResearch.WordTrace]
  refine ⟨97738439095734397944421171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130317918794312530592561561 97738439095734397944421171)
  ·
    refine ⟨146607658643601596916631757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97738439095734397944421171 146607658643601596916631757)
    ·
      refine ⟨54977871991350598843736909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146607658643601596916631757 54977871991350598843736909)
      ·
        refine ⟨20616701996756474566401341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54977871991350598843736909 20616701996756474566401341)
        ·
          refine ⟨7731263248783677962400503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20616701996756474566401341 7731263248783677962400503)
          ·
            refine ⟨11596894873175516943600755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7731263248783677962400503 11596894873175516943600755)
            ·
              refine ⟨17395342309763275415401133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11596894873175516943600755 17395342309763275415401133)
              ·
                refine ⟨6523253366161228280775425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17395342309763275415401133 6523253366161228280775425)
                ·
                  refine ⟨4892440024620921210581569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6523253366161228280775425 4892440024620921210581569)
                  ·
                    refine ⟨3669330018465690907936177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4892440024620921210581569 3669330018465690907936177)
                    ·
                      refine ⟨2751997513849268180952133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3669330018465690907936177 2751997513849268180952133)
                      ·
                        rfl

theorem cell23_5359496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_5359496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359496 prefixEnd_5359496 := by exact prefixLift 5359496
  have htrace : WordTrace (prefixWord ++ tailWord_5359496) baseStart_5359496 baseEnd_5359496 := by
    simpa [prefixWord, tailWord_5359496, baseEnd_5359496] using wordTrace_append hprefix tailTrace_5359496
  have hstable : (prefixWord ++ tailWord_5359496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359496).length < 2 ^ (prefixWord ++ tailWord_5359496).sum := by decide
  have hdescent : baseEnd_5359496 < baseStart_5359496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359535 : List Nat := [1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 4]
def baseStart_5359535 : Nat := 118140960795 + 5359535 * 2 ^ 59
def prefixEnd_5359535 : Nat := 4983230072969 + 3 ^ 40 * 5359535 * 2
def baseEnd_5359535 : Nat := 2752017539594793528364453

theorem tailTrace_5359535 : CollatzResearch.WordTrace tailWord_5359535 prefixEnd_5359535 2752017539594793528364453 := by
  unfold tailWord_5359535
  simp only [CollatzResearch.WordTrace]
  refine ⟨195478300638327505549512059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130318867092218337033008039 195478300638327505549512059)
  ·
    refine ⟨293217450957491258324268089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195478300638327505549512059 293217450957491258324268089)
    ·
      refine ⟨219913088218118443743201067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293217450957491258324268089 219913088218118443743201067)
      ·
        refine ⟨329869632327177665614801601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219913088218118443743201067 329869632327177665614801601)
        ·
          refine ⟨247402224245383249211101201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329869632327177665614801601 247402224245383249211101201)
          ·
            refine ⟨185551668184037436908325901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247402224245383249211101201 185551668184037436908325901)
            ·
              refine ⟨69581875569014038840622213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185551668184037436908325901 69581875569014038840622213)
              ·
                refine ⟨13046601669190132282616665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69581875569014038840622213 13046601669190132282616665)
                ·
                  refine ⟨9784951251892599211962499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13046601669190132282616665 9784951251892599211962499)
                  ·
                    refine ⟨14677426877838898817943749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9784951251892599211962499 14677426877838898817943749)
                    ·
                      refine ⟨2752017539594793528364453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14677426877838898817943749 2752017539594793528364453)
                      ·
                        rfl

theorem cell23_5359535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 4].length) (baseStart_5359535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359535 prefixEnd_5359535 := by exact prefixLift 5359535
  have htrace : WordTrace (prefixWord ++ tailWord_5359535) baseStart_5359535 baseEnd_5359535 := by
    simpa [prefixWord, tailWord_5359535, baseEnd_5359535] using wordTrace_append hprefix tailTrace_5359535
  have hstable : (prefixWord ++ tailWord_5359535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359535).length < 2 ^ (prefixWord ++ tailWord_5359535).sum := by decide
  have hdescent : baseEnd_5359535 < baseStart_5359535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359552 : List Nat := [2, 1, 1, 2, 3, 2, 3, 1, 2, 4, 2]
def baseStart_5359552 : Nat := 118140960795 + 5359552 * 2 ^ 59
def prefixEnd_5359552 : Nat := 4983230072969 + 3 ^ 40 * 5359552 * 2
def baseEnd_5359552 : Nat := 2752026268765919961851875

theorem tailTrace_5359552 : CollatzResearch.WordTrace tailWord_5359552 prefixEnd_5359552 2752026268765919961851875 := by
  unfold tailWord_5359552
  simp only [CollatzResearch.WordTrace]
  refine ⟨97739460339632958726440455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130319280452843944968587273 97739460339632958726440455)
  ·
    refine ⟨146609190509449438089660683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97739460339632958726440455 146609190509449438089660683)
    ·
      refine ⟨219913785764174157134491025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146609190509449438089660683 219913785764174157134491025)
      ·
        refine ⟨164935339323130617850868269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219913785764174157134491025 164935339323130617850868269)
        ·
          refine ⟨61850752246173981694075601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164935339323130617850868269 61850752246173981694075601)
          ·
            refine ⟨46388064184630486270556701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61850752246173981694075601 46388064184630486270556701)
            ·
              refine ⟨17395524069236432351458763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46388064184630486270556701 17395524069236432351458763)
              ·
                refine ⟨26093286103854648527188145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17395524069236432351458763 26093286103854648527188145)
                ·
                  refine ⟨19569964577890986395391109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26093286103854648527188145 19569964577890986395391109)
                  ·
                    refine ⟨3669368358354559949135833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19569964577890986395391109 3669368358354559949135833)
                    ·
                      refine ⟨2752026268765919961851875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3669368358354559949135833 2752026268765919961851875)
                      ·
                        rfl

theorem cell23_5359552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 2, 4, 2].length) (baseStart_5359552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359552 prefixEnd_5359552 := by exact prefixLift 5359552
  have htrace : WordTrace (prefixWord ++ tailWord_5359552) baseStart_5359552 baseEnd_5359552 := by
    simpa [prefixWord, tailWord_5359552, baseEnd_5359552] using wordTrace_append hprefix tailTrace_5359552
  have hstable : (prefixWord ++ tailWord_5359552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359552).length < 2 ^ (prefixWord ++ tailWord_5359552).sum := by decide
  have hdescent : baseEnd_5359552 < baseStart_5359552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359572 : List Nat := [2, 4, 1, 2, 1, 1, 3, 1, 1, 4, 3]
def baseStart_5359572 : Nat := 118140960795 + 5359572 * 2 ^ 59
def prefixEnd_5359572 : Nat := 4983230072969 + 3 ^ 40 * 5359572 * 2
def baseEnd_5359572 : Nat := 2752036538379009883601783

theorem tailTrace_5359572 : CollatzResearch.WordTrace tailWord_5359572 prefixEnd_5359572 2752036538379009883601783 := by
  unfold tailWord_5359572
  simp only [CollatzResearch.WordTrace]
  refine ⟨97739825069596730434304485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130319766759462307245739313 97739825069596730434304485)
  ·
    refine ⟨18326217200549386956432091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97739825069596730434304485 18326217200549386956432091)
    ·
      refine ⟨27489325800824080434648137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18326217200549386956432091 27489325800824080434648137)
      ·
        refine ⟨20616994350618060325986103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27489325800824080434648137 20616994350618060325986103)
        ·
          refine ⟨30925491525927090488979155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20616994350618060325986103 30925491525927090488979155)
          ·
            refine ⟨46388237288890635733468733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30925491525927090488979155 46388237288890635733468733)
            ·
              refine ⟨17395588983333988400050775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46388237288890635733468733 17395588983333988400050775)
              ·
                refine ⟨26093383475000982600076163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17395588983333988400050775 26093383475000982600076163)
                ·
                  refine ⟨39140075212501473900114245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26093383475000982600076163 39140075212501473900114245)
                  ·
                    refine ⟨7338764102344026356271421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39140075212501473900114245 7338764102344026356271421)
                    ·
                      refine ⟨2752036538379009883601783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7338764102344026356271421 2752036538379009883601783)
                      ·
                        rfl

theorem cell23_5359572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_5359572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359572 prefixEnd_5359572 := by exact prefixLift 5359572
  have htrace : WordTrace (prefixWord ++ tailWord_5359572) baseStart_5359572 baseEnd_5359572 := by
    simpa [prefixWord, tailWord_5359572, baseEnd_5359572] using wordTrace_append hprefix tailTrace_5359572
  have hstable : (prefixWord ++ tailWord_5359572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359572).length < 2 ^ (prefixWord ++ tailWord_5359572).sum := by decide
  have hdescent : baseEnd_5359572 < baseStart_5359572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359612 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 3, 5, 2]
def baseStart_5359612 : Nat := 118140960795 + 5359612 * 2 ^ 59
def prefixEnd_5359612 : Nat := 4983230072969 + 3 ^ 40 * 5359612 * 2
def baseEnd_5359612 : Nat := 2752057077605189727101599

theorem tailTrace_5359612 : CollatzResearch.WordTrace tailWord_5359612 prefixEnd_5359612 2752057077605189727101599 := by
  unfold tailWord_5359612
  simp only [CollatzResearch.WordTrace]
  refine ⟨97740554529524273850032545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130320739372699031800043393 97740554529524273850032545)
  ·
    refine ⟨73305415897143205387524409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97740554529524273850032545 73305415897143205387524409)
    ·
      refine ⟨54979061922857404040643307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73305415897143205387524409 54979061922857404040643307)
      ·
        refine ⟨82468592884286106060964961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54979061922857404040643307 82468592884286106060964961)
        ·
          refine ⟨61851444663214579545723721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82468592884286106060964961 61851444663214579545723721)
          ·
            refine ⟨46388583497410934659292791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61851444663214579545723721 46388583497410934659292791)
            ·
              refine ⟨69582875246116401988939187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46388583497410934659292791 69582875246116401988939187)
              ·
                refine ⟨104374312869174602983408781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69582875246116401988939187 104374312869174602983408781)
                ·
                  refine ⟨39140367325940476118778293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104374312869174602983408781 39140367325940476118778293)
                  ·
                    refine ⟨3669409436806919636135465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39140367325940476118778293 3669409436806919636135465)
                    ·
                      refine ⟨2752057077605189727101599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3669409436806919636135465 2752057077605189727101599)
                      ·
                        rfl

theorem cell23_5359612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 3, 5, 2].length) (baseStart_5359612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359612 prefixEnd_5359612 := by exact prefixLift 5359612
  have htrace : WordTrace (prefixWord ++ tailWord_5359612) baseStart_5359612 baseEnd_5359612 := by
    simpa [prefixWord, tailWord_5359612, baseEnd_5359612] using wordTrace_append hprefix tailTrace_5359612
  have hstable : (prefixWord ++ tailWord_5359612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359612).length < 2 ^ (prefixWord ++ tailWord_5359612).sum := by decide
  have hdescent : baseEnd_5359612 < baseStart_5359612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359635 : List Nat := [1, 1, 1, 2, 1, 4, 2, 4, 1, 6]
def baseStart_5359635 : Nat := 118140960795 + 5359635 * 2 ^ 59
def prefixEnd_5359635 : Nat := 4983230072969 + 3 ^ 40 * 5359635 * 2
def baseEnd_5359635 : Nat := 917356295886747712371331

theorem tailTrace_5359635 : CollatzResearch.WordTrace tailWord_5359635 prefixEnd_5359635 917356295886747712371331 := by
  unfold tailWord_5359635
  simp only [CollatzResearch.WordTrace]
  refine ⟨195481947937965222628152359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130321298625310148418768239 195481947937965222628152359)
  ·
    refine ⟨293222921906947833942228539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195481947937965222628152359 293222921906947833942228539)
    ·
      refine ⟨439834382860421750913342809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293222921906947833942228539 439834382860421750913342809)
      ·
        refine ⟨329875787145316313185007107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 439834382860421750913342809 329875787145316313185007107)
        ·
          refine ⟨494813680717974469777510661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329875787145316313185007107 494813680717974469777510661)
          ·
            refine ⟨92777565134620213083283249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 494813680717974469777510661 92777565134620213083283249)
            ·
              refine ⟨69583173850965159812462437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92777565134620213083283249 69583173850965159812462437)
              ·
                refine ⟨13046845097055967464836707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69583173850965159812462437 13046845097055967464836707)
                ·
                  refine ⟨19570267645583951197255061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13046845097055967464836707 19570267645583951197255061)
                  ·
                    refine ⟨917356295886747712371331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19570267645583951197255061 917356295886747712371331)
                    ·
                      rfl

theorem cell23_5359635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 6].length) (baseStart_5359635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359635 prefixEnd_5359635 := by exact prefixLift 5359635
  have htrace : WordTrace (prefixWord ++ tailWord_5359635) baseStart_5359635 baseEnd_5359635 := by
    simpa [prefixWord, tailWord_5359635, baseEnd_5359635] using wordTrace_append hprefix tailTrace_5359635
  have hstable : (prefixWord ++ tailWord_5359635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359635).length < 2 ^ (prefixWord ++ tailWord_5359635).sum := by decide
  have hdescent : baseEnd_5359635 < baseStart_5359635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359653 : List Nat := [1, 3, 1, 2, 2, 4, 3, 2, 1, 1, 3]
def baseStart_5359653 : Nat := 118140960795 + 5359653 * 2 ^ 59
def prefixEnd_5359653 : Nat := 4983230072969 + 3 ^ 40 * 5359653 * 2
def baseEnd_5359653 : Nat := 2752078130312024066688911

theorem tailTrace_5359653 : CollatzResearch.WordTrace tailWord_5359653 prefixEnd_5359653 2752078130312024066688911 := by
  unfold tailWord_5359653
  simp only [CollatzResearch.WordTrace]
  refine ⟨195482604451900011702307613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130321736301266674468205075 195482604451900011702307613)
  ·
    refine ⟨73305976669462504388365355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195482604451900011702307613 73305976669462504388365355)
    ·
      refine ⟨109958965004193756582548033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73305976669462504388365355 109958965004193756582548033)
      ·
        refine ⟨82469223753145317436911025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109958965004193756582548033 82469223753145317436911025)
        ·
          refine ⟨61851917814858988077683269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82469223753145317436911025 61851917814858988077683269)
          ·
            refine ⟨11597234590286060264565613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61851917814858988077683269 11597234590286060264565613)
            ·
              refine ⟨4348962971357272599212105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11597234590286060264565613 4348962971357272599212105)
              ·
                refine ⟨3261722228517954449409079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4348962971357272599212105 3261722228517954449409079)
                ·
                  refine ⟨4892583342776931674113619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3261722228517954449409079 4892583342776931674113619)
                  ·
                    refine ⟨7338875014165397511170429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4892583342776931674113619 7338875014165397511170429)
                    ·
                      refine ⟨2752078130312024066688911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7338875014165397511170429 2752078130312024066688911)
                      ·
                        rfl

theorem cell23_5359653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2, 1, 1, 3].length) (baseStart_5359653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359653 prefixEnd_5359653 := by exact prefixLift 5359653
  have htrace : WordTrace (prefixWord ++ tailWord_5359653) baseStart_5359653 baseEnd_5359653 := by
    simpa [prefixWord, tailWord_5359653, baseEnd_5359653] using wordTrace_append hprefix tailTrace_5359653
  have hstable : (prefixWord ++ tailWord_5359653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359653).length < 2 ^ (prefixWord ++ tailWord_5359653).sum := by decide
  have hdescent : baseEnd_5359653 < baseStart_5359653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359659 : List Nat := [1, 1, 1, 1, 2, 1, 4, 5, 3, 2, 2]
def baseStart_5359659 : Nat := 118140960795 + 5359659 * 2 ^ 59
def prefixEnd_5359659 : Nat := 4983230072969 + 3 ^ 40 * 5359659 * 2
def baseEnd_5359659 : Nat := 2752081211195951043213883

theorem tailTrace_5359659 : CollatzResearch.WordTrace tailWord_5359659 prefixEnd_5359659 2752081211195951043213883 := by
  unfold tailWord_5359659
  simp only [CollatzResearch.WordTrace]
  refine ⟨195482823289878274727026031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130321882193252183151350687 195482823289878274727026031)
  ·
    refine ⟨293224234934817412090539047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195482823289878274727026031 293224234934817412090539047)
    ·
      refine ⟨439836352402226118135808571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293224234934817412090539047 439836352402226118135808571)
      ·
        refine ⟨659754528603339177203712857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439836352402226118135808571 659754528603339177203712857)
        ·
          refine ⟨494815896452504382902784643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 659754528603339177203712857 494815896452504382902784643)
          ·
            refine ⟨742223844678756574354176965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494815896452504382902784643 742223844678756574354176965)
            ·
              refine ⟨139166970877266857691408181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 742223844678756574354176965 139166970877266857691408181)
              ·
                refine ⟨13046903519743767908569517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139166970877266857691408181 13046903519743767908569517)
                ·
                  refine ⟨4892588819903912965713569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13046903519743767908569517 4892588819903912965713569)
                  ·
                    refine ⟨3669441614927934724285177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4892588819903912965713569 3669441614927934724285177)
                    ·
                      refine ⟨2752081211195951043213883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3669441614927934724285177 2752081211195951043213883)
                      ·
                        rfl

theorem cell23_5359659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3, 2, 2].length) (baseStart_5359659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359659 prefixEnd_5359659 := by exact prefixLift 5359659
  have htrace : WordTrace (prefixWord ++ tailWord_5359659) baseStart_5359659 baseEnd_5359659 := by
    simpa [prefixWord, tailWord_5359659, baseEnd_5359659] using wordTrace_append hprefix tailTrace_5359659
  have hstable : (prefixWord ++ tailWord_5359659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359659).length < 2 ^ (prefixWord ++ tailWord_5359659).sum := by decide
  have hdescent : baseEnd_5359659 < baseStart_5359659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359665 : List Nat := [1, 2, 2, 3, 1, 3, 1, 10]
def baseStart_5359665 : Nat := 118140960795 + 5359665 * 2 ^ 59
def prefixEnd_5359665 : Nat := 4983230072969 + 3 ^ 40 * 5359665 * 2
def baseEnd_5359665 : Nat := 101929047854810297027365

theorem tailTrace_5359665 : CollatzResearch.WordTrace tailWord_5359665 prefixEnd_5359665 101929047854810297027365 := by
  unfold tailWord_5359665
  simp only [CollatzResearch.WordTrace]
  refine ⟨195483042127856537751744449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130322028085237691834496299 195483042127856537751744449)
  ·
    refine ⟨146612281595892403313808337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195483042127856537751744449 146612281595892403313808337)
    ·
      refine ⟨109959211196919302485356253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146612281595892403313808337 109959211196919302485356253)
      ·
        refine ⟨41234704198844738432008595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109959211196919302485356253 41234704198844738432008595)
        ·
          refine ⟨61852056298267107648012893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41234704198844738432008595 61852056298267107648012893)
          ·
            refine ⟨23194521111850165368004835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61852056298267107648012893 23194521111850165368004835)
            ·
              refine ⟨34791781667775248052007253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23194521111850165368004835 34791781667775248052007253)
              ·
                refine ⟨101929047854810297027365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34791781667775248052007253 101929047854810297027365)
                ·
                  rfl

theorem cell23_5359665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 10].length) (baseStart_5359665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359665 prefixEnd_5359665 := by exact prefixLift 5359665
  have htrace : WordTrace (prefixWord ++ tailWord_5359665) baseStart_5359665 baseEnd_5359665 := by
    simpa [prefixWord, tailWord_5359665, baseEnd_5359665] using wordTrace_append hprefix tailTrace_5359665
  have hstable : (prefixWord ++ tailWord_5359665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359665).length < 2 ^ (prefixWord ++ tailWord_5359665).sum := by decide
  have hdescent : baseEnd_5359665 < baseStart_5359665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359679 : List Nat := [1, 1, 2, 2, 3, 1, 5, 2, 1, 2, 3]
def baseStart_5359679 : Nat := 118140960795 + 5359679 * 2 ^ 59
def prefixEnd_5359679 : Nat := 4983230072969 + 3 ^ 40 * 5359679 * 2
def baseEnd_5359679 : Nat := 2752091480809040964963791

theorem tailTrace_5359679 : CollatzResearch.WordTrace tailWord_5359679 prefixEnd_5359679 2752091480809040964963791 := by
  unfold tailWord_5359679
  simp only [CollatzResearch.WordTrace]
  refine ⟨195483552749805818142754091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130322368499870545428502727 195483552749805818142754091)
  ·
    refine ⟨293225329124708727214131137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195483552749805818142754091 293225329124708727214131137)
    ·
      refine ⟨219918996843531545410598353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293225329124708727214131137 219918996843531545410598353)
      ·
        refine ⟨164939247632648659057948765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219918996843531545410598353 164939247632648659057948765)
        ·
          refine ⟨61852217862243247146730787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164939247632648659057948765 61852217862243247146730787)
          ·
            refine ⟨92778326793364870720096181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61852217862243247146730787 92778326793364870720096181)
            ·
              refine ⟨8697968136877956630009017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92778326793364870720096181 8697968136877956630009017)
              ·
                refine ⟨6523476102658467472506763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8697968136877956630009017 6523476102658467472506763)
                ·
                  refine ⟨9785214153987701208760145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6523476102658467472506763 9785214153987701208760145)
                  ·
                    refine ⟨7338910615490775906570109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9785214153987701208760145 7338910615490775906570109)
                    ·
                      refine ⟨2752091480809040964963791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7338910615490775906570109 2752091480809040964963791)
                      ·
                        rfl

theorem cell23_5359679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 2, 3].length) (baseStart_5359679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359679 prefixEnd_5359679 := by exact prefixLift 5359679
  have htrace : WordTrace (prefixWord ++ tailWord_5359679) baseStart_5359679 baseEnd_5359679 := by
    simpa [prefixWord, tailWord_5359679, baseEnd_5359679] using wordTrace_append hprefix tailTrace_5359679
  have hstable : (prefixWord ++ tailWord_5359679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359679).length < 2 ^ (prefixWord ++ tailWord_5359679).sum := by decide
  have hdescent : baseEnd_5359679 < baseStart_5359679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359692 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 3, 3, 3]
def baseStart_5359692 : Nat := 118140960795 + 5359692 * 2 ^ 59
def prefixEnd_5359692 : Nat := 4983230072969 + 3 ^ 40 * 5359692 * 2
def baseEnd_5359692 : Nat := 2752098156057549414101231

theorem tailTrace_5359692 : CollatzResearch.WordTrace tailWord_5359692 prefixEnd_5359692 2752098156057549414101231 := by
  unfold tailWord_5359692
  simp only [CollatzResearch.WordTrace]
  refine ⟨97742013449379360681488665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130322684599172480908651553 97742013449379360681488665)
  ·
    refine ⟨73306510087034520511116499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97742013449379360681488665 73306510087034520511116499)
    ·
      refine ⟨109959765130551780766674749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73306510087034520511116499 109959765130551780766674749)
      ·
        refine ⟨41234911923956917787503031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109959765130551780766674749 41234911923956917787503031)
        ·
          refine ⟨61852367885935376681254547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41234911923956917787503031 61852367885935376681254547)
          ·
            refine ⟨92778551828903065021881821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61852367885935376681254547 92778551828903065021881821)
            ·
              refine ⟨34791956935838649383205683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92778551828903065021881821 34791956935838649383205683)
              ·
                refine ⟨52187935403757974074808525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34791956935838649383205683 52187935403757974074808525)
                ·
                  refine ⟨19570475776409240278053197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52187935403757974074808525 19570475776409240278053197)
                  ·
                    refine ⟨7338928416153465104269949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19570475776409240278053197 7338928416153465104269949)
                    ·
                      refine ⟨2752098156057549414101231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7338928416153465104269949 2752098156057549414101231)
                      ·
                        rfl

theorem cell23_5359692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_5359692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359692 prefixEnd_5359692 := by exact prefixLift 5359692
  have htrace : WordTrace (prefixWord ++ tailWord_5359692) baseStart_5359692 baseEnd_5359692 := by
    simpa [prefixWord, tailWord_5359692, baseEnd_5359692] using wordTrace_append hprefix tailTrace_5359692
  have hstable : (prefixWord ++ tailWord_5359692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359692).length < 2 ^ (prefixWord ++ tailWord_5359692).sum := by decide
  have hdescent : baseEnd_5359692 < baseStart_5359692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359719 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 5, 3, 2]
def baseStart_5359719 : Nat := 118140960795 + 5359719 * 2 ^ 59
def prefixEnd_5359719 : Nat := 4983230072969 + 3 ^ 40 * 5359719 * 2
def baseEnd_5359719 : Nat := 2752112020035220808463607

theorem tailTrace_5359719 : CollatzResearch.WordTrace tailWord_5359719 prefixEnd_5359719 2752112020035220808463607 := by
  unfold tailWord_5359719
  simp only [CollatzResearch.WordTrace]
  refine ⟨195485011669660904974210211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130323341113107269982806807 195485011669660904974210211)
  ·
    refine ⟨293227517504491357461315317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195485011669660904974210211 293227517504491357461315317)
    ·
      refine ⟨27490079766046064761998311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 293227517504491357461315317 27490079766046064761998311)
      ·
        refine ⟨41235119649069097142997467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27490079766046064761998311 41235119649069097142997467)
        ·
          refine ⟨61852679473603645714496201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41235119649069097142997467 61852679473603645714496201)
          ·
            refine ⟨46389509605202734285872151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61852679473603645714496201 46389509605202734285872151)
            ·
              refine ⟨69584264407804101428808227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46389509605202734285872151 69584264407804101428808227)
              ·
                refine ⟨104376396611706152143212341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69584264407804101428808227 104376396611706152143212341)
                ·
                  refine ⟨9785287182347451763426157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104376396611706152143212341 9785287182347451763426157)
                  ·
                    refine ⟨3669482693380294411284809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9785287182347451763426157 3669482693380294411284809)
                    ·
                      refine ⟨2752112020035220808463607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3669482693380294411284809 2752112020035220808463607)
                      ·
                        rfl

theorem cell23_5359719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_5359719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359719 prefixEnd_5359719 := by exact prefixLift 5359719
  have htrace : WordTrace (prefixWord ++ tailWord_5359719) baseStart_5359719 baseEnd_5359719 := by
    simpa [prefixWord, tailWord_5359719, baseEnd_5359719] using wordTrace_append hprefix tailTrace_5359719
  have hstable : (prefixWord ++ tailWord_5359719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359719).length < 2 ^ (prefixWord ++ tailWord_5359719).sum := by decide
  have hdescent : baseEnd_5359719 < baseStart_5359719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359726 : List Nat := [4, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3]
def baseStart_5359726 : Nat := 118140960795 + 5359726 * 2 ^ 59
def prefixEnd_5359726 : Nat := 4983230072969 + 3 ^ 40 * 5359726 * 2
def baseEnd_5359726 : Nat := 2752115614399802281076075

theorem tailTrace_5359726 : CollatzResearch.WordTrace tailWord_5359726 prefixEnd_5359726 2752115614399802281076075 := by
  unfold tailWord_5359726
  simp only [CollatzResearch.WordTrace]
  refine ⟨24435658372579443146214379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130323511320423696779810021 24435658372579443146214379)
  ·
    refine ⟨36653487558869164719321569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24435658372579443146214379 36653487558869164719321569)
    ·
      refine ⟨27490115669151873539491177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36653487558869164719321569 27490115669151873539491177)
      ·
        refine ⟨20617586751863905154618383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27490115669151873539491177 20617586751863905154618383)
        ·
          refine ⟨30926380127795857731927575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20617586751863905154618383 30926380127795857731927575)
          ·
            refine ⟨46389570191693786597891363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30926380127795857731927575 46389570191693786597891363)
            ·
              refine ⟨69584355287540679896837045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46389570191693786597891363 69584355287540679896837045)
              ·
                refine ⟨6523533308206938740328473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69584355287540679896837045 6523533308206938740328473)
                ·
                  refine ⟨4892649981155204055246355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6523533308206938740328473 4892649981155204055246355)
                  ·
                    refine ⟨7338974971732806082869533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4892649981155204055246355 7338974971732806082869533)
                    ·
                      refine ⟨2752115614399802281076075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7338974971732806082869533 2752115614399802281076075)
                      ·
                        rfl

theorem cell23_5359726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_5359726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359726 prefixEnd_5359726 := by exact prefixLift 5359726
  have htrace : WordTrace (prefixWord ++ tailWord_5359726) baseStart_5359726 baseEnd_5359726 := by
    simpa [prefixWord, tailWord_5359726, baseEnd_5359726] using wordTrace_append hprefix tailTrace_5359726
  have hstable : (prefixWord ++ tailWord_5359726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359726).length < 2 ^ (prefixWord ++ tailWord_5359726).sum := by decide
  have hdescent : baseEnd_5359726 < baseStart_5359726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359789 : List Nat := [1, 5, 2, 1, 2, 1, 2, 2, 7]
def baseStart_5359789 : Nat := 118140960795 + 5359789 * 2 ^ 59
def prefixEnd_5359789 : Nat := 4983230072969 + 3 ^ 40 * 5359789 * 2
def baseEnd_5359789 : Nat := 305794218186781726065365

theorem tailTrace_5359789 : CollatzResearch.WordTrace tailWord_5359789 prefixEnd_5359789 305794218186781726065365 := by
  unfold tailWord_5359789
  simp only [CollatzResearch.WordTrace]
  refine ⟨195487564779407306929258421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130325043186271537952838947 195487564779407306929258421)
  ·
    refine ⟨18326959198069435024617977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 195487564779407306929258421 18326959198069435024617977)
    ·
      refine ⟨13745219398552076268463483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18326959198069435024617977 13745219398552076268463483)
      ·
        refine ⟨20617829097828114402695225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13745219398552076268463483 20617829097828114402695225)
        ·
          refine ⟨15463371823371085802021419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20617829097828114402695225 15463371823371085802021419)
          ·
            refine ⟨23195057735056628703032129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15463371823371085802021419 23195057735056628703032129)
            ·
              refine ⟨17396293301292471527274097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23195057735056628703032129 17396293301292471527274097)
              ·
                refine ⟨13047219975969353645455573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17396293301292471527274097 13047219975969353645455573)
                ·
                  refine ⟨305794218186781726065365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13047219975969353645455573 305794218186781726065365)
                  ·
                    rfl

theorem cell23_5359789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_5359789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359789 prefixEnd_5359789 := by exact prefixLift 5359789
  have htrace : WordTrace (prefixWord ++ tailWord_5359789) baseStart_5359789 baseEnd_5359789 := by
    simpa [prefixWord, tailWord_5359789, baseEnd_5359789] using wordTrace_append hprefix tailTrace_5359789
  have hstable : (prefixWord ++ tailWord_5359789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359789).length < 2 ^ (prefixWord ++ tailWord_5359789).sum := by decide
  have hdescent : baseEnd_5359789 < baseStart_5359789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359802 : List Nat := [3, 1, 1, 1, 2, 2, 4, 1, 1, 7]
def baseStart_5359802 : Nat := 118140960795 + 5359802 * 2 ^ 59
def prefixEnd_5359802 : Nat := 4983230072969 + 3 ^ 40 * 5359802 * 2
def baseEnd_5359802 : Nat := 917384879643181327908575

theorem tailTrace_5359802 : CollatzResearch.WordTrace tailWord_5359802 prefixEnd_5359802 917384879643181327908575 := by
  unfold tailWord_5359802
  simp only [CollatzResearch.WordTrace]
  refine ⟨48872009732090052537370415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130325359285573473432987773 48872009732090052537370415)
  ·
    refine ⟨73308014598135078806055623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48872009732090052537370415 73308014598135078806055623)
    ·
      refine ⟨109962021897202618209083435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73308014598135078806055623 109962021897202618209083435)
      ·
        refine ⟨164943032845803927313625153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109962021897202618209083435 164943032845803927313625153)
        ·
          refine ⟨123707274634352945485218865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164943032845803927313625153 123707274634352945485218865)
          ·
            refine ⟨92780455975764709113914149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123707274634352945485218865 92780455975764709113914149)
            ·
              refine ⟨17396335495455882958858903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92780455975764709113914149 17396335495455882958858903)
              ·
                refine ⟨26094503243183824438288355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17396335495455882958858903 26094503243183824438288355)
                ·
                  refine ⟨39141754864775736657432533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26094503243183824438288355 39141754864775736657432533)
                  ·
                    refine ⟨917384879643181327908575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39141754864775736657432533 917384879643181327908575)
                    ·
                      rfl

theorem cell23_5359802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 1, 7].length) (baseStart_5359802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359802 prefixEnd_5359802 := by exact prefixLift 5359802
  have htrace : WordTrace (prefixWord ++ tailWord_5359802) baseStart_5359802 baseEnd_5359802 := by
    simpa [prefixWord, tailWord_5359802, baseEnd_5359802] using wordTrace_append hprefix tailTrace_5359802
  have hstable : (prefixWord ++ tailWord_5359802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359802).length < 2 ^ (prefixWord ++ tailWord_5359802).sum := by decide
  have hdescent : baseEnd_5359802 < baseStart_5359802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359839 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 1, 6, 2]
def baseStart_5359839 : Nat := 118140960795 + 5359839 * 2 ^ 59
def prefixEnd_5359839 : Nat := 4983230072969 + 3 ^ 40 * 5359839 * 2
def baseEnd_5359839 : Nat := 2752173637713760338963055

theorem tailTrace_5359839 : CollatzResearch.WordTrace tailWord_5359839 prefixEnd_5359839 2752173637713760338963055 := by
  unfold tailWord_5359839
  simp only [CollatzResearch.WordTrace]
  refine ⟨195489388429226165468578571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130326258952817443645719047 195489388429226165468578571)
  ·
    refine ⟨293234082643839248202867857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195489388429226165468578571 293234082643839248202867857)
    ·
      refine ⟨219925561982879436152150893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293234082643839248202867857 219925561982879436152150893)
      ·
        refine ⟨82472085743579788557056585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219925561982879436152150893 82472085743579788557056585)
        ·
          refine ⟨61854064307684841417792439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82472085743579788557056585 61854064307684841417792439)
          ·
            refine ⟨92781096461527262126688659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61854064307684841417792439 92781096461527262126688659)
            ·
              refine ⟨139171644692290893190032989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92781096461527262126688659 139171644692290893190032989)
              ·
                refine ⟨52189366759609084946262371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139171644692290893190032989 52189366759609084946262371)
                ·
                  refine ⟨78284050139413627419393557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52189366759609084946262371 78284050139413627419393557)
                  ·
                    refine ⟨3669564850285013785284073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78284050139413627419393557 3669564850285013785284073)
                    ·
                      refine ⟨2752173637713760338963055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3669564850285013785284073 2752173637713760338963055)
                      ·
                        rfl

theorem cell23_5359839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 6, 2].length) (baseStart_5359839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359839 prefixEnd_5359839 := by exact prefixLift 5359839
  have htrace : WordTrace (prefixWord ++ tailWord_5359839) baseStart_5359839 baseEnd_5359839 := by
    simpa [prefixWord, tailWord_5359839, baseEnd_5359839] using wordTrace_append hprefix tailTrace_5359839
  have hstable : (prefixWord ++ tailWord_5359839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359839).length < 2 ^ (prefixWord ++ tailWord_5359839).sum := by decide
  have hdescent : baseEnd_5359839 < baseStart_5359839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359917 : List Nat := [1, 5, 3, 1, 2, 1, 2, 3, 1, 4]
def baseStart_5359917 : Nat := 118140960795 + 5359917 * 2 ^ 59
def prefixEnd_5359917 : Nat := 4983230072969 + 3 ^ 40 * 5359917 * 2
def baseEnd_5359917 : Nat := 917404563068270344595899

theorem tailTrace_5359917 : CollatzResearch.WordTrace tailWord_5359917 prefixEnd_5359917 917404563068270344595899 := by
  unfold tailWord_5359917
  simp only [CollatzResearch.WordTrace]
  refine ⟨195492233322943584789918005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130328155548629056526612003 195492233322943584789918005)
  ·
    refine ⟨18327396874025961074054813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 195492233322943584789918005 18327396874025961074054813)
    ·
      refine ⟨6872773827759735402770555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18327396874025961074054813 6872773827759735402770555)
      ·
        refine ⟨10309160741639603104155833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6872773827759735402770555 10309160741639603104155833)
        ·
          refine ⟨7731870556229702328116875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10309160741639603104155833 7731870556229702328116875)
          ·
            refine ⟨11597805834344553492175313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7731870556229702328116875 11597805834344553492175313)
            ·
              refine ⟨8698354375758415119131485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11597805834344553492175313 8698354375758415119131485)
              ·
                refine ⟨3261882890909405669674307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8698354375758415119131485 3261882890909405669674307)
                ·
                  refine ⟨4892824336364108504511461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3261882890909405669674307 4892824336364108504511461)
                  ·
                    refine ⟨917404563068270344595899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4892824336364108504511461 917404563068270344595899)
                    ·
                      rfl

theorem cell23_5359917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_5359917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359917 prefixEnd_5359917 := by exact prefixLift 5359917
  have htrace : WordTrace (prefixWord ++ tailWord_5359917) baseStart_5359917 baseEnd_5359917 := by
    simpa [prefixWord, tailWord_5359917, baseEnd_5359917] using wordTrace_append hprefix tailTrace_5359917
  have hstable : (prefixWord ++ tailWord_5359917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359917).length < 2 ^ (prefixWord ++ tailWord_5359917).sum := by decide
  have hdescent : baseEnd_5359917 < baseStart_5359917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359956 : List Nat := [2, 4, 1, 1, 2, 2, 3, 1, 1, 6]
def baseStart_5359956 : Nat := 118140960795 + 5359956 * 2 ^ 59
def prefixEnd_5359956 : Nat := 4983230072969 + 3 ^ 40 * 5359956 * 2
def baseEnd_5359956 : Nat := 917411238316778793733339

theorem tailTrace_5359956 : CollatzResearch.WordTrace tailWord_5359956 prefixEnd_5359956 917411238316778793733339 := by
  unfold tailWord_5359956
  simp only [CollatzResearch.WordTrace]
  refine ⟨97746827884901147225293861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130329103846534862967058481 97746827884901147225293861)
  ·
    refine ⟨18327530228418965104742599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97746827884901147225293861 18327530228418965104742599)
    ·
      refine ⟨27491295342628447657113899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18327530228418965104742599 27491295342628447657113899)
      ·
        refine ⟨41236943013942671485670849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27491295342628447657113899 41236943013942671485670849)
        ·
          refine ⟨30927707260457003614253137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41236943013942671485670849 30927707260457003614253137)
          ·
            refine ⟨23195780445342752710689853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30927707260457003614253137 23195780445342752710689853)
            ·
              refine ⟨8698417667003532266508695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23195780445342752710689853 8698417667003532266508695)
              ·
                refine ⟨13047626500505298399763043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8698417667003532266508695 13047626500505298399763043)
                ·
                  refine ⟨19571439750757947599644565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13047626500505298399763043 19571439750757947599644565)
                  ·
                    refine ⟨917411238316778793733339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19571439750757947599644565 917411238316778793733339)
                    ·
                      rfl

theorem cell23_5359956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_5359956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359956 prefixEnd_5359956 := by exact prefixLift 5359956
  have htrace : WordTrace (prefixWord ++ tailWord_5359956) baseStart_5359956 baseEnd_5359956 := by
    simpa [prefixWord, tailWord_5359956, baseEnd_5359956] using wordTrace_append hprefix tailTrace_5359956
  have hstable : (prefixWord ++ tailWord_5359956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359956).length < 2 ^ (prefixWord ++ tailWord_5359956).sum := by decide
  have hdescent : baseEnd_5359956 < baseStart_5359956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5359959 : List Nat := [1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 6]
def baseStart_5359959 : Nat := 118140960795 + 5359959 * 2 ^ 59
def prefixEnd_5359959 : Nat := 4983230072969 + 3 ^ 40 * 5359959 * 2
def baseEnd_5359959 : Nat := 2752235255392299869462503

theorem tailTrace_5359959 : CollatzResearch.WordTrace tailWord_5359959 prefixEnd_5359959 2752235255392299869462503 := by
  unfold tailWord_5359959
  simp only [CollatzResearch.WordTrace]
  refine ⟨195493765188791425962946931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130329176792527617308631287 195493765188791425962946931)
  ·
    refine ⟨293240647783187138944420397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195493765188791425962946931 293240647783187138944420397)
    ·
      refine ⟨109965242918695177104157649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293240647783187138944420397 109965242918695177104157649)
      ·
        refine ⟨82473932189021382828118237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109965242918695177104157649 82473932189021382828118237)
        ·
          refine ⟨30927724570883018560544339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82473932189021382828118237 30927724570883018560544339)
          ·
            refine ⟨46391586856324527840816509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30927724570883018560544339 46391586856324527840816509)
            ·
              refine ⟨17396845071121697940306191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46391586856324527840816509 17396845071121697940306191)
              ·
                refine ⟨26095267606682546910459287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17396845071121697940306191 26095267606682546910459287)
                ·
                  refine ⟨39142901410023820365688931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26095267606682546910459287 39142901410023820365688931)
                  ·
                    refine ⟨58714352115035730548533397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39142901410023820365688931 58714352115035730548533397)
                    ·
                      refine ⟨2752235255392299869462503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58714352115035730548533397 2752235255392299869462503)
                      ·
                        rfl

theorem cell23_5359959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_5359959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5359959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5359959 prefixEnd_5359959 := by exact prefixLift 5359959
  have htrace : WordTrace (prefixWord ++ tailWord_5359959) baseStart_5359959 baseEnd_5359959 := by
    simpa [prefixWord, tailWord_5359959, baseEnd_5359959] using wordTrace_append hprefix tailTrace_5359959
  have hstable : (prefixWord ++ tailWord_5359959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5359959).length < 2 ^ (prefixWord ++ tailWord_5359959).sum := by decide
  have hdescent : baseEnd_5359959 < baseStart_5359959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5359959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360030 : List Nat := [4, 3, 1, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_5360030 : Nat := 118140960795 + 5360030 * 2 ^ 59
def prefixEnd_5360030 : Nat := 4983230072969 + 3 ^ 40 * 5360030 * 2
def baseEnd_5360030 : Nat := 2752271712518769091674677

theorem tailTrace_5360030 : CollatzResearch.WordTrace tailWord_5360030 prefixEnd_5360030 2752271712518769091674677 := by
  unfold tailWord_5360030
  simp only [CollatzResearch.WordTrace]
  refine ⟨24437044346441775636097693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130330903181022803392521029 24437044346441775636097693)
  ·
    refine ⟨9163891629915665863536635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24437044346441775636097693 9163891629915665863536635)
    ·
      refine ⟨13745837444873498795304953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9163891629915665863536635 13745837444873498795304953)
      ·
        refine ⟨10309378083655124096478715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13745837444873498795304953 10309378083655124096478715)
        ·
          refine ⟨15464067125482686144718073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10309378083655124096478715 15464067125482686144718073)
          ·
            refine ⟨11598050344112014608538555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15464067125482686144718073 11598050344112014608538555)
            ·
              refine ⟨17397075516168021912807833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11598050344112014608538555 17397075516168021912807833)
              ·
                refine ⟨13047806637126016434605875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17397075516168021912807833 13047806637126016434605875)
                ·
                  refine ⟨19571709955689024651908813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13047806637126016434605875 19571709955689024651908813)
                  ·
                    refine ⟨7339391233383384244465805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19571709955689024651908813 7339391233383384244465805)
                    ·
                      refine ⟨2752271712518769091674677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7339391233383384244465805 2752271712518769091674677)
                      ·
                        rfl

theorem cell23_5360030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_5360030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360030 prefixEnd_5360030 := by exact prefixLift 5360030
  have htrace : WordTrace (prefixWord ++ tailWord_5360030) baseStart_5360030 baseEnd_5360030 := by
    simpa [prefixWord, tailWord_5360030, baseEnd_5360030] using wordTrace_append hprefix tailTrace_5360030
  have hstable : (prefixWord ++ tailWord_5360030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360030).length < 2 ^ (prefixWord ++ tailWord_5360030).sum := by decide
  have hdescent : baseEnd_5360030 < baseStart_5360030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360160 : List Nat := [2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 4]
def baseStart_5360160 : Nat := 118140960795 + 5360160 * 2 ^ 59
def prefixEnd_5360160 : Nat := 4983230072969 + 3 ^ 40 * 5360160 * 2
def baseEnd_5360160 : Nat := 2752338465003853583049079

theorem tailTrace_5360160 : CollatzResearch.WordTrace tailWord_5360160 prefixEnd_5360160 2752338465003853583049079 := by
  unfold tailWord_5360160
  simp only [CollatzResearch.WordTrace]
  refine ⟨97750548130531618645506967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130334064174042158194009289 97750548130531618645506967)
  ·
    refine ⟨146625822195797427968260451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97750548130531618645506967 146625822195797427968260451)
    ·
      refine ⟨219938733293696141952390677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146625822195797427968260451 219938733293696141952390677)
      ·
        refine ⟨10309628123142006654018313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 219938733293696141952390677 10309628123142006654018313)
        ·
          refine ⟨7732221092356504990513735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10309628123142006654018313 7732221092356504990513735)
          ·
            refine ⟨11598331638534757485770603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7732221092356504990513735 11598331638534757485770603)
            ·
              refine ⟨17397497457802136228655905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11598331638534757485770603 17397497457802136228655905)
              ·
                refine ⟨13048123093351602171491929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17397497457802136228655905 13048123093351602171491929)
                ·
                  refine ⟨9786092320013701628618947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13048123093351602171491929 9786092320013701628618947)
                  ·
                    refine ⟨14679138480020552442928421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9786092320013701628618947 14679138480020552442928421)
                    ·
                      refine ⟨2752338465003853583049079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14679138480020552442928421 2752338465003853583049079)
                      ·
                        rfl

theorem cell23_5360160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_5360160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360160 prefixEnd_5360160 := by exact prefixLift 5360160
  have htrace : WordTrace (prefixWord ++ tailWord_5360160) baseStart_5360160 baseEnd_5360160 := by
    simpa [prefixWord, tailWord_5360160, baseEnd_5360160] using wordTrace_append hprefix tailTrace_5360160
  have hstable : (prefixWord ++ tailWord_5360160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360160).length < 2 ^ (prefixWord ++ tailWord_5360160).sum := by decide
  have hdescent : baseEnd_5360160 < baseStart_5360160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360163 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 4, 2, 3]
def baseStart_5360163 : Nat := 118140960795 + 5360163 * 2 ^ 59
def prefixEnd_5360163 : Nat := 4983230072969 + 3 ^ 40 * 5360163 * 2
def baseEnd_5360163 : Nat := 2752340005445817071311565

theorem tailTrace_5360163 : CollatzResearch.WordTrace tailWord_5360163 prefixEnd_5360163 2752340005445817071311565 := by
  unfold tailWord_5360163
  simp only [CollatzResearch.WordTrace]
  refine ⟨195501205680052368803373143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130334137120034912535582095 195501205680052368803373143)
  ·
    refine ⟨293251808520078553205059715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195501205680052368803373143 293251808520078553205059715)
    ·
      refine ⟨439877712780117829807589573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293251808520078553205059715 439877712780117829807589573)
      ·
        refine ⟨82477071146272093088923045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 439877712780117829807589573 82477071146272093088923045)
        ·
          refine ⟨15464450839926017454173071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82477071146272093088923045 15464450839926017454173071)
          ·
            refine ⟨23196676259889026181259607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15464450839926017454173071 23196676259889026181259607)
            ·
              refine ⟨34795014389833539271889411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23196676259889026181259607 34795014389833539271889411)
              ·
                refine ⟨52192521584750308907834117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34795014389833539271889411 52192521584750308907834117)
                ·
                  refine ⟨9786097797140682920218897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52192521584750308907834117 9786097797140682920218897)
                  ·
                    refine ⟨7339573347855512190164173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9786097797140682920218897 7339573347855512190164173)
                    ·
                      refine ⟨2752340005445817071311565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7339573347855512190164173 2752340005445817071311565)
                      ·
                        rfl

theorem cell23_5360163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_5360163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360163 prefixEnd_5360163 := by exact prefixLift 5360163
  have htrace : WordTrace (prefixWord ++ tailWord_5360163) baseStart_5360163 baseEnd_5360163 := by
    simpa [prefixWord, tailWord_5360163, baseEnd_5360163] using wordTrace_append hprefix tailTrace_5360163
  have hstable : (prefixWord ++ tailWord_5360163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360163).length < 2 ^ (prefixWord ++ tailWord_5360163).sum := by decide
  have hdescent : baseEnd_5360163 < baseStart_5360163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360170 : List Nat := [3, 1, 4, 1, 1, 2, 3, 1, 3, 4]
def baseStart_5360170 : Nat := 118140960795 + 5360170 * 2 ^ 59
def prefixEnd_5360170 : Nat := 4983230072969 + 3 ^ 40 * 5360170 * 2
def baseEnd_5360170 : Nat := 917447866603466181308011

theorem tailTrace_5360170 : CollatzResearch.WordTrace tailWord_5360170 prefixEnd_5360170 917447866603466181308011 := by
  unfold tailWord_5360170
  simp only [CollatzResearch.WordTrace]
  refine ⟨48875365247756752249719491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130334307327351339332585309 48875365247756752249719491)
  ·
    refine ⟨73313047871635128374579237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48875365247756752249719491 73313047871635128374579237)
    ·
      refine ⟨13746196475931586570233607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73313047871635128374579237 13746196475931586570233607)
      ·
        refine ⟨20619294713897379855350411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13746196475931586570233607 20619294713897379855350411)
        ·
          refine ⟨30928942070846069783025617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20619294713897379855350411 30928942070846069783025617)
          ·
            refine ⟨23196706553134552337269213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30928942070846069783025617 23196706553134552337269213)
            ·
              refine ⟨8698764957425457126475955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23196706553134552337269213 8698764957425457126475955)
              ·
                refine ⟨13048147436138185689713933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8698764957425457126475955 13048147436138185689713933)
                ·
                  refine ⟨4893055288551819633642725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13048147436138185689713933 4893055288551819633642725)
                  ·
                    refine ⟨917447866603466181308011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4893055288551819633642725 917447866603466181308011)
                    ·
                      rfl

theorem cell23_5360170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_5360170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360170 prefixEnd_5360170 := by exact prefixLift 5360170
  have htrace : WordTrace (prefixWord ++ tailWord_5360170) baseStart_5360170 baseEnd_5360170 := by
    simpa [prefixWord, tailWord_5360170, baseEnd_5360170] using wordTrace_append hprefix tailTrace_5360170
  have hstable : (prefixWord ++ tailWord_5360170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360170).length < 2 ^ (prefixWord ++ tailWord_5360170).sum := by decide
  have hdescent : baseEnd_5360170 < baseStart_5360170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360203 : List Nat := [1, 1, 1, 1, 3, 1, 4, 3, 1, 5, 2]
def baseStart_5360203 : Nat := 118140960795 + 5360203 * 2 ^ 59
def prefixEnd_5360203 : Nat := 4983230072969 + 3 ^ 40 * 5360203 * 2
def baseEnd_5360203 : Nat := 2752360544671996914811381

theorem tailTrace_5360203 : CollatzResearch.WordTrace tailWord_5360203 prefixEnd_5360203 2752360544671996914811381 := by
  unfold tailWord_5360203
  simp only [CollatzResearch.WordTrace]
  refine ⟨195502664599907455634829263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130335109733271637089886175 195502664599907455634829263)
  ·
    refine ⟨293253996899861183452243895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195502664599907455634829263 293253996899861183452243895)
    ·
      refine ⟨439880995349791775178365843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293253996899861183452243895 439880995349791775178365843)
      ·
        refine ⟨659821493024687662767548765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439880995349791775178365843 659821493024687662767548765)
        ·
          refine ⟨247433059884257873537830787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 659821493024687662767548765 247433059884257873537830787)
          ·
            refine ⟨371149589826386810306746181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247433059884257873537830787 371149589826386810306746181)
            ·
              refine ⟨69590548092447526932514909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 371149589826386810306746181 69590548092447526932514909)
              ·
                refine ⟨26096455534667822599693091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69590548092447526932514909 26096455534667822599693091)
                ·
                  refine ⟨39144683302001733899539637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26096455534667822599693091 39144683302001733899539637)
                  ·
                    refine ⟨3669814059562662553081841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39144683302001733899539637 3669814059562662553081841)
                    ·
                      refine ⟨2752360544671996914811381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3669814059562662553081841 2752360544671996914811381)
                      ·
                        rfl

theorem cell23_5360203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 5, 2].length) (baseStart_5360203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360203 prefixEnd_5360203 := by exact prefixLift 5360203
  have htrace : WordTrace (prefixWord ++ tailWord_5360203) baseStart_5360203 baseEnd_5360203 := by
    simpa [prefixWord, tailWord_5360203, baseEnd_5360203] using wordTrace_append hprefix tailTrace_5360203
  have hstable : (prefixWord ++ tailWord_5360203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360203).length < 2 ^ (prefixWord ++ tailWord_5360203).sum := by decide
  have hdescent : baseEnd_5360203 < baseStart_5360203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360213 : List Nat := [1, 3, 2, 2, 1, 1, 2, 5, 1, 5]
def baseStart_5360213 : Nat := 118140960795 + 5360213 * 2 ^ 59
def prefixEnd_5360213 : Nat := 4983230072969 + 3 ^ 40 * 5360213 * 2
def baseEnd_5360213 : Nat := 917455226492847291895445

theorem tailTrace_5360213 : CollatzResearch.WordTrace tailWord_5360213 prefixEnd_5360213 917455226492847291895445 := by
  unfold tailWord_5360213
  simp only [CollatzResearch.WordTrace]
  refine ⟨195503029329871227342693293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130335352886580818228462195 195503029329871227342693293)
  ·
    refine ⟨73313635998701710253509985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195503029329871227342693293 73313635998701710253509985)
    ·
      refine ⟨54985226999026282690132489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73313635998701710253509985 54985226999026282690132489)
      ·
        refine ⟨41238920249269712017599367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54985226999026282690132489 41238920249269712017599367)
        ·
          refine ⟨61858380373904568026399051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41238920249269712017599367 61858380373904568026399051)
          ·
            refine ⟨92787570560856852039598577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61858380373904568026399051 92787570560856852039598577)
            ·
              refine ⟨69590677920642639029698933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92787570560856852039598577 69590677920642639029698933)
              ·
                refine ⟨6524126055060247409034275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69590677920642639029698933 6524126055060247409034275)
                ·
                  refine ⟨9786189082590371113551413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6524126055060247409034275 9786189082590371113551413)
                  ·
                    refine ⟨917455226492847291895445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9786189082590371113551413 917455226492847291895445)
                    ·
                      rfl

theorem cell23_5360213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_5360213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360213 prefixEnd_5360213 := by exact prefixLift 5360213
  have htrace : WordTrace (prefixWord ++ tailWord_5360213) baseStart_5360213 baseEnd_5360213 := by
    simpa [prefixWord, tailWord_5360213, baseEnd_5360213] using wordTrace_append hprefix tailTrace_5360213
  have hstable : (prefixWord ++ tailWord_5360213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360213).length < 2 ^ (prefixWord ++ tailWord_5360213).sum := by decide
  have hdescent : baseEnd_5360213 < baseStart_5360213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360227 : List Nat := [1, 1, 1, 5, 1, 2, 3, 4, 1, 1, 3]
def baseStart_5360227 : Nat := 118140960795 + 5360227 * 2 ^ 59
def prefixEnd_5360227 : Nat := 4983230072969 + 3 ^ 40 * 5360227 * 2
def baseEnd_5360227 : Nat := 2752372868207704820911271

theorem tailTrace_5360227 : CollatzResearch.WordTrace tailWord_5360227 prefixEnd_5360227 2752372868207704820911271 := by
  unfold tailWord_5360227
  simp only [CollatzResearch.WordTrace]
  refine ⟨195503539951820507733702935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130335693301213671822468623 195503539951820507733702935)
  ·
    refine ⟨293255309927730761600554403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195503539951820507733702935 293255309927730761600554403)
    ·
      refine ⟨439882964891596142400831605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293255309927730761600554403 439882964891596142400831605)
      ·
        refine ⟨41239027958587138350077963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 439882964891596142400831605 41239027958587138350077963)
        ·
          refine ⟨61858541937880707525116945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41239027958587138350077963 61858541937880707525116945)
          ·
            refine ⟨46393906453410530643837709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61858541937880707525116945 46393906453410530643837709)
            ·
              refine ⟨17397714920028948991439141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46393906453410530643837709 17397714920028948991439141)
              ·
                refine ⟨3262071547505427935894839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17397714920028948991439141 3262071547505427935894839)
                ·
                  refine ⟨4893107321258141903842259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3262071547505427935894839 4893107321258141903842259)
                  ·
                    refine ⟨7339660981887212855763389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4893107321258141903842259 7339660981887212855763389)
                    ·
                      refine ⟨2752372868207704820911271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7339660981887212855763389 2752372868207704820911271)
                      ·
                        rfl

theorem cell23_5360227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_5360227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360227 prefixEnd_5360227 := by exact prefixLift 5360227
  have htrace : WordTrace (prefixWord ++ tailWord_5360227) baseStart_5360227 baseEnd_5360227 := by
    simpa [prefixWord, tailWord_5360227, baseEnd_5360227] using wordTrace_append hprefix tailTrace_5360227
  have hstable : (prefixWord ++ tailWord_5360227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360227).length < 2 ^ (prefixWord ++ tailWord_5360227).sum := by decide
  have hdescent : baseEnd_5360227 < baseStart_5360227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360233 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 2, 6, 2]
def baseStart_5360233 : Nat := 118140960795 + 5360233 * 2 ^ 59
def prefixEnd_5360233 : Nat := 4983230072969 + 3 ^ 40 * 5360233 * 2
def baseEnd_5360233 : Nat := 2752375949091631797436243

theorem tailTrace_5360233 : CollatzResearch.WordTrace tailWord_5360233 prefixEnd_5360233 2752375949091631797436243 := by
  unfold tailWord_5360233
  simp only [CollatzResearch.WordTrace]
  refine ⟨195503758789798770758421353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130335839193199180505614235 195503758789798770758421353)
  ·
    refine ⟨146627819092349078068816015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195503758789798770758421353 146627819092349078068816015)
    ·
      refine ⟨219941728638523617103224023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146627819092349078068816015 219941728638523617103224023)
      ·
        refine ⟨329912592957785425654836035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219941728638523617103224023 329912592957785425654836035)
        ·
          refine ⟨494868889436678138482254053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329912592957785425654836035 494868889436678138482254053)
          ·
            refine ⟨92787916769377150965422635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 494868889436678138482254053 92787916769377150965422635)
            ·
              refine ⟨139181875154065726448133953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92787916769377150965422635 139181875154065726448133953)
              ·
                refine ⟨104386406365549294836100465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139181875154065726448133953 104386406365549294836100465)
                ·
                  refine ⟨78289804774161971127075349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104386406365549294836100465 78289804774161971127075349)
                  ·
                    refine ⟨3669834598788842396581657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78289804774161971127075349 3669834598788842396581657)
                    ·
                      refine ⟨2752375949091631797436243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3669834598788842396581657 2752375949091631797436243)
                      ·
                        rfl

theorem cell23_5360233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 6, 2].length) (baseStart_5360233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360233 prefixEnd_5360233 := by exact prefixLift 5360233
  have htrace : WordTrace (prefixWord ++ tailWord_5360233) baseStart_5360233 baseEnd_5360233 := by
    simpa [prefixWord, tailWord_5360233, baseEnd_5360233] using wordTrace_append hprefix tailTrace_5360233
  have hstable : (prefixWord ++ tailWord_5360233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360233).length < 2 ^ (prefixWord ++ tailWord_5360233).sum := by decide
  have hdescent : baseEnd_5360233 < baseStart_5360233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360263 : List Nat := [1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 4]
def baseStart_5360263 : Nat := 118140960795 + 5360263 * 2 ^ 59
def prefixEnd_5360263 : Nat := 4983230072969 + 3 ^ 40 * 5360263 * 2
def baseEnd_5360263 : Nat := 2752391353511266680061105

theorem tailTrace_5360263 : CollatzResearch.WordTrace tailWord_5360263 prefixEnd_5360263 2752391353511266680061105 := by
  unfold tailWord_5360263
  simp only [CollatzResearch.WordTrace]
  refine ⟨195504852979690085882013443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130336568653126723921342295 195504852979690085882013443)
  ·
    refine ⟨293257279469535128823020165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195504852979690085882013443 293257279469535128823020165)
    ·
      refine ⟨54985739900537836654316281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 293257279469535128823020165 54985739900537836654316281)
      ·
        refine ⟨41239304925403377490737211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54985739900537836654316281 41239304925403377490737211)
        ·
          refine ⟨61858957388105066236105817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41239304925403377490737211 61858957388105066236105817)
          ·
            refine ⟨46394218041078799677079363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61858957388105066236105817 46394218041078799677079363)
            ·
              refine ⟨69591327061618199515619045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46394218041078799677079363 69591327061618199515619045)
              ·
                refine ⟨13048373824053412409178571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69591327061618199515619045 13048373824053412409178571)
                ·
                  refine ⟨19572560736080118613767857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13048373824053412409178571 19572560736080118613767857)
                  ·
                    refine ⟨14679420552060088960325893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19572560736080118613767857 14679420552060088960325893)
                    ·
                      refine ⟨2752391353511266680061105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14679420552060088960325893 2752391353511266680061105)
                      ·
                        rfl

theorem cell23_5360263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_5360263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360263 prefixEnd_5360263 := by exact prefixLift 5360263
  have htrace : WordTrace (prefixWord ++ tailWord_5360263) baseStart_5360263 baseEnd_5360263 := by
    simpa [prefixWord, tailWord_5360263, baseEnd_5360263] using wordTrace_append hprefix tailTrace_5360263
  have hstable : (prefixWord ++ tailWord_5360263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360263).length < 2 ^ (prefixWord ++ tailWord_5360263).sum := by decide
  have hdescent : baseEnd_5360263 < baseStart_5360263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360284 : List Nat := [2, 2, 3, 2, 2, 2, 2, 1, 3, 2, 2]
def baseStart_5360284 : Nat := 118140960795 + 5360284 * 2 ^ 59
def prefixEnd_5360284 : Nat := 4983230072969 + 3 ^ 40 * 5360284 * 2
def baseEnd_5360284 : Nat := 2752402136605011097898509

theorem tailTrace_5360284 : CollatzResearch.WordTrace tailWord_5360284 prefixEnd_5360284 2752402136605011097898509 := by
  unfold tailWord_5360284
  simp only [CollatzResearch.WordTrace]
  refine ⟨97752809456307003234263953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130337079275076004312351937 97752809456307003234263953)
  ·
    refine ⟨73314607092230252425697965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97752809456307003234263953 73314607092230252425697965)
    ·
      refine ⟨27492977659586344659636737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73314607092230252425697965 27492977659586344659636737)
      ·
        refine ⟨20619733244689758494727553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27492977659586344659636737 20619733244689758494727553)
        ·
          refine ⟨15464799933517318871045665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20619733244689758494727553 15464799933517318871045665)
          ·
            refine ⟨11598599950137989153284249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15464799933517318871045665 11598599950137989153284249)
            ·
              refine ⟨8698949962603491864963187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11598599950137989153284249 8698949962603491864963187)
              ·
                refine ⟨13048424943905237797444781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8698949962603491864963187 13048424943905237797444781)
                ·
                  refine ⟨4893159353964464174041793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13048424943905237797444781 4893159353964464174041793)
                  ·
                    refine ⟨3669869515473348130531345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4893159353964464174041793 3669869515473348130531345)
                    ·
                      refine ⟨2752402136605011097898509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3669869515473348130531345 2752402136605011097898509)
                      ·
                        rfl

theorem cell23_5360284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_5360284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360284 prefixEnd_5360284 := by exact prefixLift 5360284
  have htrace : WordTrace (prefixWord ++ tailWord_5360284) baseStart_5360284 baseEnd_5360284 := by
    simpa [prefixWord, tailWord_5360284, baseEnd_5360284] using wordTrace_append hprefix tailTrace_5360284
  have hstable : (prefixWord ++ tailWord_5360284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360284).length < 2 ^ (prefixWord ++ tailWord_5360284).sum := by decide
  have hdescent : baseEnd_5360284 < baseStart_5360284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360391 : List Nat := [1, 1, 4, 4, 1, 2, 2, 2, 2, 2, 2]
def baseStart_5360391 : Nat := 118140960795 + 5360391 * 2 ^ 59
def prefixEnd_5360391 : Nat := 4983230072969 + 3 ^ 40 * 5360391 * 2
def baseEnd_5360391 : Nat := 2752457079035042179260517

theorem tailTrace_5360391 : CollatzResearch.WordTrace tailWord_5360391 prefixEnd_5360391 2752457079035042179260517 := by
  unfold tailWord_5360391
  simp only [CollatzResearch.WordTrace]
  refine ⟨195509521523226363742673027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130339681015484242495115351 195509521523226363742673027)
  ·
    refine ⟨293264282284839545614009541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195509521523226363742673027 293264282284839545614009541)
    ·
      refine ⟨54987052928407414802626789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 293264282284839545614009541 54987052928407414802626789)
      ·
        refine ⟨10310072424076390275492523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54987052928407414802626789 10310072424076390275492523)
        ·
          refine ⟨15465108636114585413238785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10310072424076390275492523 15465108636114585413238785)
          ·
            refine ⟨11598831477085939059929089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15465108636114585413238785 11598831477085939059929089)
            ·
              refine ⟨8699123607814454294946817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11598831477085939059929089 8699123607814454294946817)
              ·
                refine ⟨6524342705860840721210113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8699123607814454294946817 6524342705860840721210113)
                ·
                  refine ⟨4893257029395630540907585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6524342705860840721210113 4893257029395630540907585)
                  ·
                    refine ⟨3669942772046722905680689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4893257029395630540907585 3669942772046722905680689)
                    ·
                      refine ⟨2752457079035042179260517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3669942772046722905680689 2752457079035042179260517)
                      ·
                        rfl

theorem cell23_5360391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_5360391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360391 prefixEnd_5360391 := by exact prefixLift 5360391
  have htrace : WordTrace (prefixWord ++ tailWord_5360391) baseStart_5360391 baseEnd_5360391 := by
    simpa [prefixWord, tailWord_5360391, baseEnd_5360391] using wordTrace_append hprefix tailTrace_5360391
  have hstable : (prefixWord ++ tailWord_5360391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360391).length < 2 ^ (prefixWord ++ tailWord_5360391).sum := by decide
  have hdescent : baseEnd_5360391 < baseStart_5360391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360403 : List Nat := [1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 5]
def baseStart_5360403 : Nat := 118140960795 + 5360403 * 2 ^ 59
def prefixEnd_5360403 : Nat := 4983230072969 + 3 ^ 40 * 5360403 * 2
def baseEnd_5360403 : Nat := 2752463240802896132310461

theorem tailTrace_5360403 : CollatzResearch.WordTrace tailWord_5360403 prefixEnd_5360403 2752463240802896132310461 := by
  unfold tailWord_5360403
  simp only [CollatzResearch.WordTrace]
  refine ⟨195509959199182889792109863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130339972799455259861406575 195509959199182889792109863)
  ·
    refine ⟨293264938798774334688164795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195509959199182889792109863 293264938798774334688164795)
    ·
      refine ⟨439897408198161502032247193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293264938798774334688164795 439897408198161502032247193)
      ·
        refine ⟨329923056148621126524185395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 439897408198161502032247193 329923056148621126524185395)
        ·
          refine ⟨494884584222931689786278093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329923056148621126524185395 494884584222931689786278093)
          ·
            refine ⟨185581719083599383669854285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 494884584222931689786278093 185581719083599383669854285)
            ·
              refine ⟨69593144656349768876195357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185581719083599383669854285 69593144656349768876195357)
              ·
                refine ⟨26097429246131163328573259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69593144656349768876195357 26097429246131163328573259)
                ·
                  refine ⟨39146143869196744992859889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26097429246131163328573259 39146143869196744992859889)
                  ·
                    refine ⟨29359607901897558744644917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39146143869196744992859889 29359607901897558744644917)
                    ·
                      refine ⟨2752463240802896132310461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29359607901897558744644917 2752463240802896132310461)
                      ·
                        rfl

theorem cell23_5360403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 5].length) (baseStart_5360403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360403 prefixEnd_5360403 := by exact prefixLift 5360403
  have htrace : WordTrace (prefixWord ++ tailWord_5360403) baseStart_5360403 baseEnd_5360403 := by
    simpa [prefixWord, tailWord_5360403, baseEnd_5360403] using wordTrace_append hprefix tailTrace_5360403
  have hstable : (prefixWord ++ tailWord_5360403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360403).length < 2 ^ (prefixWord ++ tailWord_5360403).sum := by decide
  have hdescent : baseEnd_5360403 < baseStart_5360403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360407 : List Nat := [1, 1, 3, 4, 3, 1, 1, 1, 2, 3, 3]
def baseStart_5360407 : Nat := 118140960795 + 5360407 * 2 ^ 59
def prefixEnd_5360407 : Nat := 4983230072969 + 3 ^ 40 * 5360407 * 2
def baseEnd_5360407 : Nat := 2752465294725514116660443

theorem tailTrace_5360407 : CollatzResearch.WordTrace tailWord_5360407 prefixEnd_5360407 2752465294725514116660443 := by
  unfold tailWord_5360407
  simp only [CollatzResearch.WordTrace]
  refine ⟨195510105091168398475255475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130340070060778932316836983 195510105091168398475255475)
  ·
    refine ⟨293265157636752597712883213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195510105091168398475255475 293265157636752597712883213)
    ·
      refine ⟨109974434113782224142331205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293265157636752597712883213 109974434113782224142331205)
      ·
        refine ⟨20620206396334167026687101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109974434113782224142331205 20620206396334167026687101)
        ·
          refine ⟨7732577398625312635007663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20620206396334167026687101 7732577398625312635007663)
          ·
            refine ⟨11598866097937968952511495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7732577398625312635007663 11598866097937968952511495)
            ·
              refine ⟨17398299146906953428767243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11598866097937968952511495 17398299146906953428767243)
              ·
                refine ⟨26097448720360430143150865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17398299146906953428767243 26097448720360430143150865)
                ·
                  refine ⟨19573086540270322607363149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26097448720360430143150865 19573086540270322607363149)
                  ·
                    refine ⟨7339907452601370977761181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19573086540270322607363149 7339907452601370977761181)
                    ·
                      refine ⟨2752465294725514116660443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7339907452601370977761181 2752465294725514116660443)
                      ·
                        rfl

theorem cell23_5360407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_5360407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360407 prefixEnd_5360407 := by exact prefixLift 5360407
  have htrace : WordTrace (prefixWord ++ tailWord_5360407) baseStart_5360407 baseEnd_5360407 := by
    simpa [prefixWord, tailWord_5360407, baseEnd_5360407] using wordTrace_append hprefix tailTrace_5360407
  have hstable : (prefixWord ++ tailWord_5360407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360407).length < 2 ^ (prefixWord ++ tailWord_5360407).sum := by decide
  have hdescent : baseEnd_5360407 < baseStart_5360407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360440 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 5, 4]
def baseStart_5360440 : Nat := 118140960795 + 5360440 * 2 ^ 59
def prefixEnd_5360440 : Nat := 4983230072969 + 3 ^ 40 * 5360440 * 2
def baseEnd_5360440 : Nat := 917494079862370829182597

theorem tailTrace_5360440 : CollatzResearch.WordTrace tailWord_5360440 prefixEnd_5360440 917494079862370829182597 := by
  unfold tailWord_5360440
  simp only [CollatzResearch.WordTrace]
  refine ⟨97755654350024422555603387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130340872466699230074137849 97755654350024422555603387)
  ·
    refine ⟨146633481525036633833405081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97755654350024422555603387 146633481525036633833405081)
    ·
      refine ⟨109975111143777475375053811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146633481525036633833405081 109975111143777475375053811)
      ·
        refine ⟨164962666715666213062580717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109975111143777475375053811 164962666715666213062580717)
        ·
          refine ⟨61861000018374829898467769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164962666715666213062580717 61861000018374829898467769)
          ·
            refine ⟨46395750013781122423850827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61861000018374829898467769 46395750013781122423850827)
            ·
              refine ⟨69593625020671683635776241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46395750013781122423850827 69593625020671683635776241)
              ·
                refine ⟨52195218765503762726832181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69593625020671683635776241 52195218765503762726832181)
                ·
                  refine ⟨4893301759265977755640517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52195218765503762726832181 4893301759265977755640517)
                  ·
                    refine ⟨917494079862370829182597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4893301759265977755640517 917494079862370829182597)
                    ·
                      rfl

theorem cell23_5360440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 5, 4].length) (baseStart_5360440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360440 prefixEnd_5360440 := by exact prefixLift 5360440
  have htrace : WordTrace (prefixWord ++ tailWord_5360440) baseStart_5360440 baseEnd_5360440 := by
    simpa [prefixWord, tailWord_5360440, baseEnd_5360440] using wordTrace_append hprefix tailTrace_5360440
  have hstable : (prefixWord ++ tailWord_5360440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360440).length < 2 ^ (prefixWord ++ tailWord_5360440).sum := by decide
  have hdescent : baseEnd_5360440 < baseStart_5360440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360447 : List Nat := [1, 1, 2, 2, 5, 1, 1, 2, 2, 4, 2]
def baseStart_5360447 : Nat := 118140960795 + 5360447 * 2 ^ 59
def prefixEnd_5360447 : Nat := 4983230072969 + 3 ^ 40 * 5360447 * 2
def baseEnd_5360447 : Nat := 2752485833951693960160259

theorem tailTrace_5360447 : CollatzResearch.WordTrace tailWord_5360447 prefixEnd_5360447 2752485833951693960160259 := by
  unfold tailWord_5360447
  simp only [CollatzResearch.WordTrace]
  refine ⟨195511564011023485306711595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130341042674015656871141063 195511564011023485306711595)
  ·
    refine ⟨293267346016535227960067393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195511564011023485306711595 293267346016535227960067393)
    ·
      refine ⟨219950509512401420970050545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293267346016535227960067393 219950509512401420970050545)
      ·
        refine ⟨164962882134301065727537909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219950509512401420970050545 164962882134301065727537909)
        ·
          refine ⟨15465270200090724911956679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 164962882134301065727537909 15465270200090724911956679)
          ·
            refine ⟨23197905300136087367935019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15465270200090724911956679 23197905300136087367935019)
            ·
              refine ⟨34796857950204131051902529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23197905300136087367935019 34796857950204131051902529)
              ·
                refine ⟨26097643462653098288926897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34796857950204131051902529 26097643462653098288926897)
                ·
                  refine ⟨19573232596989823716695173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26097643462653098288926897 19573232596989823716695173)
                  ·
                    refine ⟨3669981111935591946880345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19573232596989823716695173 3669981111935591946880345)
                    ·
                      refine ⟨2752485833951693960160259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3669981111935591946880345 2752485833951693960160259)
                      ·
                        rfl

theorem cell23_5360447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 2, 4, 2].length) (baseStart_5360447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360447 prefixEnd_5360447 := by exact prefixLift 5360447
  have htrace : WordTrace (prefixWord ++ tailWord_5360447) baseStart_5360447 baseEnd_5360447 := by
    simpa [prefixWord, tailWord_5360447, baseEnd_5360447] using wordTrace_append hprefix tailTrace_5360447
  have hstable : (prefixWord ++ tailWord_5360447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360447).length < 2 ^ (prefixWord ++ tailWord_5360447).sum := by decide
  have hdescent : baseEnd_5360447 < baseStart_5360447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360457 : List Nat := [1, 2, 1, 1, 2, 6, 2, 1, 3, 4]
def baseStart_5360457 : Nat := 118140960795 + 5360457 * 2 ^ 59
def prefixEnd_5360457 : Nat := 4983230072969 + 3 ^ 40 * 5360457 * 2
def baseEnd_5360457 : Nat := 917496989586079640345071

theorem tailTrace_5360457 : CollatzResearch.WordTrace tailWord_5360457 prefixEnd_5360457 917496989586079640345071 := by
  unfold tailWord_5360457
  simp only [CollatzResearch.WordTrace]
  refine ⟨195511928740987257014575625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130341285827324838009717083 195511928740987257014575625)
  ·
    refine ⟨146633946555740442760931719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195511928740987257014575625 146633946555740442760931719)
    ·
      refine ⟨219950919833610664141397579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146633946555740442760931719 219950919833610664141397579)
      ·
        refine ⟨329926379750415996212096369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219950919833610664141397579 329926379750415996212096369)
        ·
          refine ⟨247444784812811997159072277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329926379750415996212096369 247444784812811997159072277)
          ·
            refine ⟨11598974288100562366831513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 247444784812811997159072277 11598974288100562366831513)
            ·
              refine ⟨8699230716075421775123635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11598974288100562366831513 8699230716075421775123635)
              ·
                refine ⟨13048846074113132662685453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8699230716075421775123635 13048846074113132662685453)
                ·
                  refine ⟨4893317277792424748507045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13048846074113132662685453 4893317277792424748507045)
                  ·
                    refine ⟨917496989586079640345071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4893317277792424748507045 917496989586079640345071)
                    ·
                      rfl

theorem cell23_5360457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3, 4].length) (baseStart_5360457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360457 prefixEnd_5360457 := by exact prefixLift 5360457
  have htrace : WordTrace (prefixWord ++ tailWord_5360457) baseStart_5360457 baseEnd_5360457 := by
    simpa [prefixWord, tailWord_5360457, baseEnd_5360457] using wordTrace_append hprefix tailTrace_5360457
  have hstable : (prefixWord ++ tailWord_5360457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360457).length < 2 ^ (prefixWord ++ tailWord_5360457).sum := by decide
  have hdescent : baseEnd_5360457 < baseStart_5360457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360480 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 3]
def baseStart_5360480 : Nat := 118140960795 + 5360480 * 2 ^ 59
def prefixEnd_5360480 : Nat := 4983230072969 + 3 ^ 40 * 5360480 * 2
def baseEnd_5360480 : Nat := 2752502778813292331047607

theorem tailTrace_5360480 : CollatzResearch.WordTrace tailWord_5360480 prefixEnd_5360480 2752502778813292331047607 := by
  unfold tailWord_5360480
  simp only [CollatzResearch.WordTrace]
  refine ⟨97756383809951965971331447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130341845079935954628441929 97756383809951965971331447)
  ·
    refine ⟨146634575714927948956997171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97756383809951965971331447 146634575714927948956997171)
    ·
      refine ⟨219951863572391923435495757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146634575714927948956997171 219951863572391923435495757)
      ·
        refine ⟨82481948839646971288310909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219951863572391923435495757 82481948839646971288310909)
        ·
          refine ⟨30930730814867614233116591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82481948839646971288310909 30930730814867614233116591)
          ·
            refine ⟨46396096222301421349674887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30930730814867614233116591 46396096222301421349674887)
            ·
              refine ⟨69594144333452132024512331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46396096222301421349674887 69594144333452132024512331)
              ·
                refine ⟨104391216500178198036768497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69594144333452132024512331 104391216500178198036768497)
                ·
                  refine ⟨78293412375133648527576373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104391216500178198036768497 78293412375133648527576373)
                  ·
                    refine ⟨7340007410168779549460285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78293412375133648527576373 7340007410168779549460285)
                    ·
                      refine ⟨2752502778813292331047607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7340007410168779549460285 2752502778813292331047607)
                      ·
                        rfl

theorem cell23_5360480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_5360480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360480 prefixEnd_5360480 := by exact prefixLift 5360480
  have htrace : WordTrace (prefixWord ++ tailWord_5360480) baseStart_5360480 baseEnd_5360480 := by
    simpa [prefixWord, tailWord_5360480, baseEnd_5360480] using wordTrace_append hprefix tailTrace_5360480
  have hstable : (prefixWord ++ tailWord_5360480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360480).length < 2 ^ (prefixWord ++ tailWord_5360480).sum := by decide
  have hdescent : baseEnd_5360480 < baseStart_5360480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360507 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 4, 3, 2]
def baseStart_5360507 : Nat := 118140960795 + 5360507 * 2 ^ 59
def prefixEnd_5360507 : Nat := 4983230072969 + 3 ^ 40 * 5360507 * 2
def baseEnd_5360507 : Nat := 2752516642790963725409983

theorem tailTrace_5360507 : CollatzResearch.WordTrace tailWord_5360507 prefixEnd_5360507 2752516642790963725409983 := by
  unfold tailWord_5360507
  simp only [CollatzResearch.WordTrace]
  refine ⟨195513752390806115553895775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130342501593870743702597183 195513752390806115553895775)
  ·
    refine ⟨293270628586209173330843663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195513752390806115553895775 293270628586209173330843663)
    ·
      refine ⟨439905942879313759996265495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293270628586209173330843663 439905942879313759996265495)
      ·
        refine ⟨659858914318970639994398243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439905942879313759996265495 659858914318970639994398243)
        ·
          refine ⟨989788371478455959991597365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 659858914318970639994398243 989788371478455959991597365)
          ·
            refine ⟨92792659826105246249212253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 989788371478455959991597365 92792659826105246249212253)
            ·
              refine ⟨34797247434789467343454595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92792659826105246249212253 34797247434789467343454595)
              ·
                refine ⟨52195871152184201015181893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34797247434789467343454595 52195871152184201015181893)
                ·
                  refine ⟨9786725841034537690346605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52195871152184201015181893 9786725841034537690346605)
                  ·
                    refine ⟨3670022190387951633879977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9786725841034537690346605 3670022190387951633879977)
                    ·
                      refine ⟨2752516642790963725409983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3670022190387951633879977 2752516642790963725409983)
                      ·
                        rfl

theorem cell23_5360507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 4, 3, 2].length) (baseStart_5360507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360507 prefixEnd_5360507 := by exact prefixLift 5360507
  have htrace : WordTrace (prefixWord ++ tailWord_5360507) baseStart_5360507 baseEnd_5360507 := by
    simpa [prefixWord, tailWord_5360507, baseEnd_5360507] using wordTrace_append hprefix tailTrace_5360507
  have hstable : (prefixWord ++ tailWord_5360507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360507).length < 2 ^ (prefixWord ++ tailWord_5360507).sum := by decide
  have hdescent : baseEnd_5360507 < baseStart_5360507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360551 : List Nat := [1, 1, 6, 1, 3, 1, 3, 1, 1, 5]
def baseStart_5360551 : Nat := 118140960795 + 5360551 * 2 ^ 59
def prefixEnd_5360551 : Nat := 4983230072969 + 3 ^ 40 * 5360551 * 2
def baseEnd_5360551 : Nat := 917513078646587184419927

theorem tailTrace_5360551 : CollatzResearch.WordTrace tailWord_5360551 prefixEnd_5360551 917513078646587184419927 := by
  unfold tailWord_5360551
  simp only [CollatzResearch.WordTrace]
  refine ⟨195515357202646711068497507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130343571468431140712331671 195515357202646711068497507)
  ·
    refine ⟨293273035803970066602746261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195515357202646711068497507 293273035803970066602746261)
    ·
      refine ⟨13747173553311096872003731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 293273035803970066602746261 13747173553311096872003731)
      ·
        refine ⟨20620760329966645308005597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13747173553311096872003731 20620760329966645308005597)
        ·
          refine ⟨7732785123737491990502099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20620760329966645308005597 7732785123737491990502099)
          ·
            refine ⟨11599177685606237985753149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7732785123737491990502099 11599177685606237985753149)
            ·
              refine ⟨4349691632102339244657431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11599177685606237985753149 4349691632102339244657431)
              ·
                refine ⟨6524537448153508866986147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4349691632102339244657431 6524537448153508866986147)
                ·
                  refine ⟨9786806172230263300479221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6524537448153508866986147 9786806172230263300479221)
                  ·
                    refine ⟨917513078646587184419927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9786806172230263300479221 917513078646587184419927)
                    ·
                      rfl

theorem cell23_5360551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_5360551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360551 prefixEnd_5360551 := by exact prefixLift 5360551
  have htrace : WordTrace (prefixWord ++ tailWord_5360551) baseStart_5360551 baseEnd_5360551 := by
    simpa [prefixWord, tailWord_5360551, baseEnd_5360551] using wordTrace_append hprefix tailTrace_5360551
  have hstable : (prefixWord ++ tailWord_5360551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360551).length < 2 ^ (prefixWord ++ tailWord_5360551).sum := by decide
  have hdescent : baseEnd_5360551 < baseStart_5360551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360582 : List Nat := [6, 1, 3, 1, 1, 1, 1, 2, 3, 1, 3]
def baseStart_5360582 : Nat := 118140960795 + 5360582 * 2 ^ 59
def prefixEnd_5360582 : Nat := 4983230072969 + 3 ^ 40 * 5360582 * 2
def baseEnd_5360582 : Nat := 2752555153840050931972139

theorem tailTrace_5360582 : CollatzResearch.WordTrace tailWord_5360582 prefixEnd_5360582 2752555153840050931972139 := by
  unfold tailWord_5360582
  simp only [CollatzResearch.WordTrace]
  refine ⟨6109890245797950105089875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 130344325243689602241917333 6109890245797950105089875)
  ·
    refine ⟨9164835368696925157634813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6109890245797950105089875 9164835368696925157634813)
    ·
      refine ⟨3436813263261346934113055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9164835368696925157634813 3436813263261346934113055)
      ·
        refine ⟨5155219894892020401169583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3436813263261346934113055 5155219894892020401169583)
        ·
          refine ⟨7732829842338030601754375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5155219894892020401169583 7732829842338030601754375)
          ·
            refine ⟨11599244763507045902631563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7732829842338030601754375 11599244763507045902631563)
            ·
              refine ⟨17398867145260568853947345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11599244763507045902631563 17398867145260568853947345)
              ·
                refine ⟨13049150358945426640460509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17398867145260568853947345 13049150358945426640460509)
                ·
                  refine ⟨4893431384604534990172691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13049150358945426640460509 4893431384604534990172691)
                  ·
                    refine ⟨7340147076906802485259037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4893431384604534990172691 7340147076906802485259037)
                    ·
                      refine ⟨2752555153840050931972139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7340147076906802485259037 2752555153840050931972139)
                      ·
                        rfl

theorem cell23_5360582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_5360582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360582 prefixEnd_5360582 := by exact prefixLift 5360582
  have htrace : WordTrace (prefixWord ++ tailWord_5360582) baseStart_5360582 baseEnd_5360582 := by
    simpa [prefixWord, tailWord_5360582, baseEnd_5360582] using wordTrace_append hprefix tailTrace_5360582
  have hstable : (prefixWord ++ tailWord_5360582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360582).length < 2 ^ (prefixWord ++ tailWord_5360582).sum := by decide
  have hdescent : baseEnd_5360582 < baseStart_5360582 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360584 : List Nat := [2, 1, 3, 1, 5, 1, 2, 1, 1, 2, 4]
def baseStart_5360584 : Nat := 118140960795 + 5360584 * 2 ^ 59
def prefixEnd_5360584 : Nat := 4983230072969 + 3 ^ 40 * 5360584 * 2
def baseEnd_5360584 : Nat := 2752556180801359924147129

theorem tailTrace_5360584 : CollatzResearch.WordTrace tailWord_5360584 prefixEnd_5360584 2752556180801359924147129 := by
  unfold tailWord_5360584
  simp only [CollatzResearch.WordTrace]
  refine ⟨97758280405763578852224403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130344373874351438469632537 97758280405763578852224403)
  ·
    refine ⟨146637420608645368278336605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97758280405763578852224403 146637420608645368278336605)
    ·
      refine ⟨54989032728242013104376227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146637420608645368278336605 54989032728242013104376227)
      ·
        refine ⟨82483549092363019656564341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54989032728242013104376227 82483549092363019656564341)
        ·
          refine ⟨7732832727409033092802907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82483549092363019656564341 7732832727409033092802907)
          ·
            refine ⟨11599249091113549639204361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7732832727409033092802907 11599249091113549639204361)
            ·
              refine ⟨8699436818335162229403271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11599249091113549639204361 8699436818335162229403271)
              ·
                refine ⟨13049155227502743344104907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8699436818335162229403271 13049155227502743344104907)
                ·
                  refine ⟨19573732841254115016157361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13049155227502743344104907 19573732841254115016157361)
                  ·
                    refine ⟨14680299630940586262118021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19573732841254115016157361 14680299630940586262118021)
                    ·
                      refine ⟨2752556180801359924147129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14680299630940586262118021 2752556180801359924147129)
                      ·
                        rfl

theorem cell23_5360584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_5360584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360584 prefixEnd_5360584 := by exact prefixLift 5360584
  have htrace : WordTrace (prefixWord ++ tailWord_5360584) baseStart_5360584 baseEnd_5360584 := by
    simpa [prefixWord, tailWord_5360584, baseEnd_5360584] using wordTrace_append hprefix tailTrace_5360584
  have hstable : (prefixWord ++ tailWord_5360584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360584).length < 2 ^ (prefixWord ++ tailWord_5360584).sum := by decide
  have hdescent : baseEnd_5360584 < baseStart_5360584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360587 : List Nat := [1, 1, 1, 1, 3, 5, 1, 3, 1, 3, 3]
def baseStart_5360587 : Nat := 118140960795 + 5360587 * 2 ^ 59
def prefixEnd_5360587 : Nat := 4983230072969 + 3 ^ 40 * 5360587 * 2
def baseEnd_5360587 : Nat := 2752557721243323412409615

theorem tailTrace_5360587 : CollatzResearch.WordTrace tailWord_5360587 prefixEnd_5360587 2752557721243323412409615 := by
  unfold tailWord_5360587
  simp only [CollatzResearch.WordTrace]
  refine ⟨195516670230516289216808015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130344446820344192811205343 195516670230516289216808015)
  ·
    refine ⟨293275005345774433825212023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195516670230516289216808015 293275005345774433825212023)
    ·
      refine ⟨439912508018661650737818035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293275005345774433825212023 439912508018661650737818035)
      ·
        refine ⟨659868762027992476106727053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439912508018661650737818035 659868762027992476106727053)
        ·
          refine ⟨247450785760497178540022645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 659868762027992476106727053 247450785760497178540022645)
          ·
            refine ⟨23198511165046610488127123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 247450785760497178540022645 23198511165046610488127123)
            ·
              refine ⟨34797766747569915732190685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23198511165046610488127123 34797766747569915732190685)
              ·
                refine ⟨13049162530338718399571507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34797766747569915732190685 13049162530338718399571507)
                ·
                  refine ⟨19573743795508077599357261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13049162530338718399571507 19573743795508077599357261)
                  ·
                    refine ⟨7340153923315529099758973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19573743795508077599357261 7340153923315529099758973)
                    ·
                      refine ⟨2752557721243323412409615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7340153923315529099758973 2752557721243323412409615)
                      ·
                        rfl

theorem cell23_5360587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3, 3].length) (baseStart_5360587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360587 prefixEnd_5360587 := by exact prefixLift 5360587
  have htrace : WordTrace (prefixWord ++ tailWord_5360587) baseStart_5360587 baseEnd_5360587 := by
    simpa [prefixWord, tailWord_5360587, baseEnd_5360587] using wordTrace_append hprefix tailTrace_5360587
  have hstable : (prefixWord ++ tailWord_5360587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360587).length < 2 ^ (prefixWord ++ tailWord_5360587).sum := by decide
  have hdescent : baseEnd_5360587 < baseStart_5360587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360594 : List Nat := [3, 2, 2, 3, 1, 2, 3, 7]
def baseStart_5360594 : Nat := 118140960795 + 5360594 * 2 ^ 59
def prefixEnd_5360594 : Nat := 4983230072969 + 3 ^ 40 * 5360594 * 2
def baseEnd_5360594 : Nat := 101946715392885366111929

theorem tailTrace_5360594 : CollatzResearch.WordTrace tailWord_5360594 prefixEnd_5360594 101946715392885366111929 := by
  unfold tailWord_5360594
  simp only [CollatzResearch.WordTrace]
  refine ⟨48879231385372732353078209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130344617027660619608208557 48879231385372732353078209)
  ·
    refine ⟨36659423539029549264808657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48879231385372732353078209 36659423539029549264808657)
    ·
      refine ⟨27494567654272161948606493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36659423539029549264808657 27494567654272161948606493)
      ·
        refine ⟨10310462870352060730727435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27494567654272161948606493 10310462870352060730727435)
        ·
          refine ⟨15465694305528091096091153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10310462870352060730727435 15465694305528091096091153)
          ·
            refine ⟨11599270729146068322068365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15465694305528091096091153 11599270729146068322068365)
            ·
              refine ⟨4349726523429775620775637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11599270729146068322068365 4349726523429775620775637)
              ·
                refine ⟨101946715392885366111929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4349726523429775620775637 101946715392885366111929)
                ·
                  rfl

theorem cell23_5360594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 7].length) (baseStart_5360594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360594 prefixEnd_5360594 := by exact prefixLift 5360594
  have htrace : WordTrace (prefixWord ++ tailWord_5360594) baseStart_5360594 baseEnd_5360594 := by
    simpa [prefixWord, tailWord_5360594, baseEnd_5360594] using wordTrace_append hprefix tailTrace_5360594
  have hstable : (prefixWord ++ tailWord_5360594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360594).length < 2 ^ (prefixWord ++ tailWord_5360594).sum := by decide
  have hdescent : baseEnd_5360594 < baseStart_5360594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360605 : List Nat := [1, 4, 3, 1, 2, 2, 2, 3, 1, 2, 2]
def baseStart_5360605 : Nat := 118140960795 + 5360605 * 2 ^ 59
def prefixEnd_5360605 : Nat := 4983230072969 + 3 ^ 40 * 5360605 * 2
def baseEnd_5360605 : Nat := 2752566963895104341984533

theorem tailTrace_5360605 : CollatzResearch.WordTrace tailWord_5360605 prefixEnd_5360605 2752566963895104341984533 := by
  unfold tailWord_5360605
  simp only [CollatzResearch.WordTrace]
  refine ⟨195517326744451078290963269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130344884496300718860642179 195517326744451078290963269)
  ·
    refine ⟨36659498764584577179555613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195517326744451078290963269 36659498764584577179555613)
    ·
      refine ⟨13747312036719216442333355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36659498764584577179555613 13747312036719216442333355)
      ·
        refine ⟨20620968055078824663500033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13747312036719216442333355 20620968055078824663500033)
        ·
          refine ⟨15465726041309118497625025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20620968055078824663500033 15465726041309118497625025)
          ·
            refine ⟨11599294530981838873218769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15465726041309118497625025 11599294530981838873218769)
            ·
              refine ⟨8699470898236379154914077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11599294530981838873218769 8699470898236379154914077)
              ·
                refine ⟨3262301586838642183092779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8699470898236379154914077 3262301586838642183092779)
                ·
                  refine ⟨4893452380257963274639169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3262301586838642183092779 4893452380257963274639169)
                  ·
                    refine ⟨3670089285193472455979377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4893452380257963274639169 3670089285193472455979377)
                    ·
                      refine ⟨2752566963895104341984533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3670089285193472455979377 2752566963895104341984533)
                      ·
                        rfl

theorem cell23_5360605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_5360605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360605 prefixEnd_5360605 := by exact prefixLift 5360605
  have htrace : WordTrace (prefixWord ++ tailWord_5360605) baseStart_5360605 baseEnd_5360605 := by
    simpa [prefixWord, tailWord_5360605, baseEnd_5360605] using wordTrace_append hprefix tailTrace_5360605
  have hstable : (prefixWord ++ tailWord_5360605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360605).length < 2 ^ (prefixWord ++ tailWord_5360605).sum := by decide
  have hdescent : baseEnd_5360605 < baseStart_5360605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360627 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 2, 8, 2]
def baseStart_5360627 : Nat := 118140960795 + 5360627 * 2 ^ 59
def prefixEnd_5360627 : Nat := 4983230072969 + 3 ^ 40 * 5360627 * 2
def baseEnd_5360627 : Nat := 2752578260469503255909431

theorem tailTrace_5360627 : CollatzResearch.WordTrace tailWord_5360627 prefixEnd_5360627 2752578260469503255909431 := by
  unfold tailWord_5360627
  simp only [CollatzResearch.WordTrace]
  refine ⟨195518129150371376048264135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130345419433580917365509423 195518129150371376048264135)
  ·
    refine ⟨293277193725557064072396203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195518129150371376048264135 293277193725557064072396203)
    ·
      refine ⟨439915790588335596108594305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293277193725557064072396203 439915790588335596108594305)
      ·
        refine ⟨329936842941251697081445729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 439915790588335596108594305 329936842941251697081445729)
        ·
          refine ⟨247452632205938772811084297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329936842941251697081445729 247452632205938772811084297)
          ·
            refine ⟨185589474154454079608313223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247452632205938772811084297 185589474154454079608313223)
            ·
              refine ⟨278384211231681119412469835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185589474154454079608313223 278384211231681119412469835)
              ·
                refine ⟨417576316847521679118704753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278384211231681119412469835 417576316847521679118704753)
                ·
                  refine ⟨313182237635641259339028565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 417576316847521679118704753 313182237635641259339028565)
                  ·
                    refine ⟨3670104347292671007879241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 313182237635641259339028565 3670104347292671007879241)
                    ·
                      refine ⟨2752578260469503255909431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3670104347292671007879241 2752578260469503255909431)
                      ·
                        rfl

theorem cell23_5360627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 8, 2].length) (baseStart_5360627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360627 prefixEnd_5360627 := by exact prefixLift 5360627
  have htrace : WordTrace (prefixWord ++ tailWord_5360627) baseStart_5360627 baseEnd_5360627 := by
    simpa [prefixWord, tailWord_5360627, baseEnd_5360627] using wordTrace_append hprefix tailTrace_5360627
  have hstable : (prefixWord ++ tailWord_5360627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360627).length < 2 ^ (prefixWord ++ tailWord_5360627).sum := by decide
  have hdescent : baseEnd_5360627 < baseStart_5360627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360638 : List Nat := [4, 2, 2, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_5360638 : Nat := 118140960795 + 5360638 * 2 ^ 59
def prefixEnd_5360638 : Nat := 4983230072969 + 3 ^ 40 * 5360638 * 2
def baseEnd_5360638 : Nat := 2752583908756702712871881

theorem tailTrace_5360638 : CollatzResearch.WordTrace tailWord_5360638 prefixEnd_5360638 2752583908756702712871881 := by
  unfold tailWord_5360638
  simp only [CollatzResearch.WordTrace]
  refine ⟨24439816294166440615864321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130345686902221016617943045 24439816294166440615864321)
  ·
    refine ⟨18329862220624830461898241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24439816294166440615864321 18329862220624830461898241)
    ·
      refine ⟨13747396665468622846423681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18329862220624830461898241 13747396665468622846423681)
      ·
        refine ⟨10310547499101467134817761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13747396665468622846423681 10310547499101467134817761)
        ·
          refine ⟨7732910624326100351113321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10310547499101467134817761 7732910624326100351113321)
          ·
            refine ⟨5799682968244575263334991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7732910624326100351113321 5799682968244575263334991)
            ·
              refine ⟨8699524452366862895002487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5799682968244575263334991 8699524452366862895002487)
              ·
                refine ⟨13049286678550294342503731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8699524452366862895002487 13049286678550294342503731)
                ·
                  refine ⟨19573930017825441513755597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13049286678550294342503731 19573930017825441513755597)
                  ·
                    refine ⟨7340223756684540567658349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19573930017825441513755597 7340223756684540567658349)
                    ·
                      refine ⟨2752583908756702712871881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7340223756684540567658349 2752583908756702712871881)
                      ·
                        rfl

theorem cell23_5360638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_5360638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360638 prefixEnd_5360638 := by exact prefixLift 5360638
  have htrace : WordTrace (prefixWord ++ tailWord_5360638) baseStart_5360638 baseEnd_5360638 := by
    simpa [prefixWord, tailWord_5360638, baseEnd_5360638] using wordTrace_append hprefix tailTrace_5360638
  have hstable : (prefixWord ++ tailWord_5360638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360638).length < 2 ^ (prefixWord ++ tailWord_5360638).sum := by decide
  have hdescent : baseEnd_5360638 < baseStart_5360638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360647 : List Nat := [1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 5]
def baseStart_5360647 : Nat := 118140960795 + 5360647 * 2 ^ 59
def prefixEnd_5360647 : Nat := 4983230072969 + 3 ^ 40 * 5360647 * 2
def baseEnd_5360647 : Nat := 2752588530082593177659339

theorem tailTrace_5360647 : CollatzResearch.WordTrace tailWord_5360647 prefixEnd_5360647 2752588530082593177659339 := by
  unfold tailWord_5360647
  simp only [CollatzResearch.WordTrace]
  refine ⟨195518858610298919463992195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130345905740199279642661463 195518858610298919463992195)
  ·
    refine ⟨293278287915448379195988293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195518858610298919463992195 293278287915448379195988293)
    ·
      refine ⟨54989678984146571099247805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 293278287915448379195988293 54989678984146571099247805)
      ·
        refine ⟨20621129619054964162217927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54989678984146571099247805 20621129619054964162217927)
        ·
          refine ⟨30931694428582446243326891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20621129619054964162217927 30931694428582446243326891)
          ·
            refine ⟨46397541642873669364990337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30931694428582446243326891 46397541642873669364990337)
            ·
              refine ⟨34798156232155252023742753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46397541642873669364990337 34798156232155252023742753)
              ·
                refine ⟨26098617174116439017807065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34798156232155252023742753 26098617174116439017807065)
                ·
                  refine ⟨19573962880587329263355299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26098617174116439017807065 19573962880587329263355299)
                  ·
                    refine ⟨29360944320880993895032949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19573962880587329263355299 29360944320880993895032949)
                    ·
                      refine ⟨2752588530082593177659339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29360944320880993895032949 2752588530082593177659339)
                      ·
                        rfl

theorem cell23_5360647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_5360647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360647 prefixEnd_5360647 := by exact prefixLift 5360647
  have htrace : WordTrace (prefixWord ++ tailWord_5360647) baseStart_5360647 baseEnd_5360647 := by
    simpa [prefixWord, tailWord_5360647, baseEnd_5360647] using wordTrace_append hprefix tailTrace_5360647
  have hstable : (prefixWord ++ tailWord_5360647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360647).length < 2 ^ (prefixWord ++ tailWord_5360647).sum := by decide
  have hdescent : baseEnd_5360647 < baseStart_5360647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360661 : List Nat := [1, 3, 2, 1, 4, 1, 1, 2, 4, 2, 2]
def baseStart_5360661 : Nat := 118140960795 + 5360661 * 2 ^ 59
def prefixEnd_5360661 : Nat := 4983230072969 + 3 ^ 40 * 5360661 * 2
def baseEnd_5360661 : Nat := 2752595718811756122884275

theorem tailTrace_5360661 : CollatzResearch.WordTrace tailWord_5360661 prefixEnd_5360661 2752595718811756122884275 := by
  unfold tailWord_5360661
  simp only [CollatzResearch.WordTrace]
  refine ⟨195519369232248199855001837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130346246154832133236667891 195519369232248199855001837)
  ·
    refine ⟨73319763462093074945625689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195519369232248199855001837 73319763462093074945625689)
    ·
      refine ⟨54989822596569806209219267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73319763462093074945625689 54989822596569806209219267)
      ·
        refine ⟨82484733894854709313828901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54989822596569806209219267 82484733894854709313828901)
        ·
          refine ⟨15465887605285257996342919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82484733894854709313828901 15465887605285257996342919)
          ·
            refine ⟨23198831407927886994514379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15465887605285257996342919 23198831407927886994514379)
            ·
              refine ⟨34798247111891830491771569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23198831407927886994514379 34798247111891830491771569)
              ·
                refine ⟨26098685333918872868828677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34798247111891830491771569 26098685333918872868828677)
                ·
                  refine ⟨4893503500109788662905377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26098685333918872868828677 4893503500109788662905377)
                  ·
                    refine ⟨3670127625082341497179033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4893503500109788662905377 3670127625082341497179033)
                    ·
                      refine ⟨2752595718811756122884275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3670127625082341497179033 2752595718811756122884275)
                      ·
                        rfl

theorem cell23_5360661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4, 2, 2].length) (baseStart_5360661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360661 prefixEnd_5360661 := by exact prefixLift 5360661
  have htrace : WordTrace (prefixWord ++ tailWord_5360661) baseStart_5360661 baseEnd_5360661 := by
    simpa [prefixWord, tailWord_5360661, baseEnd_5360661] using wordTrace_append hprefix tailTrace_5360661
  have hstable : (prefixWord ++ tailWord_5360661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360661).length < 2 ^ (prefixWord ++ tailWord_5360661).sum := by decide
  have hdescent : baseEnd_5360661 < baseStart_5360661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360754 : List Nat := [3, 2, 1, 2, 2, 1, 2, 2, 1, 4, 3]
def baseStart_5360754 : Nat := 118140960795 + 5360754 * 2 ^ 59
def prefixEnd_5360754 : Nat := 4983230072969 + 3 ^ 40 * 5360754 * 2
def baseEnd_5360754 : Nat := 2752643472512624259021347

theorem tailTrace_5360754 : CollatzResearch.WordTrace tailWord_5360754 prefixEnd_5360754 2752643472512624259021347 := by
  unfold tailWord_5360754
  simp only [CollatzResearch.WordTrace]
  refine ⟨48880690305227819184534329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130348507480607517825424877 48880690305227819184534329)
  ·
    refine ⟨36660517728920864388400747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48880690305227819184534329 36660517728920864388400747)
    ·
      refine ⟨54990776593381296582601121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36660517728920864388400747 54990776593381296582601121)
      ·
        refine ⟨41243082445035972436950841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54990776593381296582601121 41243082445035972436950841)
        ·
          refine ⟨30932311833776979327713131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41243082445035972436950841 30932311833776979327713131)
          ·
            refine ⟨46398467750665468991569697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30932311833776979327713131 46398467750665468991569697)
            ·
              refine ⟨34798850812999101743677273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46398467750665468991569697 34798850812999101743677273)
              ·
                refine ⟨26099138109749326307757955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34798850812999101743677273 26099138109749326307757955)
                ·
                  refine ⟨39148707164623989461636933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26099138109749326307757955 39148707164623989461636933)
                  ·
                    refine ⟨7340382593366998024056925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39148707164623989461636933 7340382593366998024056925)
                    ·
                      refine ⟨2752643472512624259021347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7340382593366998024056925 2752643472512624259021347)
                      ·
                        rfl

theorem cell23_5360754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_5360754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360754 prefixEnd_5360754 := by exact prefixLift 5360754
  have htrace : WordTrace (prefixWord ++ tailWord_5360754) baseStart_5360754 baseEnd_5360754 := by
    simpa [prefixWord, tailWord_5360754, baseEnd_5360754] using wordTrace_append hprefix tailTrace_5360754
  have hstable : (prefixWord ++ tailWord_5360754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360754).length < 2 ^ (prefixWord ++ tailWord_5360754).sum := by decide
  have hdescent : baseEnd_5360754 < baseStart_5360754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360761 : List Nat := [1, 2, 1, 3, 5, 1, 1, 2, 3, 4]
def baseStart_5360761 : Nat := 118140960795 + 5360761 * 2 ^ 59
def prefixEnd_5360761 : Nat := 4983230072969 + 3 ^ 40 * 5360761 * 2
def baseEnd_5360761 : Nat := 917549022292401910544605

theorem tailTrace_5360761 : CollatzResearch.WordTrace tailWord_5360761 prefixEnd_5360761 917549022292401910544605 := by
  unfold tailWord_5360761
  simp only [CollatzResearch.WordTrace]
  refine ⟨195523016531885916933642137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130348677687923944622428091 195523016531885916933642137)
  ·
    refine ⟨146642262398914437700231603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195523016531885916933642137 146642262398914437700231603)
    ·
      refine ⟨219963393598371656550347405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146642262398914437700231603 219963393598371656550347405)
      ·
        refine ⟨82486272599389371206380277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219963393598371656550347405 82486272599389371206380277)
        ·
          refine ⟨7733088056192753550598151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82486272599389371206380277 7733088056192753550598151)
          ·
            refine ⟨11599632084289130325897227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7733088056192753550598151 11599632084289130325897227)
            ·
              refine ⟨17399448126433695488845841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11599632084289130325897227 17399448126433695488845841)
              ·
                refine ⟨13049586094825271616634381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17399448126433695488845841 13049586094825271616634381)
                ·
                  refine ⟨4893594785559476856237893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13049586094825271616634381 4893594785559476856237893)
                  ·
                    refine ⟨917549022292401910544605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4893594785559476856237893 917549022292401910544605)
                    ·
                      rfl

theorem cell23_5360761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3, 4].length) (baseStart_5360761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360761 prefixEnd_5360761 := by exact prefixLift 5360761
  have htrace : WordTrace (prefixWord ++ tailWord_5360761) baseStart_5360761 baseEnd_5360761 := by
    simpa [prefixWord, tailWord_5360761, baseEnd_5360761] using wordTrace_append hprefix tailTrace_5360761
  have hstable : (prefixWord ++ tailWord_5360761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360761).length < 2 ^ (prefixWord ++ tailWord_5360761).sum := by decide
  have hdescent : baseEnd_5360761 < baseStart_5360761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360778 : List Nat := [3, 1, 2, 3, 1, 1, 4, 3, 1, 4]
def baseStart_5360778 : Nat := 118140960795 + 5360778 * 2 ^ 59
def prefixEnd_5360778 : Nat := 4983230072969 + 3 ^ 40 * 5360778 * 2
def baseEnd_5360778 : Nat := 917551932016110721707079

theorem tailTrace_5360778 : CollatzResearch.WordTrace tailWord_5360778 prefixEnd_5360778 917551932016110721707079 := by
  unfold tailWord_5360778
  simp only [CollatzResearch.WordTrace]
  refine ⟨48880909143206082209252747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130349091048549552558007325 48880909143206082209252747)
  ·
    refine ⟨73321363714809123313879121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48880909143206082209252747 73321363714809123313879121)
    ·
      refine ⟨54991022786106842485409341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73321363714809123313879121 54991022786106842485409341)
      ·
        refine ⟨20621633544790065932028503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54991022786106842485409341 20621633544790065932028503)
        ·
          refine ⟨30932450317185098898042755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20621633544790065932028503 30932450317185098898042755)
          ·
            refine ⟨46398675475777648347064133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30932450317185098898042755 46398675475777648347064133)
            ·
              refine ⟨8699751651708309065074525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46398675475777648347064133 8699751651708309065074525)
              ·
                refine ⟨3262406869390615899402947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8699751651708309065074525 3262406869390615899402947)
                ·
                  refine ⟨4893610304085923849104421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3262406869390615899402947 4893610304085923849104421)
                  ·
                    refine ⟨917551932016110721707079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4893610304085923849104421 917551932016110721707079)
                    ·
                      rfl

theorem cell23_5360778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_5360778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360778 prefixEnd_5360778 := by exact prefixLift 5360778
  have htrace : WordTrace (prefixWord ++ tailWord_5360778) baseStart_5360778 baseEnd_5360778 := by
    simpa [prefixWord, tailWord_5360778, baseEnd_5360778] using wordTrace_append hprefix tailTrace_5360778
  have hstable : (prefixWord ++ tailWord_5360778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360778).length < 2 ^ (prefixWord ++ tailWord_5360778).sum := by decide
  have hdescent : baseEnd_5360778 < baseStart_5360778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360791 : List Nat := [1, 1, 3, 3, 3, 3, 1, 2, 6]
def baseStart_5360791 : Nat := 118140960795 + 5360791 * 2 ^ 59
def prefixEnd_5360791 : Nat := 4983230072969 + 3 ^ 40 * 5360791 * 2
def baseEnd_5360791 : Nat := 305851385699648957139853

theorem tailTrace_5360791 : CollatzResearch.WordTrace tailWord_5360791 prefixEnd_5360791 305851385699648957139853 := by
  unfold tailWord_5360791
  simp only [CollatzResearch.WordTrace]
  refine ⟨195524110721777232057234227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130349407147851488038156151 195524110721777232057234227)
  ·
    refine ⟨293286166082665848085851341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195524110721777232057234227 293286166082665848085851341)
    ·
      refine ⟨109982312280999693032194253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293286166082665848085851341 109982312280999693032194253)
      ·
        refine ⟨41243367105374884887072845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109982312280999693032194253 41243367105374884887072845)
        ·
          refine ⟨15466262664515581832652317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41243367105374884887072845 15466262664515581832652317)
          ·
            refine ⟨5799848499193343187244619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15466262664515581832652317 5799848499193343187244619)
            ·
              refine ⟨8699772748790014780866929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5799848499193343187244619 8699772748790014780866929)
              ·
                refine ⟨6524829561592511085650197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8699772748790014780866929 6524829561592511085650197)
                ·
                  refine ⟨305851385699648957139853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6524829561592511085650197 305851385699648957139853)
                  ·
                    rfl

theorem cell23_5360791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 6].length) (baseStart_5360791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360791 prefixEnd_5360791 := by exact prefixLift 5360791
  have htrace : WordTrace (prefixWord ++ tailWord_5360791) baseStart_5360791 baseEnd_5360791 := by
    simpa [prefixWord, tailWord_5360791, baseEnd_5360791] using wordTrace_append hprefix tailTrace_5360791
  have hstable : (prefixWord ++ tailWord_5360791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360791).length < 2 ^ (prefixWord ++ tailWord_5360791).sum := by decide
  have hdescent : baseEnd_5360791 < baseStart_5360791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360794 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6]
def baseStart_5360794 : Nat := 118140960795 + 5360794 * 2 ^ 59
def prefixEnd_5360794 : Nat := 4983230072969 + 3 ^ 40 * 5360794 * 2
def baseEnd_5360794 : Nat := 2752664011738804102521163

theorem tailTrace_5360794 : CollatzResearch.WordTrace tailWord_5360794 prefixEnd_5360794 2752664011738804102521163 := by
  unfold tailWord_5360794
  simp only [CollatzResearch.WordTrace]
  refine ⟨48881055035191590892398359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130349480093844242379728957 48881055035191590892398359)
  ·
    refine ⟨73321582552787386338597539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48881055035191590892398359 73321582552787386338597539)
    ·
      refine ⟨109982373829181079507896309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73321582552787386338597539 109982373829181079507896309)
      ·
        refine ⟨10310847546485726203865279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109982373829181079507896309 10310847546485726203865279)
        ·
          refine ⟨15466271319728589305797919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10310847546485726203865279 15466271319728589305797919)
          ·
            refine ⟨23199406979592883958696879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15466271319728589305797919 23199406979592883958696879)
            ·
              refine ⟨34799110469389325938045319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23199406979592883958696879 34799110469389325938045319)
              ·
                refine ⟨52198665704083988907067979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34799110469389325938045319 52198665704083988907067979)
                ·
                  refine ⟨78297998556125983360601969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52198665704083988907067979 78297998556125983360601969)
                  ·
                    refine ⟨58723498917094487520451477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78297998556125983360601969 58723498917094487520451477)
                    ·
                      refine ⟨2752664011738804102521163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58723498917094487520451477 2752664011738804102521163)
                      ·
                        rfl

theorem cell23_5360794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_5360794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360794 prefixEnd_5360794 := by exact prefixLift 5360794
  have htrace : WordTrace (prefixWord ++ tailWord_5360794) baseStart_5360794 baseEnd_5360794 := by
    simpa [prefixWord, tailWord_5360794, baseEnd_5360794] using wordTrace_append hprefix tailTrace_5360794
  have hstable : (prefixWord ++ tailWord_5360794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360794).length < 2 ^ (prefixWord ++ tailWord_5360794).sum := by decide
  have hdescent : baseEnd_5360794 < baseStart_5360794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360852 : List Nat := [2, 4, 1, 4, 1, 2, 1, 1, 3, 1, 3]
def baseStart_5360852 : Nat := 118140960795 + 5360852 * 2 ^ 59
def prefixEnd_5360852 : Nat := 4983230072969 + 3 ^ 40 * 5360852 * 2
def baseEnd_5360852 : Nat := 2752693793616764875595897

theorem tailTrace_5360852 : CollatzResearch.WordTrace tailWord_5360852 prefixEnd_5360852 2752693793616764875595897 := by
  unfold tailWord_5360852
  simp only [CollatzResearch.WordTrace]
  refine ⟨97763167787278119737602405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130350890383037492983469873 97763167787278119737602405)
  ·
    refine ⟨18330593960114647450800451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97763167787278119737602405 18330593960114647450800451)
    ·
      refine ⟨27495890940171971176200677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18330593960114647450800451 27495890940171971176200677)
      ·
        refine ⟨5155479551282244595537627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27495890940171971176200677 5155479551282244595537627)
        ·
          refine ⟨7733219326923366893306441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5155479551282244595537627 7733219326923366893306441)
          ·
            refine ⟨5799914495192525169979831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7733219326923366893306441 5799914495192525169979831)
            ·
              refine ⟨8699871742788787754969747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5799914495192525169979831 8699871742788787754969747)
              ·
                refine ⟨13049807614183181632454621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8699871742788787754969747 13049807614183181632454621)
                ·
                  refine ⟨4893677855318693112170483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13049807614183181632454621 4893677855318693112170483)
                  ·
                    refine ⟨7340516782978039668255725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4893677855318693112170483 7340516782978039668255725)
                    ·
                      refine ⟨2752693793616764875595897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7340516782978039668255725 2752693793616764875595897)
                      ·
                        rfl

theorem cell23_5360852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_5360852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360852 prefixEnd_5360852 := by exact prefixLift 5360852
  have htrace : WordTrace (prefixWord ++ tailWord_5360852) baseStart_5360852 baseEnd_5360852 := by
    simpa [prefixWord, tailWord_5360852, baseEnd_5360852] using wordTrace_append hprefix tailTrace_5360852
  have hstable : (prefixWord ++ tailWord_5360852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360852).length < 2 ^ (prefixWord ++ tailWord_5360852).sum := by decide
  have hdescent : baseEnd_5360852 < baseStart_5360852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360864 : List Nat := [2, 1, 1, 3, 1, 5, 2, 8]
def baseStart_5360864 : Nat := 118140960795 + 5360864 * 2 ^ 59
def prefixEnd_5360864 : Nat := 4983230072969 + 3 ^ 40 * 5360864 * 2
def baseEnd_5360864 : Nat := 101951850199430326986883

theorem tailTrace_5360864 : CollatzResearch.WordTrace tailWord_5360864 prefixEnd_5360864 101951850199430326986883 := by
  unfold tailWord_5360864
  simp only [CollatzResearch.WordTrace]
  refine ⟨97763386625256382762320823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130351182167008510349761097 97763386625256382762320823)
  ·
    refine ⟨146645079937884574143481235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97763386625256382762320823 146645079937884574143481235)
    ·
      refine ⟨219967619906826861215221853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146645079937884574143481235 219967619906826861215221853)
      ·
        refine ⟨82487857465060072955708195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219967619906826861215221853 82487857465060072955708195)
        ·
          refine ⟨123731786197590109433562293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82487857465060072955708195 123731786197590109433562293)
          ·
            refine ⟨11599854956024072759396465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 123731786197590109433562293 11599854956024072759396465)
            ·
              refine ⟨8699891217018054569547349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11599854956024072759396465 8699891217018054569547349)
              ·
                refine ⟨101951850199430326986883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8699891217018054569547349 101951850199430326986883)
                ·
                  rfl

theorem cell23_5360864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 8].length) (baseStart_5360864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360864 prefixEnd_5360864 := by exact prefixLift 5360864
  have htrace : WordTrace (prefixWord ++ tailWord_5360864) baseStart_5360864 baseEnd_5360864 := by
    simpa [prefixWord, tailWord_5360864, baseEnd_5360864] using wordTrace_append hprefix tailTrace_5360864
  have hstable : (prefixWord ++ tailWord_5360864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360864).length < 2 ^ (prefixWord ++ tailWord_5360864).sum := by decide
  have hdescent : baseEnd_5360864 < baseStart_5360864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360868 : List Nat := [2, 3, 1, 1, 1, 2, 6, 1, 2, 4]
def baseStart_5360868 : Nat := 118140960795 + 5360868 * 2 ^ 59
def prefixEnd_5360868 : Nat := 4983230072969 + 3 ^ 40 * 5360868 * 2
def baseEnd_5360868 : Nat := 917567336435745604331941

theorem tailTrace_5360868 : CollatzResearch.WordTrace tailWord_5360868 prefixEnd_5360868 917567336435745604331941 := by
  unfold tailWord_5360868
  simp only [CollatzResearch.WordTrace]
  refine ⟨97763459571249137103893629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130351279428332182805191505 97763459571249137103893629)
  ·
    refine ⟨36661297339218426413960111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97763459571249137103893629 36661297339218426413960111)
    ·
      refine ⟨54991946008827639620940167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36661297339218426413960111 54991946008827639620940167)
      ·
        refine ⟨82487919013241459431410251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54991946008827639620940167 82487919013241459431410251)
        ·
          refine ⟨123731878519862189147115377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82487919013241459431410251 123731878519862189147115377)
          ·
            refine ⟨92798908889896641860336533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123731878519862189147115377 92798908889896641860336533)
            ·
              refine ⟨4349948854213905087203275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 92798908889896641860336533 4349948854213905087203275)
              ·
                refine ⟨6524923281320857630804913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4349948854213905087203275 6524923281320857630804913)
                ·
                  refine ⟨4893692460990643223103685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6524923281320857630804913 4893692460990643223103685)
                  ·
                    refine ⟨917567336435745604331941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4893692460990643223103685 917567336435745604331941)
                    ·
                      rfl

theorem cell23_5360868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_5360868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360868 prefixEnd_5360868 := by exact prefixLift 5360868
  have htrace : WordTrace (prefixWord ++ tailWord_5360868) baseStart_5360868 baseEnd_5360868 := by
    simpa [prefixWord, tailWord_5360868, baseEnd_5360868] using wordTrace_append hprefix tailTrace_5360868
  have hstable : (prefixWord ++ tailWord_5360868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360868).length < 2 ^ (prefixWord ++ tailWord_5360868).sum := by decide
  have hdescent : baseEnd_5360868 < baseStart_5360868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360878 : List Nat := [4, 1, 2, 1, 1, 1, 5, 2, 1, 2, 3]
def baseStart_5360878 : Nat := 118140960795 + 5360878 * 2 ^ 59
def prefixEnd_5360878 : Nat := 4983230072969 + 3 ^ 40 * 5360878 * 2
def baseEnd_5360878 : Nat := 2752707144113781773870777

theorem tailTrace_5360878 : CollatzResearch.WordTrace tailWord_5360878 prefixEnd_5360878 2752707144113781773870777 := by
  unfold tailWord_5360878
  simp only [CollatzResearch.WordTrace]
  refine ⟨24440910484057755739456411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130351522581641363943767525 24440910484057755739456411)
  ·
    refine ⟨36661365726086633609184617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24440910484057755739456411 36661365726086633609184617)
    ·
      refine ⟨27496024294564975206888463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36661365726086633609184617 27496024294564975206888463)
      ·
        refine ⟨41244036441847462810332695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27496024294564975206888463 41244036441847462810332695)
        ·
          refine ⟨61866054662771194215499043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41244036441847462810332695 61866054662771194215499043)
          ·
            refine ⟨92799081994156791323248565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61866054662771194215499043 92799081994156791323248565)
            ·
              refine ⟨8699913936952199186554553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92799081994156791323248565 8699913936952199186554553)
              ·
                refine ⟨6524935452714149389915915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8699913936952199186554553 6524935452714149389915915)
                ·
                  refine ⟨9787403179071224084873873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6524935452714149389915915 9787403179071224084873873)
                  ·
                    refine ⟨7340552384303418063655405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9787403179071224084873873 7340552384303418063655405)
                    ·
                      refine ⟨2752707144113781773870777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7340552384303418063655405 2752707144113781773870777)
                      ·
                        rfl

theorem cell23_5360878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_5360878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360878 prefixEnd_5360878 := by exact prefixLift 5360878
  have htrace : WordTrace (prefixWord ++ tailWord_5360878) baseStart_5360878 baseEnd_5360878 := by
    simpa [prefixWord, tailWord_5360878, baseEnd_5360878] using wordTrace_append hprefix tailTrace_5360878
  have hstable : (prefixWord ++ tailWord_5360878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360878).length < 2 ^ (prefixWord ++ tailWord_5360878).sum := by decide
  have hdescent : baseEnd_5360878 < baseStart_5360878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360908 : List Nat := [2, 2, 1, 2, 2, 3, 1, 4, 2, 1, 3]
def baseStart_5360908 : Nat := 118140960795 + 5360908 * 2 ^ 59
def prefixEnd_5360908 : Nat := 4983230072969 + 3 ^ 40 * 5360908 * 2
def baseEnd_5360908 : Nat := 2752722548533416656495639

theorem tailTrace_5360908 : CollatzResearch.WordTrace tailWord_5360908 prefixEnd_5360908 2752722548533416656495639 := by
  unfold tailWord_5360908
  simp only [CollatzResearch.WordTrace]
  refine ⟨97764189031176680519621689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130352252041568907359495585 97764189031176680519621689)
  ·
    refine ⟨73323141773382510389716267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97764189031176680519621689 73323141773382510389716267)
    ·
      refine ⟨109984712660073765584574401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73323141773382510389716267 109984712660073765584574401)
      ·
        refine ⟨82488534495055324188430801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109984712660073765584574401 82488534495055324188430801)
        ·
          refine ⟨61866400871291493141323101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82488534495055324188430801 61866400871291493141323101)
          ·
            refine ⟨23199900326734309927996163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61866400871291493141323101 23199900326734309927996163)
            ·
              refine ⟨34799850490101464891994245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23199900326734309927996163 34799850490101464891994245)
              ·
                refine ⟨6524971966894024667248921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34799850490101464891994245 6524971966894024667248921)
                ·
                  refine ⟨4893728975170518500436691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6524971966894024667248921 4893728975170518500436691)
                  ·
                    refine ⟨7340593462755777750655037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4893728975170518500436691 7340593462755777750655037)
                    ·
                      refine ⟨2752722548533416656495639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7340593462755777750655037 2752722548533416656495639)
                      ·
                        rfl

theorem cell23_5360908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_5360908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360908 prefixEnd_5360908 := by exact prefixLift 5360908
  have htrace : WordTrace (prefixWord ++ tailWord_5360908) baseStart_5360908 baseEnd_5360908 := by
    simpa [prefixWord, tailWord_5360908, baseEnd_5360908] using wordTrace_append hprefix tailTrace_5360908
  have hstable : (prefixWord ++ tailWord_5360908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360908).length < 2 ^ (prefixWord ++ tailWord_5360908).sum := by decide
  have hdescent : baseEnd_5360908 < baseStart_5360908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360924 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 1, 8]
def baseStart_5360924 : Nat := 118140960795 + 5360924 * 2 ^ 59
def prefixEnd_5360924 : Nat := 4983230072969 + 3 ^ 40 * 5360924 * 2
def baseEnd_5360924 : Nat := 917576921407962864631855

theorem tailTrace_5360924 : CollatzResearch.WordTrace tailWord_5360924 prefixEnd_5360924 917576921407962864631855 := by
  unfold tailWord_5360924
  simp only [CollatzResearch.WordTrace]
  refine ⟨97764480815147697885912913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130352641086863597181217217 97764480815147697885912913)
  ·
    refine ⟨73323360611360773414434685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97764480815147697885912913 73323360611360773414434685)
    ·
      refine ⟨27496260229260290030413007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73323360611360773414434685 27496260229260290030413007)
      ·
        refine ⟨41244390343890435045619511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27496260229260290030413007 41244390343890435045619511)
        ·
          refine ⟨61866585515835652568429267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41244390343890435045619511 61866585515835652568429267)
          ·
            refine ⟨92799878273753478852643901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61866585515835652568429267 92799878273753478852643901)
            ·
              refine ⟨34799954352657554569741463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92799878273753478852643901 34799954352657554569741463)
              ·
                refine ⟨52199931528986331854612195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34799954352657554569741463 52199931528986331854612195)
                ·
                  refine ⟨78299897293479497781918293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52199931528986331854612195 78299897293479497781918293)
                  ·
                    refine ⟨917576921407962864631855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78299897293479497781918293 917576921407962864631855)
                    ·
                      rfl

theorem cell23_5360924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_5360924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360924 prefixEnd_5360924 := by exact prefixLift 5360924
  have htrace : WordTrace (prefixWord ++ tailWord_5360924) baseStart_5360924 baseEnd_5360924 := by
    simpa [prefixWord, tailWord_5360924, baseEnd_5360924] using wordTrace_append hprefix tailTrace_5360924
  have hstable : (prefixWord ++ tailWord_5360924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360924).length < 2 ^ (prefixWord ++ tailWord_5360924).sum := by decide
  have hdescent : baseEnd_5360924 < baseStart_5360924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360925 : List Nat := [1, 4, 2, 3, 1, 1, 2, 3, 2, 1, 3]
def baseStart_5360925 : Nat := 118140960795 + 5360925 * 2 ^ 59
def prefixEnd_5360925 : Nat := 4983230072969 + 3 ^ 40 * 5360925 * 2
def baseEnd_5360925 : Nat := 2752731277704543089983061

theorem tailTrace_5360925 : CollatzResearch.WordTrace tailWord_5360925 prefixEnd_5360925 2752731277704543089983061 := by
  unfold tailWord_5360925
  simp only [CollatzResearch.WordTrace]
  refine ⟨195528998103291772942612229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130352665402194515295074819 195528998103291772942612229)
  ·
    refine ⟨36661687144367207426739793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195528998103291772942612229 36661687144367207426739793)
    ·
      refine ⟨27496265358275405570054845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36661687144367207426739793 27496265358275405570054845)
      ·
        refine ⟨10311099509353277088770567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27496265358275405570054845 10311099509353277088770567)
        ·
          refine ⟨15466649264029915633155851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10311099509353277088770567 15466649264029915633155851)
          ·
            refine ⟨23199973896044873449733777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15466649264029915633155851 23199973896044873449733777)
            ·
              refine ⟨17399980422033655087300333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23199973896044873449733777 17399980422033655087300333)
              ·
                refine ⟨6524992658262620657737625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17399980422033655087300333 6524992658262620657737625)
                ·
                  refine ⟨4893744493696965493303219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6524992658262620657737625 4893744493696965493303219)
                  ·
                    refine ⟨7340616740545448239954829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4893744493696965493303219 7340616740545448239954829)
                    ·
                      refine ⟨2752731277704543089983061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7340616740545448239954829 2752731277704543089983061)
                      ·
                        rfl

theorem cell23_5360925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_5360925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360925 prefixEnd_5360925 := by exact prefixLift 5360925
  have htrace : WordTrace (prefixWord ++ tailWord_5360925) baseStart_5360925 baseEnd_5360925 := by
    simpa [prefixWord, tailWord_5360925, baseEnd_5360925] using wordTrace_append hprefix tailTrace_5360925
  have hstable : (prefixWord ++ tailWord_5360925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360925).length < 2 ^ (prefixWord ++ tailWord_5360925).sum := by decide
  have hdescent : baseEnd_5360925 < baseStart_5360925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360944 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 4]
def baseStart_5360944 : Nat := 118140960795 + 5360944 * 2 ^ 59
def prefixEnd_5360944 : Nat := 4983230072969 + 3 ^ 40 * 5360944 * 2
def baseEnd_5360944 : Nat := 2752741033836978515645473

theorem tailTrace_5360944 : CollatzResearch.WordTrace tailWord_5360944 prefixEnd_5360944 2752741033836978515645473 := by
  unfold tailWord_5360944
  simp only [CollatzResearch.WordTrace]
  refine ⟨97764845545111469593776943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130353127393481959458369257 97764845545111469593776943)
  ·
    refine ⟨146647268317667204390665415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97764845545111469593776943 146647268317667204390665415)
    ·
      refine ⟨219970902476500806585998123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146647268317667204390665415 219970902476500806585998123)
      ·
        refine ⟨329956353714751209878997185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219970902476500806585998123 329956353714751209878997185)
        ·
          refine ⟨247467265286063407409247889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329956353714751209878997185 247467265286063407409247889)
          ·
            refine ⟨185600448964547555556935917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247467265286063407409247889 185600448964547555556935917)
            ·
              refine ⟨69600168361705333333850969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185600448964547555556935917 69600168361705333333850969)
              ·
                refine ⟨52200126271279000000388227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69600168361705333333850969 52200126271279000000388227)
                ·
                  refine ⟨78300189406918500000582341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52200126271279000000388227 78300189406918500000582341)
                  ·
                    refine ⟨14681285513797218750109189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78300189406918500000582341 14681285513797218750109189)
                    ·
                      refine ⟨2752741033836978515645473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14681285513797218750109189 2752741033836978515645473)
                      ·
                        rfl

theorem cell23_5360944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 4].length) (baseStart_5360944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360944 prefixEnd_5360944 := by exact prefixLift 5360944
  have htrace : WordTrace (prefixWord ++ tailWord_5360944) baseStart_5360944 baseEnd_5360944 := by
    simpa [prefixWord, tailWord_5360944, baseEnd_5360944] using wordTrace_append hprefix tailTrace_5360944
  have hstable : (prefixWord ++ tailWord_5360944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360944).length < 2 ^ (prefixWord ++ tailWord_5360944).sum := by decide
  have hdescent : baseEnd_5360944 < baseStart_5360944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360954 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 9]
def baseStart_5360954 : Nat := 118140960795 + 5360954 * 2 ^ 59
def prefixEnd_5360954 : Nat := 4983230072969 + 3 ^ 40 * 5360954 * 2
def baseEnd_5360954 : Nat := 305860685404835941835603

theorem tailTrace_5360954 : CollatzResearch.WordTrace tailWord_5360954 prefixEnd_5360954 305860685404835941835603 := by
  unfold tailWord_5360954
  simp only [CollatzResearch.WordTrace]
  refine ⟨48882513955046677723854479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130353370546791140596945277 48882513955046677723854479)
  ·
    refine ⟨73323770932570016585781719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48882513955046677723854479 73323770932570016585781719)
    ·
      refine ⟨109985656398855024878672579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73323770932570016585781719 109985656398855024878672579)
      ·
        refine ⟨164978484598282537318008869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109985656398855024878672579 164978484598282537318008869)
        ·
          refine ⟨30933465862177975747126663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164978484598282537318008869 30933465862177975747126663)
          ·
            refine ⟨46400198793266963620689995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30933465862177975747126663 46400198793266963620689995)
            ·
              refine ⟨69600298189900445431034993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46400198793266963620689995 69600298189900445431034993)
              ·
                refine ⟨52200223642425334073276245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69600298189900445431034993 52200223642425334073276245)
                ·
                  refine ⟨305860685404835941835603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52200223642425334073276245 305860685404835941835603)
                  ·
                    rfl

theorem cell23_5360954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 9].length) (baseStart_5360954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360954 prefixEnd_5360954 := by exact prefixLift 5360954
  have htrace : WordTrace (prefixWord ++ tailWord_5360954) baseStart_5360954 baseEnd_5360954 := by
    simpa [prefixWord, tailWord_5360954, baseEnd_5360954] using wordTrace_append hprefix tailTrace_5360954
  have hstable : (prefixWord ++ tailWord_5360954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360954).length < 2 ^ (prefixWord ++ tailWord_5360954).sum := by decide
  have hdescent : baseEnd_5360954 < baseStart_5360954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5360984 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 3, 7]
def baseStart_5360984 : Nat := 118140960795 + 5360984 * 2 ^ 59
def prefixEnd_5360984 : Nat := 4983230072969 + 3 ^ 40 * 5360984 * 2
def baseEnd_5360984 : Nat := 917587191021052786381763

theorem tailTrace_5360984 : CollatzResearch.WordTrace tailWord_5360984 prefixEnd_5360984 917587191021052786381763 := by
  unfold tailWord_5360984
  simp only [CollatzResearch.WordTrace]
  refine ⟨97765575005039013009505003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130354100006718684012673337 97765575005039013009505003)
  ·
    refine ⟨146648362507558519514257505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97765575005039013009505003 146648362507558519514257505)
    ·
      refine ⟨109986271880668889635693129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146648362507558519514257505 109986271880668889635693129)
      ·
        refine ⟨82489703910501667226769847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109986271880668889635693129 82489703910501667226769847)
        ·
          refine ⟨123734555865752500840154771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82489703910501667226769847 123734555865752500840154771)
          ·
            refine ⟨185601833798628751260232157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123734555865752500840154771 185601833798628751260232157)
            ·
              refine ⟨69600687674485781722587059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185601833798628751260232157 69600687674485781722587059)
              ·
                refine ⟨104401031511728672583880589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69600687674485781722587059 104401031511728672583880589)
                ·
                  refine ⟨39150386816898252218955221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104401031511728672583880589 39150386816898252218955221)
                  ·
                    refine ⟨917587191021052786381763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39150386816898252218955221 917587191021052786381763)
                    ·
                      rfl

theorem cell23_5360984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_5360984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5360984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5360984 prefixEnd_5360984 := by exact prefixLift 5360984
  have htrace : WordTrace (prefixWord ++ tailWord_5360984) baseStart_5360984 baseEnd_5360984 := by
    simpa [prefixWord, tailWord_5360984, baseEnd_5360984] using wordTrace_append hprefix tailTrace_5360984
  have hstable : (prefixWord ++ tailWord_5360984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5360984).length < 2 ^ (prefixWord ++ tailWord_5360984).sum := by decide
  have hdescent : baseEnd_5360984 < baseStart_5360984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5360984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361005 : List Nat := [1, 5, 1, 1, 1, 5, 1, 3, 5]
def baseStart_5361005 : Nat := 118140960795 + 5361005 * 2 ^ 59
def prefixEnd_5361005 : Nat := 4983230072969 + 3 ^ 40 * 5361005 * 2
def baseEnd_5361005 : Nat := 305863595128544752998077

theorem tailTrace_5361005 : CollatzResearch.WordTrace tailWord_5361005 prefixEnd_5361005 305863595128544752998077 := by
  unfold tailWord_5361005
  simp only [CollatzResearch.WordTrace]
  refine ⟨195531915943001946605524469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130354610628667964403682979 195531915943001946605524469)
  ·
    refine ⟨18331117119656432494267919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 195531915943001946605524469 18331117119656432494267919)
    ·
      refine ⟨27496675679484648741401879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18331117119656432494267919 27496675679484648741401879)
      ·
        refine ⟨41245013519226973112102819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27496675679484648741401879 41245013519226973112102819)
        ·
          refine ⟨61867520278840459668154229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41245013519226973112102819 61867520278840459668154229)
          ·
            refine ⟨5800080026141293093889459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61867520278840459668154229 5800080026141293093889459)
            ·
              refine ⟨8700120039211939640834189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5800080026141293093889459 8700120039211939640834189)
              ·
                refine ⟨3262545014704477365312821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8700120039211939640834189 3262545014704477365312821)
                ·
                  refine ⟨305863595128544752998077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3262545014704477365312821 305863595128544752998077)
                  ·
                    rfl

theorem cell23_5361005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_5361005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361005 prefixEnd_5361005 := by exact prefixLift 5361005
  have htrace : WordTrace (prefixWord ++ tailWord_5361005) baseStart_5361005 baseEnd_5361005 := by
    simpa [prefixWord, tailWord_5361005, baseEnd_5361005] using wordTrace_append hprefix tailTrace_5361005
  have hstable : (prefixWord ++ tailWord_5361005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361005).length < 2 ^ (prefixWord ++ tailWord_5361005).sum := by decide
  have hdescent : baseEnd_5361005 < baseStart_5361005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361022 : List Nat := [4, 2, 3, 2, 1, 2, 1, 1, 7]
def baseStart_5361022 : Nat := 118140960795 + 5361022 * 2 ^ 59
def prefixEnd_5361022 : Nat := 4983230072969 + 3 ^ 40 * 5361022 * 2
def baseEnd_5361022 : Nat := 305864565036447690052235

theorem tailTrace_5361022 : CollatzResearch.WordTrace tailWord_5361022 prefixEnd_5361022 305864565036447690052235 := by
  unfold tailWord_5361022
  simp only [CollatzResearch.WordTrace]
  refine ⟨24441566997992544813611665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130355023989293572339262213 24441566997992544813611665)
  ·
    refine ⟨18331175248494408610208749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24441566997992544813611665 18331175248494408610208749)
    ·
      refine ⟨6874190718185403228828281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18331175248494408610208749 6874190718185403228828281)
      ·
        refine ⟨5155643038639052421621211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6874190718185403228828281 5155643038639052421621211)
        ·
          refine ⟨7733464557958578632431817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5155643038639052421621211 7733464557958578632431817)
          ·
            refine ⟨5800098418468933974323863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7733464557958578632431817 5800098418468933974323863)
            ·
              refine ⟨8700147627703400961485795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5800098418468933974323863 8700147627703400961485795)
              ·
                refine ⟨13050221441555101442228693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8700147627703400961485795 13050221441555101442228693)
                ·
                  refine ⟨305864565036447690052235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13050221441555101442228693 305864565036447690052235)
                  ·
                    rfl

theorem cell23_5361022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_5361022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361022 prefixEnd_5361022 := by exact prefixLift 5361022
  have htrace : WordTrace (prefixWord ++ tailWord_5361022) baseStart_5361022 baseEnd_5361022 := by
    simpa [prefixWord, tailWord_5361022, baseEnd_5361022] using wordTrace_append hprefix tailTrace_5361022
  have hstable : (prefixWord ++ tailWord_5361022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361022).length < 2 ^ (prefixWord ++ tailWord_5361022).sum := by decide
  have hdescent : baseEnd_5361022 < baseStart_5361022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361091 : List Nat := [1, 1, 1, 3, 1, 1, 5, 2, 3, 5]
def baseStart_5361091 : Nat := 118140960795 + 5361091 * 2 ^ 59
def prefixEnd_5361091 : Nat := 4983230072969 + 3 ^ 40 * 5361091 * 2
def baseEnd_5361091 : Nat := 917605505164396480169099

theorem tailTrace_5361091 : CollatzResearch.WordTrace tailWord_5361091 prefixEnd_5361091 917605505164396480169099 := by
  unfold tailWord_5361091
  simp only [CollatzResearch.WordTrace]
  refine ⟨195535052620690383293155127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130356701747126922195436751 195535052620690383293155127)
  ·
    refine ⟨293302578931035574939732691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195535052620690383293155127 293302578931035574939732691)
    ·
      refine ⟨439953868396553362409599037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293302578931035574939732691 439953868396553362409599037)
      ·
        refine ⟨164982700648707510903599639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 439953868396553362409599037 164982700648707510903599639)
        ·
          refine ⟨247474050973061266355399459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164982700648707510903599639 247474050973061266355399459)
          ·
            refine ⟨371211076459591899533099189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247474050973061266355399459 371211076459591899533099189)
            ·
              refine ⟨34801038418086740581228049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 371211076459591899533099189 34801038418086740581228049)
              ·
                refine ⟨26100778813565055435921037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34801038418086740581228049 26100778813565055435921037)
                ·
                  refine ⟨9787792055086895788470389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26100778813565055435921037 9787792055086895788470389)
                  ·
                    refine ⟨917605505164396480169099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9787792055086895788470389 917605505164396480169099)
                    ·
                      rfl

theorem cell23_5361091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 5].length) (baseStart_5361091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361091 prefixEnd_5361091 := by exact prefixLift 5361091
  have htrace : WordTrace (prefixWord ++ tailWord_5361091) baseStart_5361091 baseEnd_5361091 := by
    simpa [prefixWord, tailWord_5361091, baseEnd_5361091] using wordTrace_append hprefix tailTrace_5361091
  have hstable : (prefixWord ++ tailWord_5361091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361091).length < 2 ^ (prefixWord ++ tailWord_5361091).sum := by decide
  have hdescent : baseEnd_5361091 < baseStart_5361091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361125 : List Nat := [1, 3, 1, 5, 1, 2, 1, 3, 1, 5]
def baseStart_5361125 : Nat := 118140960795 + 5361125 * 2 ^ 59
def prefixEnd_5361125 : Nat := 4983230072969 + 3 ^ 40 * 5361125 * 2
def baseEnd_5361125 : Nat := 917611324611814102494047

theorem tailTrace_5361125 : CollatzResearch.WordTrace tailWord_5361125 prefixEnd_5361125 917611324611814102494047 := by
  unfold tailWord_5361125
  simp only [CollatzResearch.WordTrace]
  refine ⟨195536292702567207099892829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130357528468378138066595219 195536292702567207099892829)
  ·
    refine ⟨73326109763462702662459811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195536292702567207099892829 73326109763462702662459811)
    ·
      refine ⟨109989164645194053993689717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73326109763462702662459811 109989164645194053993689717)
      ·
        refine ⟨10311484185486942561908411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109989164645194053993689717 10311484185486942561908411)
        ·
          refine ⟨15467226278230413842862617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10311484185486942561908411 15467226278230413842862617)
          ·
            refine ⟨11600419708672810382146963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15467226278230413842862617 11600419708672810382146963)
            ·
              refine ⟨17400629563009215573220445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11600419708672810382146963 17400629563009215573220445)
              ·
                refine ⟨6525236086128455839957667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17400629563009215573220445 6525236086128455839957667)
                ·
                  refine ⟨9787854129192683759936501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6525236086128455839957667 9787854129192683759936501)
                  ·
                    refine ⟨917611324611814102494047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9787854129192683759936501 917611324611814102494047)
                    ·
                      rfl

theorem cell23_5361125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 5].length) (baseStart_5361125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361125 prefixEnd_5361125 := by exact prefixLift 5361125
  have htrace : WordTrace (prefixWord ++ tailWord_5361125) baseStart_5361125 baseEnd_5361125 := by
    simpa [prefixWord, tailWord_5361125, baseEnd_5361125] using wordTrace_append hprefix tailTrace_5361125
  have hstable : (prefixWord ++ tailWord_5361125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361125).length < 2 ^ (prefixWord ++ tailWord_5361125).sum := by decide
  have hdescent : baseEnd_5361125 < baseStart_5361125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361148 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 5, 2, 3]
def baseStart_5361148 : Nat := 118140960795 + 5361148 * 2 ^ 59
def prefixEnd_5361148 : Nat := 4983230072969 + 3 ^ 40 * 5361148 * 2
def baseEnd_5361148 : Nat := 2752845783890495717494535

theorem tailTrace_5361148 : CollatzResearch.WordTrace tailWord_5361148 prefixEnd_5361148 2752845783890495717494535 := by
  unfold tailWord_5361148
  simp only [CollatzResearch.WordTrace]
  refine ⟨97768565790741941013990049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130358087720989254685320065 97768565790741941013990049)
  ·
    refine ⟨73326424343056455760492537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97768565790741941013990049 73326424343056455760492537)
    ·
      refine ⟨54994818257292341820369403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73326424343056455760492537 54994818257292341820369403)
      ·
        refine ⟨82492227385938512730554105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54994818257292341820369403 82492227385938512730554105)
        ·
          refine ⟨61869170539453884547915579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82492227385938512730554105 61869170539453884547915579)
          ·
            refine ⟨92803755809180826821873369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61869170539453884547915579 92803755809180826821873369)
            ·
              refine ⟨69602816856885620116405027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92803755809180826821873369 69602816856885620116405027)
              ·
                refine ⟨104404225285328430174607541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69602816856885620116405027 104404225285328430174607541)
                ·
                  refine ⟨9787896120499540328869457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104404225285328430174607541 9787896120499540328869457)
                  ·
                    refine ⟨7340922090374655246652093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9787896120499540328869457 7340922090374655246652093)
                    ·
                      refine ⟨2752845783890495717494535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7340922090374655246652093 2752845783890495717494535)
                      ·
                        rfl

theorem cell23_5361148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_5361148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361148 prefixEnd_5361148 := by exact prefixLift 5361148
  have htrace : WordTrace (prefixWord ++ tailWord_5361148) baseStart_5361148 baseEnd_5361148 := by
    simpa [prefixWord, tailWord_5361148, baseEnd_5361148] using wordTrace_append hprefix tailTrace_5361148
  have hstable : (prefixWord ++ tailWord_5361148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361148).length < 2 ^ (prefixWord ++ tailWord_5361148).sum := by decide
  have hdescent : baseEnd_5361148 < baseStart_5361148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361162 : List Nat := [3, 1, 2, 2, 2, 2, 2, 2, 3, 2, 2]
def baseStart_5361162 : Nat := 118140960795 + 5361162 * 2 ^ 59
def prefixEnd_5361162 : Nat := 4983230072969 + 3 ^ 40 * 5361162 * 2
def baseEnd_5361162 : Nat := 2752852972619658662719471

theorem tailTrace_5361162 : CollatzResearch.WordTrace tailWord_5361162 prefixEnd_5361162 2752852972619658662719471 := by
  unfold tailWord_5361162
  simp only [CollatzResearch.WordTrace]
  refine ⟨48884410550858290604747435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130358428135622108279326493 48884410550858290604747435)
  ·
    refine ⟨73326615826287435907121153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48884410550858290604747435 73326615826287435907121153)
    ·
      refine ⟨54994961869715576930340865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73326615826287435907121153 54994961869715576930340865)
      ·
        refine ⟨41246221402286682697755649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54994961869715576930340865 41246221402286682697755649)
        ·
          refine ⟨30934666051715012023316737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41246221402286682697755649 30934666051715012023316737)
          ·
            refine ⟨23200999538786259017487553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30934666051715012023316737 23200999538786259017487553)
            ·
              refine ⟨17400749654089694263115665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23200999538786259017487553 17400749654089694263115665)
              ·
                refine ⟨13050562240567270697336749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17400749654089694263115665 13050562240567270697336749)
                ·
                  refine ⟨4893960840212726511501281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13050562240567270697336749 4893960840212726511501281)
                  ·
                    refine ⟨3670470630159544883625961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4893960840212726511501281 3670470630159544883625961)
                    ·
                      refine ⟨2752852972619658662719471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3670470630159544883625961 2752852972619658662719471)
                      ·
                        rfl

theorem cell23_5361162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_5361162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361162 prefixEnd_5361162 := by exact prefixLift 5361162
  have htrace : WordTrace (prefixWord ++ tailWord_5361162) baseStart_5361162 baseEnd_5361162 := by
    simpa [prefixWord, tailWord_5361162, baseEnd_5361162] using wordTrace_append hprefix tailTrace_5361162
  have hstable : (prefixWord ++ tailWord_5361162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361162).length < 2 ^ (prefixWord ++ tailWord_5361162).sum := by decide
  have hdescent : baseEnd_5361162 < baseStart_5361162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361178 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3]
def baseStart_5361178 : Nat := 118140960795 + 5361178 * 2 ^ 59
def prefixEnd_5361178 : Nat := 4983230072969 + 3 ^ 40 * 5361178 * 2
def baseEnd_5361178 : Nat := 2752861188310130600119397

theorem tailTrace_5361178 : CollatzResearch.WordTrace tailWord_5361178 prefixEnd_5361178 2752861188310130600119397 := by
  unfold tailWord_5361178
  simp only [CollatzResearch.WordTrace]
  refine ⟨48884556442843799287893047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130358817180916798101048125 48884556442843799287893047)
  ·
    refine ⟨73326834664265698931839571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48884556442843799287893047 73326834664265698931839571)
    ·
      refine ⟨109990251996398548397759357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73326834664265698931839571 109990251996398548397759357)
      ·
        refine ⟨41246344498649455649159759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109990251996398548397759357 41246344498649455649159759)
        ·
          refine ⟨61869516747974183473739639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41246344498649455649159759 61869516747974183473739639)
          ·
            refine ⟨92804275121961275210609459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61869516747974183473739639 92804275121961275210609459)
            ·
              refine ⟨139206412682941912815914189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92804275121961275210609459 139206412682941912815914189)
              ·
                refine ⟨52202404756103217305967821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139206412682941912815914189 52202404756103217305967821)
                ·
                  refine ⟨19575901783538706489737933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52202404756103217305967821 19575901783538706489737933)
                  ·
                    refine ⟨7340963168827014933651725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19575901783538706489737933 7340963168827014933651725)
                    ·
                      refine ⟨2752861188310130600119397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7340963168827014933651725 2752861188310130600119397)
                      ·
                        rfl

theorem cell23_5361178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_5361178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361178 prefixEnd_5361178 := by exact prefixLift 5361178
  have htrace : WordTrace (prefixWord ++ tailWord_5361178) baseStart_5361178 baseEnd_5361178 := by
    simpa [prefixWord, tailWord_5361178, baseEnd_5361178] using wordTrace_append hprefix tailTrace_5361178
  have hstable : (prefixWord ++ tailWord_5361178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361178).length < 2 ^ (prefixWord ++ tailWord_5361178).sum := by decide
  have hdescent : baseEnd_5361178 < baseStart_5361178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361206 : List Nat := [5, 1, 2, 1, 3, 2, 2, 1, 2, 4]
def baseStart_5361206 : Nat := 118140960795 + 5361206 * 2 ^ 59
def prefixEnd_5361206 : Nat := 4983230072969 + 3 ^ 40 * 5361206 * 2
def baseEnd_5361206 : Nat := 917625188589485496856423

theorem tailTrace_5361206 : CollatzResearch.WordTrace tailWord_5361206 prefixEnd_5361206 917625188589485496856423 := by
  unfold tailWord_5361206
  simp only [CollatzResearch.WordTrace]
  refine ⟨12221202938454609870849467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130359498010182505289060981 12221202938454609870849467)
  ·
    refine ⟨18331804407681914806274201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12221202938454609870849467 18331804407681914806274201)
    ·
      refine ⟨13748853305761436104705651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18331804407681914806274201 13748853305761436104705651)
      ·
        refine ⟨20623279958642154157058477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13748853305761436104705651 20623279958642154157058477)
        ·
          refine ⟨7733729984490807808896929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20623279958642154157058477 7733729984490807808896929)
          ·
            refine ⟨5800297488368105856672697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7733729984490807808896929 5800297488368105856672697)
            ·
              refine ⟨4350223116276079392504523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5800297488368105856672697 4350223116276079392504523)
              ·
                refine ⟨6525334674414119088756785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4350223116276079392504523 6525334674414119088756785)
                ·
                  refine ⟨4894001005810589316567589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6525334674414119088756785 4894001005810589316567589)
                  ·
                    refine ⟨917625188589485496856423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4894001005810589316567589 917625188589485496856423)
                    ·
                      rfl

theorem cell23_5361206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_5361206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361206 prefixEnd_5361206 := by exact prefixLift 5361206
  have htrace : WordTrace (prefixWord ++ tailWord_5361206) baseStart_5361206 baseEnd_5361206 := by
    simpa [prefixWord, tailWord_5361206, baseEnd_5361206] using wordTrace_append hprefix tailTrace_5361206
  have hstable : (prefixWord ++ tailWord_5361206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361206).length < 2 ^ (prefixWord ++ tailWord_5361206).sum := by decide
  have hdescent : baseEnd_5361206 < baseStart_5361206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361239 : List Nat := [1, 1, 3, 2, 2, 4, 3, 1, 1, 3, 2]
def baseStart_5361239 : Nat := 118140960795 + 5361239 * 2 ^ 59
def prefixEnd_5361239 : Nat := 4983230072969 + 3 ^ 40 * 5361239 * 2
def baseEnd_5361239 : Nat := 2752892510630054861456617

theorem tailTrace_5361239 : CollatzResearch.WordTrace tailWord_5361239 prefixEnd_5361239 2752892510630054861456617 := by
  unfold tailWord_5361239
  simp only [CollatzResearch.WordTrace]
  refine ⟨195540450624154204569542771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130360300416102803046361847 195540450624154204569542771)
  ·
    refine ⟨293310675936231306854314157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195540450624154204569542771 293310675936231306854314157)
    ·
      refine ⟨109991503476086740070367809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293310675936231306854314157 109991503476086740070367809)
      ·
        refine ⟨82493627607065055052775857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109991503476086740070367809 82493627607065055052775857)
        ·
          refine ⟨61870220705298791289581893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82493627607065055052775857 61870220705298791289581893)
          ·
            refine ⟨11600666382243523366796605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61870220705298791289581893 11600666382243523366796605)
            ·
              refine ⟨4350249893341321262548727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11600666382243523366796605 4350249893341321262548727)
              ·
                refine ⟨6525374840011981893823091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4350249893341321262548727 6525374840011981893823091)
                ·
                  refine ⟨9788062260017972840734637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6525374840011981893823091 9788062260017972840734637)
                  ·
                    refine ⟨3670523347506739815275489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9788062260017972840734637 3670523347506739815275489)
                    ·
                      refine ⟨2752892510630054861456617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3670523347506739815275489 2752892510630054861456617)
                      ·
                        rfl

theorem cell23_5361239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 1, 3, 2].length) (baseStart_5361239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361239 prefixEnd_5361239 := by exact prefixLift 5361239
  have htrace : WordTrace (prefixWord ++ tailWord_5361239) baseStart_5361239 baseEnd_5361239 := by
    simpa [prefixWord, tailWord_5361239, baseEnd_5361239] using wordTrace_append hprefix tailTrace_5361239
  have hstable : (prefixWord ++ tailWord_5361239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361239).length < 2 ^ (prefixWord ++ tailWord_5361239).sum := by decide
  have hdescent : baseEnd_5361239 < baseStart_5361239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361248 : List Nat := [2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 4]
def baseStart_5361248 : Nat := 118140960795 + 5361248 * 2 ^ 59
def prefixEnd_5361248 : Nat := 4983230072969 + 3 ^ 40 * 5361248 * 2
def baseEnd_5361248 : Nat := 2752897131955945326244075

theorem tailTrace_5361248 : CollatzResearch.WordTrace tailWord_5361248 prefixEnd_5361248 2752897131955945326244075 := by
  unfold tailWord_5361248
  simp only [CollatzResearch.WordTrace]
  refine ⟨97770389440560799553310199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130360519254081066071080265 97770389440560799553310199)
  ·
    refine ⟨146655584160841199329965299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97770389440560799553310199 146655584160841199329965299)
    ·
      refine ⟨219983376241261798994947949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146655584160841199329965299 219983376241261798994947949)
      ·
        refine ⟨82493766090473174623105481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219983376241261798994947949 82493766090473174623105481)
        ·
          refine ⟨61870324567854880967329111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82493766090473174623105481 61870324567854880967329111)
          ·
            refine ⟨92805486851782321450993667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61870324567854880967329111 92805486851782321450993667)
            ·
              refine ⟨139208230277673482176490501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92805486851782321450993667 139208230277673482176490501)
              ·
                refine ⟨26101543177063777908091969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139208230277673482176490501 26101543177063777908091969)
                ·
                  refine ⟨19576157382797833431068977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26101543177063777908091969 19576157382797833431068977)
                  ·
                    refine ⟨14682118037098375073301733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19576157382797833431068977 14682118037098375073301733)
                    ·
                      refine ⟨2752897131955945326244075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14682118037098375073301733 2752897131955945326244075)
                      ·
                        rfl

theorem cell23_5361248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_5361248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361248 prefixEnd_5361248 := by exact prefixLift 5361248
  have htrace : WordTrace (prefixWord ++ tailWord_5361248) baseStart_5361248 baseEnd_5361248 := by
    simpa [prefixWord, tailWord_5361248, baseEnd_5361248] using wordTrace_append hprefix tailTrace_5361248
  have hstable : (prefixWord ++ tailWord_5361248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361248).length < 2 ^ (prefixWord ++ tailWord_5361248).sum := by decide
  have hdescent : baseEnd_5361248 < baseStart_5361248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361269 : List Nat := [1, 3, 4, 2, 1, 2, 2, 1, 1, 4, 2]
def baseStart_5361269 : Nat := 118140960795 + 5361269 * 2 ^ 59
def prefixEnd_5361269 : Nat := 4983230072969 + 3 ^ 40 * 5361269 * 2
def baseEnd_5361269 : Nat := 2752907915049689744081479

theorem tailTrace_5361269 : CollatzResearch.WordTrace tailWord_5361269 prefixEnd_5361269 2752907915049689744081479 := by
  unfold tailWord_5361269
  simp only [CollatzResearch.WordTrace]
  refine ⟨195541544814045519693134861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130361029876030346462089907 195541544814045519693134861)
  ·
    refine ⟨73328079305267069884925573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195541544814045519693134861 73328079305267069884925573)
    ·
      refine ⟨13749014869737575603423545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73328079305267069884925573 13749014869737575603423545)
      ·
        refine ⟨10311761152303181702567659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13749014869737575603423545 10311761152303181702567659)
        ·
          refine ⟨15467641728454772553851489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10311761152303181702567659 15467641728454772553851489)
          ·
            refine ⟨11600731296341079415388617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15467641728454772553851489 11600731296341079415388617)
            ·
              refine ⟨8700548472255809561541463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11600731296341079415388617 8700548472255809561541463)
              ·
                refine ⟨13050822708383714342312195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8700548472255809561541463 13050822708383714342312195)
                ·
                  refine ⟨19576234062575571513468293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13050822708383714342312195 19576234062575571513468293)
                  ·
                    refine ⟨3670543886732919658775305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19576234062575571513468293 3670543886732919658775305)
                    ·
                      refine ⟨2752907915049689744081479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3670543886732919658775305 2752907915049689744081479)
                      ·
                        rfl

theorem cell23_5361269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_5361269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361269 prefixEnd_5361269 := by exact prefixLift 5361269
  have htrace : WordTrace (prefixWord ++ tailWord_5361269) baseStart_5361269 baseEnd_5361269 := by
    simpa [prefixWord, tailWord_5361269, baseEnd_5361269] using wordTrace_append hprefix tailTrace_5361269
  have hstable : (prefixWord ++ tailWord_5361269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361269).length < 2 ^ (prefixWord ++ tailWord_5361269).sum := by decide
  have hdescent : baseEnd_5361269 < baseStart_5361269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361320 : List Nat := [2, 1, 7, 1, 2, 1, 1, 1, 1, 4, 2]
def baseStart_5361320 : Nat := 118140960795 + 5361320 * 2 ^ 59
def prefixEnd_5361320 : Nat := 4983230072969 + 3 ^ 40 * 5361320 * 2
def baseEnd_5361320 : Nat := 2752934102563069044543745

theorem tailTrace_5361320 : CollatzResearch.WordTrace tailWord_5361320 prefixEnd_5361320 2752934102563069044543745 := by
  unfold tailWord_5361320
  simp only [CollatzResearch.WordTrace]
  refine ⟨97771702468430377701620707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130362269957907170268827609 97771702468430377701620707)
  ·
    refine ⟨146657553702645566552431061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97771702468430377701620707 146657553702645566552431061)
    ·
      refine ⟨3437286414905755466072603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 146657553702645566552431061 3437286414905755466072603)
      ·
        refine ⟨5155929622358633199108905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3437286414905755466072603 5155929622358633199108905)
        ·
          refine ⟨3866947216768974899331679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5155929622358633199108905 3866947216768974899331679)
          ·
            refine ⟨5800420825153462348997519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3866947216768974899331679 5800420825153462348997519)
            ·
              refine ⟨8700631237730193523496279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5800420825153462348997519 8700631237730193523496279)
              ·
                refine ⟨13050946856595290285244419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8700631237730193523496279 13050946856595290285244419)
                ·
                  refine ⟨19576420284892935427866629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13050946856595290285244419 19576420284892935427866629)
                  ·
                    refine ⟨3670578803417425392724993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19576420284892935427866629 3670578803417425392724993)
                    ·
                      refine ⟨2752934102563069044543745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3670578803417425392724993 2752934102563069044543745)
                      ·
                        rfl

theorem cell23_5361320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_5361320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361320 prefixEnd_5361320 := by exact prefixLift 5361320
  have htrace : WordTrace (prefixWord ++ tailWord_5361320) baseStart_5361320 baseEnd_5361320 := by
    simpa [prefixWord, tailWord_5361320, baseEnd_5361320] using wordTrace_append hprefix tailTrace_5361320
  have hstable : (prefixWord ++ tailWord_5361320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361320).length < 2 ^ (prefixWord ++ tailWord_5361320).sum := by decide
  have hdescent : baseEnd_5361320 < baseStart_5361320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361325 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_5361325 : Nat := 118140960795 + 5361325 * 2 ^ 59
def prefixEnd_5361325 : Nat := 4983230072969 + 3 ^ 40 * 5361325 * 2
def baseEnd_5361325 : Nat := 2752936669966341524981221

theorem tailTrace_5361325 : CollatzResearch.WordTrace tailWord_5361325 prefixEnd_5361325 2752936669966341524981221 := by
  unfold tailWord_5361325
  simp only [CollatzResearch.WordTrace]
  refine ⟨195543587301842641257173429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130362391534561760838115619 195543587301842641257173429)
  ·
    refine ⟨18332211309547747617860009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 195543587301842641257173429 18332211309547747617860009)
    ·
      refine ⟨13749158482160810713395007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18332211309547747617860009 13749158482160810713395007)
      ·
        refine ⟨20623737723241216070092511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13749158482160810713395007 20623737723241216070092511)
        ·
          refine ⟨30935606584861824105138767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20623737723241216070092511 30935606584861824105138767)
          ·
            refine ⟨46403409877292736157708151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30935606584861824105138767 46403409877292736157708151)
            ·
              refine ⟨69605114815939104236562227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46403409877292736157708151 69605114815939104236562227)
              ·
                refine ⟨104407672223908656354843341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69605114815939104236562227 104407672223908656354843341)
                ·
                  refine ⟨39152877083965746133066253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104407672223908656354843341 39152877083965746133066253)
                  ·
                    refine ⟨14682328906487154799899845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39152877083965746133066253 14682328906487154799899845)
                    ·
                      refine ⟨2752936669966341524981221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14682328906487154799899845 2752936669966341524981221)
                      ·
                        rfl

theorem cell23_5361325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_5361325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361325 prefixEnd_5361325 := by exact prefixLift 5361325
  have htrace : WordTrace (prefixWord ++ tailWord_5361325) baseStart_5361325 baseEnd_5361325 := by
    simpa [prefixWord, tailWord_5361325, baseEnd_5361325] using wordTrace_append hprefix tailTrace_5361325
  have hstable : (prefixWord ++ tailWord_5361325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361325).length < 2 ^ (prefixWord ++ tailWord_5361325).sum := by decide
  have hdescent : baseEnd_5361325 < baseStart_5361325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361362 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 4, 2, 3]
def baseStart_5361362 : Nat := 118140960795 + 5361362 * 2 ^ 59
def prefixEnd_5361362 : Nat := 4983230072969 + 3 ^ 40 * 5361362 * 2
def baseEnd_5361362 : Nat := 2752955668750557880218551

theorem tailTrace_5361362 : CollatzResearch.WordTrace tailWord_5361362 prefixEnd_5361362 2752955668750557880218551 := by
  unfold tailWord_5361362
  simp only [CollatzResearch.WordTrace]
  refine ⟨48886234200677149144067585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130363291201805731050846893 48886234200677149144067585)
  ·
    refine ⟨36664675650507861858050689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48886234200677149144067585 36664675650507861858050689)
    ·
      refine ⟨27498506737880896393538017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36664675650507861858050689 27498506737880896393538017)
      ·
        refine ⟨20623880053410672295153513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27498506737880896393538017 20623880053410672295153513)
        ·
          refine ⟨15467910040058004221365135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20623880053410672295153513 15467910040058004221365135)
          ·
            refine ⟨23201865060087006332047703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15467910040058004221365135 23201865060087006332047703)
            ·
              refine ⟨34802797590130509498071555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23201865060087006332047703 34802797590130509498071555)
              ·
                refine ⟨52204196385195764247107333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34802797590130509498071555 52204196385195764247107333)
                ·
                  refine ⟨9788286822224205796332625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52204196385195764247107333 9788286822224205796332625)
                  ·
                    refine ⟨7341215116668154347249469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9788286822224205796332625 7341215116668154347249469)
                    ·
                      refine ⟨2752955668750557880218551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7341215116668154347249469 2752955668750557880218551)
                      ·
                        rfl

theorem cell23_5361362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_5361362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361362 prefixEnd_5361362 := by exact prefixLift 5361362
  have htrace : WordTrace (prefixWord ++ tailWord_5361362) baseStart_5361362 baseEnd_5361362 := by
    simpa [prefixWord, tailWord_5361362, baseEnd_5361362] using wordTrace_append hprefix tailTrace_5361362
  have hstable : (prefixWord ++ tailWord_5361362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361362).length < 2 ^ (prefixWord ++ tailWord_5361362).sum := by decide
  have hdescent : baseEnd_5361362 < baseStart_5361362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361396 : List Nat := [2, 6, 1, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_5361396 : Nat := 118140960795 + 5361396 * 2 ^ 59
def prefixEnd_5361396 : Nat := 4983230072969 + 3 ^ 40 * 5361396 * 2
def baseEnd_5361396 : Nat := 2752973127092810747193395

theorem tailTrace_5361396 : CollatzResearch.WordTrace tailWord_5361396 prefixEnd_5361396 2752973127092810747193395 := by
  unfold tailWord_5361396
  simp only [CollatzResearch.WordTrace]
  refine ⟨97773088442292710191504021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130364117923056946922005361 97773088442292710191504021)
  ·
    refine ⟨4583113520732470790226751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 97773088442292710191504021 4583113520732470790226751)
    ·
      refine ⟨6874670281098706185340127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4583113520732470790226751 6874670281098706185340127)
      ·
        refine ⟨10312005421648059278010191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6874670281098706185340127 10312005421648059278010191)
        ·
          refine ⟨15468008132472088917015287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10312005421648059278010191 15468008132472088917015287)
          ·
            refine ⟨23202012198708133375522931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15468008132472088917015287 23202012198708133375522931)
            ·
              refine ⟨34803018298062200063284397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23202012198708133375522931 34803018298062200063284397)
              ·
                refine ⟨13051131861773325023731649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34803018298062200063284397 13051131861773325023731649)
                ·
                  refine ⟨9788348896329993767798737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13051131861773325023731649 9788348896329993767798737)
                  ·
                    refine ⟨7341261672247495325849053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9788348896329993767798737 7341261672247495325849053)
                    ·
                      refine ⟨2752973127092810747193395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7341261672247495325849053 2752973127092810747193395)
                      ·
                        rfl

theorem cell23_5361396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_5361396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361396 prefixEnd_5361396 := by exact prefixLift 5361396
  have htrace : WordTrace (prefixWord ++ tailWord_5361396) baseStart_5361396 baseEnd_5361396 := by
    simpa [prefixWord, tailWord_5361396, baseEnd_5361396] using wordTrace_append hprefix tailTrace_5361396
  have hstable : (prefixWord ++ tailWord_5361396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361396).length < 2 ^ (prefixWord ++ tailWord_5361396).sum := by decide
  have hdescent : baseEnd_5361396 < baseStart_5361396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361442 : List Nat := [3, 3, 1, 1, 2, 1, 4, 1, 1, 6]
def baseStart_5361442 : Nat := 118140960795 + 5361442 * 2 ^ 59
def prefixEnd_5361442 : Nat := 4983230072969 + 3 ^ 40 * 5361442 * 2
def baseEnd_5361442 : Nat := 917665582400972522406061

theorem tailTrace_5361442 : CollatzResearch.WordTrace tailWord_5361442 prefixEnd_5361442 917665582400972522406061 := by
  unfold tailWord_5361442
  simp only [CollatzResearch.WordTrace]
  refine ⟨48886963660604692559795645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130365236428279180159455053 48886963660604692559795645)
  ·
    refine ⟨18332611372726759709923367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48886963660604692559795645 18332611372726759709923367)
    ·
      refine ⟨27498917059090139564885051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18332611372726759709923367 27498917059090139564885051)
      ·
        refine ⟨41248375588635209347327577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27498917059090139564885051 41248375588635209347327577)
        ·
          refine ⟨30936281691476407010495683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41248375588635209347327577 30936281691476407010495683)
          ·
            refine ⟨46404422537214610515743525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30936281691476407010495683 46404422537214610515743525)
            ·
              refine ⟨8700829225727739471701911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46404422537214610515743525 8700829225727739471701911)
              ·
                refine ⟨13051243838591609207552867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8700829225727739471701911 13051243838591609207552867)
                ·
                  refine ⟨19576865757887413811329301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13051243838591609207552867 19576865757887413811329301)
                  ·
                    refine ⟨917665582400972522406061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19576865757887413811329301 917665582400972522406061)
                    ·
                      rfl

theorem cell23_5361442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_5361442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361442 prefixEnd_5361442 := by exact prefixLift 5361442
  have htrace : WordTrace (prefixWord ++ tailWord_5361442) baseStart_5361442 baseEnd_5361442 := by
    simpa [prefixWord, tailWord_5361442, baseEnd_5361442] using wordTrace_append hprefix tailTrace_5361442
  have hstable : (prefixWord ++ tailWord_5361442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361442).length < 2 ^ (prefixWord ++ tailWord_5361442).sum := by decide
  have hdescent : baseEnd_5361442 < baseStart_5361442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361452 : List Nat := [2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 3]
def baseStart_5361452 : Nat := 118140960795 + 5361452 * 2 ^ 59
def prefixEnd_5361452 : Nat := 4983230072969 + 3 ^ 40 * 5361452 * 2
def baseEnd_5361452 : Nat := 2753001882009462528093137

theorem tailTrace_5361452 : CollatzResearch.WordTrace tailWord_5361452 prefixEnd_5361452 2753001882009462528093137 := by
  unfold tailWord_5361452
  simp only [CollatzResearch.WordTrace]
  refine ⟨97774109686191270973523305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130365479581588361298031073 97774109686191270973523305)
  ·
    refine ⟨73330582264643453230142479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97774109686191270973523305 73330582264643453230142479)
    ·
      refine ⟨109995873396965179845213719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73330582264643453230142479 109995873396965179845213719)
      ·
        refine ⟨164993810095447769767820579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109995873396965179845213719 164993810095447769767820579)
        ·
          refine ⟨247490715143171654651730869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164993810095447769767820579 247490715143171654651730869)
          ·
            refine ⟨23202254544672342623599769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 247490715143171654651730869 23202254544672342623599769)
            ·
              refine ⟨17401690908504256967699827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23202254544672342623599769 17401690908504256967699827)
              ·
                refine ⟨26102536362756385451549741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17401690908504256967699827 26102536362756385451549741)
                ·
                  refine ⟨9788451136033644544331153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26102536362756385451549741 9788451136033644544331153)
                  ·
                    refine ⟨7341338352025233408248365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9788451136033644544331153 7341338352025233408248365)
                    ·
                      refine ⟨2753001882009462528093137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7341338352025233408248365 2753001882009462528093137)
                      ·
                        rfl

theorem cell23_5361452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 3].length) (baseStart_5361452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361452 prefixEnd_5361452 := by exact prefixLift 5361452
  have htrace : WordTrace (prefixWord ++ tailWord_5361452) baseStart_5361452 baseEnd_5361452 := by
    simpa [prefixWord, tailWord_5361452, baseEnd_5361452] using wordTrace_append hprefix tailTrace_5361452
  have hstable : (prefixWord ++ tailWord_5361452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361452).length < 2 ^ (prefixWord ++ tailWord_5361452).sum := by decide
  have hdescent : baseEnd_5361452 < baseStart_5361452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361466 : List Nat := [3, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4]
def baseStart_5361466 : Nat := 118140960795 + 5361466 * 2 ^ 59
def prefixEnd_5361466 : Nat := 4983230072969 + 3 ^ 40 * 5361466 * 2
def baseEnd_5361466 : Nat := 2753009070738625473318073

theorem tailTrace_5361466 : CollatzResearch.WordTrace tailWord_5361466 prefixEnd_5361466 2753009070738625473318073 := by
  unfold tailWord_5361466
  simp only [CollatzResearch.WordTrace]
  refine ⟨48887182498582955584514063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130365819996221214892037501 48887182498582955584514063)
  ·
    refine ⟨73330773747874433376771095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48887182498582955584514063 73330773747874433376771095)
    ·
      refine ⟨109996160621811650065156643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73330773747874433376771095 109996160621811650065156643)
      ·
        refine ⟨164994240932717475097734965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109996160621811650065156643 164994240932717475097734965)
        ·
          refine ⟨15468210087442263290412653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 164994240932717475097734965 15468210087442263290412653)
          ·
            refine ⟨5800578782790848733904745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15468210087442263290412653 5800578782790848733904745)
            ·
              refine ⟨4350434087093136550428559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5800578782790848733904745 4350434087093136550428559)
              ·
                refine ⟨6525651130639704825642839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4350434087093136550428559 6525651130639704825642839)
                ·
                  refine ⟨9788476695959557238464259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6525651130639704825642839 9788476695959557238464259)
                  ·
                    refine ⟨14682715043939335857696389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9788476695959557238464259 14682715043939335857696389)
                    ·
                      refine ⟨2753009070738625473318073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14682715043939335857696389 2753009070738625473318073)
                      ·
                        rfl

theorem cell23_5361466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4].length) (baseStart_5361466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361466 prefixEnd_5361466 := by exact prefixLift 5361466
  have htrace : WordTrace (prefixWord ++ tailWord_5361466) baseStart_5361466 baseEnd_5361466 := by
    simpa [prefixWord, tailWord_5361466, baseEnd_5361466] using wordTrace_append hprefix tailTrace_5361466
  have hstable : (prefixWord ++ tailWord_5361466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361466).length < 2 ^ (prefixWord ++ tailWord_5361466).sum := by decide
  have hdescent : baseEnd_5361466 < baseStart_5361466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361560 : List Nat := [2, 1, 2, 6, 1, 2, 1, 2, 1, 3, 2]
def baseStart_5361560 : Nat := 118140960795 + 5361560 * 2 ^ 59
def prefixEnd_5361560 : Nat := 4983230072969 + 3 ^ 40 * 5361560 * 2
def baseEnd_5361560 : Nat := 2753057337920148105542641

theorem tailTrace_5361560 : CollatzResearch.WordTrace tailWord_5361560 prefixEnd_5361560 2753057337920148105542641 := by
  unfold tailWord_5361560
  simp only [CollatzResearch.WordTrace]
  refine ⟨97776079227995638195989067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130368105637327517594652089 97776079227995638195989067)
  ·
    refine ⟨146664118841993457293983601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97776079227995638195989067 146664118841993457293983601)
    ·
      refine ⟨109998089131495092970487701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146664118841993457293983601 109998089131495092970487701)
      ·
        refine ⟨5156160428038832482991611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 109998089131495092970487701 5156160428038832482991611)
        ·
          refine ⟨7734240642058248724487417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5156160428038832482991611 7734240642058248724487417)
          ·
            refine ⟨5800680481543686543365563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7734240642058248724487417 5800680481543686543365563)
            ·
              refine ⟨8701020722315529815048345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5800680481543686543365563 8701020722315529815048345)
              ·
                refine ⟨6525765541736647361286259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8701020722315529815048345 6525765541736647361286259)
                ·
                  refine ⟨9788648312604971041929389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6525765541736647361286259 9788648312604971041929389)
                  ·
                    refine ⟨3670743117226864140723521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9788648312604971041929389 3670743117226864140723521)
                    ·
                      refine ⟨2753057337920148105542641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3670743117226864140723521 2753057337920148105542641)
                      ·
                        rfl

theorem cell23_5361560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_5361560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361560 prefixEnd_5361560 := by exact prefixLift 5361560
  have htrace : WordTrace (prefixWord ++ tailWord_5361560) baseStart_5361560 baseEnd_5361560 := by
    simpa [prefixWord, tailWord_5361560, baseEnd_5361560] using wordTrace_append hprefix tailTrace_5361560
  have hstable : (prefixWord ++ tailWord_5361560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361560).length < 2 ^ (prefixWord ++ tailWord_5361560).sum := by decide
  have hdescent : baseEnd_5361560 < baseStart_5361560 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361592 : List Nat := [2, 1, 2, 1, 2, 3, 1, 4, 2, 5]
def baseStart_5361592 : Nat := 118140960795 + 5361592 * 2 ^ 59
def prefixEnd_5361592 : Nat := 4983230072969 + 3 ^ 40 * 5361592 * 2
def baseEnd_5361592 : Nat := 917691256433697326780831

theorem tailTrace_5361592 : CollatzResearch.WordTrace tailWord_5361592 prefixEnd_5361592 917691256433697326780831 := by
  unfold tailWord_5361592
  simp only [CollatzResearch.WordTrace]
  refine ⟨97776662795937672928571515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130368883727916897238095353 97776662795937672928571515)
  ·
    refine ⟨146664994193906509392857273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97776662795937672928571515 146664994193906509392857273)
    ·
      refine ⟨109998745645429882044642955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146664994193906509392857273 109998745645429882044642955)
      ·
        refine ⟨164998118468144823066964433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109998745645429882044642955 164998118468144823066964433)
        ·
          refine ⟨123748588851108617300223325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164998118468144823066964433 123748588851108617300223325)
          ·
            refine ⟨46405720819165731487583747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123748588851108617300223325 46405720819165731487583747)
            ·
              refine ⟨69608581228748597231375621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46405720819165731487583747 69608581228748597231375621)
              ·
                refine ⟨13051608980390361980882929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69608581228748597231375621 13051608980390361980882929)
                ·
                  refine ⟨9788706735292771485662197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13051608980390361980882929 9788706735292771485662197)
                  ·
                    refine ⟨917691256433697326780831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9788706735292771485662197 917691256433697326780831)
                    ·
                      rfl

theorem cell23_5361592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 2, 5].length) (baseStart_5361592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361592 prefixEnd_5361592 := by exact prefixLift 5361592
  have htrace : WordTrace (prefixWord ++ tailWord_5361592) baseStart_5361592 baseEnd_5361592 := by
    simpa [prefixWord, tailWord_5361592, baseEnd_5361592] using wordTrace_append hprefix tailTrace_5361592
  have hstable : (prefixWord ++ tailWord_5361592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361592).length < 2 ^ (prefixWord ++ tailWord_5361592).sum := by decide
  have hdescent : baseEnd_5361592 < baseStart_5361592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361626 : List Nat := [3, 1, 1, 2, 5, 2, 1, 1, 2, 5]
def baseStart_5361626 : Nat := 118140960795 + 5361626 * 2 ^ 59
def prefixEnd_5361626 : Nat := 4983230072969 + 3 ^ 40 * 5361626 * 2
def baseEnd_5361626 : Nat := 917697075881114949105779

theorem tailTrace_5361626 : CollatzResearch.WordTrace tailWord_5361626 prefixEnd_5361626 917697075881114949105779 := by
  unfold tailWord_5361626
  simp only [CollatzResearch.WordTrace]
  refine ⟨48888641418438042415970183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130369710449168113109253821 48888641418438042415970183)
  ·
    refine ⟨73332962127657063623955275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48888641418438042415970183 73332962127657063623955275)
    ·
      refine ⟨109999443191485595435932913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73332962127657063623955275 109999443191485595435932913)
      ·
        refine ⟨82499582393614196576949685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109999443191485595435932913 82499582393614196576949685)
        ·
          refine ⟨7734335849401330929089033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82499582393614196576949685 7734335849401330929089033)
          ·
            refine ⟨5800751887050998196816775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7734335849401330929089033 5800751887050998196816775)
            ·
              refine ⟨8701127830576497295225163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5800751887050998196816775 8701127830576497295225163)
              ·
                refine ⟨13051691745864745942837745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8701127830576497295225163 13051691745864745942837745)
                ·
                  refine ⟨9788768809398559457128309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13051691745864745942837745 9788768809398559457128309)
                  ·
                    refine ⟨917697075881114949105779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9788768809398559457128309 917697075881114949105779)
                    ·
                      rfl

theorem cell23_5361626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 2, 5].length) (baseStart_5361626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361626 prefixEnd_5361626 := by exact prefixLift 5361626
  have htrace : WordTrace (prefixWord ++ tailWord_5361626) baseStart_5361626 baseEnd_5361626 := by
    simpa [prefixWord, tailWord_5361626, baseEnd_5361626] using wordTrace_append hprefix tailTrace_5361626
  have hstable : (prefixWord ++ tailWord_5361626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361626).length < 2 ^ (prefixWord ++ tailWord_5361626).sum := by decide
  have hdescent : baseEnd_5361626 < baseStart_5361626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361642 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_5361642 : Nat := 118140960795 + 5361642 * 2 ^ 59
def prefixEnd_5361642 : Nat := 4983230072969 + 3 ^ 40 * 5361642 * 2
def baseEnd_5361642 : Nat := 2753099443333816784717263

theorem tailTrace_5361642 : CollatzResearch.WordTrace tailWord_5361642 prefixEnd_5361642 2753099443333816784717263 := by
  unfold tailWord_5361642
  simp only [CollatzResearch.WordTrace]
  refine ⟨48888787310423551099115795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130370099494462802930975453 48888787310423551099115795)
  ·
    refine ⟨73333180965635326648673693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48888787310423551099115795 73333180965635326648673693)
    ·
      refine ⟨27499942862113247493252635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73333180965635326648673693 27499942862113247493252635)
      ·
        refine ⟨41249914293169871239878953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27499942862113247493252635 41249914293169871239878953)
        ·
          refine ⟨30937435719877403429909215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41249914293169871239878953 30937435719877403429909215)
          ·
            refine ⟨46406153579816105144863823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30937435719877403429909215 46406153579816105144863823)
            ·
              refine ⟨69609230369724157717295735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46406153579816105144863823 69609230369724157717295735)
              ·
                refine ⟨104413845554586236575943603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69609230369724157717295735 104413845554586236575943603)
                ·
                  refine ⟨156620768331879354863915405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104413845554586236575943603 156620768331879354863915405)
                  ·
                    refine ⟨58732788124454758073968277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 156620768331879354863915405 58732788124454758073968277)
                    ·
                      refine ⟨2753099443333816784717263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58732788124454758073968277 2753099443333816784717263)
                      ·
                        rfl

theorem cell23_5361642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_5361642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361642 prefixEnd_5361642 := by exact prefixLift 5361642
  have htrace : WordTrace (prefixWord ++ tailWord_5361642) baseStart_5361642 baseEnd_5361642 := by
    simpa [prefixWord, tailWord_5361642, baseEnd_5361642] using wordTrace_append hprefix tailTrace_5361642
  have hstable : (prefixWord ++ tailWord_5361642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361642).length < 2 ^ (prefixWord ++ tailWord_5361642).sum := by decide
  have hdescent : baseEnd_5361642 < baseStart_5361642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361646 : List Nat := [4, 1, 2, 1, 3, 1, 1, 2, 2, 4, 2]
def baseStart_5361646 : Nat := 118140960795 + 5361646 * 2 ^ 59
def prefixEnd_5361646 : Nat := 4983230072969 + 3 ^ 40 * 5361646 * 2
def baseEnd_5361646 : Nat := 2753101497256434769067245

theorem tailTrace_5361646 : CollatzResearch.WordTrace tailWord_5361646 prefixEnd_5361646 2753101497256434769067245 := by
  unfold tailWord_5361646
  simp only [CollatzResearch.WordTrace]
  refine ⟨24444411891709964134951099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130370196755786475386405861 24444411891709964134951099)
  ·
    refine ⟨36666617837564946202426649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24444411891709964134951099 36666617837564946202426649)
    ·
      refine ⟨27499963378173709651819987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36666617837564946202426649 27499963378173709651819987)
      ·
        refine ⟨41249945067260564477729981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27499963378173709651819987 41249945067260564477729981)
        ·
          refine ⟨15468729400222711679148743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41249945067260564477729981 15468729400222711679148743)
          ·
            refine ⟨23203094100334067518723115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15468729400222711679148743 23203094100334067518723115)
            ·
              refine ⟨34804641150501101278084673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23203094100334067518723115 34804641150501101278084673)
              ·
                refine ⟨26103480862875825958563505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34804641150501101278084673 26103480862875825958563505)
                ·
                  refine ⟨19577610647156869468922629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26103480862875825958563505 19577610647156869468922629)
                  ·
                    refine ⟨3670801996341913025422993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19577610647156869468922629 3670801996341913025422993)
                    ·
                      refine ⟨2753101497256434769067245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3670801996341913025422993 2753101497256434769067245)
                      ·
                        rfl

theorem cell23_5361646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_5361646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361646 prefixEnd_5361646 := by exact prefixLift 5361646
  have htrace : WordTrace (prefixWord ++ tailWord_5361646) baseStart_5361646 baseEnd_5361646 := by
    simpa [prefixWord, tailWord_5361646, baseEnd_5361646] using wordTrace_append hprefix tailTrace_5361646
  have hstable : (prefixWord ++ tailWord_5361646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361646).length < 2 ^ (prefixWord ++ tailWord_5361646).sum := by decide
  have hdescent : baseEnd_5361646 < baseStart_5361646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361656 : List Nat := [2, 1, 2, 1, 1, 3, 4, 4, 1, 4]
def baseStart_5361656 : Nat := 118140960795 + 5361656 * 2 ^ 59
def prefixEnd_5361656 : Nat := 4983230072969 + 3 ^ 40 * 5361656 * 2
def baseEnd_5361656 : Nat := 917702210687659909980733

theorem tailTrace_5361656 : CollatzResearch.WordTrace tailWord_5361656 prefixEnd_5361656 917702210687659909980733 := by
  unfold tailWord_5361656
  simp only [CollatzResearch.WordTrace]
  refine ⟨97777829931821742393736411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130370439909095656524981881 97777829931821742393736411)
  ·
    refine ⟨146666744897732613590604617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97777829931821742393736411 146666744897732613590604617)
    ·
      refine ⟨110000058673299460192953463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146666744897732613590604617 110000058673299460192953463)
      ·
        refine ⟨165000088009949190289430195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110000058673299460192953463 165000088009949190289430195)
        ·
          refine ⟨247500132014923785434145293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165000088009949190289430195 247500132014923785434145293)
          ·
            refine ⟨92812549505596419537804485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 247500132014923785434145293 92812549505596419537804485)
            ·
              refine ⟨17402353032299328663338341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92812549505596419537804485 17402353032299328663338341)
              ·
                refine ⟨3262941193556124124375939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17402353032299328663338341 3262941193556124124375939)
                ·
                  refine ⟨4894411790334186186563909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3262941193556124124375939 4894411790334186186563909)
                  ·
                    refine ⟨917702210687659909980733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4894411790334186186563909 917702210687659909980733)
                    ·
                      rfl

theorem cell23_5361656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4, 1, 4].length) (baseStart_5361656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361656 prefixEnd_5361656 := by exact prefixLift 5361656
  have htrace : WordTrace (prefixWord ++ tailWord_5361656) baseStart_5361656 baseEnd_5361656 := by
    simpa [prefixWord, tailWord_5361656, baseEnd_5361656] using wordTrace_append hprefix tailTrace_5361656
  have hstable : (prefixWord ++ tailWord_5361656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361656).length < 2 ^ (prefixWord ++ tailWord_5361656).sum := by decide
  have hdescent : baseEnd_5361656 < baseStart_5361656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361672 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 1, 2, 6]
def baseStart_5361672 : Nat := 118140960795 + 5361672 * 2 ^ 59
def prefixEnd_5361672 : Nat := 4983230072969 + 3 ^ 40 * 5361672 * 2
def baseEnd_5361672 : Nat := 2753114847753451667342125

theorem tailTrace_5361672 : CollatzResearch.WordTrace tailWord_5361672 prefixEnd_5361672 2753114847753451667342125 := by
  unfold tailWord_5361672
  simp only [CollatzResearch.WordTrace]
  refine ⟨97778121715792759760027635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130370828954390346346703513 97778121715792759760027635)
  ·
    refine ⟨146667182573689139640041453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97778121715792759760027635 146667182573689139640041453)
    ·
      refine ⟨55000193465133427365015545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146667182573689139640041453 55000193465133427365015545)
      ·
        refine ⟨41250145098850070523761659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55000193465133427365015545 41250145098850070523761659)
        ·
          refine ⟨61875217648275105785642489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41250145098850070523761659 61875217648275105785642489)
          ·
            refine ⟨46406413236206329339231867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61875217648275105785642489 46406413236206329339231867)
            ·
              refine ⟨69609619854309494008847801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46406413236206329339231867 69609619854309494008847801)
              ·
                refine ⟨52207214890732120506635851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69609619854309494008847801 52207214890732120506635851)
                ·
                  refine ⟨78310822336098180759953777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52207214890732120506635851 78310822336098180759953777)
                  ·
                    refine ⟨58733116752073635569965333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78310822336098180759953777 58733116752073635569965333)
                    ·
                      refine ⟨2753114847753451667342125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58733116752073635569965333 2753114847753451667342125)
                      ·
                        rfl

theorem cell23_5361672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_5361672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361672 prefixEnd_5361672 := by exact prefixLift 5361672
  have htrace : WordTrace (prefixWord ++ tailWord_5361672) baseStart_5361672 baseEnd_5361672 := by
    simpa [prefixWord, tailWord_5361672, baseEnd_5361672] using wordTrace_append hprefix tailTrace_5361672
  have hstable : (prefixWord ++ tailWord_5361672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361672).length < 2 ^ (prefixWord ++ tailWord_5361672).sum := by decide
  have hdescent : baseEnd_5361672 < baseStart_5361672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361699 : List Nat := [1, 1, 1, 4, 3, 1, 1, 5, 1, 5]
def baseStart_5361699 : Nat := 118140960795 + 5361699 * 2 ^ 59
def prefixEnd_5361699 : Nat := 4983230072969 + 3 ^ 40 * 5361699 * 2
def baseEnd_5361699 : Nat := 917709570577041020568167

theorem tailTrace_5361699 : CollatzResearch.WordTrace tailWord_5361699 prefixEnd_5361699 917709570577041020568167 := by
  unfold tailWord_5361699
  simp only [CollatzResearch.WordTrace]
  refine ⟨195557228202487703131288151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130371485468325135420858767 195557228202487703131288151)
  ·
    refine ⟨293335842303731554696932227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195557228202487703131288151 293335842303731554696932227)
    ·
      refine ⟨440003763455597332045398341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293335842303731554696932227 440003763455597332045398341)
      ·
        refine ⟨82500705647924499758512189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 440003763455597332045398341 82500705647924499758512189)
        ·
          refine ⟨30937764617971687409442071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82500705647924499758512189 30937764617971687409442071)
          ·
            refine ⟨46406646926957531114163107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30937764617971687409442071 46406646926957531114163107)
            ·
              refine ⟨69609970390436296671244661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46406646926957531114163107 69609970390436296671244661)
              ·
                refine ⟨6525934724103402812929187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69609970390436296671244661 6525934724103402812929187)
                ·
                  refine ⟨9788902086155104219393781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6525934724103402812929187 9788902086155104219393781)
                  ·
                    refine ⟨917709570577041020568167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9788902086155104219393781 917709570577041020568167)
                    ·
                      rfl

theorem cell23_5361699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 5].length) (baseStart_5361699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361699 prefixEnd_5361699 := by exact prefixLift 5361699
  have htrace : WordTrace (prefixWord ++ tailWord_5361699) baseStart_5361699 baseEnd_5361699 := by
    simpa [prefixWord, tailWord_5361699, baseEnd_5361699] using wordTrace_append hprefix tailTrace_5361699
  have hstable : (prefixWord ++ tailWord_5361699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361699).length < 2 ^ (prefixWord ++ tailWord_5361699).sum := by decide
  have hdescent : baseEnd_5361699 < baseStart_5361699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361713 : List Nat := [1, 2, 2, 3, 1, 5, 1, 1, 3, 1, 3]
def baseStart_5361713 : Nat := 118140960795 + 5361713 * 2 ^ 59
def prefixEnd_5361713 : Nat := 4983230072969 + 3 ^ 40 * 5361713 * 2
def baseEnd_5361713 : Nat := 2753135900460286006929437

theorem tailTrace_5361713 : CollatzResearch.WordTrace tailWord_5361713 prefixEnd_5361713 2753135900460286006929437 := by
  unfold tailWord_5361713
  simp only [CollatzResearch.WordTrace]
  refine ⟨195557738824436983522297793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130371825882957989014865195 195557738824436983522297793)
  ·
    refine ⟨146668304118327737641723345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195557738824436983522297793 146668304118327737641723345)
    ·
      refine ⟨110001228088745803231292509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146668304118327737641723345 110001228088745803231292509)
      ·
        refine ⟨41250460533279676211734691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110001228088745803231292509 41250460533279676211734691)
        ·
          refine ⟨61875690799919514317602037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41250460533279676211734691 61875690799919514317602037)
          ·
            refine ⟨5800846012492454467275191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61875690799919514317602037 5800846012492454467275191)
            ·
              refine ⟨8701269018738681700912787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5800846012492454467275191 8701269018738681700912787)
              ·
                refine ⟨13051903528108022551369181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8701269018738681700912787 13051903528108022551369181)
                ·
                  refine ⟨4894463823040508456763443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13051903528108022551369181 4894463823040508456763443)
                  ·
                    refine ⟨7341695734560762685145165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4894463823040508456763443 7341695734560762685145165)
                    ·
                      refine ⟨2753135900460286006929437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7341695734560762685145165 2753135900460286006929437)
                      ·
                        rfl

theorem cell23_5361713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_5361713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361713 prefixEnd_5361713 := by exact prefixLift 5361713
  have htrace : WordTrace (prefixWord ++ tailWord_5361713) baseStart_5361713 baseEnd_5361713 := by
    simpa [prefixWord, tailWord_5361713, baseEnd_5361713] using wordTrace_append hprefix tailTrace_5361713
  have hstable : (prefixWord ++ tailWord_5361713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361713).length < 2 ^ (prefixWord ++ tailWord_5361713).sum := by decide
  have hdescent : baseEnd_5361713 < baseStart_5361713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361739 : List Nat := [1, 1, 1, 1, 3, 1, 2, 5, 3, 2, 3]
def baseStart_5361739 : Nat := 118140960795 + 5361739 * 2 ^ 59
def prefixEnd_5361739 : Nat := 4983230072969 + 3 ^ 40 * 5361739 * 2
def baseEnd_5361739 : Nat := 2753149250957302905204317

theorem tailTrace_5361739 : CollatzResearch.WordTrace tailWord_5361739 prefixEnd_5361739 2753149250957302905204317 := by
  unfold tailWord_5361739
  simp only [CollatzResearch.WordTrace]
  refine ⟨195558687122342789962744271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130372458081561859975162847 195558687122342789962744271)
  ·
    refine ⟨293338030683514184944116407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195558687122342789962744271 293338030683514184944116407)
    ·
      refine ⟨440007046025271277416174611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293338030683514184944116407 440007046025271277416174611)
      ·
        refine ⟨660010569037906916124261917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440007046025271277416174611 660010569037906916124261917)
        ·
          refine ⟨247503963389215093546598219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 660010569037906916124261917 247503963389215093546598219)
          ·
            refine ⟨371255945083822640319897329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247503963389215093546598219 371255945083822640319897329)
            ·
              refine ⟨278441958812866980239922997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 371255945083822640319897329 278441958812866980239922997)
              ·
                refine ⟨26103933638706279397492781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 278441958812866980239922997 26103933638706279397492781)
                ·
                  refine ⟨9788975114514854774059793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26103933638706279397492781 9788975114514854774059793)
                  ·
                    refine ⟨7341731335886141080544845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9788975114514854774059793 7341731335886141080544845)
                    ·
                      refine ⟨2753149250957302905204317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7341731335886141080544845 2753149250957302905204317)
                      ·
                        rfl

theorem cell23_5361739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2, 3].length) (baseStart_5361739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361739 prefixEnd_5361739 := by exact prefixLift 5361739
  have htrace : WordTrace (prefixWord ++ tailWord_5361739) baseStart_5361739 baseEnd_5361739 := by
    simpa [prefixWord, tailWord_5361739, baseEnd_5361739] using wordTrace_append hprefix tailTrace_5361739
  have hstable : (prefixWord ++ tailWord_5361739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361739).length < 2 ^ (prefixWord ++ tailWord_5361739).sum := by decide
  have hdescent : baseEnd_5361739 < baseStart_5361739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361746 : List Nat := [3, 2, 2, 1, 4, 1, 1, 2, 1, 6]
def baseStart_5361746 : Nat := 118140960795 + 5361746 * 2 ^ 59
def prefixEnd_5361746 : Nat := 4983230072969 + 3 ^ 40 * 5361746 * 2
def baseEnd_5361746 : Nat := 917717615107294792605595

theorem tailTrace_5361746 : CollatzResearch.WordTrace tailWord_5361746 prefixEnd_5361746 917717615107294792605595 := by
  unfold tailWord_5361746
  simp only [CollatzResearch.WordTrace]
  refine ⟨48889735608329357539562273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130372628288878286772166061 48889735608329357539562273)
  ·
    refine ⟨36667301706247018154671705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48889735608329357539562273 36667301706247018154671705)
    ·
      refine ⟨27500476279685263616003779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36667301706247018154671705 27500476279685263616003779)
      ·
        refine ⟨41250714419527895424005669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27500476279685263616003779 41250714419527895424005669)
        ·
          refine ⟨7734508953661480392001063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41250714419527895424005669 7734508953661480392001063)
          ·
            refine ⟨11601763430492220588001595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7734508953661480392001063 11601763430492220588001595)
            ·
              refine ⟨17402645145738330882002393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11601763430492220588001595 17402645145738330882002393)
              ·
                refine ⟨13051983859303748161501795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17402645145738330882002393 13051983859303748161501795)
                ·
                  refine ⟨19577975788955622242252693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13051983859303748161501795 19577975788955622242252693)
                  ·
                    refine ⟨917717615107294792605595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19577975788955622242252693 917717615107294792605595)
                    ·
                      rfl

theorem cell23_5361746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_5361746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361746 prefixEnd_5361746 := by exact prefixLift 5361746
  have htrace : WordTrace (prefixWord ++ tailWord_5361746) baseStart_5361746 baseEnd_5361746 := by
    simpa [prefixWord, tailWord_5361746, baseEnd_5361746] using wordTrace_append hprefix tailTrace_5361746
  have hstable : (prefixWord ++ tailWord_5361746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361746).length < 2 ^ (prefixWord ++ tailWord_5361746).sum := by decide
  have hdescent : baseEnd_5361746 < baseStart_5361746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361749 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 3, 2, 4]
def baseStart_5361749 : Nat := 118140960795 + 5361749 * 2 ^ 59
def prefixEnd_5361749 : Nat := 4983230072969 + 3 ^ 40 * 5361749 * 2
def baseEnd_5361749 : Nat := 2753154385763847866079271

theorem tailTrace_5361749 : CollatzResearch.WordTrace tailWord_5361749 prefixEnd_5361749 2753154385763847866079271 := by
  unfold tailWord_5361749
  simp only [CollatzResearch.WordTrace]
  refine ⟨195559051852306561670608301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130372701234871041113738867 195559051852306561670608301)
  ·
    refine ⟨73334644444614960626478113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195559051852306561670608301 73334644444614960626478113)
    ·
      refine ⟨55000983333461220469858585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73334644444614960626478113 55000983333461220469858585)
      ·
        refine ⟨41250737500095915352393939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55000983333461220469858585 41250737500095915352393939)
        ·
          refine ⟨61876106250143873028590909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41250737500095915352393939 61876106250143873028590909)
          ·
            refine ⟨23203539843803952385721591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61876106250143873028590909 23203539843803952385721591)
            ·
              refine ⟨34805309765705928578582387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23203539843803952385721591 34805309765705928578582387)
              ·
                refine ⟨52207964648558892867873581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34805309765705928578582387 52207964648558892867873581)
                ·
                  refine ⟨19577986743209584825452593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52207964648558892867873581 19577986743209584825452593)
                  ·
                    refine ⟨14683490057407188619089445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19577986743209584825452593 14683490057407188619089445)
                    ·
                      refine ⟨2753154385763847866079271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14683490057407188619089445 2753154385763847866079271)
                      ·
                        rfl

theorem cell23_5361749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_5361749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361749 prefixEnd_5361749 := by exact prefixLift 5361749
  have htrace : WordTrace (prefixWord ++ tailWord_5361749) baseStart_5361749 baseEnd_5361749 := by
    simpa [prefixWord, tailWord_5361749, baseEnd_5361749] using wordTrace_append hprefix tailTrace_5361749
  have hstable : (prefixWord ++ tailWord_5361749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361749).length < 2 ^ (prefixWord ++ tailWord_5361749).sum := by decide
  have hdescent : baseEnd_5361749 < baseStart_5361749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361756 : List Nat := [2, 2, 4, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_5361756 : Nat := 118140960795 + 5361756 * 2 ^ 59
def prefixEnd_5361756 : Nat := 4983230072969 + 3 ^ 40 * 5361756 * 2
def baseEnd_5361756 : Nat := 2753157980128429338691739

theorem tailTrace_5361756 : CollatzResearch.WordTrace tailWord_5361756 prefixEnd_5361756 2753157980128429338691739 := by
  unfold tailWord_5361756
  simp only [CollatzResearch.WordTrace]
  refine ⟨97779653581640600933056561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130372871442187467910742081 97779653581640600933056561)
  ·
    refine ⟨73334740186230450699792421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97779653581640600933056561 73334740186230450699792421)
    ·
      refine ⟨13750263784918209506211079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73334740186230450699792421 13750263784918209506211079)
      ·
        refine ⟨20625395677377314259316619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13750263784918209506211079 20625395677377314259316619)
        ·
          refine ⟨30938093516065971388974929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20625395677377314259316619 30938093516065971388974929)
          ·
            refine ⟨23203570137049478541731197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30938093516065971388974929 23203570137049478541731197)
            ·
              refine ⟨8701338801393554453149199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23203570137049478541731197 8701338801393554453149199)
              ·
                refine ⟨13052008202090331679723799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8701338801393554453149199 13052008202090331679723799)
                ·
                  refine ⟨19578012303135497519585699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13052008202090331679723799 19578012303135497519585699)
                  ·
                    refine ⟨29367018454703246279378549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19578012303135497519585699 29367018454703246279378549)
                    ·
                      refine ⟨2753157980128429338691739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29367018454703246279378549 2753157980128429338691739)
                      ·
                        rfl

theorem cell23_5361756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_5361756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361756 prefixEnd_5361756 := by exact prefixLift 5361756
  have htrace : WordTrace (prefixWord ++ tailWord_5361756) baseStart_5361756 baseEnd_5361756 := by
    simpa [prefixWord, tailWord_5361756, baseEnd_5361756] using wordTrace_append hprefix tailTrace_5361756
  have hstable : (prefixWord ++ tailWord_5361756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361756).length < 2 ^ (prefixWord ++ tailWord_5361756).sum := by decide
  have hdescent : baseEnd_5361756 < baseStart_5361756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361769 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 3, 3, 3]
def baseStart_5361769 : Nat := 118140960795 + 5361769 * 2 ^ 59
def prefixEnd_5361769 : Nat := 4983230072969 + 3 ^ 40 * 5361769 * 2
def baseEnd_5361769 : Nat := 2753164655376937787829179

theorem tailTrace_5361769 : CollatzResearch.WordTrace tailWord_5361769 prefixEnd_5361769 2753164655376937787829179 := by
  unfold tailWord_5361769
  simp only [CollatzResearch.WordTrace]
  refine ⟨195559781312234105086336361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130373187541489403390890907 195559781312234105086336361)
  ·
    refine ⟨146669835984175578814752271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195559781312234105086336361 146669835984175578814752271)
    ·
      refine ⟨220004753976263368222128407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146669835984175578814752271 220004753976263368222128407)
      ·
        refine ⟨330007130964395052333192611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220004753976263368222128407 330007130964395052333192611)
        ·
          refine ⟨495010696446592578499788917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330007130964395052333192611 495010696446592578499788917)
          ·
            refine ⟨46407252791868054234355211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 495010696446592578499788917 46407252791868054234355211)
            ·
              refine ⟨69610879187802081351532817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46407252791868054234355211 69610879187802081351532817)
              ·
                refine ⟨52208159390851561013649613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69610879187802081351532817 52208159390851561013649613)
                ·
                  refine ⟨19578059771569335380118605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52208159390851561013649613 19578059771569335380118605)
                  ·
                    refine ⟨7341772414338500767544477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19578059771569335380118605 7341772414338500767544477)
                    ·
                      refine ⟨2753164655376937787829179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7341772414338500767544477 2753164655376937787829179)
                      ·
                        rfl

theorem cell23_5361769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 3, 3].length) (baseStart_5361769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361769 prefixEnd_5361769 := by exact prefixLift 5361769
  have htrace : WordTrace (prefixWord ++ tailWord_5361769) baseStart_5361769 baseEnd_5361769 := by
    simpa [prefixWord, tailWord_5361769, baseEnd_5361769] using wordTrace_append hprefix tailTrace_5361769
  have hstable : (prefixWord ++ tailWord_5361769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361769).length < 2 ^ (prefixWord ++ tailWord_5361769).sum := by decide
  have hdescent : baseEnd_5361769 < baseStart_5361769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361813 : List Nat := [1, 3, 2, 1, 1, 1, 5, 3, 1, 3, 2]
def baseStart_5361813 : Nat := 118140960795 + 5361813 * 2 ^ 59
def prefixEnd_5361813 : Nat := 4983230072969 + 3 ^ 40 * 5361813 * 2
def baseEnd_5361813 : Nat := 2753187248525735615678977

theorem tailTrace_5361813 : CollatzResearch.WordTrace tailWord_5361813 prefixEnd_5361813 2753187248525735615678977 := by
  unfold tailWord_5361813
  simp only [CollatzResearch.WordTrace]
  refine ⟨195561386124074700600938093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130374257416049800400625395 195561386124074700600938093)
  ·
    refine ⟨73335519796528012725351785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195561386124074700600938093 73335519796528012725351785)
    ·
      refine ⟨55001639847396009544013839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73335519796528012725351785 55001639847396009544013839)
      ·
        refine ⟨82502459771094014316020759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55001639847396009544013839 82502459771094014316020759)
        ·
          refine ⟨123753689656641021474031139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82502459771094014316020759 123753689656641021474031139)
          ·
            refine ⟨185630534484961532211046709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123753689656641021474031139 185630534484961532211046709)
            ·
              refine ⟨17402862607965143644785629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 185630534484961532211046709 17402862607965143644785629)
              ·
                refine ⟨6526073477986928866794611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17402862607965143644785629 6526073477986928866794611)
                ·
                  refine ⟨9789110216980393300191917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6526073477986928866794611 9789110216980393300191917)
                  ·
                    refine ⟨3670916331367647487571969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9789110216980393300191917 3670916331367647487571969)
                    ·
                      refine ⟨2753187248525735615678977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3670916331367647487571969 2753187248525735615678977)
                      ·
                        rfl

theorem cell23_5361813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 3, 2].length) (baseStart_5361813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361813 prefixEnd_5361813 := by exact prefixLift 5361813
  have htrace : WordTrace (prefixWord ++ tailWord_5361813) baseStart_5361813 baseEnd_5361813 := by
    simpa [prefixWord, tailWord_5361813, baseEnd_5361813] using wordTrace_append hprefix tailTrace_5361813
  have hstable : (prefixWord ++ tailWord_5361813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361813).length < 2 ^ (prefixWord ++ tailWord_5361813).sum := by decide
  have hdescent : baseEnd_5361813 < baseStart_5361813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361814 : List Nat := [5, 3, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_5361814 : Nat := 118140960795 + 5361814 * 2 ^ 59
def prefixEnd_5361814 : Nat := 4983230072969 + 3 ^ 40 * 5361814 * 2
def baseEnd_5361814 : Nat := 917729254002130037255491

theorem tailTrace_5361814 : CollatzResearch.WordTrace tailWord_5361814 prefixEnd_5361814 917729254002130037255491 := by
  unfold tailWord_5361814
  simp only [CollatzResearch.WordTrace]
  refine ⟨12222588912316942360732781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130374281731380718514482997 12222588912316942360732781)
  ·
    refine ⟨4583470842118853385274793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12222588912316942360732781 4583470842118853385274793)
    ·
      refine ⟨3437603131589140038956095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4583470842118853385274793 3437603131589140038956095)
      ·
        refine ⟨5156404697383710058434143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3437603131589140038956095 5156404697383710058434143)
        ·
          refine ⟨7734607046075565087651215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5156404697383710058434143 7734607046075565087651215)
          ·
            refine ⟨11601910569113347631476823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7734607046075565087651215 11601910569113347631476823)
            ·
              refine ⟨17402865853670021447215235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11601910569113347631476823 17402865853670021447215235)
              ·
                refine ⟨26104298780505032170822853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17402865853670021447215235 26104298780505032170822853)
                ·
                  refine ⟨4894556021344693532029285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26104298780505032170822853 4894556021344693532029285)
                  ·
                    refine ⟨917729254002130037255491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4894556021344693532029285 917729254002130037255491)
                    ·
                      rfl

theorem cell23_5361814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_5361814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361814 prefixEnd_5361814 := by exact prefixLift 5361814
  have htrace : WordTrace (prefixWord ++ tailWord_5361814) baseStart_5361814 baseEnd_5361814 := by
    simpa [prefixWord, tailWord_5361814, baseEnd_5361814] using wordTrace_append hprefix tailTrace_5361814
  have hstable : (prefixWord ++ tailWord_5361814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361814).length < 2 ^ (prefixWord ++ tailWord_5361814).sum := by decide
  have hdescent : baseEnd_5361814 < baseStart_5361814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361837 : List Nat := [1, 5, 2, 1, 2, 2, 3, 1, 2, 1, 3]
def baseStart_5361837 : Nat := 118140960795 + 5361837 * 2 ^ 59
def prefixEnd_5361837 : Nat := 4983230072969 + 3 ^ 40 * 5361837 * 2
def baseEnd_5361837 : Nat := 2753199572061443521778867

theorem tailTrace_5361837 : CollatzResearch.WordTrace tailWord_5361837 prefixEnd_5361837 2753199572061443521778867 := by
  unfold tailWord_5361837
  simp only [CollatzResearch.WordTrace]
  refine ⟨195562261475987752699811765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130374840983991835133207843 195562261475987752699811765)
  ·
    refine ⟨18333962013373851815607353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 195562261475987752699811765 18333962013373851815607353)
    ·
      refine ⟨13750471510030388861705515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18333962013373851815607353 13750471510030388861705515)
      ·
        refine ⟨20625707265045583292558273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13750471510030388861705515 20625707265045583292558273)
        ·
          refine ⟨15469280448784187469418705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20625707265045583292558273 15469280448784187469418705)
          ·
            refine ⟨11601960336588140602064029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15469280448784187469418705 11601960336588140602064029)
            ·
              refine ⟨4350735126220552725774011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11601960336588140602064029 4350735126220552725774011)
              ·
                refine ⟨6526102689330829088661017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4350735126220552725774011 6526102689330829088661017)
                ·
                  refine ⟨4894577016998121816495763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6526102689330829088661017 4894577016998121816495763)
                  ·
                    refine ⟨7341865525497182724743645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4894577016998121816495763 7341865525497182724743645)
                    ·
                      refine ⟨2753199572061443521778867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7341865525497182724743645 2753199572061443521778867)
                      ·
                        rfl

theorem cell23_5361837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_5361837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361837 prefixEnd_5361837 := by exact prefixLift 5361837
  have htrace : WordTrace (prefixWord ++ tailWord_5361837) baseStart_5361837 baseEnd_5361837 := by
    simpa [prefixWord, tailWord_5361837, baseEnd_5361837] using wordTrace_append hprefix tailTrace_5361837
  have hstable : (prefixWord ++ tailWord_5361837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361837).length < 2 ^ (prefixWord ++ tailWord_5361837).sum := by decide
  have hdescent : baseEnd_5361837 < baseStart_5361837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361844 : List Nat := [2, 5, 3, 1, 2, 1, 2, 7]
def baseStart_5361844 : Nat := 118140960795 + 5361844 * 2 ^ 59
def prefixEnd_5361844 : Nat := 4983230072969 + 3 ^ 40 * 5361844 * 2
def baseEnd_5361844 : Nat := 101970487645408333125605

theorem tailTrace_5361844 : CollatzResearch.WordTrace tailWord_5361844 prefixEnd_5361844 101970487645408333125605 := by
  unfold tailWord_5361844
  simp only [CollatzResearch.WordTrace]
  refine ⟨97781258393481196447658293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130375011191308261930211057 97781258393481196447658293)
  ·
    refine ⟨9166992974388862166967965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97781258393481196447658293 9166992974388862166967965)
    ·
      refine ⟨3437622365395823312612987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9166992974388862166967965 3437622365395823312612987)
      ·
        refine ⟨5156433548093734968919481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3437622365395823312612987 5156433548093734968919481)
        ·
          refine ⟨3867325161070301226689611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5156433548093734968919481 3867325161070301226689611)
          ·
            refine ⟨5800987741605451840034417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3867325161070301226689611 5800987741605451840034417)
            ·
              refine ⟨4350740806204088880025813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5800987741605451840034417 4350740806204088880025813)
              ·
                refine ⟨101970487645408333125605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4350740806204088880025813 101970487645408333125605)
                ·
                  rfl

theorem cell23_5361844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 7].length) (baseStart_5361844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361844 prefixEnd_5361844 := by exact prefixLift 5361844
  have htrace : WordTrace (prefixWord ++ tailWord_5361844) baseStart_5361844 baseEnd_5361844 := by
    simpa [prefixWord, tailWord_5361844, baseEnd_5361844] using wordTrace_append hprefix tailTrace_5361844
  have hstable : (prefixWord ++ tailWord_5361844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361844).length < 2 ^ (prefixWord ++ tailWord_5361844).sum := by decide
  have hdescent : baseEnd_5361844 < baseStart_5361844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361849 : List Nat := [1, 2, 1, 4, 1, 2, 1, 4, 7]
def baseStart_5361849 : Nat := 118140960795 + 5361849 * 2 ^ 59
def prefixEnd_5361849 : Nat := 4983230072969 + 3 ^ 40 * 5361849 * 2
def baseEnd_5361849 : Nat := 305911748203255274980979

theorem tailTrace_5361849 : CollatzResearch.WordTrace tailWord_5361849 prefixEnd_5361849 305911748203255274980979 := by
  unfold tailWord_5361849
  simp only [CollatzResearch.WordTrace]
  refine ⟨195562699151944278749248601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130375132767962852499499067 195562699151944278749248601)
  ·
    refine ⟨146672024363958209061936451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195562699151944278749248601 146672024363958209061936451)
    ·
      refine ⟨220008036545937313592904677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146672024363958209061936451 220008036545937313592904677)
      ·
        refine ⟨41251506852363246298669627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220008036545937313592904677 41251506852363246298669627)
        ·
          refine ⟨61877260278544869448004441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41251506852363246298669627 61877260278544869448004441)
          ·
            refine ⟨46407945208908652086003331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61877260278544869448004441 46407945208908652086003331)
            ·
              refine ⟨69611917813362978129004997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46407945208908652086003331 69611917813362978129004997)
              ·
                refine ⟨13052234590005558399188437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69611917813362978129004997 13052234590005558399188437)
                ·
                  refine ⟨305911748203255274980979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13052234590005558399188437 305911748203255274980979)
                  ·
                    rfl

theorem cell23_5361849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 7].length) (baseStart_5361849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361849 prefixEnd_5361849 := by exact prefixLift 5361849
  have htrace : WordTrace (prefixWord ++ tailWord_5361849) baseStart_5361849 baseEnd_5361849 := by
    simpa [prefixWord, tailWord_5361849, baseEnd_5361849] using wordTrace_append hprefix tailTrace_5361849
  have hstable : (prefixWord ++ tailWord_5361849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361849).length < 2 ^ (prefixWord ++ tailWord_5361849).sum := by decide
  have hdescent : baseEnd_5361849 < baseStart_5361849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361860 : List Nat := [2, 3, 3, 1, 2, 1, 1, 2, 4, 2, 2]
def baseStart_5361860 : Nat := 118140960795 + 5361860 * 2 ^ 59
def prefixEnd_5361860 : Nat := 4983230072969 + 3 ^ 40 * 5361860 * 2
def baseEnd_5361860 : Nat := 2753211382116496931791261

theorem tailTrace_5361860 : CollatzResearch.WordTrace tailWord_5361860 prefixEnd_5361860 2753211382116496931791261 := by
  unfold tailWord_5361860
  simp only [CollatzResearch.WordTrace]
  refine ⟨97781550177452213813949517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130375400236602951751932689 97781550177452213813949517)
  ·
    refine ⟨36668081316544580180231069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97781550177452213813949517 36668081316544580180231069)
    ·
      refine ⟨13750530493704217567586651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36668081316544580180231069 13750530493704217567586651)
      ·
        refine ⟨20625795740556326351379977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13750530493704217567586651 20625795740556326351379977)
        ·
          refine ⟨15469346805417244763534983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20625795740556326351379977 15469346805417244763534983)
          ·
            refine ⟨23204020208125867145302475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15469346805417244763534983 23204020208125867145302475)
            ·
              refine ⟨34806030312188800717953713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23204020208125867145302475 34806030312188800717953713)
              ·
                refine ⟨26104522734141600538465285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34806030312188800717953713 26104522734141600538465285)
                ·
                  refine ⟨4894598012651550100962241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26104522734141600538465285 4894598012651550100962241)
                  ·
                    refine ⟨3670948509488662575721681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4894598012651550100962241 3670948509488662575721681)
                    ·
                      refine ⟨2753211382116496931791261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3670948509488662575721681 2753211382116496931791261)
                      ·
                        rfl

theorem cell23_5361860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_5361860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361860 prefixEnd_5361860 := by exact prefixLift 5361860
  have htrace : WordTrace (prefixWord ++ tailWord_5361860) baseStart_5361860 baseEnd_5361860 := by
    simpa [prefixWord, tailWord_5361860, baseEnd_5361860] using wordTrace_append hprefix tailTrace_5361860
  have hstable : (prefixWord ++ tailWord_5361860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361860).length < 2 ^ (prefixWord ++ tailWord_5361860).sum := by decide
  have hdescent : baseEnd_5361860 < baseStart_5361860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361939 : List Nat := [1, 1, 1, 2, 1, 3, 1, 5, 8]
def baseStart_5361939 : Nat := 118140960795 + 5361939 * 2 ^ 59
def prefixEnd_5361939 : Nat := 4983230072969 + 3 ^ 40 * 5361939 * 2
def baseEnd_5361939 : Nat := 305916883009800235855933

theorem tailTrace_5361939 : CollatzResearch.WordTrace tailWord_5361939 prefixEnd_5361939 305916883009800235855933 := by
  unfold tailWord_5361939
  simp only [CollatzResearch.WordTrace]
  refine ⟨195565981721618224120024871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130377321147745482746683247 195565981721618224120024871)
  ·
    refine ⟨293348972582427336180037307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195565981721618224120024871 293348972582427336180037307)
    ·
      refine ⟨440023458873641004270055961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293348972582427336180037307 440023458873641004270055961)
      ·
        refine ⟨330017594155230753202541971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 440023458873641004270055961 330017594155230753202541971)
        ·
          refine ⟨495026391232846129803812957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330017594155230753202541971 495026391232846129803812957)
          ·
            refine ⟨185634896712317298676429859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 495026391232846129803812957 185634896712317298676429859)
            ·
              refine ⟨278452345068475948014644789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185634896712317298676429859 278452345068475948014644789)
              ·
                refine ⟨26104907350169620126372949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 278452345068475948014644789 26104907350169620126372949)
                ·
                  refine ⟨305916883009800235855933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26104907350169620126372949 305916883009800235855933)
                  ·
                    rfl

theorem cell23_5361939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 8].length) (baseStart_5361939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361939 prefixEnd_5361939 := by exact prefixLift 5361939
  have htrace : WordTrace (prefixWord ++ tailWord_5361939) baseStart_5361939 baseEnd_5361939 := by
    simpa [prefixWord, tailWord_5361939, baseEnd_5361939] using wordTrace_append hprefix tailTrace_5361939
  have hstable : (prefixWord ++ tailWord_5361939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361939).length < 2 ^ (prefixWord ++ tailWord_5361939).sum := by decide
  have hdescent : baseEnd_5361939 < baseStart_5361939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361960 : List Nat := [2, 1, 5, 1, 3, 1, 1, 2, 3, 4]
def baseStart_5361960 : Nat := 118140960795 + 5361960 * 2 ^ 59
def prefixEnd_5361960 : Nat := 4983230072969 + 3 ^ 40 * 5361960 * 2
def baseEnd_5361960 : Nat := 917754243393982180180267

theorem tailTrace_5361960 : CollatzResearch.WordTrace tailWord_5361960 prefixEnd_5361960 917754243393982180180267 := by
  unfold tailWord_5361960
  simp only [CollatzResearch.WordTrace]
  refine ⟨97783373827271072353269667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130377831769694763137692889 97783373827271072353269667)
  ·
    refine ⟨146675060740906608529904501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97783373827271072353269667 146675060740906608529904501)
    ·
      refine ⟨13750786944459994549678547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 146675060740906608529904501 13750786944459994549678547)
      ·
        refine ⟨20626180416689991824517821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13750786944459994549678547 20626180416689991824517821)
        ·
          refine ⟨7734817656258746934194183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20626180416689991824517821 7734817656258746934194183)
          ·
            refine ⟨11602226484388120401291275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7734817656258746934194183 11602226484388120401291275)
            ·
              refine ⟨17403339726582180601936913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11602226484388120401291275 17403339726582180601936913)
              ·
                refine ⟨13052504794936635451452685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17403339726582180601936913 13052504794936635451452685)
                ·
                  refine ⟨4894689298101238294294757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13052504794936635451452685 4894689298101238294294757)
                  ·
                    refine ⟨917754243393982180180267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4894689298101238294294757 917754243393982180180267)
                    ·
                      rfl

theorem cell23_5361960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_5361960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361960 prefixEnd_5361960 := by exact prefixLift 5361960
  have htrace : WordTrace (prefixWord ++ tailWord_5361960) baseStart_5361960 baseEnd_5361960 := by
    simpa [prefixWord, tailWord_5361960, baseEnd_5361960] using wordTrace_append hprefix tailTrace_5361960
  have hstable : (prefixWord ++ tailWord_5361960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361960).length < 2 ^ (prefixWord ++ tailWord_5361960).sum := by decide
  have hdescent : baseEnd_5361960 < baseStart_5361960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
