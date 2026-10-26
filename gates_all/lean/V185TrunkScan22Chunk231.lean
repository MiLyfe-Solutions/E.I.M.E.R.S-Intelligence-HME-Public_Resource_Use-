import V185TrunkScan22Chunk230

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2059225 : List Nat := [1, 2, 1, 2, 5, 2, 2, 1, 6]
def baseStart_2059225 : Nat := 118140960795 + 2059225 * 2 ^ 59
def prefixEnd_2059225 : Nat := 4983230072969 + 3 ^ 40 * 2059225 * 2
def baseEnd_2059225 : Nat := 234971600167735779203845

theorem tailTrace_2059225 : CollatzResearch.WordTrace tailWord_2059225 prefixEnd_2059225 234971600167735779203845 := by
  unfold tailWord_2059225
  simp only [CollatzResearch.WordTrace]
  refine ⟨75106105964786987475827129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50070737309857991650551419 75106105964786987475827129)
  ·
    refine ⟨56329579473590240606870347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75106105964786987475827129 56329579473590240606870347)
    ·
      refine ⟨84494369210385360910305521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56329579473590240606870347 84494369210385360910305521)
      ·
        refine ⟨63370776907789020682729141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84494369210385360910305521 63370776907789020682729141)
        ·
          refine ⟨5941010335105220689005857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63370776907789020682729141 5941010335105220689005857)
          ·
            refine ⟨4455757751328915516754393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5941010335105220689005857 4455757751328915516754393)
            ·
              refine ⟨3341818313496686637565795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4455757751328915516754393 3341818313496686637565795)
              ·
                refine ⟨5012727470245029956348693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3341818313496686637565795 5012727470245029956348693)
                ·
                  refine ⟨234971600167735779203845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5012727470245029956348693 234971600167735779203845)
                  ·
                    rfl

theorem cell22_2059225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 6].length) (baseStart_2059225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2059225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2059225 prefixEnd_2059225 := by exact prefixLift 2059225
  have htrace : WordTrace (prefixWord ++ tailWord_2059225) baseStart_2059225 baseEnd_2059225 := by
    simpa [prefixWord, tailWord_2059225, baseEnd_2059225] using wordTrace_append hprefix tailTrace_2059225
  have hstable : (prefixWord ++ tailWord_2059225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059225).length < 2 ^ (prefixWord ++ tailWord_2059225).sum := by decide
  have hdescent : baseEnd_2059225 < baseStart_2059225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059240 : List Nat := [2, 1, 4, 1, 1, 1, 5, 1, 1, 5]
def baseStart_2059240 : Nat := 118140960795 + 2059240 * 2 ^ 59
def prefixEnd_2059240 : Nat := 4983230072969 + 3 ^ 40 * 2059240 * 2
def baseEnd_2059240 : Nat := 704919935309752298486489

theorem tailTrace_2059240 : CollatzResearch.WordTrace tailWord_2059240 prefixEnd_2059240 704919935309752298486489 := by
  unfold tailWord_2059240
  simp only [CollatzResearch.WordTrace]
  refine ⟨37553326529866322518811587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50071102039821763358415449 37553326529866322518811587)
  ·
    refine ⟨56329989794799483778217381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37553326529866322518811587 56329989794799483778217381)
    ·
      refine ⟨10561873086524903208415759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56329989794799483778217381 10561873086524903208415759)
      ·
        refine ⟨15842809629787354812623639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10561873086524903208415759 15842809629787354812623639)
        ·
          refine ⟨23764214444681032218935459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15842809629787354812623639 23764214444681032218935459)
          ·
            refine ⟨35646321667021548328403189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23764214444681032218935459 35646321667021548328403189)
            ·
              refine ⟨3341842656283270155787799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35646321667021548328403189 3341842656283270155787799)
              ·
                refine ⟨5012763984424905233681699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3341842656283270155787799 5012763984424905233681699)
                ·
                  refine ⟨7519145976637357850522549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5012763984424905233681699 7519145976637357850522549)
                  ·
                    refine ⟨704919935309752298486489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7519145976637357850522549 704919935309752298486489)
                    ·
                      rfl

theorem cell22_2059240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_2059240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2059240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2059240 prefixEnd_2059240 := by exact prefixLift 2059240
  have htrace : WordTrace (prefixWord ++ tailWord_2059240) baseStart_2059240 baseEnd_2059240 := by
    simpa [prefixWord, tailWord_2059240, baseEnd_2059240] using wordTrace_append hprefix tailTrace_2059240
  have hstable : (prefixWord ++ tailWord_2059240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059240).length < 2 ^ (prefixWord ++ tailWord_2059240).sum := by decide
  have hdescent : baseEnd_2059240 < baseStart_2059240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059252 : List Nat := [2, 6, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_2059252 : Nat := 118140960795 + 2059252 * 2 ^ 59
def prefixEnd_2059252 : Nat := 4983230072969 + 3 ^ 40 * 2059252 * 2
def baseEnd_2059252 : Nat := 704924043154988267186453

theorem tailTrace_2059252 : CollatzResearch.WordTrace tailWord_2059252 prefixEnd_2059252 704924043154988267186453 := by
  unfold tailWord_2059252
  simp only [CollatzResearch.WordTrace]
  refine ⟨37553545367844585543530005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50071393823792780724706673 37553545367844585543530005)
  ·
    refine ⟨1760322439117714947352969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37553545367844585543530005 1760322439117714947352969)
    ·
      refine ⟨1320241829338286210514727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1760322439117714947352969 1320241829338286210514727)
      ·
        refine ⟨1980362744007429315772091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1320241829338286210514727 1980362744007429315772091)
        ·
          refine ⟨2970544116011143973658137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1980362744007429315772091 2970544116011143973658137)
          ·
            refine ⟨2227908087008357980243603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2970544116011143973658137 2227908087008357980243603)
            ·
              refine ⟨3341862130512536970365405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2227908087008357980243603 3341862130512536970365405)
              ·
                refine ⟨1253198298942201363887027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3341862130512536970365405 1253198298942201363887027)
                ·
                  refine ⟨1879797448413302045830541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1253198298942201363887027 1879797448413302045830541)
                  ·
                    refine ⟨704924043154988267186453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1879797448413302045830541 704924043154988267186453)
                    ·
                      rfl

theorem cell22_2059252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_2059252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2059252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2059252 prefixEnd_2059252 := by exact prefixLift 2059252
  have htrace : WordTrace (prefixWord ++ tailWord_2059252) baseStart_2059252 baseEnd_2059252 := by
    simpa [prefixWord, tailWord_2059252, baseEnd_2059252] using wordTrace_append hprefix tailTrace_2059252
  have hstable : (prefixWord ++ tailWord_2059252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059252).length < 2 ^ (prefixWord ++ tailWord_2059252).sum := by decide
  have hdescent : baseEnd_2059252 < baseStart_2059252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059283 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 2, 6]
def baseStart_2059283 : Nat := 118140960795 + 2059283 * 2 ^ 59
def prefixEnd_2059283 : Nat := 4983230072969 + 3 ^ 40 * 2059283 * 2
def baseEnd_2059283 : Nat := 704934655088514519661357

theorem tailTrace_2059283 : CollatzResearch.WordTrace tailWord_2059283 prefixEnd_2059283 704934655088514519661357 := by
  unfold tailWord_2059283
  simp only [CollatzResearch.WordTrace]
  refine ⟨75108221398576863381438503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50072147599051242254292335 75108221398576863381438503)
  ·
    refine ⟨112662332097865295072157755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75108221398576863381438503 112662332097865295072157755)
    ·
      refine ⟨168993498146797942608236633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112662332097865295072157755 168993498146797942608236633)
      ·
        refine ⟨126745123610098456956177475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168993498146797942608236633 126745123610098456956177475)
        ·
          refine ⟨190117685415147685434266213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126745123610098456956177475 190117685415147685434266213)
          ·
            refine ⟨35647066015340191018924915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190117685415147685434266213 35647066015340191018924915)
            ·
              refine ⟨53470599023010286528387373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35647066015340191018924915 53470599023010286528387373)
              ·
                refine ⟨20051474633628857448145265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53470599023010286528387373 20051474633628857448145265)
                ·
                  refine ⟨15038605975221643086108949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20051474633628857448145265 15038605975221643086108949)
                  ·
                    refine ⟨704934655088514519661357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15038605975221643086108949 704934655088514519661357)
                    ·
                      rfl

theorem cell22_2059283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 6].length) (baseStart_2059283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2059283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2059283 prefixEnd_2059283 := by exact prefixLift 2059283
  have htrace : WordTrace (prefixWord ++ tailWord_2059283) baseStart_2059283 baseEnd_2059283 := by
    simpa [prefixWord, tailWord_2059283, baseEnd_2059283] using wordTrace_append hprefix tailTrace_2059283
  have hstable : (prefixWord ++ tailWord_2059283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059283).length < 2 ^ (prefixWord ++ tailWord_2059283).sum := by decide
  have hdescent : baseEnd_2059283 < baseStart_2059283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059345 : List Nat := [1, 2, 2, 1, 3, 1, 3, 2, 3, 4]
def baseStart_2059345 : Nat := 118140960795 + 2059345 * 2 ^ 59
def prefixEnd_2059345 : Nat := 4983230072969 + 3 ^ 40 * 2059345 * 2
def baseEnd_2059345 : Nat := 704955878955567024611167

theorem tailTrace_2059345 : CollatzResearch.WordTrace tailWord_2059345 prefixEnd_2059345 704955878955567024611167 := by
  unfold tailWord_2059345
  simp only [CollatzResearch.WordTrace]
  refine ⟨75110482724352247970195489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50073655149568165313463659 75110482724352247970195489)
  ·
    refine ⟨56332862043264185977646617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75110482724352247970195489 56332862043264185977646617)
    ·
      refine ⟨42249646532448139483234963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56332862043264185977646617 42249646532448139483234963)
      ·
        refine ⟨63374469798672209224852445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42249646532448139483234963 63374469798672209224852445)
        ·
          refine ⟨23765426174502078459319667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63374469798672209224852445 23765426174502078459319667)
          ·
            refine ⟨35648139261753117688979501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23765426174502078459319667 35648139261753117688979501)
            ·
              refine ⟨13368052223157419133367313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35648139261753117688979501 13368052223157419133367313)
              ·
                refine ⟨10026039167368064350025485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13368052223157419133367313 10026039167368064350025485)
                ·
                  refine ⟨3759764687763024131259557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10026039167368064350025485 3759764687763024131259557)
                  ·
                    refine ⟨704955878955567024611167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3759764687763024131259557 704955878955567024611167)
                    ·
                      rfl

theorem cell22_2059345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_2059345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2059345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2059345 prefixEnd_2059345 := by exact prefixLift 2059345
  have htrace : WordTrace (prefixWord ++ tailWord_2059345) baseStart_2059345 baseEnd_2059345 := by
    simpa [prefixWord, tailWord_2059345, baseEnd_2059345] using wordTrace_append hprefix tailTrace_2059345
  have hstable : (prefixWord ++ tailWord_2059345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059345).length < 2 ^ (prefixWord ++ tailWord_2059345).sum := by decide
  have hdescent : baseEnd_2059345 < baseStart_2059345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059360 : List Nat := [2, 1, 1, 3, 2, 2, 3, 2, 6]
def baseStart_2059360 : Nat := 118140960795 + 2059360 * 2 ^ 59
def prefixEnd_2059360 : Nat := 4983230072969 + 3 ^ 40 * 2059360 * 2
def baseEnd_2059360 : Nat := 234987004587370661828707

theorem tailTrace_2059360 : CollatzResearch.WordTrace tailWord_2059360 prefixEnd_2059360 234987004587370661828707 := by
  unfold tailWord_2059360
  simp only [CollatzResearch.WordTrace]
  refine ⟨37555514909648952765995767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50074019879531937021327689 37555514909648952765995767)
  ·
    refine ⟨56333272364473429148993651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37555514909648952765995767 56333272364473429148993651)
    ·
      refine ⟨84499908546710143723490477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56333272364473429148993651 84499908546710143723490477)
      ·
        refine ⟨31687465705016303896308929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84499908546710143723490477 31687465705016303896308929)
        ·
          refine ⟨23765599278762227922231697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31687465705016303896308929 23765599278762227922231697)
          ·
            refine ⟨17824199459071670941673773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23765599278762227922231697 17824199459071670941673773)
            ·
              refine ⟨6684074797151876603127665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17824199459071670941673773 6684074797151876603127665)
              ·
                refine ⟨5013056097863907452345749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6684074797151876603127665 5013056097863907452345749)
                ·
                  refine ⟨234987004587370661828707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5013056097863907452345749 234987004587370661828707)
                  ·
                    rfl

theorem cell22_2059360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 6].length) (baseStart_2059360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2059360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2059360 prefixEnd_2059360 := by exact prefixLift 2059360
  have htrace : WordTrace (prefixWord ++ tailWord_2059360) baseStart_2059360 baseEnd_2059360 := by
    simpa [prefixWord, tailWord_2059360, baseEnd_2059360] using wordTrace_append hprefix tailTrace_2059360
  have hstable : (prefixWord ++ tailWord_2059360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059360).length < 2 ^ (prefixWord ++ tailWord_2059360).sum := by decide
  have hdescent : baseEnd_2059360 < baseStart_2059360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059375 : List Nat := [1, 1, 2, 1, 3, 3, 1, 4, 1, 5]
def baseStart_2059375 : Nat := 118140960795 + 2059375 * 2 ^ 59
def prefixEnd_2059375 : Nat := 4983230072969 + 3 ^ 40 * 2059375 * 2
def baseEnd_2059375 : Nat := 704966148568656946361075

theorem tailTrace_2059375 : CollatzResearch.WordTrace tailWord_2059375 prefixEnd_2059375 704966148568656946361075 := by
  unfold tailWord_2059375
  simp only [CollatzResearch.WordTrace]
  refine ⟨75111576914243563093787579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50074384609495708729191719 75111576914243563093787579)
  ·
    refine ⟨112667365371365344640681369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75111576914243563093787579 112667365371365344640681369)
    ·
      refine ⟨84500524028524008480511027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112667365371365344640681369 84500524028524008480511027)
      ·
        refine ⟨126750786042786012720766541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84500524028524008480511027 126750786042786012720766541)
        ·
          refine ⟨47531544766044754770287453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126750786042786012720766541 47531544766044754770287453)
          ·
            refine ⟨17824329287266783038857795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47531544766044754770287453 17824329287266783038857795)
            ·
              refine ⟨26736493930900174558286693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17824329287266783038857795 26736493930900174558286693)
              ·
                refine ⟨5013092612043782729678755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26736493930900174558286693 5013092612043782729678755)
                ·
                  refine ⟨7519638918065674094518133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5013092612043782729678755 7519638918065674094518133)
                  ·
                    refine ⟨704966148568656946361075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7519638918065674094518133 704966148568656946361075)
                    ·
                      rfl

theorem cell22_2059375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 5].length) (baseStart_2059375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2059375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2059375 prefixEnd_2059375 := by exact prefixLift 2059375
  have htrace : WordTrace (prefixWord ++ tailWord_2059375) baseStart_2059375 baseEnd_2059375 := by
    simpa [prefixWord, tailWord_2059375, baseEnd_2059375] using wordTrace_append hprefix tailTrace_2059375
  have hstable : (prefixWord ++ tailWord_2059375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059375).length < 2 ^ (prefixWord ++ tailWord_2059375).sum := by decide
  have hdescent : baseEnd_2059375 < baseStart_2059375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059460 : List Nat := [2, 3, 3, 1, 4, 1, 2, 1, 2, 3]
def baseStart_2059460 : Nat := 118140960795 + 2059460 * 2 ^ 59
def prefixEnd_2059460 : Nat := 4983230072969 + 3 ^ 40 * 2059460 * 2
def baseEnd_2059460 : Nat := 704995245805745057985815

theorem tailTrace_2059460 : CollatzResearch.WordTrace tailWord_2059460 prefixEnd_2059460 704995245805745057985815 := by
  unfold tailWord_2059460
  simp only [CollatzResearch.WordTrace]
  refine ⟨37557338559467811305315917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50076451412623748407087889 37557338559467811305315917)
  ·
    refine ⟨14084001959800429239493469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37557338559467811305315917 14084001959800429239493469)
    ·
      refine ⟨5281500734925160964810051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14084001959800429239493469 5281500734925160964810051)
      ·
        refine ⟨7922251102387741447215077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5281500734925160964810051 7922251102387741447215077)
        ·
          refine ⟨1485422081697701521352827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7922251102387741447215077 1485422081697701521352827)
          ·
            refine ⟨2228133122546552282029241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1485422081697701521352827 2228133122546552282029241)
            ·
              refine ⟨1671099841909914211521931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2228133122546552282029241 1671099841909914211521931)
              ·
                refine ⟨2506649762864871317282897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1671099841909914211521931 2506649762864871317282897)
                ·
                  refine ⟨1879987322148653487962173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2506649762864871317282897 1879987322148653487962173)
                  ·
                    refine ⟨704995245805745057985815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1879987322148653487962173 704995245805745057985815)
                    ·
                      rfl

theorem cell22_2059460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_2059460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2059460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2059460 prefixEnd_2059460 := by exact prefixLift 2059460
  have htrace : WordTrace (prefixWord ++ tailWord_2059460) baseStart_2059460 baseEnd_2059460 := by
    simpa [prefixWord, tailWord_2059460, baseEnd_2059460] using wordTrace_append hprefix tailTrace_2059460
  have hstable : (prefixWord ++ tailWord_2059460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059460).length < 2 ^ (prefixWord ++ tailWord_2059460).sum := by decide
  have hdescent : baseEnd_2059460 < baseStart_2059460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059465 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 6, 5]
def baseStart_2059465 : Nat := 118140960795 + 2059465 * 2 ^ 59
def prefixEnd_2059465 : Nat := 4983230072969 + 3 ^ 40 * 2059465 * 2
def baseEnd_2059465 : Nat := 704996957407926711610799

theorem tailTrace_2059465 : CollatzResearch.WordTrace tailWord_2059465 prefixEnd_2059465 704996957407926711610799 := by
  unfold tailWord_2059465
  simp only [CollatzResearch.WordTrace]
  refine ⟨75114859483917508464563849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50076572989278338976375899 75114859483917508464563849)
  ·
    refine ⟨56336144612938131348422887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75114859483917508464563849 56336144612938131348422887)
    ·
      refine ⟨84504216919407197022634331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56336144612938131348422887 84504216919407197022634331)
      ·
        refine ⟨126756325379110795533951497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84504216919407197022634331 126756325379110795533951497)
        ·
          refine ⟨95067244034333096650463623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126756325379110795533951497 95067244034333096650463623)
          ·
            refine ⟨142600866051499644975695435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95067244034333096650463623 142600866051499644975695435)
            ·
              refine ⟨213901299077249467463543153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142600866051499644975695435 213901299077249467463543153)
              ·
                refine ⟨160425974307937100597657365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213901299077249467463543153 160425974307937100597657365)
                ·
                  refine ⟨7519967545684551590515189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 160425974307937100597657365 7519967545684551590515189)
                  ·
                    refine ⟨704996957407926711610799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7519967545684551590515189 704996957407926711610799)
                    ·
                      rfl

theorem cell22_2059465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 5].length) (baseStart_2059465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2059465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2059465 prefixEnd_2059465 := by exact prefixLift 2059465
  have htrace : WordTrace (prefixWord ++ tailWord_2059465) baseStart_2059465 baseEnd_2059465 := by
    simpa [prefixWord, tailWord_2059465, baseEnd_2059465] using wordTrace_append hprefix tailTrace_2059465
  have hstable : (prefixWord ++ tailWord_2059465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059465).length < 2 ^ (prefixWord ++ tailWord_2059465).sum := by decide
  have hdescent : baseEnd_2059465 < baseStart_2059465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059546 : List Nat := [3, 1, 1, 3, 3, 2, 2, 3, 4]
def baseStart_2059546 : Nat := 118140960795 + 2059546 * 2 ^ 59
def prefixEnd_2059546 : Nat := 4983230072969 + 3 ^ 40 * 2059546 * 2
def baseEnd_2059546 : Nat := 235008228454423166778517

theorem tailTrace_2059546 : CollatzResearch.WordTrace tailWord_2059546 prefixEnd_2059546 235008228454423166778517 := by
  unfold tailWord_2059546
  simp only [CollatzResearch.WordTrace]
  refine ⟨18779453449156014824565623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50078542531082706198841661 18779453449156014824565623)
  ·
    refine ⟨28169180173734022236848435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18779453449156014824565623 28169180173734022236848435)
    ·
      refine ⟨42253770260601033355272653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28169180173734022236848435 42253770260601033355272653)
      ·
        refine ⟨15845163847725387508227245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42253770260601033355272653 15845163847725387508227245)
        ·
          refine ⟨5941936442897020315585217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15845163847725387508227245 5941936442897020315585217)
          ·
            refine ⟨4456452332172765236688913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5941936442897020315585217 4456452332172765236688913)
            ·
              refine ⟨3342339249129573927516685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4456452332172765236688913 3342339249129573927516685)
              ·
                refine ⟨1253377218423590222818757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3342339249129573927516685 1253377218423590222818757)
                ·
                  refine ⟨235008228454423166778517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1253377218423590222818757 235008228454423166778517)
                  ·
                    rfl

theorem cell22_2059546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3, 4].length) (baseStart_2059546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2059546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2059546 prefixEnd_2059546 := by exact prefixLift 2059546
  have htrace : WordTrace (prefixWord ++ tailWord_2059546) baseStart_2059546 baseEnd_2059546 := by
    simpa [prefixWord, tailWord_2059546, baseEnd_2059546] using wordTrace_append hprefix tailTrace_2059546
  have hstable : (prefixWord ++ tailWord_2059546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059546).length < 2 ^ (prefixWord ++ tailWord_2059546).sum := by decide
  have hdescent : baseEnd_2059546 < baseStart_2059546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059557 : List Nat := [1, 3, 1, 2, 4, 2, 9]
def baseStart_2059557 : Nat := 118140960795 + 2059557 * 2 ^ 59
def prefixEnd_2059557 : Nat := 4983230072969 + 3 ^ 40 * 2059557 * 2
def baseEnd_2059557 : Nat := 26112164847706264381871

theorem tailTrace_2059557 : CollatzResearch.WordTrace tailWord_2059557 prefixEnd_2059557 26112164847706264381871 := by
  unfold tailWord_2059557
  simp only [CollatzResearch.WordTrace]
  refine ⟨75118214999584208176912925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50078809999722805451275283 75118214999584208176912925)
  ·
    refine ⟨28169330624844078066342347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75118214999584208176912925 28169330624844078066342347)
    ·
      refine ⟨42253995937266117099513521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28169330624844078066342347 42253995937266117099513521)
      ·
        refine ⟨31690496952949587824635141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42253995937266117099513521 31690496952949587824635141)
        ·
          refine ⟨5941968178678047717119089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31690496952949587824635141 5941968178678047717119089)
          ·
            refine ⟨4456476134008535787839317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5941968178678047717119089 4456476134008535787839317)
            ·
              refine ⟨26112164847706264381871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4456476134008535787839317 26112164847706264381871)
              ·
                rfl

theorem cell22_2059557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 9].length) (baseStart_2059557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2059557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2059557 prefixEnd_2059557 := by exact prefixLift 2059557
  have htrace : WordTrace (prefixWord ++ tailWord_2059557) baseStart_2059557 baseEnd_2059557 := by
    simpa [prefixWord, tailWord_2059557, baseEnd_2059557] using wordTrace_append hprefix tailTrace_2059557
  have hstable : (prefixWord ++ tailWord_2059557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059557).length < 2 ^ (prefixWord ++ tailWord_2059557).sum := by decide
  have hdescent : baseEnd_2059557 < baseStart_2059557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059597 : List Nat := [1, 6, 1, 3, 2, 1, 1, 3, 4]
def baseStart_2059597 : Nat := 118140960795 + 2059597 * 2 ^ 59
def prefixEnd_2059597 : Nat := 4983230072969 + 3 ^ 40 * 2059597 * 2
def baseEnd_2059597 : Nat := 235014047901840789103465

theorem tailTrace_2059597 : CollatzResearch.WordTrace tailWord_2059597 prefixEnd_2059597 235014047901840789103465 := by
  unfold tailWord_2059597
  simp only [CollatzResearch.WordTrace]
  refine ⟨75119673919439295008369045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50079782612959530005579363 75119673919439295008369045)
  ·
    refine ⟨3521234714973716953517299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75119673919439295008369045 3521234714973716953517299)
    ·
      refine ⟨5281852072460575430275949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3521234714973716953517299 5281852072460575430275949)
      ·
        refine ⟨1980694527172715786353481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5281852072460575430275949 1980694527172715786353481)
        ·
          refine ⟨1485520895379536839765111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1980694527172715786353481 1485520895379536839765111)
          ·
            refine ⟨2228281343069305259647667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1485520895379536839765111 2228281343069305259647667)
            ·
              refine ⟨3342422014603957889471501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2228281343069305259647667 3342422014603957889471501)
              ·
                refine ⟨1253408255476484208551813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3342422014603957889471501 1253408255476484208551813)
                ·
                  refine ⟨235014047901840789103465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1253408255476484208551813 235014047901840789103465)
                  ·
                    rfl

theorem cell22_2059597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_2059597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2059597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2059597 prefixEnd_2059597 := by exact prefixLift 2059597
  have htrace : WordTrace (prefixWord ++ tailWord_2059597) baseStart_2059597 baseEnd_2059597 := by
    simpa [prefixWord, tailWord_2059597, baseEnd_2059597] using wordTrace_append hprefix tailTrace_2059597
  have hstable : (prefixWord ++ tailWord_2059597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059597).length < 2 ^ (prefixWord ++ tailWord_2059597).sum := by decide
  have hdescent : baseEnd_2059597 < baseStart_2059597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059617 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 4, 5]
def baseStart_2059617 : Nat := 118140960795 + 2059617 * 2 ^ 59
def prefixEnd_2059617 : Nat := 4983230072969 + 3 ^ 40 * 2059617 * 2
def baseEnd_2059617 : Nat := 705048990114248981810333

theorem tailTrace_2059617 : CollatzResearch.WordTrace tailWord_2059617 prefixEnd_2059617 705048990114248981810333 := by
  unfold tailWord_2059617
  simp only [CollatzResearch.WordTrace]
  refine ⟨75120403379366838424097105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50080268919577892282731403 75120403379366838424097105)
  ·
    refine ⟨56340302534525128818072829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75120403379366838424097105 56340302534525128818072829)
    ·
      refine ⟨21127613450446923306777311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56340302534525128818072829 21127613450446923306777311)
      ·
        refine ⟨31691420175670384960165967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21127613450446923306777311 31691420175670384960165967)
        ·
          refine ⟨47537130263505577440248951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31691420175670384960165967 47537130263505577440248951)
          ·
            refine ⟨71305695395258366160373427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47537130263505577440248951 71305695395258366160373427)
            ·
              refine ⟨106958543092887549240560141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71305695395258366160373427 106958543092887549240560141)
              ·
                refine ⟨40109453659832830965210053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106958543092887549240560141 40109453659832830965210053)
                ·
                  refine ⟨7520522561218655805976885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40109453659832830965210053 7520522561218655805976885)
                  ·
                    refine ⟨705048990114248981810333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7520522561218655805976885 705048990114248981810333)
                    ·
                      rfl

theorem cell22_2059617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_2059617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2059617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2059617 prefixEnd_2059617 := by exact prefixLift 2059617
  have htrace : WordTrace (prefixWord ++ tailWord_2059617) baseStart_2059617 baseEnd_2059617 := by
    simpa [prefixWord, tailWord_2059617, baseEnd_2059617] using wordTrace_append hprefix tailTrace_2059617
  have hstable : (prefixWord ++ tailWord_2059617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059617).length < 2 ^ (prefixWord ++ tailWord_2059617).sum := by decide
  have hdescent : baseEnd_2059617 < baseStart_2059617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059623 : List Nat := [1, 1, 5, 1, 4, 2, 1, 1, 3, 3]
def baseStart_2059623 : Nat := 118140960795 + 2059623 * 2 ^ 59
def prefixEnd_2059623 : Nat := 4983230072969 + 3 ^ 40 * 2059623 * 2
def baseEnd_2059623 : Nat := 705051044036866966160315

theorem tailTrace_2059623 : CollatzResearch.WordTrace tailWord_2059623 prefixEnd_2059623 705051044036866966160315 := by
  unfold tailWord_2059623
  simp only [CollatzResearch.WordTrace]
  refine ⟨75120622217345101448815523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50080414811563400965877015 75120622217345101448815523)
  ·
    refine ⟨112680933326017652173223285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75120622217345101448815523 112680933326017652173223285)
    ·
      refine ⟨10563837499314154891239683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112680933326017652173223285 10563837499314154891239683)
      ·
        refine ⟨15845756248971232336859525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10563837499314154891239683 15845756248971232336859525)
        ·
          refine ⟨2971079296682106063161161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15845756248971232336859525 2971079296682106063161161)
          ·
            refine ⟨2228309472511579547370871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2971079296682106063161161 2228309472511579547370871)
            ·
              refine ⟨3342464208767369321056307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2228309472511579547370871 3342464208767369321056307)
              ·
                refine ⟨5013696313151053981584461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3342464208767369321056307 5013696313151053981584461)
                ·
                  refine ⟨1880136117431645243094173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5013696313151053981584461 1880136117431645243094173)
                  ·
                    refine ⟨705051044036866966160315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1880136117431645243094173 705051044036866966160315)
                    ·
                      rfl

theorem cell22_2059623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_2059623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2059623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2059623 prefixEnd_2059623 := by exact prefixLift 2059623
  have htrace : WordTrace (prefixWord ++ tailWord_2059623) baseStart_2059623 baseEnd_2059623 := by
    simpa [prefixWord, tailWord_2059623, baseEnd_2059623] using wordTrace_append hprefix tailTrace_2059623
  have hstable : (prefixWord ++ tailWord_2059623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059623).length < 2 ^ (prefixWord ++ tailWord_2059623).sum := by decide
  have hdescent : baseEnd_2059623 < baseStart_2059623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059831 : List Nat := [1, 1, 3, 1, 2, 5, 1, 2, 1, 5]
def baseStart_2059831 : Nat := 118140960795 + 2059831 * 2 ^ 59
def prefixEnd_2059831 : Nat := 4983230072969 + 3 ^ 40 * 2059831 * 2
def baseEnd_2059831 : Nat := 705122246687623756959677

theorem tailTrace_2059831 : CollatzResearch.WordTrace tailWord_2059831 prefixEnd_2059831 705122246687623756959677 := by
  unfold tailWord_2059831
  simp only [CollatzResearch.WordTrace]
  refine ⟨75128208600591552972387347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50085472400394368648258231 75128208600591552972387347)
  ·
    refine ⟨112692312900887329458581021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75128208600591552972387347 112692312900887329458581021)
    ·
      refine ⟨42259617337832748546967883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112692312900887329458581021 42259617337832748546967883)
      ·
        refine ⟨63389426006749122820451825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42259617337832748546967883 63389426006749122820451825)
        ·
          refine ⟨47542069505061842115338869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63389426006749122820451825 47542069505061842115338869)
          ·
            refine ⟨4457069016099547698313019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47542069505061842115338869 4457069016099547698313019)
            ·
              refine ⟨6685603524149321547469529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4457069016099547698313019 6685603524149321547469529)
              ·
                refine ⟨5014202643111991160602147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6685603524149321547469529 5014202643111991160602147)
                ·
                  refine ⟨7521303964667986740903221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5014202643111991160602147 7521303964667986740903221)
                  ·
                    refine ⟨705122246687623756959677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7521303964667986740903221 705122246687623756959677)
                    ·
                      rfl

theorem cell22_2059831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_2059831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2059831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2059831 prefixEnd_2059831 := by exact prefixLift 2059831
  have htrace : WordTrace (prefixWord ++ tailWord_2059831) baseStart_2059831 baseEnd_2059831 := by
    simpa [prefixWord, tailWord_2059831, baseEnd_2059831] using wordTrace_append hprefix tailTrace_2059831
  have hstable : (prefixWord ++ tailWord_2059831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059831).length < 2 ^ (prefixWord ++ tailWord_2059831).sum := by decide
  have hdescent : baseEnd_2059831 < baseStart_2059831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059880 : List Nat := [2, 1, 4, 3, 1, 3, 1, 1, 2, 4]
def baseStart_2059880 : Nat := 118140960795 + 2059880 * 2 ^ 59
def prefixEnd_2059880 : Nat := 4983230072969 + 3 ^ 40 * 2059880 * 2
def baseEnd_2059880 : Nat := 705139020389003962484527

theorem tailTrace_2059880 : CollatzResearch.WordTrace tailWord_2059880 prefixEnd_2059880 705139020389003962484527 := by
  unfold tailWord_2059880
  simp only [CollatzResearch.WordTrace]
  refine ⟨37564997888707017170460547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50086663851609356227280729 37564997888707017170460547)
  ·
    refine ⟨56347496833060525755690821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37564997888707017170460547 56347496833060525755690821)
    ·
      refine ⟨10565155656198848579192029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56347496833060525755690821 10565155656198848579192029)
      ·
        refine ⟨3961933371074568217197011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10565155656198848579192029 3961933371074568217197011)
        ·
          refine ⟨5942900056611852325795517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3961933371074568217197011 5942900056611852325795517)
          ·
            refine ⟨2228587521229444622173319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5942900056611852325795517 2228587521229444622173319)
            ·
              refine ⟨3342881281844166933259979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2228587521229444622173319 3342881281844166933259979)
              ·
                refine ⟨5014321922766250399889969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3342881281844166933259979 5014321922766250399889969)
                ·
                  refine ⟨3760741442074687799917477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5014321922766250399889969 3760741442074687799917477)
                  ·
                    refine ⟨705139020389003962484527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3760741442074687799917477 705139020389003962484527)
                    ·
                      rfl

theorem cell22_2059880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_2059880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2059880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2059880 prefixEnd_2059880 := by exact prefixLift 2059880
  have htrace : WordTrace (prefixWord ++ tailWord_2059880) baseStart_2059880 baseEnd_2059880 := by
    simpa [prefixWord, tailWord_2059880, baseEnd_2059880] using wordTrace_append hprefix tailTrace_2059880
  have hstable : (prefixWord ++ tailWord_2059880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059880).length < 2 ^ (prefixWord ++ tailWord_2059880).sum := by decide
  have hdescent : baseEnd_2059880 < baseStart_2059880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059974 : List Nat := [6, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_2059974 : Nat := 118140960795 + 2059974 * 2 ^ 59
def prefixEnd_2059974 : Nat := 4983230072969 + 3 ^ 40 * 2059974 * 2
def baseEnd_2059974 : Nat := 235057066170006350211413

theorem tailTrace_2059974 : CollatzResearch.WordTrace tailWord_2059974 prefixEnd_2059974 235057066170006350211413 := by
  unfold tailWord_2059974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2347919507471046512338843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50088949492715658929895317 2347919507471046512338843)
  ·
    refine ⟨3521879261206569768508265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2347919507471046512338843 3521879261206569768508265)
    ·
      refine ⟨2641409445904927326381199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3521879261206569768508265 2641409445904927326381199)
      ·
        refine ⟨3962114168857390989571799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2641409445904927326381199 3962114168857390989571799)
        ·
          refine ⟨5943171253286086484357699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3962114168857390989571799 5943171253286086484357699)
          ·
            refine ⟨8914756879929129726536549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5943171253286086484357699 8914756879929129726536549)
            ·
              refine ⟨1671516914986711823725603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8914756879929129726536549 1671516914986711823725603)
              ·
                refine ⟨2507275372480067735588405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1671516914986711823725603 2507275372480067735588405)
                ·
                  refine ⟨235057066170006350211413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2507275372480067735588405 235057066170006350211413)
                  ·
                    rfl

theorem cell22_2059974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_2059974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2059974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2059974 prefixEnd_2059974 := by exact prefixLift 2059974
  have htrace : WordTrace (prefixWord ++ tailWord_2059974) baseStart_2059974 baseEnd_2059974 := by
    simpa [prefixWord, tailWord_2059974, baseEnd_2059974] using wordTrace_append hprefix tailTrace_2059974
  have hstable : (prefixWord ++ tailWord_2059974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059974).length < 2 ^ (prefixWord ++ tailWord_2059974).sum := by decide
  have hdescent : baseEnd_2059974 < baseStart_2059974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060041 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 9]
def baseStart_2060041 : Nat := 118140960795 + 2060041 * 2 ^ 59
def prefixEnd_2060041 : Nat := 4983230072969 + 3 ^ 40 * 2060041 * 2
def baseEnd_2060041 : Nat := 235064711326417736403011

theorem tailTrace_2060041 : CollatzResearch.WordTrace tailWord_2060041 prefixEnd_2060041 235064711326417736403011 := by
  unfold tailWord_2060041
  simp only [CollatzResearch.WordTrace]
  refine ⟨75135867929830758837531977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50090578619887172558354651 75135867929830758837531977)
  ·
    refine ⟨56351900947373069128148983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75135867929830758837531977 56351900947373069128148983)
    ·
      refine ⟨84527851421059603692223475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56351900947373069128148983 84527851421059603692223475)
      ·
        refine ⟨126791777131589405538335213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84527851421059603692223475 126791777131589405538335213)
        ·
          refine ⟨47546916424346027076875705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126791777131589405538335213 47546916424346027076875705)
          ·
            refine ⟨35660187318259520307656779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47546916424346027076875705 35660187318259520307656779)
            ·
              refine ⟨53490280977389280461485169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35660187318259520307656779 53490280977389280461485169)
              ·
                refine ⟨40117710733041960346113877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53490280977389280461485169 40117710733041960346113877)
                ·
                  refine ⟨235064711326417736403011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40117710733041960346113877 235064711326417736403011)
                  ·
                    rfl

theorem cell22_2060041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 9].length) (baseStart_2060041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060041 prefixEnd_2060041 := by exact prefixLift 2060041
  have htrace : WordTrace (prefixWord ++ tailWord_2060041) baseStart_2060041 baseEnd_2060041 := by
    simpa [prefixWord, tailWord_2060041, baseEnd_2060041] using wordTrace_append hprefix tailTrace_2060041
  have hstable : (prefixWord ++ tailWord_2060041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060041).length < 2 ^ (prefixWord ++ tailWord_2060041).sum := by decide
  have hdescent : baseEnd_2060041 < baseStart_2060041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060103 : List Nat := [1, 1, 4, 1, 2, 1, 4, 2, 6]
def baseStart_2060103 : Nat := 118140960795 + 2060103 * 2 ^ 59
def prefixEnd_2060103 : Nat := 4983230072969 + 3 ^ 40 * 2060103 * 2
def baseEnd_2060103 : Nat := 235071785948768571386281

theorem tailTrace_2060103 : CollatzResearch.WordTrace tailWord_2060103 prefixEnd_2060103 235071785948768571386281 := by
  unfold tailWord_2060103
  simp only [CollatzResearch.WordTrace]
  refine ⟨75138129255606143426288963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50092086170404095617525975 75138129255606143426288963)
  ·
    refine ⟨112707193883409215139433445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75138129255606143426288963 112707193883409215139433445)
    ·
      refine ⟨21132598853139227838643771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112707193883409215139433445 21132598853139227838643771)
      ·
        refine ⟨31698898279708841757965657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21132598853139227838643771 31698898279708841757965657)
        ·
          refine ⟨23774173709781631318474243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31698898279708841757965657 23774173709781631318474243)
          ·
            refine ⟨35661260564672446977711365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23774173709781631318474243 35661260564672446977711365)
            ·
              refine ⟨6686486355876083808320881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35661260564672446977711365 6686486355876083808320881)
              ·
                refine ⟨5014864766907062856240661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6686486355876083808320881 5014864766907062856240661)
                ·
                  refine ⟨235071785948768571386281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5014864766907062856240661 235071785948768571386281)
                  ·
                    rfl

theorem cell22_2060103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 6].length) (baseStart_2060103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060103 prefixEnd_2060103 := by exact prefixLift 2060103
  have htrace : WordTrace (prefixWord ++ tailWord_2060103) baseStart_2060103 baseEnd_2060103 := by
    simpa [prefixWord, tailWord_2060103, baseEnd_2060103] using wordTrace_append hprefix tailTrace_2060103
  have hstable : (prefixWord ++ tailWord_2060103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060103).length < 2 ^ (prefixWord ++ tailWord_2060103).sum := by decide
  have hdescent : baseEnd_2060103 < baseStart_2060103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060105 : List Nat := [1, 2, 1, 1, 2, 4, 4, 2, 1, 4]
def baseStart_2060105 : Nat := 118140960795 + 2060105 * 2 ^ 59
def prefixEnd_2060105 : Nat := 4983230072969 + 3 ^ 40 * 2060105 * 2
def baseEnd_2060105 : Nat := 705216042487178375608837

theorem tailTrace_2060105 : CollatzResearch.WordTrace tailWord_2060105 prefixEnd_2060105 705216042487178375608837 := by
  unfold tailWord_2060105
  simp only [CollatzResearch.WordTrace]
  refine ⟨75138202201598897767861769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50092134801065931845241179 75138202201598897767861769)
  ·
    refine ⟨56353651651199173325896327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75138202201598897767861769 56353651651199173325896327)
    ·
      refine ⟨84530477476798759988844491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56353651651199173325896327 84530477476798759988844491)
      ·
        refine ⟨126795716215198139983266737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84530477476798759988844491 126795716215198139983266737)
        ·
          refine ⟨95096787161398604987450053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126795716215198139983266737 95096787161398604987450053)
          ·
            refine ⟨17830647592762238435146885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95096787161398604987450053 17830647592762238435146885)
            ·
              refine ⟨3343246423642919706590041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17830647592762238435146885 3343246423642919706590041)
              ·
                refine ⟨2507434817732189779942531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3343246423642919706590041 2507434817732189779942531)
                ·
                  refine ⟨3761152226598284669913797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2507434817732189779942531 3761152226598284669913797)
                  ·
                    refine ⟨705216042487178375608837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3761152226598284669913797 705216042487178375608837)
                    ·
                      rfl

theorem cell22_2060105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 4].length) (baseStart_2060105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060105 prefixEnd_2060105 := by exact prefixLift 2060105
  have htrace : WordTrace (prefixWord ++ tailWord_2060105) baseStart_2060105 baseEnd_2060105 := by
    simpa [prefixWord, tailWord_2060105, baseEnd_2060105] using wordTrace_append hprefix tailTrace_2060105
  have hstable : (prefixWord ++ tailWord_2060105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060105).length < 2 ^ (prefixWord ++ tailWord_2060105).sum := by decide
  have hdescent : baseEnd_2060105 < baseStart_2060105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060135 : List Nat := [1, 1, 5, 1, 2, 1, 1, 3, 4, 3]
def baseStart_2060135 : Nat := 118140960795 + 2060135 * 2 ^ 59
def prefixEnd_2060135 : Nat := 4983230072969 + 3 ^ 40 * 2060135 * 2
def baseEnd_2060135 : Nat := 705226312100268297358745

theorem tailTrace_2060135 : CollatzResearch.WordTrace tailWord_2060135 prefixEnd_2060135 705226312100268297358745 := by
  unfold tailWord_2060135
  simp only [CollatzResearch.WordTrace]
  refine ⟨75139296391490212891453859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50092864260993475260969239 75139296391490212891453859)
  ·
    refine ⟨112708944587235319337180789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75139296391490212891453859 112708944587235319337180789)
    ·
      refine ⟨10566463555053311187860699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112708944587235319337180789 10566463555053311187860699)
      ·
        refine ⟨15849695332579966781791049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10566463555053311187860699 15849695332579966781791049)
        ·
          refine ⟨11887271499434975086343287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15849695332579966781791049 11887271499434975086343287)
          ·
            refine ⟨17830907249152462629514931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11887271499434975086343287 17830907249152462629514931)
            ·
              refine ⟨26746360873728693944272397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17830907249152462629514931 26746360873728693944272397)
              ·
                refine ⟨10029885327648260229102149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26746360873728693944272397 10029885327648260229102149)
                ·
                  refine ⟨1880603498934048792956653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10029885327648260229102149 1880603498934048792956653)
                  ·
                    refine ⟨705226312100268297358745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1880603498934048792956653 705226312100268297358745)
                    ·
                      rfl

theorem cell22_2060135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_2060135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060135 prefixEnd_2060135 := by exact prefixLift 2060135
  have htrace : WordTrace (prefixWord ++ tailWord_2060135) baseStart_2060135 baseEnd_2060135 := by
    simpa [prefixWord, tailWord_2060135, baseEnd_2060135] using wordTrace_append hprefix tailTrace_2060135
  have hstable : (prefixWord ++ tailWord_2060135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060135).length < 2 ^ (prefixWord ++ tailWord_2060135).sum := by decide
  have hdescent : baseEnd_2060135 < baseStart_2060135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060167 : List Nat := [1, 1, 4, 2, 4, 1, 2, 1, 2, 4]
def baseStart_2060167 : Nat := 118140960795 + 2060167 * 2 ^ 59
def prefixEnd_2060167 : Nat := 4983230072969 + 3 ^ 40 * 2060167 * 2
def baseEnd_2060167 : Nat := 705237266354230880558647

theorem tailTrace_2060167 : CollatzResearch.WordTrace tailWord_2060167 prefixEnd_2060167 705237266354230880558647 := by
  unfold tailWord_2060167
  simp only [CollatzResearch.WordTrace]
  refine ⟨75140463527374282356618755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50093642351582854904412503 75140463527374282356618755)
  ·
    refine ⟨112710695291061423534928133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75140463527374282356618755 112710695291061423534928133)
    ·
      refine ⟨21133255367074016912799025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112710695291061423534928133 21133255367074016912799025)
      ·
        refine ⟨15849941525305512684599269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21133255367074016912799025 15849941525305512684599269)
        ·
          refine ⟨2971864035994783628362363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15849941525305512684599269 2971864035994783628362363)
          ·
            refine ⟨4457796053992175442543545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2971864035994783628362363 4457796053992175442543545)
            ·
              refine ⟨3343347040494131581907659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4457796053992175442543545 3343347040494131581907659)
              ·
                refine ⟨5015020560741197372861489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3343347040494131581907659 5015020560741197372861489)
                ·
                  refine ⟨3761265420555898029646117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5015020560741197372861489 3761265420555898029646117)
                  ·
                    refine ⟨705237266354230880558647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3761265420555898029646117 705237266354230880558647)
                    ·
                      rfl

theorem cell22_2060167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_2060167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060167 prefixEnd_2060167 := by exact prefixLift 2060167
  have htrace : WordTrace (prefixWord ++ tailWord_2060167) baseStart_2060167 baseEnd_2060167 := by
    simpa [prefixWord, tailWord_2060167, baseEnd_2060167] using wordTrace_append hprefix tailTrace_2060167
  have hstable : (prefixWord ++ tailWord_2060167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060167).length < 2 ^ (prefixWord ++ tailWord_2060167).sum := by decide
  have hdescent : baseEnd_2060167 < baseStart_2060167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060182 : List Nat := [5, 3, 1, 1, 12]
def baseStart_2060182 : Nat := 118140960795 + 2060182 * 2 ^ 59
def prefixEnd_2060182 : Nat := 4983230072969 + 3 ^ 40 * 2060182 * 2
def baseEnd_2060182 : Nat := 2902232103542287413307

theorem tailTrace_2060182 : CollatzResearch.WordTrace tailWord_2060182 prefixEnd_2060182 2902232103542287413307 := by
  unfold tailWord_2060182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4696313163894996244900925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50094007081546626612276533 4696313163894996244900925)
  ·
    refine ⟨1761117436460623591837847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4696313163894996244900925 1761117436460623591837847)
    ·
      refine ⟨2641676154690935387756771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1761117436460623591837847 2641676154690935387756771)
      ·
        refine ⟨3962514232036403081635157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2641676154690935387756771 3962514232036403081635157)
        ·
          refine ⟨2902232103542287413307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3962514232036403081635157 2902232103542287413307)
          ·
            rfl

theorem cell22_2060182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 12].length) (baseStart_2060182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060182 prefixEnd_2060182 := by exact prefixLift 2060182
  have htrace : WordTrace (prefixWord ++ tailWord_2060182) baseStart_2060182 baseEnd_2060182 := by
    simpa [prefixWord, tailWord_2060182, baseEnd_2060182] using wordTrace_append hprefix tailTrace_2060182
  have hstable : (prefixWord ++ tailWord_2060182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060182).length < 2 ^ (prefixWord ++ tailWord_2060182).sum := by decide
  have hdescent : baseEnd_2060182 < baseStart_2060182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060255 : List Nat := [1, 1, 2, 3, 4, 1, 1, 3, 6]
def baseStart_2060255 : Nat := 118140960795 + 2060255 * 2 ^ 59
def prefixEnd_2060255 : Nat := 4983230072969 + 3 ^ 40 * 2060255 * 2
def baseEnd_2060255 : Nat := 235089130184209328119459

theorem tailTrace_2060255 : CollatzResearch.WordTrace tailWord_2060255 prefixEnd_2060255 235089130184209328119459 := by
  unfold tailWord_2060255
  simp only [CollatzResearch.WordTrace]
  refine ⟨75143673151055473385822219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50095782100703648923881479 75143673151055473385822219)
  ·
    refine ⟨112715509726583210078733329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75143673151055473385822219 112715509726583210078733329)
    ·
      refine ⟨84536632294937407559049997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112715509726583210078733329 84536632294937407559049997)
      ·
        refine ⟨31701237110601527834643749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84536632294937407559049997 31701237110601527834643749)
        ·
          refine ⟨5943981958237786468995703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31701237110601527834643749 5943981958237786468995703)
          ·
            refine ⟨8915972937356679703493555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5943981958237786468995703 8915972937356679703493555)
            ·
              refine ⟨13373959406035019555240333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8915972937356679703493555 13373959406035019555240333)
              ·
                refine ⟨5015234777263132333215125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13373959406035019555240333 5015234777263132333215125)
                ·
                  refine ⟨235089130184209328119459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5015234777263132333215125 235089130184209328119459)
                  ·
                    rfl

theorem cell22_2060255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 6].length) (baseStart_2060255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060255 prefixEnd_2060255 := by exact prefixLift 2060255
  have htrace : WordTrace (prefixWord ++ tailWord_2060255) baseStart_2060255 baseEnd_2060255 := by
    simpa [prefixWord, tailWord_2060255, baseEnd_2060255] using wordTrace_append hprefix tailTrace_2060255
  have hstable : (prefixWord ++ tailWord_2060255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060255).length < 2 ^ (prefixWord ++ tailWord_2060255).sum := by decide
  have hdescent : baseEnd_2060255 < baseStart_2060255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060285 : List Nat := [1, 4, 1, 1, 1, 2, 4, 1, 1, 6]
def baseStart_2060285 : Nat := 118140960795 + 2060285 * 2 ^ 59
def prefixEnd_2060285 : Nat := 4983230072969 + 3 ^ 40 * 2060285 * 2
def baseEnd_2060285 : Nat := 705277660165717906108285

theorem tailTrace_2060285 : CollatzResearch.WordTrace tailWord_2060285 prefixEnd_2060285 705277660165717906108285 := by
  unfold tailWord_2060285
  simp only [CollatzResearch.WordTrace]
  refine ⟨75144767340946788509414309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50096511560631192339609539 75144767340946788509414309)
  ·
    refine ⟨14089643876427522845515183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75144767340946788509414309 14089643876427522845515183)
    ·
      refine ⟨21134465814641284268272775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14089643876427522845515183 21134465814641284268272775)
      ·
        refine ⟨31701698721961926402409163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21134465814641284268272775 31701698721961926402409163)
        ·
          refine ⟨47552548082942889603613745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31701698721961926402409163 47552548082942889603613745)
          ·
            refine ⟨35664411062207167202710309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47552548082942889603613745 35664411062207167202710309)
            ·
              refine ⟨6687077074163843850508183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35664411062207167202710309 6687077074163843850508183)
              ·
                refine ⟨10030615611245765775762275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6687077074163843850508183 10030615611245765775762275)
                ·
                  refine ⟨15045923416868648663643413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10030615611245765775762275 15045923416868648663643413)
                  ·
                    refine ⟨705277660165717906108285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15045923416868648663643413 705277660165717906108285)
                    ·
                      rfl

theorem cell22_2060285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_2060285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060285 prefixEnd_2060285 := by exact prefixLift 2060285
  have htrace : WordTrace (prefixWord ++ tailWord_2060285) baseStart_2060285 baseEnd_2060285 := by
    simpa [prefixWord, tailWord_2060285, baseEnd_2060285] using wordTrace_append hprefix tailTrace_2060285
  have hstable : (prefixWord ++ tailWord_2060285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060285).length < 2 ^ (prefixWord ++ tailWord_2060285).sum := by decide
  have hdescent : baseEnd_2060285 < baseStart_2060285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060302 : List Nat := [4, 1, 1, 2, 2, 1, 3, 2, 2, 4]
def baseStart_2060302 : Nat := 118140960795 + 2060302 * 2 ^ 59
def prefixEnd_2060302 : Nat := 4983230072969 + 3 ^ 40 * 2060302 * 2
def baseEnd_2060302 : Nat := 705283479613135528433233

theorem tailTrace_2060302 : CollatzResearch.WordTrace tailWord_2060302 prefixEnd_2060302 705283479613135528433233 := by
  unfold tailWord_2060302
  simp only [CollatzResearch.WordTrace]
  refine ⟨9393173422735650051597895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50096924921256800275188773 9393173422735650051597895)
  ·
    refine ⟨14089760134103475077396843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9393173422735650051597895 14089760134103475077396843)
    ·
      refine ⟨21134640201155212616095265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14089760134103475077396843 21134640201155212616095265)
      ·
        refine ⟨15850980150866409462071449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21134640201155212616095265 15850980150866409462071449)
        ·
          refine ⟨11888235113149807096553587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15850980150866409462071449 11888235113149807096553587)
          ·
            refine ⟨17832352669724710644830381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11888235113149807096553587 17832352669724710644830381)
            ·
              refine ⟨6687132251146766491811393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17832352669724710644830381 6687132251146766491811393)
              ·
                refine ⟨5015349188360074868858545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6687132251146766491811393 5015349188360074868858545)
                ·
                  refine ⟨3761511891270056151643909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5015349188360074868858545 3761511891270056151643909)
                  ·
                    refine ⟨705283479613135528433233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3761511891270056151643909 705283479613135528433233)
                    ·
                      rfl

theorem cell22_2060302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_2060302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060302 prefixEnd_2060302 := by exact prefixLift 2060302
  have htrace : WordTrace (prefixWord ++ tailWord_2060302) baseStart_2060302 baseEnd_2060302 := by
    simpa [prefixWord, tailWord_2060302, baseEnd_2060302] using wordTrace_append hprefix tailTrace_2060302
  have hstable : (prefixWord ++ tailWord_2060302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060302).length < 2 ^ (prefixWord ++ tailWord_2060302).sum := by decide
  have hdescent : baseEnd_2060302 < baseStart_2060302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060317 : List Nat := [1, 4, 2, 2, 2, 2, 2, 7]
def baseStart_2060317 : Nat := 118140960795 + 2060317 * 2 ^ 59
def prefixEnd_2060317 : Nat := 4983230072969 + 3 ^ 40 * 2060317 * 2
def baseEnd_2060317 : Nat := 78365401602186721034243

theorem tailTrace_2060317 : CollatzResearch.WordTrace tailWord_2060317 prefixEnd_2060317 78365401602186721034243 := by
  unfold tailWord_2060317
  simp only [CollatzResearch.WordTrace]
  refine ⟨75145934476830857974579205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50097289651220571983052803 75145934476830857974579205)
  ·
    refine ⟨14089862714405785870233601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75145934476830857974579205 14089862714405785870233601)
    ·
      refine ⟨10567397035804339402675201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14089862714405785870233601 10567397035804339402675201)
      ·
        refine ⟨7925547776853254552006401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10567397035804339402675201 7925547776853254552006401)
        ·
          refine ⟨5944160832639940914004801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7925547776853254552006401 5944160832639940914004801)
          ·
            refine ⟨4458120624479955685503601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5944160832639940914004801 4458120624479955685503601)
            ·
              refine ⟨3343590468359966764127701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4458120624479955685503601 3343590468359966764127701)
              ·
                refine ⟨78365401602186721034243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3343590468359966764127701 78365401602186721034243)
                ·
                  rfl

theorem cell22_2060317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 7].length) (baseStart_2060317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060317 prefixEnd_2060317 := by exact prefixLift 2060317
  have htrace : WordTrace (prefixWord ++ tailWord_2060317) baseStart_2060317 baseEnd_2060317 := by
    simpa [prefixWord, tailWord_2060317, baseEnd_2060317] using wordTrace_append hprefix tailTrace_2060317
  have hstable : (prefixWord ++ tailWord_2060317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060317).length < 2 ^ (prefixWord ++ tailWord_2060317).sum := by decide
  have hdescent : baseEnd_2060317 < baseStart_2060317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060366 : List Nat := [4, 1, 1, 1, 1, 5, 1, 4, 1, 3]
def baseStart_2060366 : Nat := 118140960795 + 2060366 * 2 ^ 59
def prefixEnd_2060366 : Nat := 4983230072969 + 3 ^ 40 * 2060366 * 2
def baseEnd_2060366 : Nat := 705305388121060694833037

theorem tailTrace_2060366 : CollatzResearch.WordTrace tailWord_2060366 prefixEnd_2060366 705305388121060694833037 := by
  unfold tailWord_2060366
  simp only [CollatzResearch.WordTrace]
  refine ⟨9393465206706667417889119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50098481102435559562075301 9393465206706667417889119)
  ·
    refine ⟨14090197810060001126833679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9393465206706667417889119 14090197810060001126833679)
    ·
      refine ⟨21135296715090001690250519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14090197810060001126833679 21135296715090001690250519)
      ·
        refine ⟨31702945072635002535375779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21135296715090001690250519 31702945072635002535375779)
        ·
          refine ⟨47554417608952503803063669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31702945072635002535375779 47554417608952503803063669)
          ·
            refine ⟨4458226650839297231537219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47554417608952503803063669 4458226650839297231537219)
            ·
              refine ⟨6687339976258945847305829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4458226650839297231537219 6687339976258945847305829)
              ·
                refine ⟨1253876245548552346369843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6687339976258945847305829 1253876245548552346369843)
                ·
                  refine ⟨1880814368322828519554765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1253876245548552346369843 1880814368322828519554765)
                  ·
                    refine ⟨705305388121060694833037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1880814368322828519554765 705305388121060694833037)
                    ·
                      rfl

theorem cell22_2060366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_2060366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060366 prefixEnd_2060366 := by exact prefixLift 2060366
  have htrace : WordTrace (prefixWord ++ tailWord_2060366) baseStart_2060366 baseEnd_2060366 := by
    simpa [prefixWord, tailWord_2060366, baseEnd_2060366] using wordTrace_append hprefix tailTrace_2060366
  have hstable : (prefixWord ++ tailWord_2060366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060366).length < 2 ^ (prefixWord ++ tailWord_2060366).sum := by decide
  have hdescent : baseEnd_2060366 < baseStart_2060366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060409 : List Nat := [1, 2, 1, 3, 4, 2, 1, 3, 1, 4]
def baseStart_2060409 : Nat := 118140960795 + 2060409 * 2 ^ 59
def prefixEnd_2060409 : Nat := 4983230072969 + 3 ^ 40 * 2060409 * 2
def baseEnd_2060409 : Nat := 705320107899822916007905

theorem tailTrace_2060409 : CollatzResearch.WordTrace tailWord_2060409 prefixEnd_2060409 705320107899822916007905 := by
  unfold tailWord_2060409
  simp only [CollatzResearch.WordTrace]
  refine ⟨75149289992497557686928281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50099526661665038457952187 75149289992497557686928281)
  ·
    refine ⟨56361967494373168265196211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75149289992497557686928281 56361967494373168265196211)
    ·
      refine ⟨84542951241559752397794317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56361967494373168265196211 84542951241559752397794317)
      ·
        refine ⟨31703606715584907149172869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84542951241559752397794317 31703606715584907149172869)
        ·
          refine ⟨5944426259172170090469913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31703606715584907149172869 5944426259172170090469913)
          ·
            refine ⟨4458319694379127567852435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5944426259172170090469913 4458319694379127567852435)
            ·
              refine ⟨6687479541568691351778653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4458319694379127567852435 6687479541568691351778653)
              ·
                refine ⟨2507804828088259256916995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6687479541568691351778653 2507804828088259256916995)
                ·
                  refine ⟨3761707242132388885375493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2507804828088259256916995 3761707242132388885375493)
                  ·
                    refine ⟨705320107899822916007905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3761707242132388885375493 705320107899822916007905)
                    ·
                      rfl

theorem cell22_2060409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 1, 4].length) (baseStart_2060409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060409 prefixEnd_2060409 := by exact prefixLift 2060409
  have htrace : WordTrace (prefixWord ++ tailWord_2060409) baseStart_2060409 baseEnd_2060409 := by
    simpa [prefixWord, tailWord_2060409, baseEnd_2060409] using wordTrace_append hprefix tailTrace_2060409
  have hstable : (prefixWord ++ tailWord_2060409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060409).length < 2 ^ (prefixWord ++ tailWord_2060409).sum := by decide
  have hdescent : baseEnd_2060409 < baseStart_2060409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060424 : List Nat := [2, 1, 3, 4, 1, 2, 2, 1, 6]
def baseStart_2060424 : Nat := 118140960795 + 2060424 * 2 ^ 59
def prefixEnd_2060424 : Nat := 4983230072969 + 3 ^ 40 * 2060424 * 2
def baseEnd_2060424 : Nat := 235108414235455958960953

theorem tailTrace_2060424 : CollatzResearch.WordTrace tailWord_2060424 prefixEnd_2060424 235108414235455958960953 := by
  unfold tailWord_2060424
  simp only [CollatzResearch.WordTrace]
  refine ⟨37574918543721607624362163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50099891391628810165816217 37574918543721607624362163)
  ·
    refine ⟨56362377815582411436543245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37574918543721607624362163 56362377815582411436543245)
    ·
      refine ⟨21135891680843404288703717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56362377815582411436543245 21135891680843404288703717)
      ·
        refine ⟨3962979690158138304131947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21135891680843404288703717 3962979690158138304131947)
        ·
          refine ⟨5944469535237207456197921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3962979690158138304131947 5944469535237207456197921)
          ·
            refine ⟨4458352151427905592148441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5944469535237207456197921 4458352151427905592148441)
            ·
              refine ⟨3343764113570929194111331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4458352151427905592148441 3343764113570929194111331)
              ·
                refine ⟨5015646170356393791166997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3343764113570929194111331 5015646170356393791166997)
                ·
                  refine ⟨235108414235455958960953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5015646170356393791166997 235108414235455958960953)
                  ·
                    rfl

theorem cell22_2060424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 6].length) (baseStart_2060424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060424 prefixEnd_2060424 := by exact prefixLift 2060424
  have htrace : WordTrace (prefixWord ++ tailWord_2060424) baseStart_2060424 baseEnd_2060424 := by
    simpa [prefixWord, tailWord_2060424, baseEnd_2060424] using wordTrace_append hprefix tailTrace_2060424
  have hstable : (prefixWord ++ tailWord_2060424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060424).length < 2 ^ (prefixWord ++ tailWord_2060424).sum := by decide
  have hdescent : baseEnd_2060424 < baseStart_2060424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060435 : List Nat := [1, 1, 1, 2, 1, 2, 3, 11]
def baseStart_2060435 : Nat := 118140960795 + 2060435 * 2 ^ 59
def prefixEnd_2060435 : Nat := 4983230072969 + 3 ^ 40 * 2060435 * 2
def baseEnd_2060435 : Nat := 78369889803463057206425

theorem tailTrace_2060435 : CollatzResearch.WordTrace tailWord_2060435 prefixEnd_2060435 78369889803463057206425 := by
  unfold tailWord_2060435
  simp only [CollatzResearch.WordTrace]
  refine ⟨75150238290403364127374759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50100158860268909418249839 75150238290403364127374759)
  ·
    refine ⟨112725357435605046191062139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75150238290403364127374759 112725357435605046191062139)
    ·
      refine ⟨169088036153407569286593209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112725357435605046191062139 169088036153407569286593209)
      ·
        refine ⟨126816027115055676964944907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169088036153407569286593209 126816027115055676964944907)
        ·
          refine ⟨190224040672583515447417361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126816027115055676964944907 190224040672583515447417361)
          ·
            refine ⟨142668030504437636585563021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190224040672583515447417361 142668030504437636585563021)
            ·
              refine ⟨53500511439164113719586133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142668030504437636585563021 53500511439164113719586133)
              ·
                refine ⟨78369889803463057206425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 53500511439164113719586133 78369889803463057206425)
                ·
                  rfl

theorem cell22_2060435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 11].length) (baseStart_2060435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060435 prefixEnd_2060435 := by exact prefixLift 2060435
  have htrace : WordTrace (prefixWord ++ tailWord_2060435) baseStart_2060435 baseEnd_2060435 := by
    simpa [prefixWord, tailWord_2060435, baseEnd_2060435] using wordTrace_append hprefix tailTrace_2060435
  have hstable : (prefixWord ++ tailWord_2060435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060435).length < 2 ^ (prefixWord ++ tailWord_2060435).sum := by decide
  have hdescent : baseEnd_2060435 < baseStart_2060435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060546 : List Nat := [3, 4, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_2060546 : Nat := 118140960795 + 2060546 * 2 ^ 59
def prefixEnd_2060546 : Nat := 4983230072969 + 3 ^ 40 * 2060546 * 2
def baseEnd_2060546 : Nat := 705367005799600225332485

theorem tailTrace_2060546 : CollatzResearch.WordTrace tailWord_2060546 prefixEnd_2060546 705367005799600225332485 := by
  unfold tailWord_2060546
  simp only [CollatzResearch.WordTrace]
  refine ⟨18788571698250307521166373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50102857862000820056443661 18788571698250307521166373)
  ·
    refine ⟨3522857193421932660218695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18788571698250307521166373 3522857193421932660218695)
    ·
      refine ⟨5284285790132898990328043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3522857193421932660218695 5284285790132898990328043)
      ·
        refine ⟨7926428685199348485492065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5284285790132898990328043 7926428685199348485492065)
        ·
          refine ⟨5944821513899511364119049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7926428685199348485492065 5944821513899511364119049)
          ·
            refine ⟨4458616135424633523089287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5944821513899511364119049 4458616135424633523089287)
            ·
              refine ⟨6687924203136950284633931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4458616135424633523089287 6687924203136950284633931)
              ·
                refine ⟨10031886304705425426950897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6687924203136950284633931 10031886304705425426950897)
                ·
                  refine ⟨7523914728529069070213173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10031886304705425426950897 7523914728529069070213173)
                  ·
                    refine ⟨705367005799600225332485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7523914728529069070213173 705367005799600225332485)
                    ·
                      rfl

theorem cell22_2060546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_2060546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060546 prefixEnd_2060546 := by exact prefixLift 2060546
  have htrace : WordTrace (prefixWord ++ tailWord_2060546) baseStart_2060546 baseEnd_2060546 := by
    simpa [prefixWord, tailWord_2060546, baseEnd_2060546] using wordTrace_append hprefix tailTrace_2060546
  have hstable : (prefixWord ++ tailWord_2060546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060546).length < 2 ^ (prefixWord ++ tailWord_2060546).sum := by decide
  have hdescent : baseEnd_2060546 < baseStart_2060546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060576 : List Nat := [2, 1, 1, 5, 2, 1, 1, 5, 4]
def baseStart_2060576 : Nat := 118140960795 + 2060576 * 2 ^ 59
def prefixEnd_2060576 : Nat := 4983230072969 + 3 ^ 40 * 2060576 * 2
def baseEnd_2060576 : Nat := 235125758470896715694131

theorem tailTrace_2060576 : CollatzResearch.WordTrace tailWord_2060576 prefixEnd_2060576 235125758470896715694131 := by
  unfold tailWord_2060576
  simp only [CollatzResearch.WordTrace]
  refine ⟨37577690491446272604128791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50103587321928363472171721 37577690491446272604128791)
  ·
    refine ⟨56366535737169408906193187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37577690491446272604128791 56366535737169408906193187)
    ·
      refine ⟨84549803605754113359289781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56366535737169408906193187 84549803605754113359289781)
      ·
        refine ⟨7926544088039448127433417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84549803605754113359289781 7926544088039448127433417)
        ·
          refine ⟨5944908066029586095575063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7926544088039448127433417 5944908066029586095575063)
          ·
            refine ⟨8917362099044379143362595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5944908066029586095575063 8917362099044379143362595)
            ·
              refine ⟨13376043148566568715043893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8917362099044379143362595 13376043148566568715043893)
              ·
                refine ⟨1254004045178115817035365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13376043148566568715043893 1254004045178115817035365)
                ·
                  refine ⟨235125758470896715694131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1254004045178115817035365 235125758470896715694131)
                  ·
                    rfl

theorem cell22_2060576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5, 4].length) (baseStart_2060576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060576 prefixEnd_2060576 := by exact prefixLift 2060576
  have htrace : WordTrace (prefixWord ++ tailWord_2060576) baseStart_2060576 baseEnd_2060576 := by
    simpa [prefixWord, tailWord_2060576, baseEnd_2060576] using wordTrace_append hprefix tailTrace_2060576
  have hstable : (prefixWord ++ tailWord_2060576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060576).length < 2 ^ (prefixWord ++ tailWord_2060576).sum := by decide
  have hdescent : baseEnd_2060576 < baseStart_2060576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060578 : List Nat := [3, 3, 1, 1, 3, 1, 4, 1, 1, 4]
def baseStart_2060578 : Nat := 118140960795 + 2060578 * 2 ^ 59
def prefixEnd_2060578 : Nat := 4983230072969 + 3 ^ 40 * 2060578 * 2
def baseEnd_2060578 : Nat := 705377960053562808532387

theorem tailTrace_2060578 : CollatzResearch.WordTrace tailWord_2060578 prefixEnd_2060578 705377960053562808532387 := by
  unfold tailWord_2060578
  simp only [CollatzResearch.WordTrace]
  refine ⟨18788863482221324887457597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50103635952590199699886925 18788863482221324887457597)
  ·
    refine ⟨7045823805832996832796599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18788863482221324887457597 7045823805832996832796599)
    ·
      refine ⟨10568735708749495249194899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7045823805832996832796599 10568735708749495249194899)
      ·
        refine ⟨15853103563124242873792349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10568735708749495249194899 15853103563124242873792349)
        ·
          refine ⟨5944913836171591077672131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15853103563124242873792349 5944913836171591077672131)
          ·
            refine ⟨8917370754257386616508197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5944913836171591077672131 8917370754257386616508197)
            ·
              refine ⟨1672007016423259990595287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8917370754257386616508197 1672007016423259990595287)
              ·
                refine ⟨2508010524634889985892931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1672007016423259990595287 2508010524634889985892931)
                ·
                  refine ⟨3762015786952334978839397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2508010524634889985892931 3762015786952334978839397)
                  ·
                    refine ⟨705377960053562808532387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3762015786952334978839397 705377960053562808532387)
                    ·
                      rfl

theorem cell22_2060578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_2060578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060578 prefixEnd_2060578 := by exact prefixLift 2060578
  have htrace : WordTrace (prefixWord ++ tailWord_2060578) baseStart_2060578 baseEnd_2060578 := by
    simpa [prefixWord, tailWord_2060578, baseEnd_2060578] using wordTrace_append hprefix tailTrace_2060578
  have hstable : (prefixWord ++ tailWord_2060578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060578).length < 2 ^ (prefixWord ++ tailWord_2060578).sum := by decide
  have hdescent : baseEnd_2060578 < baseStart_2060578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060591 : List Nat := [1, 1, 2, 1, 2, 1, 7, 2, 2, 3]
def baseStart_2060591 : Nat := 118140960795 + 2060591 * 2 ^ 59
def prefixEnd_2060591 : Nat := 4983230072969 + 3 ^ 40 * 2060591 * 2
def baseEnd_2060591 : Nat := 705382410219235107957347

theorem tailTrace_2060591 : CollatzResearch.WordTrace tailWord_2060591 prefixEnd_2060591 705382410219235107957347 := by
  unfold tailWord_2060591
  simp only [CollatzResearch.WordTrace]
  refine ⟨75155928077838202770053627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50103952051892135180035751 75155928077838202770053627)
  ·
    refine ⟨112733892116757304155080441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75155928077838202770053627 112733892116757304155080441)
    ·
      refine ⟨84550419087567978116310331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112733892116757304155080441 84550419087567978116310331)
      ·
        refine ⟨126825628631351967174465497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84550419087567978116310331 126825628631351967174465497)
        ·
          refine ⟨95119221473513975380849123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126825628631351967174465497 95119221473513975380849123)
          ·
            refine ⟨142678832210270963071273685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95119221473513975380849123 142678832210270963071273685)
            ·
              refine ⟨3344035129928225696982977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 142678832210270963071273685 3344035129928225696982977)
              ·
                refine ⟨2508026347446169272737233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3344035129928225696982977 2508026347446169272737233)
                ·
                  refine ⟨1881019760584626954552925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2508026347446169272737233 1881019760584626954552925)
                  ·
                    refine ⟨705382410219235107957347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1881019760584626954552925 705382410219235107957347)
                    ·
                      rfl

theorem cell22_2060591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 2, 3].length) (baseStart_2060591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060591 prefixEnd_2060591 := by exact prefixLift 2060591
  have htrace : WordTrace (prefixWord ++ tailWord_2060591) baseStart_2060591 baseEnd_2060591 := by
    simpa [prefixWord, tailWord_2060591, baseEnd_2060591] using wordTrace_append hprefix tailTrace_2060591
  have hstable : (prefixWord ++ tailWord_2060591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060591).length < 2 ^ (prefixWord ++ tailWord_2060591).sum := by decide
  have hdescent : baseEnd_2060591 < baseStart_2060591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060619 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 5, 3]
def baseStart_2060619 : Nat := 118140960795 + 2060619 * 2 ^ 59
def prefixEnd_2060619 : Nat := 4983230072969 + 3 ^ 40 * 2060619 * 2
def baseEnd_2060619 : Nat := 705391995191452368257261

theorem tailTrace_2060619 : CollatzResearch.WordTrace tailWord_2060619 prefixEnd_2060619 705391995191452368257261 := by
  unfold tailWord_2060619
  simp only [CollatzResearch.WordTrace]
  refine ⟨75156949321736763552072911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50104632881157842368048607 75156949321736763552072911)
  ·
    refine ⟨112735423982605145328109367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75156949321736763552072911 112735423982605145328109367)
    ·
      refine ⟨169103135973907717992164051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112735423982605145328109367 169103135973907717992164051)
      ·
        refine ⟨253654703960861576988246077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169103135973907717992164051 253654703960861576988246077)
        ·
          refine ⟨95120513985323091370592279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253654703960861576988246077 95120513985323091370592279)
          ·
            refine ⟨142680770977984637055888419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95120513985323091370592279 142680770977984637055888419)
            ·
              refine ⟨214021156466976955583832629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142680770977984637055888419 214021156466976955583832629)
              ·
                refine ⟨20064483418779089585984309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 214021156466976955583832629 20064483418779089585984309)
                ·
                  refine ⟨1881045320510539648686029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20064483418779089585984309 1881045320510539648686029)
                  ·
                    refine ⟨705391995191452368257261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1881045320510539648686029 705391995191452368257261)
                    ·
                      rfl

theorem cell22_2060619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 5, 3].length) (baseStart_2060619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060619 prefixEnd_2060619 := by exact prefixLift 2060619
  have htrace : WordTrace (prefixWord ++ tailWord_2060619) baseStart_2060619 baseEnd_2060619 := by
    simpa [prefixWord, tailWord_2060619, baseEnd_2060619] using wordTrace_append hprefix tailTrace_2060619
  have hstable : (prefixWord ++ tailWord_2060619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060619).length < 2 ^ (prefixWord ++ tailWord_2060619).sum := by decide
  have hdescent : baseEnd_2060619 < baseStart_2060619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060649 : List Nat := [1, 2, 1, 1, 1, 3, 4, 4, 5]
def baseStart_2060649 : Nat := 118140960795 + 2060649 * 2 ^ 59
def prefixEnd_2060649 : Nat := 4983230072969 + 3 ^ 40 * 2060649 * 2
def baseEnd_2060649 : Nat := 235134088268180763335723

theorem tailTrace_2060649 : CollatzResearch.WordTrace tailWord_2060649 prefixEnd_2060649 235134088268180763335723 := by
  unfold tailWord_2060649
  simp only [CollatzResearch.WordTrace]
  refine ⟨75158043511628078675665001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50105362341085385783776667 75158043511628078675665001)
  ·
    refine ⟨56368532633721059006748751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75158043511628078675665001 56368532633721059006748751)
    ·
      refine ⟨84552798950581588510123127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56368532633721059006748751 84552798950581588510123127)
      ·
        refine ⟨126829198425872382765184691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84552798950581588510123127 126829198425872382765184691)
        ·
          refine ⟨190243797638808574147777037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126829198425872382765184691 190243797638808574147777037)
          ·
            refine ⟨71341424114553215305416389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190243797638808574147777037 71341424114553215305416389)
            ·
              refine ⟨13376517021478727869765573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71341424114553215305416389 13376517021478727869765573)
              ·
                refine ⟨2508096941527261475581045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13376517021478727869765573 2508096941527261475581045)
                ·
                  refine ⟨235134088268180763335723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2508096941527261475581045 235134088268180763335723)
                  ·
                    rfl

theorem cell22_2060649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 4, 5].length) (baseStart_2060649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060649 prefixEnd_2060649 := by exact prefixLift 2060649
  have htrace : WordTrace (prefixWord ++ tailWord_2060649) baseStart_2060649 baseEnd_2060649 := by
    simpa [prefixWord, tailWord_2060649, baseEnd_2060649] using wordTrace_append hprefix tailTrace_2060649
  have hstable : (prefixWord ++ tailWord_2060649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060649).length < 2 ^ (prefixWord ++ tailWord_2060649).sum := by decide
  have hdescent : baseEnd_2060649 < baseStart_2060649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060709 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 3, 5]
def baseStart_2060709 : Nat := 118140960795 + 2060709 * 2 ^ 59
def prefixEnd_2060709 : Nat := 4983230072969 + 3 ^ 40 * 2060709 * 2
def baseEnd_2060709 : Nat := 705422804030722133506985

theorem tailTrace_2060709 : CollatzResearch.WordTrace tailWord_2060709 prefixEnd_2060709 705422804030722133506985 := by
  unfold tailWord_2060709
  simp only [CollatzResearch.WordTrace]
  refine ⟨75160231891410708922849181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50106821260940472615232787 75160231891410708922849181)
  ·
    refine ⟨28185086959279015846068443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75160231891410708922849181 28185086959279015846068443)
    ·
      refine ⟨42277630438918523769102665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28185086959279015846068443 42277630438918523769102665)
      ·
        refine ⟨31708222829188892826826999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42277630438918523769102665 31708222829188892826826999)
        ·
          refine ⟨47562334243783339240240499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31708222829188892826826999 47562334243783339240240499)
          ·
            refine ⟨71343501365675008860360749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47562334243783339240240499 71343501365675008860360749)
            ·
              refine ⟨26753813012128128322635281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71343501365675008860360749 26753813012128128322635281)
              ·
                refine ⟨20065359759096096241976461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26753813012128128322635281 20065359759096096241976461)
                ·
                  refine ⟨7524509909661036090741173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20065359759096096241976461 7524509909661036090741173)
                  ·
                    refine ⟨705422804030722133506985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7524509909661036090741173 705422804030722133506985)
                    ·
                      rfl

theorem cell22_2060709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_2060709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060709 prefixEnd_2060709 := by exact prefixLift 2060709
  have htrace : WordTrace (prefixWord ++ tailWord_2060709) baseStart_2060709 baseEnd_2060709 := by
    simpa [prefixWord, tailWord_2060709, baseEnd_2060709] using wordTrace_append hprefix tailTrace_2060709
  have hstable : (prefixWord ++ tailWord_2060709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060709).length < 2 ^ (prefixWord ++ tailWord_2060709).sum := by decide
  have hdescent : baseEnd_2060709 < baseStart_2060709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060756 : List Nat := [2, 4, 1, 2, 2, 2, 9]
def baseStart_2060756 : Nat := 118140960795 + 2060756 * 2 ^ 59
def prefixEnd_2060756 : Nat := 4983230072969 + 3 ^ 40 * 2060756 * 2
def baseEnd_2060756 : Nat := 26127366410786284354883

theorem tailTrace_2060756 : CollatzResearch.WordTrace tailWord_2060756 prefixEnd_2060756 26127366410786284354883 := by
  unfold tailWord_2060756
  simp only [CollatzResearch.WordTrace]
  refine ⟨37580973061120217974905061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50107964081493623966540081 37580973061120217974905061)
  ·
    refine ⟨7046432448960040870294699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37580973061120217974905061 7046432448960040870294699)
    ·
      refine ⟨10569648673440061305442049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7046432448960040870294699 10569648673440061305442049)
      ·
        refine ⟨7927236505080045979081537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10569648673440061305442049 7927236505080045979081537)
        ·
          refine ⟨5945427378810034484311153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7927236505080045979081537 5945427378810034484311153)
          ·
            refine ⟨4459070534107525863233365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5945427378810034484311153 4459070534107525863233365)
            ·
              refine ⟨26127366410786284354883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4459070534107525863233365 26127366410786284354883)
              ·
                rfl

theorem cell22_2060756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 9].length) (baseStart_2060756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060756 prefixEnd_2060756 := by exact prefixLift 2060756
  have htrace : WordTrace (prefixWord ++ tailWord_2060756) baseStart_2060756 baseEnd_2060756 := by
    simpa [prefixWord, tailWord_2060756, baseEnd_2060756] using wordTrace_append hprefix tailTrace_2060756
  have hstable : (prefixWord ++ tailWord_2060756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060756).length < 2 ^ (prefixWord ++ tailWord_2060756).sum := by decide
  have hdescent : baseEnd_2060756 < baseStart_2060756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060758 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_2060758 : Nat := 118140960795 + 2060758 * 2 ^ 59
def prefixEnd_2060758 : Nat := 4983230072969 + 3 ^ 40 * 2060758 * 2
def baseEnd_2060758 : Nat := 705439577732102339031835

theorem tailTrace_2060758 : CollatzResearch.WordTrace tailWord_2060758 prefixEnd_2060758 705439577732102339031835 := by
  unfold tailWord_2060758
  simp only [CollatzResearch.WordTrace]
  refine ⟨4697626191764574393211433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50108012712155460194255285 4697626191764574393211433)
  ·
    refine ⟨3523219643823430794908575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4697626191764574393211433 3523219643823430794908575)
    ·
      refine ⟨5284829465735146192362863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3523219643823430794908575 5284829465735146192362863)
      ·
        refine ⟨7927244198602719288544295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5284829465735146192362863 7927244198602719288544295)
        ·
          refine ⟨11890866297904078932816443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7927244198602719288544295 11890866297904078932816443)
          ·
            refine ⟨17836299446856118399224665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11890866297904078932816443 17836299446856118399224665)
            ·
              refine ⟨13377224585142088799418499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17836299446856118399224665 13377224585142088799418499)
              ·
                refine ⟨20065836877713133199127749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13377224585142088799418499 20065836877713133199127749)
                ·
                  refine ⟨3762344414571212474836453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20065836877713133199127749 3762344414571212474836453)
                  ·
                    refine ⟨705439577732102339031835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3762344414571212474836453 705439577732102339031835)
                    ·
                      rfl

theorem cell22_2060758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_2060758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060758 prefixEnd_2060758 := by exact prefixLift 2060758
  have htrace : WordTrace (prefixWord ++ tailWord_2060758) baseStart_2060758 baseEnd_2060758 := by
    simpa [prefixWord, tailWord_2060758, baseEnd_2060758] using wordTrace_append hprefix tailTrace_2060758
  have hstable : (prefixWord ++ tailWord_2060758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060758).length < 2 ^ (prefixWord ++ tailWord_2060758).sum := by decide
  have hdescent : baseEnd_2060758 < baseStart_2060758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060801 : List Nat := [1, 2, 4, 1, 3, 1, 1, 2, 7]
def baseStart_2060801 : Nat := 118140960795 + 2060801 * 2 ^ 59
def prefixEnd_2060801 : Nat := 4983230072969 + 3 ^ 40 * 2060801 * 2
def baseEnd_2060801 : Nat := 235151432503621520068901

theorem tailTrace_2060801 : CollatzResearch.WordTrace tailWord_2060801 prefixEnd_2060801 235151432503621520068901 := by
  unfold tailWord_2060801
  simp only [CollatzResearch.WordTrace]
  refine ⟨75163587407077408635198257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50109058271384939090132171 75163587407077408635198257)
  ·
    refine ⟨56372690555308056476398693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75163587407077408635198257 56372690555308056476398693)
    ·
      refine ⟨10569879479120260589324755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56372690555308056476398693 10569879479120260589324755)
      ·
        refine ⟨15854819218680390883987133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10569879479120260589324755 15854819218680390883987133)
        ·
          refine ⟨5945557207005146581495175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15854819218680390883987133 5945557207005146581495175)
          ·
            refine ⟨8918335810507719872242763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5945557207005146581495175 8918335810507719872242763)
            ·
              refine ⟨13377503715761579808364145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8918335810507719872242763 13377503715761579808364145)
              ·
                refine ⟨10033127786821184856273109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13377503715761579808364145 10033127786821184856273109)
                ·
                  refine ⟨235151432503621520068901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10033127786821184856273109 235151432503621520068901)
                  ·
                    rfl

theorem cell22_2060801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 7].length) (baseStart_2060801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060801 prefixEnd_2060801 := by exact prefixLift 2060801
  have htrace : WordTrace (prefixWord ++ tailWord_2060801) baseStart_2060801 baseEnd_2060801 := by
    simpa [prefixWord, tailWord_2060801, baseEnd_2060801] using wordTrace_append hprefix tailTrace_2060801
  have hstable : (prefixWord ++ tailWord_2060801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060801).length < 2 ^ (prefixWord ++ tailWord_2060801).sum := by decide
  have hdescent : baseEnd_2060801 < baseStart_2060801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060805 : List Nat := [1, 3, 1, 1, 2, 2, 5, 3, 1, 3]
def baseStart_2060805 : Nat := 118140960795 + 2060805 * 2 ^ 59
def prefixEnd_2060805 : Nat := 4983230072969 + 3 ^ 40 * 2060805 * 2
def baseEnd_2060805 : Nat := 705455666792609883106691

theorem tailTrace_2060805 : CollatzResearch.WordTrace tailWord_2060805 prefixEnd_2060805 705455666792609883106691 := by
  unfold tailWord_2060805
  simp only [CollatzResearch.WordTrace]
  refine ⟨75163733299062917318343869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50109155532708611545562579 75163733299062917318343869)
  ·
    refine ⟨28186399987148593994378951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75163733299062917318343869 28186399987148593994378951)
    ·
      refine ⟨42279599980722890991568427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28186399987148593994378951 42279599980722890991568427)
      ·
        refine ⟨63419399971084336487352641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42279599980722890991568427 63419399971084336487352641)
        ·
          refine ⟨47564549978313252365514481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63419399971084336487352641 47564549978313252365514481)
          ·
            refine ⟨35673412483734939274135861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47564549978313252365514481 35673412483734939274135861)
            ·
              refine ⟨3344382420350150556950237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35673412483734939274135861 3344382420350150556950237)
              ·
                refine ⟨1254143407631306458856339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3344382420350150556950237 1254143407631306458856339)
                ·
                  refine ⟨1881215111446959688284509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1254143407631306458856339 1881215111446959688284509)
                  ·
                    refine ⟨705455666792609883106691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1881215111446959688284509 705455666792609883106691)
                    ·
                      rfl

theorem cell22_2060805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3, 1, 3].length) (baseStart_2060805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060805 prefixEnd_2060805 := by exact prefixLift 2060805
  have htrace : WordTrace (prefixWord ++ tailWord_2060805) baseStart_2060805 baseEnd_2060805 := by
    simpa [prefixWord, tailWord_2060805, baseEnd_2060805] using wordTrace_append hprefix tailTrace_2060805
  have hstable : (prefixWord ++ tailWord_2060805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060805).length < 2 ^ (prefixWord ++ tailWord_2060805).sum := by decide
  have hdescent : baseEnd_2060805 < baseStart_2060805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060831 : List Nat := [1, 1, 2, 4, 1, 1, 1, 4, 3, 4]
def baseStart_2060831 : Nat := 118140960795 + 2060831 * 2 ^ 59
def prefixEnd_2060831 : Nat := 4983230072969 + 3 ^ 40 * 2060831 * 2
def baseEnd_2060831 : Nat := 705464567123954481956611

theorem tailTrace_2060831 : CollatzResearch.WordTrace tailWord_2060831 prefixEnd_2060831 705464567123954481956611 := by
  unfold tailWord_2060831
  simp only [CollatzResearch.WordTrace]
  refine ⟨75164681596968723758790347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50109787731312482505860231 75164681596968723758790347)
  ·
    refine ⟨112747022395453085638185521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75164681596968723758790347 112747022395453085638185521)
    ·
      refine ⟨84560266796589814228639141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112747022395453085638185521 84560266796589814228639141)
      ·
        refine ⟨15855050024360590167869839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84560266796589814228639141 15855050024360590167869839)
        ·
          refine ⟨23782575036540885251804759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15855050024360590167869839 23782575036540885251804759)
          ·
            refine ⟨35673862554811327877707139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23782575036540885251804759 35673862554811327877707139)
            ·
              refine ⟨53510793832216991816560709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35673862554811327877707139 53510793832216991816560709)
              ·
                refine ⟨10033273843540685965605133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53510793832216991816560709 10033273843540685965605133)
                ·
                  refine ⟨3762477691327757237101925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10033273843540685965605133 3762477691327757237101925)
                  ·
                    refine ⟨705464567123954481956611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3762477691327757237101925 705464567123954481956611)
                    ·
                      rfl

theorem cell22_2060831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 3, 4].length) (baseStart_2060831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060831 prefixEnd_2060831 := by exact prefixLift 2060831
  have htrace : WordTrace (prefixWord ++ tailWord_2060831) baseStart_2060831 baseEnd_2060831 := by
    simpa [prefixWord, tailWord_2060831, baseEnd_2060831] using wordTrace_append hprefix tailTrace_2060831
  have hstable : (prefixWord ++ tailWord_2060831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060831).length < 2 ^ (prefixWord ++ tailWord_2060831).sum := by decide
  have hdescent : baseEnd_2060831 < baseStart_2060831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060835 : List Nat := [1, 1, 1, 4, 4, 3, 2, 1, 5]
def baseStart_2060835 : Nat := 118140960795 + 2060835 * 2 ^ 59
def prefixEnd_2060835 : Nat := 4983230072969 + 3 ^ 40 * 2060835 * 2
def baseEnd_2060835 : Nat := 235155312135233268285533

theorem tailTrace_2060835 : CollatzResearch.WordTrace tailWord_2060835 prefixEnd_2060835 235155312135233268285533 := by
  unfold tailWord_2060835
  simp only [CollatzResearch.WordTrace]
  refine ⟨75164827488954232441935959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50109884992636154961290639 75164827488954232441935959)
  ·
    refine ⟨112747241233431348662903939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75164827488954232441935959 112747241233431348662903939)
    ·
      refine ⟨169120861850147022994355909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112747241233431348662903939 169120861850147022994355909)
      ·
        refine ⟨31710161596902566811441733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169120861850147022994355909 31710161596902566811441733)
        ·
          refine ⟨5945655299419231277145325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31710161596902566811441733 5945655299419231277145325)
          ·
            refine ⟨2229620737282211728929497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5945655299419231277145325 2229620737282211728929497)
            ·
              refine ⟨1672215552961658796697123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2229620737282211728929497 1672215552961658796697123)
              ·
                refine ⟨2508323329442488195045685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1672215552961658796697123 2508323329442488195045685)
                ·
                  refine ⟨235155312135233268285533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2508323329442488195045685 235155312135233268285533)
                  ·
                    rfl

theorem cell22_2060835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 5].length) (baseStart_2060835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060835 prefixEnd_2060835 := by exact prefixLift 2060835
  have htrace : WordTrace (prefixWord ++ tailWord_2060835) baseStart_2060835 baseEnd_2060835 := by
    simpa [prefixWord, tailWord_2060835, baseEnd_2060835] using wordTrace_append hprefix tailTrace_2060835
  have hstable : (prefixWord ++ tailWord_2060835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060835).length < 2 ^ (prefixWord ++ tailWord_2060835).sum := by decide
  have hdescent : baseEnd_2060835 < baseStart_2060835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060848 : List Nat := [2, 1, 1, 1, 2, 3, 5, 2, 1, 4]
def baseStart_2060848 : Nat := 118140960795 + 2060848 * 2 ^ 59
def prefixEnd_2060848 : Nat := 4983230072969 + 3 ^ 40 * 2060848 * 2
def baseEnd_2060848 : Nat := 705470386571372104281559

theorem tailTrace_2060848 : CollatzResearch.WordTrace tailWord_2060848 prefixEnd_2060848 705470386571372104281559 := by
  unfold tailWord_2060848
  simp only [CollatzResearch.WordTrace]
  refine ⟨37582650818953567831079599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50110201091938090441439465 37582650818953567831079599)
  ·
    refine ⟨56373976228430351746619399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37582650818953567831079599 56373976228430351746619399)
    ·
      refine ⟨84560964342645527619929099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56373976228430351746619399 84560964342645527619929099)
      ·
        refine ⟨126841446513968291429893649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84560964342645527619929099 126841446513968291429893649)
        ·
          refine ⟨95131084885476218572420237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126841446513968291429893649 95131084885476218572420237)
          ·
            refine ⟨35674156832053581964657589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95131084885476218572420237 35674156832053581964657589)
            ·
              refine ⟨3344452203005023309186649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35674156832053581964657589 3344452203005023309186649)
              ·
                refine ⟨2508339152253767481889987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3344452203005023309186649 2508339152253767481889987)
                ·
                  refine ⟨3762508728380651222834981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2508339152253767481889987 3762508728380651222834981)
                  ·
                    refine ⟨705470386571372104281559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3762508728380651222834981 705470386571372104281559)
                    ·
                      rfl

theorem cell22_2060848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 1, 4].length) (baseStart_2060848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060848 prefixEnd_2060848 := by exact prefixLift 2060848
  have htrace : WordTrace (prefixWord ++ tailWord_2060848) baseStart_2060848 baseEnd_2060848 := by
    simpa [prefixWord, tailWord_2060848, baseEnd_2060848] using wordTrace_append hprefix tailTrace_2060848
  have hstable : (prefixWord ++ tailWord_2060848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060848).length < 2 ^ (prefixWord ++ tailWord_2060848).sum := by decide
  have hdescent : baseEnd_2060848 < baseStart_2060848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060863 : List Nat := [1, 1, 2, 2, 3, 2, 2, 5, 4]
def baseStart_2060863 : Nat := 118140960795 + 2060863 * 2 ^ 59
def prefixEnd_2060863 : Nat := 4983230072969 + 3 ^ 40 * 2060863 * 2
def baseEnd_2060863 : Nat := 235158507125972355052171

theorem tailTrace_2060863 : CollatzResearch.WordTrace tailWord_2060863 prefixEnd_2060863 235158507125972355052171 := by
  unfold tailWord_2060863
  simp only [CollatzResearch.WordTrace]
  refine ⟨75165848732852793223955243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50110565821901862149303495 75165848732852793223955243)
  ·
    refine ⟨112748773099279189835932865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75165848732852793223955243 112748773099279189835932865)
    ·
      refine ⟨84561579824459392376949649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112748773099279189835932865 84561579824459392376949649)
      ·
        refine ⟨63421184868344544282712237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84561579824459392376949649 63421184868344544282712237)
        ·
          refine ⟨23782944325629204106017089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63421184868344544282712237 23782944325629204106017089)
          ·
            refine ⟨17837208244221903079512817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23782944325629204106017089 17837208244221903079512817)
            ·
              refine ⟨13377906183166427309634613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17837208244221903079512817 13377906183166427309634613)
              ·
                refine ⟨1254178704671852560278245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13377906183166427309634613 1254178704671852560278245)
                ·
                  refine ⟨235158507125972355052171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1254178704671852560278245 235158507125972355052171)
                  ·
                    rfl

theorem cell22_2060863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 5, 4].length) (baseStart_2060863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060863 prefixEnd_2060863 := by exact prefixLift 2060863
  have htrace : WordTrace (prefixWord ++ tailWord_2060863) baseStart_2060863 baseEnd_2060863 := by
    simpa [prefixWord, tailWord_2060863, baseEnd_2060863] using wordTrace_append hprefix tailTrace_2060863
  have hstable : (prefixWord ++ tailWord_2060863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060863).length < 2 ^ (prefixWord ++ tailWord_2060863).sum := by decide
  have hdescent : baseEnd_2060863 < baseStart_2060863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060878 : List Nat := [4, 1, 1, 1, 1, 2, 2, 3, 4, 3]
def baseStart_2060878 : Nat := 118140960795 + 2060878 * 2 ^ 59
def prefixEnd_2060878 : Nat := 4983230072969 + 3 ^ 40 * 2060878 * 2
def baseEnd_2060878 : Nat := 705480656184462026031467

theorem tailTrace_2060878 : CollatzResearch.WordTrace tailWord_2060878 prefixEnd_2060878 705480656184462026031467 := by
  unfold tailWord_2060878
  simp only [CollatzResearch.WordTrace]
  refine ⟨9395799478474806348218911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50110930551865633857167525 9395799478474806348218911)
  ·
    refine ⟨14093699217712209522328367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9395799478474806348218911 14093699217712209522328367)
    ·
      refine ⟨21140548826568314283492551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14093699217712209522328367 21140548826568314283492551)
      ·
        refine ⟨31710823239852471425238827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21140548826568314283492551 31710823239852471425238827)
        ·
          refine ⟨47566234859778707137858241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31710823239852471425238827 47566234859778707137858241)
          ·
            refine ⟨35674676144834030353393681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47566234859778707137858241 35674676144834030353393681)
            ·
              refine ⟨26756007108625522765045261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35674676144834030353393681 26756007108625522765045261)
              ·
                refine ⟨10033502665734571036891973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26756007108625522765045261 10033502665734571036891973)
                ·
                  refine ⟨1881281749825232069417245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10033502665734571036891973 1881281749825232069417245)
                  ·
                    refine ⟨705480656184462026031467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1881281749825232069417245 705480656184462026031467)
                    ·
                      rfl

theorem cell22_2060878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_2060878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060878 prefixEnd_2060878 := by exact prefixLift 2060878
  have htrace : WordTrace (prefixWord ++ tailWord_2060878) baseStart_2060878 baseEnd_2060878 := by
    simpa [prefixWord, tailWord_2060878, baseEnd_2060878] using wordTrace_append hprefix tailTrace_2060878
  have hstable : (prefixWord ++ tailWord_2060878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060878).length < 2 ^ (prefixWord ++ tailWord_2060878).sum := by decide
  have hdescent : baseEnd_2060878 < baseStart_2060878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060910 : List Nat := [4, 1, 2, 2, 2, 1, 3, 1, 2, 4]
def baseStart_2060910 : Nat := 118140960795 + 2060910 * 2 ^ 59
def prefixEnd_2060910 : Nat := 4983230072969 + 3 ^ 40 * 2060910 * 2
def baseEnd_2060910 : Nat := 705491610438424609231369

theorem tailTrace_2060910 : CollatzResearch.WordTrace tailWord_2060910 prefixEnd_2060910 705491610438424609231369 := by
  unfold tailWord_2060910
  simp only [CollatzResearch.WordTrace]
  refine ⟨9395945370460315031364523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50111708642455013500610789 9395945370460315031364523)
  ·
    refine ⟨14093918055690472547046785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9395945370460315031364523 14093918055690472547046785)
    ·
      refine ⟨10570438541767854410285089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14093918055690472547046785 10570438541767854410285089)
      ·
        refine ⟨7927828906325890807713817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10570438541767854410285089 7927828906325890807713817)
        ·
          refine ⟨5945871679744418105785363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7927828906325890807713817 5945871679744418105785363)
          ·
            refine ⟨8918807519616627158678045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5945871679744418105785363 8918807519616627158678045)
            ·
              refine ⟨3344552819856235184504267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8918807519616627158678045 3344552819856235184504267)
              ·
                refine ⟨5016829229784352776756401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3344552819856235184504267 5016829229784352776756401)
                ·
                  refine ⟨3762621922338264582567301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5016829229784352776756401 3762621922338264582567301)
                  ·
                    refine ⟨705491610438424609231369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3762621922338264582567301 705491610438424609231369)
                    ·
                      rfl

theorem cell22_2060910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_2060910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2060910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2060910 prefixEnd_2060910 := by exact prefixLift 2060910
  have htrace : WordTrace (prefixWord ++ tailWord_2060910) baseStart_2060910 baseEnd_2060910 := by
    simpa [prefixWord, tailWord_2060910, baseEnd_2060910] using wordTrace_append hprefix tailTrace_2060910
  have hstable : (prefixWord ++ tailWord_2060910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060910).length < 2 ^ (prefixWord ++ tailWord_2060910).sum := by decide
  have hdescent : baseEnd_2060910 < baseStart_2060910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061075 : List Nat := [1, 1, 1, 2, 1, 3, 5, 2, 3, 3]
def baseStart_2061075 : Nat := 118140960795 + 2061075 * 2 ^ 59
def prefixEnd_2061075 : Nat := 4983230072969 + 3 ^ 40 * 2061075 * 2
def baseEnd_2061075 : Nat := 705548093310419178855863

theorem tailTrace_2061075 : CollatzResearch.WordTrace tailWord_2061075 prefixEnd_2061075 705548093310419178855863 := by
  unfold tailWord_2061075
  simp only [CollatzResearch.WordTrace]
  refine ⟨75173581008084753430672679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50115720672056502287115119 75173581008084753430672679)
  ·
    refine ⟨112760371512127130146009019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75173581008084753430672679 112760371512127130146009019)
    ·
      refine ⟨169140557268190695219013529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112760371512127130146009019 169140557268190695219013529)
      ·
        refine ⟨126855417951143021414260147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169140557268190695219013529 126855417951143021414260147)
        ·
          refine ⟨190283126926714532121390221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126855417951143021414260147 190283126926714532121390221)
          ·
            refine ⟨71356172597517949545521333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190283126926714532121390221 71356172597517949545521333)
            ·
              refine ⟨6689641181017307769892625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71356172597517949545521333 6689641181017307769892625)
              ·
                refine ⟨5017230885762980827419469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6689641181017307769892625 5017230885762980827419469)
                ·
                  refine ⟨1881461582161117810282301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5017230885762980827419469 1881461582161117810282301)
                  ·
                    refine ⟨705548093310419178855863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1881461582161117810282301 705548093310419178855863)
                    ·
                      rfl

theorem cell22_2061075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 3, 3].length) (baseStart_2061075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061075 prefixEnd_2061075 := by exact prefixLift 2061075
  have htrace : WordTrace (prefixWord ++ tailWord_2061075) baseStart_2061075 baseEnd_2061075 := by
    simpa [prefixWord, tailWord_2061075, baseEnd_2061075] using wordTrace_append hprefix tailTrace_2061075
  have hstable : (prefixWord ++ tailWord_2061075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061075).length < 2 ^ (prefixWord ++ tailWord_2061075).sum := by decide
  have hdescent : baseEnd_2061075 < baseStart_2061075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061079 : List Nat := [1, 1, 3, 4, 4, 1, 1, 1, 2, 4]
def baseStart_2061079 : Nat := 118140960795 + 2061079 * 2 ^ 59
def prefixEnd_2061079 : Nat := 4983230072969 + 3 ^ 40 * 2061079 * 2
def baseEnd_2061079 : Nat := 705549462592164501755851

theorem tailTrace_2061079 : CollatzResearch.WordTrace tailWord_2061079 prefixEnd_2061079 705549462592164501755851 := by
  unfold tailWord_2061079
  simp only [CollatzResearch.WordTrace]
  refine ⟨75173726900070262113818291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50115817933380174742545527 75173726900070262113818291)
  ·
    refine ⟨112760590350105393170727437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75173726900070262113818291 112760590350105393170727437)
    ·
      refine ⟨42285221381289522439022789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112760590350105393170727437 42285221381289522439022789)
      ·
        refine ⟨7928479008991785457316773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42285221381289522439022789 7928479008991785457316773)
        ·
          refine ⟨1486589814185959773246895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7928479008991785457316773 1486589814185959773246895)
          ·
            refine ⟨2229884721278939659870343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1486589814185959773246895 2229884721278939659870343)
            ·
              refine ⟨3344827081918409489805515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2229884721278939659870343 3344827081918409489805515)
              ·
                refine ⟨5017240622877614234708273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3344827081918409489805515 5017240622877614234708273)
                ·
                  refine ⟨3762930467158210676031205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5017240622877614234708273 3762930467158210676031205)
                  ·
                    refine ⟨705549462592164501755851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3762930467158210676031205 705549462592164501755851)
                    ·
                      rfl

theorem cell22_2061079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 2, 4].length) (baseStart_2061079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061079 prefixEnd_2061079 := by exact prefixLift 2061079
  have htrace : WordTrace (prefixWord ++ tailWord_2061079) baseStart_2061079 baseEnd_2061079 := by
    simpa [prefixWord, tailWord_2061079, baseEnd_2061079] using wordTrace_append hprefix tailTrace_2061079
  have hstable : (prefixWord ++ tailWord_2061079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061079).length < 2 ^ (prefixWord ++ tailWord_2061079).sum := by decide
  have hdescent : baseEnd_2061079 < baseStart_2061079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061098 : List Nat := [3, 1, 4, 3, 2, 1, 1, 2, 2, 3]
def baseStart_2061098 : Nat := 118140960795 + 2061098 * 2 ^ 59
def prefixEnd_2061098 : Nat := 4983230072969 + 3 ^ 40 * 2061098 * 2
def baseEnd_2061098 : Nat := 705555966680454785530793

theorem tailTrace_2061098 : CollatzResearch.WordTrace tailWord_2061098 prefixEnd_2061098 705555966680454785530793 := by
  unfold tailWord_2061098
  simp only [CollatzResearch.WordTrace]
  refine ⟨18793604971750357089689987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50116279924667618905839965 18793604971750357089689987)
  ·
    refine ⟨28190407457625535634534981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18793604971750357089689987 28190407457625535634534981)
    ·
      refine ⟨5285701398304787931475309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28190407457625535634534981 5285701398304787931475309)
      ·
        refine ⟨1982138024364295474303241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5285701398304787931475309 1982138024364295474303241)
        ·
          refine ⟨1486603518273221605727431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1982138024364295474303241 1486603518273221605727431)
          ·
            refine ⟨2229905277409832408591147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1486603518273221605727431 2229905277409832408591147)
            ·
              refine ⟨3344857916114748612886721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2229905277409832408591147 3344857916114748612886721)
              ·
                refine ⟨2508643437086061459665041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3344857916114748612886721 2508643437086061459665041)
                ·
                  refine ⟨1881482577814546094748781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2508643437086061459665041 1881482577814546094748781)
                  ·
                    refine ⟨705555966680454785530793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1881482577814546094748781 705555966680454785530793)
                    ·
                      rfl

theorem cell22_2061098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_2061098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061098 prefixEnd_2061098 := by exact prefixLift 2061098
  have htrace : WordTrace (prefixWord ++ tailWord_2061098) baseStart_2061098 baseEnd_2061098 := by
    simpa [prefixWord, tailWord_2061098, baseEnd_2061098] using wordTrace_append hprefix tailTrace_2061098
  have hstable : (prefixWord ++ tailWord_2061098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061098).length < 2 ^ (prefixWord ++ tailWord_2061098).sum := by decide
  have hdescent : baseEnd_2061098 < baseStart_2061098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061109 : List Nat := [1, 3, 3, 1, 3, 1, 2, 4, 1, 3]
def baseStart_2061109 : Nat := 118140960795 + 2061109 * 2 ^ 59
def prefixEnd_2061109 : Nat := 4983230072969 + 3 ^ 40 * 2061109 * 2
def baseEnd_2061109 : Nat := 705559732205254423505759

theorem tailTrace_2061109 : CollatzResearch.WordTrace tailWord_2061109 prefixEnd_2061109 705559732205254423505759 := by
  unfold tailWord_2061109
  simp only [CollatzResearch.WordTrace]
  refine ⟨75174821089961577237410381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50116547393307718158273587 75174821089961577237410381)
  ·
    refine ⟨28190557908735591464028893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75174821089961577237410381 28190557908735591464028893)
    ·
      refine ⟨10571459215775846799010835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28190557908735591464028893 10571459215775846799010835)
      ·
        refine ⟨15857188823663770198516253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10571459215775846799010835 15857188823663770198516253)
        ·
          refine ⟨5946445808873913824443595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15857188823663770198516253 5946445808873913824443595)
          ·
            refine ⟨8919668713310870736665393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5946445808873913824443595 8919668713310870736665393)
            ·
              refine ⟨6689751534983153052499045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8919668713310870736665393 6689751534983153052499045)
              ·
                refine ⟨1254328412809341197343571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6689751534983153052499045 1254328412809341197343571)
                ·
                  refine ⟨1881492619214011796015357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1254328412809341197343571 1881492619214011796015357)
                  ·
                    refine ⟨705559732205254423505759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1881492619214011796015357 705559732205254423505759)
                    ·
                      rfl

theorem cell22_2061109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_2061109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061109 prefixEnd_2061109 := by exact prefixLift 2061109
  have htrace : WordTrace (prefixWord ++ tailWord_2061109) baseStart_2061109 baseEnd_2061109 := by
    simpa [prefixWord, tailWord_2061109, baseEnd_2061109] using wordTrace_append hprefix tailTrace_2061109
  have hstable : (prefixWord ++ tailWord_2061109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061109).length < 2 ^ (prefixWord ++ tailWord_2061109).sum := by decide
  have hdescent : baseEnd_2061109 < baseStart_2061109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061186 : List Nat := [3, 4, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_2061186 : Nat := 118140960795 + 2061186 * 2 ^ 59
def prefixEnd_2061186 : Nat := 4983230072969 + 3 ^ 40 * 2061186 * 2
def baseEnd_2061186 : Nat := 705586090878851889330523

theorem tailTrace_2061186 : CollatzResearch.WordTrace tailWord_2061186 prefixEnd_2061186 705586090878851889330523 := by
  unfold tailWord_2061186
  simp only [CollatzResearch.WordTrace]
  refine ⟨18794407377670654846990853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50118419673788412925308941 18794407377670654846990853)
  ·
    refine ⟨3523951383313247783810785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18794407377670654846990853 3523951383313247783810785)
    ·
      refine ⟨2642963537484935837858089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3523951383313247783810785 2642963537484935837858089)
      ·
        refine ⟨1982222653113701878393567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2642963537484935837858089 1982222653113701878393567)
        ·
          refine ⟨2973333979670552817590351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1982222653113701878393567 2973333979670552817590351)
          ·
            refine ⟨4460000969505829226385527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2973333979670552817590351 4460000969505829226385527)
            ·
              refine ⟨6690001454258743839578291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4460000969505829226385527 6690001454258743839578291)
              ·
                refine ⟨10035002181388115759367437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6690001454258743839578291 10035002181388115759367437)
                ·
                  refine ⟨3763125818020543409762789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10035002181388115759367437 3763125818020543409762789)
                  ·
                    refine ⟨705586090878851889330523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3763125818020543409762789 705586090878851889330523)
                    ·
                      rfl

theorem cell22_2061186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_2061186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061186 prefixEnd_2061186 := by exact prefixLift 2061186
  have htrace : WordTrace (prefixWord ++ tailWord_2061186) baseStart_2061186 baseEnd_2061186 := by
    simpa [prefixWord, tailWord_2061186, baseEnd_2061186] using wordTrace_append hprefix tailTrace_2061186
  have hstable : (prefixWord ++ tailWord_2061186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061186).length < 2 ^ (prefixWord ++ tailWord_2061186).sum := by decide
  have hdescent : baseEnd_2061186 < baseStart_2061186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061212 : List Nat := [2, 2, 3, 3, 3, 9]
def baseStart_2061212 : Nat := 118140960795 + 2061212 * 2 ^ 59
def prefixEnd_2061212 : Nat := 4983230072969 + 3 ^ 40 * 2061212 * 2
def baseEnd_2061212 : Nat := 8711049274199956644203

theorem tailTrace_2061212 : CollatzResearch.WordTrace tailWord_2061212 prefixEnd_2061212 8711049274199956644203 := by
  unfold tailWord_2061212
  simp only [CollatzResearch.WordTrace]
  refine ⟨37589288904294212914204945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50119051872392283885606593 37589288904294212914204945)
  ·
    refine ⟨28191966678220659685653709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37589288904294212914204945 28191966678220659685653709)
    ·
      refine ⟨10571987504332747382120141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28191966678220659685653709 10571987504332747382120141)
      ·
        refine ⟨3964495314124780268295053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10571987504332747382120141 3964495314124780268295053)
        ·
          refine ⟨1486685742796792600610645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3964495314124780268295053 1486685742796792600610645)
          ·
            refine ⟨8711049274199956644203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1486685742796792600610645 8711049274199956644203)
            ·
              rfl

theorem cell22_2061212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 9].length) (baseStart_2061212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061212 prefixEnd_2061212 := by exact prefixLift 2061212
  have htrace : WordTrace (prefixWord ++ tailWord_2061212) baseStart_2061212 baseEnd_2061212 := by
    simpa [prefixWord, tailWord_2061212, baseEnd_2061212] using wordTrace_append hprefix tailTrace_2061212
  have hstable : (prefixWord ++ tailWord_2061212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061212).length < 2 ^ (prefixWord ++ tailWord_2061212).sum := by decide
  have hdescent : baseEnd_2061212 < baseStart_2061212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061254 : List Nat := [6, 1, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_2061254 : Nat := 118140960795 + 2061254 * 2 ^ 59
def prefixEnd_2061254 : Nat := 4983230072969 + 3 ^ 40 * 2061254 * 2
def baseEnd_2061254 : Nat := 705609368668522378630315

theorem tailTrace_2061254 : CollatzResearch.WordTrace tailWord_2061254 prefixEnd_2061254 705609368668522378630315 := by
  unfold tailWord_2061254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2349378427326133343794963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50120073116290844667625877 2349378427326133343794963)
  ·
    refine ⟨3524067640989200015692445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2349378427326133343794963 3524067640989200015692445)
    ·
      refine ⟨1321525365370950005884667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3524067640989200015692445 1321525365370950005884667)
      ·
        refine ⟨1982288048056425008827001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1321525365370950005884667 1982288048056425008827001)
        ·
          refine ⟨1486716036042318756620251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1982288048056425008827001 1486716036042318756620251)
          ·
            refine ⟨2230074054063478134930377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1486716036042318756620251 2230074054063478134930377)
            ·
              refine ⟨1672555540547608601197783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2230074054063478134930377 1672555540547608601197783)
              ·
                refine ⟨2508833310821412901796675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1672555540547608601197783 2508833310821412901796675)
                ·
                  refine ⟨3763249966232119352695013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2508833310821412901796675 3763249966232119352695013)
                  ·
                    refine ⟨705609368668522378630315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3763249966232119352695013 705609368668522378630315)
                    ·
                      rfl

theorem cell22_2061254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_2061254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061254 prefixEnd_2061254 := by exact prefixLift 2061254
  have htrace : WordTrace (prefixWord ++ tailWord_2061254) baseStart_2061254 baseEnd_2061254 := by
    simpa [prefixWord, tailWord_2061254, baseEnd_2061254] using wordTrace_append hprefix tailTrace_2061254
  have hstable : (prefixWord ++ tailWord_2061254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061254).length < 2 ^ (prefixWord ++ tailWord_2061254).sum := by decide
  have hdescent : baseEnd_2061254 < baseStart_2061254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061274 : List Nat := [3, 1, 1, 2, 4, 3, 1, 2, 5]
def baseStart_2061274 : Nat := 118140960795 + 2061274 * 2 ^ 59
def prefixEnd_2061274 : Nat := 4983230072969 + 3 ^ 40 * 2061274 * 2
def baseEnd_2061274 : Nat := 235205405025749664376751

theorem tailTrace_2061274 : CollatzResearch.WordTrace tailWord_2061274 prefixEnd_2061274 235205405025749664376751 := by
  unfold tailWord_2061274
  simp only [CollatzResearch.WordTrace]
  refine ⟨18795209783590952604291719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50120559422909206944777917 18795209783590952604291719)
  ·
    refine ⟨28192814675386428906437579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18795209783590952604291719 28192814675386428906437579)
    ·
      refine ⟨42289222013079643359656369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28192814675386428906437579 42289222013079643359656369)
      ·
        refine ⟨31716916509809732519742277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42289222013079643359656369 31716916509809732519742277)
        ·
          refine ⟨5946921845589324847451677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31716916509809732519742277 5946921845589324847451677)
          ·
            refine ⟨2230095692095996817794379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5946921845589324847451677 2230095692095996817794379)
            ·
              refine ⟨3345143538143995226691569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2230095692095996817794379 3345143538143995226691569)
              ·
                refine ⟨2508857653607996420018677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3345143538143995226691569 2508857653607996420018677)
                ·
                  refine ⟨235205405025749664376751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2508857653607996420018677 235205405025749664376751)
                  ·
                    rfl

theorem cell22_2061274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 2, 5].length) (baseStart_2061274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061274 prefixEnd_2061274 := by exact prefixLift 2061274
  have htrace : WordTrace (prefixWord ++ tailWord_2061274) baseStart_2061274 baseEnd_2061274 := by
    simpa [prefixWord, tailWord_2061274, baseEnd_2061274] using wordTrace_append hprefix tailTrace_2061274
  have hstable : (prefixWord ++ tailWord_2061274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061274).length < 2 ^ (prefixWord ++ tailWord_2061274).sum := by decide
  have hdescent : baseEnd_2061274 < baseStart_2061274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061317 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 6, 3]
def baseStart_2061317 : Nat := 118140960795 + 2061317 * 2 ^ 59
def prefixEnd_2061317 : Nat := 4983230072969 + 3 ^ 40 * 2061317 * 2
def baseEnd_2061317 : Nat := 705630934856011214305121

theorem tailTrace_2061317 : CollatzResearch.WordTrace tailWord_2061317 prefixEnd_2061317 705630934856011214305121 := by
  unfold tailWord_2061317
  simp only [CollatzResearch.WordTrace]
  refine ⟨75182407473208028760982205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50121604982138685840654803 75182407473208028760982205)
  ·
    refine ⟨28193402802453010785368327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75182407473208028760982205 28193402802453010785368327)
    ·
      refine ⟨42290104203679516178052491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28193402802453010785368327 42290104203679516178052491)
      ·
        refine ⟨63435156305519274267078737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42290104203679516178052491 63435156305519274267078737)
        ·
          refine ⟨47576367229139455700309053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63435156305519274267078737 47576367229139455700309053)
          ·
            refine ⟨17841137710927295887615895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47576367229139455700309053 17841137710927295887615895)
            ·
              refine ⟨26761706566390943831423843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17841137710927295887615895 26761706566390943831423843)
              ·
                refine ⟨40142559849586415747135765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26761706566390943831423843 40142559849586415747135765)
                ·
                  refine ⟨1881682492949363238146989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40142559849586415747135765 1881682492949363238146989)
                  ·
                    refine ⟨705630934856011214305121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1881682492949363238146989 705630934856011214305121)
                    ·
                      rfl

theorem cell22_2061317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 6, 3].length) (baseStart_2061317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061317 prefixEnd_2061317 := by exact prefixLift 2061317
  have htrace : WordTrace (prefixWord ++ tailWord_2061317) baseStart_2061317 baseEnd_2061317 := by
    simpa [prefixWord, tailWord_2061317, baseEnd_2061317] using wordTrace_append hprefix tailTrace_2061317
  have hstable : (prefixWord ++ tailWord_2061317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061317).length < 2 ^ (prefixWord ++ tailWord_2061317).sum := by decide
  have hdescent : baseEnd_2061317 < baseStart_2061317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061336 : List Nat := [2, 1, 2, 3, 2, 3, 3, 2, 4]
def baseStart_2061336 : Nat := 118140960795 + 2061336 * 2 ^ 59
def prefixEnd_2061336 : Nat := 4983230072969 + 3 ^ 40 * 2061336 * 2
def baseEnd_2061336 : Nat := 235212479648100499360021

theorem tailTrace_2061336 : CollatzResearch.WordTrace tailWord_2061336 prefixEnd_2061336 235212479648100499360021 := by
  unfold tailWord_2061336
  simp only [CollatzResearch.WordTrace]
  refine ⟨37591550230069597502961931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50122066973426130003949241 37591550230069597502961931)
  ·
    refine ⟨56387325345104396254442897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37591550230069597502961931 56387325345104396254442897)
    ·
      refine ⟨42290494008828297190832173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56387325345104396254442897 42290494008828297190832173)
      ·
        refine ⟨15858935253310611446562065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42290494008828297190832173 15858935253310611446562065)
        ·
          refine ⟨11894201439982958584921549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15858935253310611446562065 11894201439982958584921549)
          ·
            refine ⟨4460325539993609469345581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11894201439982958584921549 4460325539993609469345581)
            ·
              refine ⟨1672622077497603551004593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4460325539993609469345581 1672622077497603551004593)
              ·
                refine ⟨1254466558123202663253445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1672622077497603551004593 1254466558123202663253445)
                ·
                  refine ⟨235212479648100499360021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1254466558123202663253445 235212479648100499360021)
                  ·
                    rfl

theorem cell22_2061336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 2, 4].length) (baseStart_2061336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061336 prefixEnd_2061336 := by exact prefixLift 2061336
  have htrace : WordTrace (prefixWord ++ tailWord_2061336) baseStart_2061336 baseEnd_2061336 := by
    simpa [prefixWord, tailWord_2061336, baseEnd_2061336] using wordTrace_append hprefix tailTrace_2061336
  have hstable : (prefixWord ++ tailWord_2061336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061336).length < 2 ^ (prefixWord ++ tailWord_2061336).sum := by decide
  have hdescent : baseEnd_2061336 < baseStart_2061336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061347 : List Nat := [1, 1, 1, 4, 3, 3, 2, 7]
def baseStart_2061347 : Nat := 118140960795 + 2061347 * 2 ^ 59
def prefixEnd_2061347 : Nat := 4983230072969 + 3 ^ 40 * 2061347 * 2
def baseEnd_2061347 : Nat := 78404578274344570672781

theorem tailTrace_2061347 : CollatzResearch.WordTrace tailWord_2061347 prefixEnd_2061347 78404578274344570672781 := by
  unfold tailWord_2061347
  simp only [CollatzResearch.WordTrace]
  refine ⟨75183501663099343884574295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50122334442066229256382863 75183501663099343884574295)
  ·
    refine ⟨112775252494649015826861443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75183501663099343884574295 112775252494649015826861443)
    ·
      refine ⟨169162878741973523740292165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112775252494649015826861443 169162878741973523740292165)
      ·
        refine ⟨31718039764120035701304781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169162878741973523740292165 31718039764120035701304781)
        ·
          refine ⟨11894264911545013387989293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31718039764120035701304781 11894264911545013387989293)
          ·
            refine ⟨4460349341829380020495985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11894264911545013387989293 4460349341829380020495985)
            ·
              refine ⟨3345262006372035015371989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4460349341829380020495985 3345262006372035015371989)
              ·
                refine ⟨78404578274344570672781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3345262006372035015371989 78404578274344570672781)
                ·
                  rfl

theorem cell22_2061347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 7].length) (baseStart_2061347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061347 prefixEnd_2061347 := by exact prefixLift 2061347
  have htrace : WordTrace (prefixWord ++ tailWord_2061347) baseStart_2061347 baseEnd_2061347 := by
    simpa [prefixWord, tailWord_2061347, baseEnd_2061347] using wordTrace_append hprefix tailTrace_2061347
  have hstable : (prefixWord ++ tailWord_2061347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061347).length < 2 ^ (prefixWord ++ tailWord_2061347).sum := by decide
  have hdescent : baseEnd_2061347 < baseStart_2061347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061364 : List Nat := [2, 5, 1, 2, 1, 1, 2, 8]
def baseStart_2061364 : Nat := 118140960795 + 2061364 * 2 ^ 59
def prefixEnd_2061364 : Nat := 4983230072969 + 3 ^ 40 * 2061364 * 2
def baseEnd_2061364 : Nat := 78405224879613195375553

theorem tailTrace_2061364 : CollatzResearch.WordTrace tailWord_2061364 prefixEnd_2061364 78405224879613195375553 := by
  unfold tailWord_2061364
  simp only [CollatzResearch.WordTrace]
  refine ⟨37592060852018877893971573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50122747802691837191962097 37592060852018877893971573)
  ·
    refine ⟨3524255704876769802559835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37592060852018877893971573 3524255704876769802559835)
    ·
      refine ⟨5286383557315154703839753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3524255704876769802559835 5286383557315154703839753)
      ·
        refine ⟨3964787667986366027879815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5286383557315154703839753 3964787667986366027879815)
        ·
          refine ⟨5947181501979549041819723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3964787667986366027879815 5947181501979549041819723)
          ·
            refine ⟨8920772252969323562729585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5947181501979549041819723 8920772252969323562729585)
            ·
              refine ⟨6690579189726992672047189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8920772252969323562729585 6690579189726992672047189)
              ·
                refine ⟨78405224879613195375553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6690579189726992672047189 78405224879613195375553)
                ·
                  rfl

theorem cell22_2061364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 8].length) (baseStart_2061364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061364 prefixEnd_2061364 := by exact prefixLift 2061364
  have htrace : WordTrace (prefixWord ++ tailWord_2061364) baseStart_2061364 baseEnd_2061364 := by
    simpa [prefixWord, tailWord_2061364, baseEnd_2061364] using wordTrace_append hprefix tailTrace_2061364
  have hstable : (prefixWord ++ tailWord_2061364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061364).length < 2 ^ (prefixWord ++ tailWord_2061364).sum := by decide
  have hdescent : baseEnd_2061364 < baseStart_2061364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061366 : List Nat := [5, 1, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_2061366 : Nat := 118140960795 + 2061366 * 2 ^ 59
def prefixEnd_2061366 : Nat := 4983230072969 + 3 ^ 40 * 2061366 * 2
def baseEnd_2061366 : Nat := 705647708557391419829971

theorem tailTrace_2061366 : CollatzResearch.WordTrace tailWord_2061366 prefixEnd_2061366 705647708557391419829971 := by
  unfold tailWord_2061366
  simp only [CollatzResearch.WordTrace]
  refine ⟨4699012165626906883094747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50122796433353673419677301 4699012165626906883094747)
  ·
    refine ⟨7048518248440360324642121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4699012165626906883094747 7048518248440360324642121)
    ·
      refine ⟨5286388686330270243481591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7048518248440360324642121 5286388686330270243481591)
      ·
        refine ⟨7929583029495405365222387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5286388686330270243481591 7929583029495405365222387)
        ·
          refine ⟨11894374544243108047833581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7929583029495405365222387 11894374544243108047833581)
          ·
            refine ⟨4460390454091165517937593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11894374544243108047833581 4460390454091165517937593)
            ·
              refine ⟨3345292840568374138453195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4460390454091165517937593 3345292840568374138453195)
              ·
                refine ⟨5017939260852561207679793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3345292840568374138453195 5017939260852561207679793)
                ·
                  refine ⟨3763454445639420905759845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5017939260852561207679793 3763454445639420905759845)
                  ·
                    refine ⟨705647708557391419829971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3763454445639420905759845 705647708557391419829971)
                    ·
                      rfl

theorem cell22_2061366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_2061366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061366 prefixEnd_2061366 := by exact prefixLift 2061366
  have htrace : WordTrace (prefixWord ++ tailWord_2061366) baseStart_2061366 baseEnd_2061366 := by
    simpa [prefixWord, tailWord_2061366, baseEnd_2061366] using wordTrace_append hprefix tailTrace_2061366
  have hstable : (prefixWord ++ tailWord_2061366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061366).length < 2 ^ (prefixWord ++ tailWord_2061366).sum := by decide
  have hdescent : baseEnd_2061366 < baseStart_2061366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061398 : List Nat := [5, 2, 2, 1, 2, 2, 1, 7]
def baseStart_2061398 : Nat := 118140960795 + 2061398 * 2 ^ 59
def prefixEnd_2061398 : Nat := 4983230072969 + 3 ^ 40 * 2061398 * 2
def baseEnd_2061398 : Nat := 78406518090150444781097

theorem tailTrace_2061398 : CollatzResearch.WordTrace tailWord_2061398 prefixEnd_2061398 78406518090150444781097 := by
  unfold tailWord_2061398
  simp only [CollatzResearch.WordTrace]
  refine ⟨4699085111619661224667553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50123574523943053063120565 4699085111619661224667553)
  ·
    refine ⟨3524313833714745918500665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4699085111619661224667553 3524313833714745918500665)
    ·
      refine ⟨2643235375286059438875499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3524313833714745918500665 2643235375286059438875499)
      ·
        refine ⟨3964853062929089158313249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2643235375286059438875499 3964853062929089158313249)
        ·
          refine ⟨2973639797196816868734937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3964853062929089158313249 2973639797196816868734937)
          ·
            refine ⟨2230229847897612651551203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2973639797196816868734937 2230229847897612651551203)
            ·
              refine ⟨3345344771846418977326805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2230229847897612651551203 3345344771846418977326805)
              ·
                refine ⟨78406518090150444781097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3345344771846418977326805 78406518090150444781097)
                ·
                  rfl

theorem cell22_2061398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_2061398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061398 prefixEnd_2061398 := by exact prefixLift 2061398
  have htrace : WordTrace (prefixWord ++ tailWord_2061398) baseStart_2061398 baseEnd_2061398 := by
    simpa [prefixWord, tailWord_2061398, baseEnd_2061398] using wordTrace_append hprefix tailTrace_2061398
  have hstable : (prefixWord ++ tailWord_2061398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061398).length < 2 ^ (prefixWord ++ tailWord_2061398).sum := by decide
  have hdescent : baseEnd_2061398 < baseStart_2061398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061407 : List Nat := [1, 1, 2, 3, 1, 1, 5, 1, 2, 5]
def baseStart_2061407 : Nat := 118140960795 + 2061407 * 2 ^ 59
def prefixEnd_2061407 : Nat := 4983230072969 + 3 ^ 40 * 2061407 * 2
def baseEnd_2061407 : Nat := 705661743695280979554845

theorem tailTrace_2061407 : CollatzResearch.WordTrace tailWord_2061407 prefixEnd_2061407 705661743695280979554845 := by
  unfold tailWord_2061407
  simp only [CollatzResearch.WordTrace]
  refine ⟨75185690042881974131758475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50123793361921316087838983 75185690042881974131758475)
  ·
    refine ⟨112778535064322961197637713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75185690042881974131758475 112778535064322961197637713)
    ·
      refine ⟨84583901298242220898228285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112778535064322961197637713 84583901298242220898228285)
      ·
        refine ⟨31718962986840832836835607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84583901298242220898228285 31718962986840832836835607)
        ·
          refine ⟨47578444480261249255253411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31718962986840832836835607 47578444480261249255253411)
          ·
            refine ⟨71367666720391873882880117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47578444480261249255253411 71367666720391873882880117)
            ·
              refine ⟨6690718755036738176520011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71367666720391873882880117 6690718755036738176520011)
              ·
                refine ⟨10036078132555107264780017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6690718755036738176520011 10036078132555107264780017)
                ·
                  refine ⟨7527058599416330448585013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10036078132555107264780017 7527058599416330448585013)
                  ·
                    refine ⟨705661743695280979554845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7527058599416330448585013 705661743695280979554845)
                    ·
                      rfl

theorem cell22_2061407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 2, 5].length) (baseStart_2061407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061407 prefixEnd_2061407 := by exact prefixLift 2061407
  have htrace : WordTrace (prefixWord ++ tailWord_2061407) baseStart_2061407 baseEnd_2061407 := by
    simpa [prefixWord, tailWord_2061407, baseEnd_2061407] using wordTrace_append hprefix tailTrace_2061407
  have hstable : (prefixWord ++ tailWord_2061407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061407).length < 2 ^ (prefixWord ++ tailWord_2061407).sum := by decide
  have hdescent : baseEnd_2061407 < baseStart_2061407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061437 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 8]
def baseStart_2061437 : Nat := 118140960795 + 2061437 * 2 ^ 59
def prefixEnd_2061437 : Nat := 4983230072969 + 3 ^ 40 * 2061437 * 2
def baseEnd_2061437 : Nat := 235224004436123633768251

theorem tailTrace_2061437 : CollatzResearch.WordTrace tailWord_2061437 prefixEnd_2061437 235224004436123633768251 := by
  unfold tailWord_2061437
  simp only [CollatzResearch.WordTrace]
  refine ⟨75186784232773289255350565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50124522821848859503567043 75186784232773289255350565)
  ·
    refine ⟨14097522043644991735378231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75186784232773289255350565 14097522043644991735378231)
    ·
      refine ⟨21146283065467487603067347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14097522043644991735378231 21146283065467487603067347)
      ·
        refine ⟨31719424598201231404601021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21146283065467487603067347 31719424598201231404601021)
        ·
          refine ⟨11894784224325461776725383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31719424598201231404601021 11894784224325461776725383)
          ·
            refine ⟨17842176336488192665088075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11894784224325461776725383 17842176336488192665088075)
            ·
              refine ⟨26763264504732288997632113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17842176336488192665088075 26763264504732288997632113)
              ·
                refine ⟨20072448378549216748224085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26763264504732288997632113 20072448378549216748224085)
                ·
                  refine ⟨235224004436123633768251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20072448378549216748224085 235224004436123633768251)
                  ·
                    rfl

theorem cell22_2061437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_2061437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061437 prefixEnd_2061437 := by exact prefixLift 2061437
  have htrace : WordTrace (prefixWord ++ tailWord_2061437) baseStart_2061437 baseEnd_2061437 := by
    simpa [prefixWord, tailWord_2061437, baseEnd_2061437] using wordTrace_append hprefix tailTrace_2061437
  have hstable : (prefixWord ++ tailWord_2061437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061437).length < 2 ^ (prefixWord ++ tailWord_2061437).sum := by decide
  have hdescent : baseEnd_2061437 < baseStart_2061437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061452 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 3, 5]
def baseStart_2061452 : Nat := 118140960795 + 2061452 * 2 ^ 59
def prefixEnd_2061452 : Nat := 4983230072969 + 3 ^ 40 * 2061452 * 2
def baseEnd_2061452 : Nat := 705677148114915862179707

theorem tailTrace_2061452 : CollatzResearch.WordTrace tailWord_2061452 prefixEnd_2061452 705677148114915862179707 := by
  unfold tailWord_2061452
  simp only [CollatzResearch.WordTrace]
  refine ⟨37593665663859473408573305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50124887551812631211431073 37593665663859473408573305)
  ·
    refine ⟨28195249247894605056429979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37593665663859473408573305 28195249247894605056429979)
    ·
      refine ⟨42292873871841907584644969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28195249247894605056429979 42292873871841907584644969)
      ·
        refine ⟨31719655403881430688483727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42292873871841907584644969 31719655403881430688483727)
        ·
          refine ⟨47579483105822146032725591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31719655403881430688483727 47579483105822146032725591)
          ·
            refine ⟨71369224658733219049088387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47579483105822146032725591 71369224658733219049088387)
            ·
              refine ⟨107053836988099828573632581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71369224658733219049088387 107053836988099828573632581)
              ·
                refine ⟨20072594435268717857556109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107053836988099828573632581 20072594435268717857556109)
                ·
                  refine ⟨7527222913225769196583541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20072594435268717857556109 7527222913225769196583541)
                  ·
                    refine ⟨705677148114915862179707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7527222913225769196583541 705677148114915862179707)
                    ·
                      rfl

theorem cell22_2061452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_2061452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061452 prefixEnd_2061452 := by exact prefixLift 2061452
  have htrace : WordTrace (prefixWord ++ tailWord_2061452) baseStart_2061452 baseEnd_2061452 := by
    simpa [prefixWord, tailWord_2061452, baseEnd_2061452] using wordTrace_append hprefix tailTrace_2061452
  have hstable : (prefixWord ++ tailWord_2061452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061452).length < 2 ^ (prefixWord ++ tailWord_2061452).sum := by decide
  have hdescent : baseEnd_2061452 < baseStart_2061452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061454 : List Nat := [4, 1, 1, 3, 2, 1, 1, 3, 6]
def baseStart_2061454 : Nat := 118140960795 + 2061454 * 2 ^ 59
def prefixEnd_2061454 : Nat := 4983230072969 + 3 ^ 40 * 2061454 * 2
def baseEnd_2061454 : Nat := 235225944251929507876567

theorem tailTrace_2061454 : CollatzResearch.WordTrace tailWord_2061454 prefixEnd_2061454 235225944251929507876567 := by
  unfold tailWord_2061454
  simp only [CollatzResearch.WordTrace]
  refine ⟨9398425534213962644839927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50124936182474467439146277 9398425534213962644839927)
  ·
    refine ⟨14097638301320943967259891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9398425534213962644839927 14097638301320943967259891)
    ·
      refine ⟨21146457451981415950889837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14097638301320943967259891 21146457451981415950889837)
      ·
        refine ⟨7929921544493030981583689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21146457451981415950889837 7929921544493030981583689)
        ·
          refine ⟨5947441158369773236187767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7929921544493030981583689 5947441158369773236187767)
          ·
            refine ⟨8921161737554659854281651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5947441158369773236187767 8921161737554659854281651)
            ·
              refine ⟨13381742606331989781422477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8921161737554659854281651 13381742606331989781422477)
              ·
                refine ⟨5018153477374496168033429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13381742606331989781422477 5018153477374496168033429)
                ·
                  refine ⟨235225944251929507876567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5018153477374496168033429 235225944251929507876567)
                  ·
                    rfl

theorem cell22_2061454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_2061454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061454 prefixEnd_2061454 := by exact prefixLift 2061454
  have htrace : WordTrace (prefixWord ++ tailWord_2061454) baseStart_2061454 baseEnd_2061454 := by
    simpa [prefixWord, tailWord_2061454, baseEnd_2061454] using wordTrace_append hprefix tailTrace_2061454
  have hstable : (prefixWord ++ tailWord_2061454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061454).length < 2 ^ (prefixWord ++ tailWord_2061454).sum := by decide
  have hdescent : baseEnd_2061454 < baseStart_2061454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061505 : List Nat := [1, 2, 6, 1, 1, 2, 3, 2, 4]
def baseStart_2061505 : Nat := 118140960795 + 2061505 * 2 ^ 59
def prefixEnd_2061505 : Nat := 4983230072969 + 3 ^ 40 * 2061505 * 2
def baseEnd_2061505 : Nat := 235231763699347130201515

theorem tailTrace_2061505 : CollatzResearch.WordTrace tailWord_2061505 prefixEnd_2061505 235231763699347130201515 := by
  unfold tailWord_2061505
  simp only [CollatzResearch.WordTrace]
  refine ⟨75189264396526936868825969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50126176264351291245883979 75189264396526936868825969)
  ·
    refine ⟨56391948297395202651619477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75189264396526936868825969 56391948297395202651619477)
    ·
      refine ⟨2643372576440400124294663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56391948297395202651619477 2643372576440400124294663)
      ·
        refine ⟨3965058864660600186441995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2643372576440400124294663 3965058864660600186441995)
        ·
          refine ⟨5947588296990900279662993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3965058864660600186441995 5947588296990900279662993)
          ·
            refine ⟨4460691222743175209747245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5947588296990900279662993 4460691222743175209747245)
            ·
              refine ⟨1672759208528690703655217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4460691222743175209747245 1672759208528690703655217)
              ·
                refine ⟨1254569406396518027741413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1672759208528690703655217 1254569406396518027741413)
                ·
                  refine ⟨235231763699347130201515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1254569406396518027741413 235231763699347130201515)
                  ·
                    rfl

theorem cell22_2061505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 2, 4].length) (baseStart_2061505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061505 prefixEnd_2061505 := by exact prefixLift 2061505
  have htrace : WordTrace (prefixWord ++ tailWord_2061505) baseStart_2061505 baseEnd_2061505 := by
    simpa [prefixWord, tailWord_2061505, baseEnd_2061505] using wordTrace_append hprefix tailTrace_2061505
  have hstable : (prefixWord ++ tailWord_2061505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061505).length < 2 ^ (prefixWord ++ tailWord_2061505).sum := by decide
  have hdescent : baseEnd_2061505 < baseStart_2061505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061556 : List Nat := [2, 6, 1, 2, 2, 1, 2, 2, 4]
def baseStart_2061556 : Nat := 118140960795 + 2061556 * 2 ^ 59
def prefixEnd_2061556 : Nat := 4983230072969 + 3 ^ 40 * 2061556 * 2
def baseEnd_2061556 : Nat := 235237583146764752526463

theorem tailTrace_2061556 : CollatzResearch.WordTrace tailWord_2061556 prefixEnd_2061556 235237583146764752526463 := by
  unfold tailWord_2061556
  simp only [CollatzResearch.WordTrace]
  refine ⟨37595562259671086289466261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50127416346228115052621681 37595562259671086289466261)
  ·
    refine ⟨1762291980922082169818731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37595562259671086289466261 1762291980922082169818731)
    ·
      refine ⟨2643437971383123254728097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1762291980922082169818731 2643437971383123254728097)
      ·
        refine ⟨1982578478537342441046073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2643437971383123254728097 1982578478537342441046073)
        ·
          refine ⟨1486933858903006830784555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1982578478537342441046073 1486933858903006830784555)
          ·
            refine ⟨2230400788354510246176833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1486933858903006830784555 2230400788354510246176833)
            ·
              refine ⟨1672800591265882684632625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2230400788354510246176833 1672800591265882684632625)
              ·
                refine ⟨1254600443449412013474469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1672800591265882684632625 1254600443449412013474469)
                ·
                  refine ⟨235237583146764752526463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1254600443449412013474469 235237583146764752526463)
                  ·
                    rfl

theorem cell22_2061556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_2061556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061556 prefixEnd_2061556 := by exact prefixLift 2061556
  have htrace : WordTrace (prefixWord ++ tailWord_2061556) baseStart_2061556 baseEnd_2061556 := by
    simpa [prefixWord, tailWord_2061556, baseEnd_2061556] using wordTrace_append hprefix tailTrace_2061556
  have hstable : (prefixWord ++ tailWord_2061556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061556).length < 2 ^ (prefixWord ++ tailWord_2061556).sum := by decide
  have hdescent : baseEnd_2061556 < baseStart_2061556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061576 : List Nat := [2, 1, 3, 2, 4, 1, 1, 1, 2, 5]
def baseStart_2061576 : Nat := 118140960795 + 2061576 * 2 ^ 59
def prefixEnd_2061576 : Nat := 4983230072969 + 3 ^ 40 * 2061576 * 2
def baseEnd_2061576 : Nat := 705719595849020872079327

theorem tailTrace_2061576 : CollatzResearch.WordTrace tailWord_2061576 prefixEnd_2061576 705719595849020872079327 := by
  unfold tailWord_2061576
  simp only [CollatzResearch.WordTrace]
  refine ⟨37595926989634857997330291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50127902652846477329773721 37595926989634857997330291)
  ·
    refine ⟨56393890484452286995995437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37595926989634857997330291 56393890484452286995995437)
    ·
      refine ⟨21147708931669607623498289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56393890484452286995995437 21147708931669607623498289)
      ·
        refine ⟨15860781698752205717623717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21147708931669607623498289 15860781698752205717623717)
        ·
          refine ⟨2973896568516038572054447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15860781698752205717623717 2973896568516038572054447)
          ·
            refine ⟨4460844852774057858081671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2973896568516038572054447 4460844852774057858081671)
            ·
              refine ⟨6691267279161086787122507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4460844852774057858081671 6691267279161086787122507)
              ·
                refine ⟨10036900918741630180683761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6691267279161086787122507 10036900918741630180683761)
                ·
                  refine ⟨7527675689056222635512821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10036900918741630180683761 7527675689056222635512821)
                  ·
                    refine ⟨705719595849020872079327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7527675689056222635512821 705719595849020872079327)
                    ·
                      rfl

theorem cell22_2061576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_2061576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061576 prefixEnd_2061576 := by exact prefixLift 2061576
  have htrace : WordTrace (prefixWord ++ tailWord_2061576) baseStart_2061576 baseEnd_2061576 := by
    simpa [prefixWord, tailWord_2061576, baseEnd_2061576] using wordTrace_append hprefix tailTrace_2061576
  have hstable : (prefixWord ++ tailWord_2061576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061576).length < 2 ^ (prefixWord ++ tailWord_2061576).sum := by decide
  have hdescent : baseEnd_2061576 < baseStart_2061576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061591 : List Nat := [1, 1, 3, 4, 1, 1, 2, 4, 1, 4]
def baseStart_2061591 : Nat := 118140960795 + 2061591 * 2 ^ 59
def prefixEnd_2061591 : Nat := 4983230072969 + 3 ^ 40 * 2061591 * 2
def baseEnd_2061591 : Nat := 705724730655565832954281

theorem tailTrace_2061591 : CollatzResearch.WordTrace tailWord_2061591 prefixEnd_2061591 705724730655565832954281 := by
  unfold tailWord_2061591
  simp only [CollatzResearch.WordTrace]
  refine ⟨75192401074215373556456627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50128267382810249037637751 75192401074215373556456627)
  ·
    refine ⟨112788601611323060334684941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75192401074215373556456627 112788601611323060334684941)
    ·
      refine ⟨42295725604246147625506853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112788601611323060334684941 42295725604246147625506853)
      ·
        refine ⟨7930448550796152679782535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42295725604246147625506853 7930448550796152679782535)
        ·
          refine ⟨11895672826194229019673803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7930448550796152679782535 11895672826194229019673803)
          ·
            refine ⟨17843509239291343529510705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11895672826194229019673803 17843509239291343529510705)
            ·
              refine ⟨13382631929468507647133029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17843509239291343529510705 13382631929468507647133029)
              ·
                refine ⟨2509243486775345183837443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13382631929468507647133029 2509243486775345183837443)
                ·
                  refine ⟨3763865230163017775756165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2509243486775345183837443 3763865230163017775756165)
                  ·
                    refine ⟨705724730655565832954281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3763865230163017775756165 705724730655565832954281)
                    ·
                      rfl

theorem cell22_2061591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_2061591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061591 prefixEnd_2061591 := by exact prefixLift 2061591
  have htrace : WordTrace (prefixWord ++ tailWord_2061591) baseStart_2061591 baseEnd_2061591 := by
    simpa [prefixWord, tailWord_2061591, baseEnd_2061591] using wordTrace_append hprefix tailTrace_2061591
  have hstable : (prefixWord ++ tailWord_2061591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061591).length < 2 ^ (prefixWord ++ tailWord_2061591).sum := by decide
  have hdescent : baseEnd_2061591 < baseStart_2061591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061608 : List Nat := [2, 1, 5, 1, 2, 2, 1, 3, 1, 4]
def baseStart_2061608 : Nat := 118140960795 + 2061608 * 2 ^ 59
def prefixEnd_2061608 : Nat := 4983230072969 + 3 ^ 40 * 2061608 * 2
def baseEnd_2061608 : Nat := 705730550102983455279229

theorem tailTrace_2061608 : CollatzResearch.WordTrace tailWord_2061608 prefixEnd_2061608 705730550102983455279229 := by
  unfold tailWord_2061608
  simp only [CollatzResearch.WordTrace]
  refine ⟨37596510557576892729912739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50128680743435856973216985 37596510557576892729912739)
  ·
    refine ⟨56394765836365339094869109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37596510557576892729912739 56394765836365339094869109)
    ·
      refine ⟨5287009297159250540143979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56394765836365339094869109 5287009297159250540143979)
      ·
        refine ⟨7930513945738875810215969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5287009297159250540143979 7930513945738875810215969)
        ·
          refine ⟨5947885459304156857661977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7930513945738875810215969 5947885459304156857661977)
          ·
            refine ⟨4460914094478117643246483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5947885459304156857661977 4460914094478117643246483)
            ·
              refine ⟨6691371141717176464869725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4460914094478117643246483 6691371141717176464869725)
              ·
                refine ⟨2509264178143941174326147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6691371141717176464869725 2509264178143941174326147)
                ·
                  refine ⟨3763896267215911761489221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2509264178143941174326147 3763896267215911761489221)
                  ·
                    refine ⟨705730550102983455279229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3763896267215911761489221 705730550102983455279229)
                    ·
                      rfl

theorem cell22_2061608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_2061608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061608 prefixEnd_2061608 := by exact prefixLift 2061608
  have htrace : WordTrace (prefixWord ++ tailWord_2061608) baseStart_2061608 baseEnd_2061608 := by
    simpa [prefixWord, tailWord_2061608, baseEnd_2061608] using wordTrace_append hprefix tailTrace_2061608
  have hstable : (prefixWord ++ tailWord_2061608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061608).length < 2 ^ (prefixWord ++ tailWord_2061608).sum := by decide
  have hdescent : baseEnd_2061608 < baseStart_2061608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061649 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 2, 7]
def baseStart_2061649 : Nat := 118140960795 + 2061649 * 2 ^ 59
def prefixEnd_2061649 : Nat := 4983230072969 + 3 ^ 40 * 2061649 * 2
def baseEnd_2061649 : Nat := 705744585240873015004103

theorem tailTrace_2061649 : CollatzResearch.WordTrace tailWord_2061649 prefixEnd_2061649 705744585240873015004103 := by
  unfold tailWord_2061649
  simp only [CollatzResearch.WordTrace]
  refine ⟨75194516508005249462068001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50129677672003499641378667 75194516508005249462068001)
  ·
    refine ⟨56395887381003937096551001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75194516508005249462068001 56395887381003937096551001)
    ·
      refine ⟨42296915535752952822413251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56395887381003937096551001 42296915535752952822413251)
      ·
        refine ⟨63445373303629429233619877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42296915535752952822413251 63445373303629429233619877)
        ·
          refine ⟨11896007494430517981303727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63445373303629429233619877 11896007494430517981303727)
          ·
            refine ⟨17844011241645776971955591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11896007494430517981303727 17844011241645776971955591)
            ·
              refine ⟨26766016862468665457933387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17844011241645776971955591 26766016862468665457933387)
              ·
                refine ⟨40149025293702998186900081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26766016862468665457933387 40149025293702998186900081)
                ·
                  refine ⟨30111768970277248640175061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40149025293702998186900081 30111768970277248640175061)
                  ·
                    refine ⟨705744585240873015004103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30111768970277248640175061 705744585240873015004103)
                    ·
                      rfl

theorem cell22_2061649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_2061649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061649 prefixEnd_2061649 := by exact prefixLift 2061649
  have htrace : WordTrace (prefixWord ++ tailWord_2061649) baseStart_2061649 baseEnd_2061649 := by
    simpa [prefixWord, tailWord_2061649, baseEnd_2061649] using wordTrace_append hprefix tailTrace_2061649
  have hstable : (prefixWord ++ tailWord_2061649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061649).length < 2 ^ (prefixWord ++ tailWord_2061649).sum := by decide
  have hdescent : baseEnd_2061649 < baseStart_2061649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061679 : List Nat := [1, 1, 2, 1, 3, 1, 3, 3, 7]
def baseStart_2061679 : Nat := 118140960795 + 2061679 * 2 ^ 59
def prefixEnd_2061679 : Nat := 4983230072969 + 3 ^ 40 * 2061679 * 2
def baseEnd_2061679 : Nat := 235251618284654312251337

theorem tailTrace_2061679 : CollatzResearch.WordTrace tailWord_2061679 prefixEnd_2061679 235251618284654312251337 := by
  unfold tailWord_2061679
  simp only [CollatzResearch.WordTrace]
  refine ⟨75195610697896564585660091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50130407131931043057106727 75195610697896564585660091)
  ·
    refine ⟨112793416046844846878490137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75195610697896564585660091 112793416046844846878490137)
    ·
      refine ⟨84595062035133635158867603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112793416046844846878490137 84595062035133635158867603)
      ·
        refine ⟨126892593052700452738301405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84595062035133635158867603 126892593052700452738301405)
        ·
          refine ⟨47584722394762669776863027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 126892593052700452738301405 47584722394762669776863027)
          ·
            refine ⟨71377083592144004665294541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47584722394762669776863027 71377083592144004665294541)
            ·
              refine ⟨26766406347054001749485453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71377083592144004665294541 26766406347054001749485453)
              ·
                refine ⟨10037402380145250656057045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26766406347054001749485453 10037402380145250656057045)
                ·
                  refine ⟨235251618284654312251337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10037402380145250656057045 235251618284654312251337)
                  ·
                    rfl

theorem cell22_2061679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 7].length) (baseStart_2061679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061679 prefixEnd_2061679 := by exact prefixLift 2061679
  have htrace : WordTrace (prefixWord ++ tailWord_2061679) baseStart_2061679 baseEnd_2061679 := by
    simpa [prefixWord, tailWord_2061679, baseEnd_2061679] using wordTrace_append hprefix tailTrace_2061679
  have hstable : (prefixWord ++ tailWord_2061679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061679).length < 2 ^ (prefixWord ++ tailWord_2061679).sum := by decide
  have hdescent : baseEnd_2061679 < baseStart_2061679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061786 : List Nat := [3, 1, 1, 2, 3, 3, 9]
def baseStart_2061786 : Nat := 118140960795 + 2061786 * 2 ^ 59
def prefixEnd_2061786 : Nat := 4983230072969 + 3 ^ 40 * 2061786 * 2
def baseEnd_2061786 : Nat := 26140425301505567567729

theorem tailTrace_2061786 : CollatzResearch.WordTrace tailWord_2061786 prefixEnd_2061786 26140425301505567567729 := by
  unfold tailWord_2061786
  simp only [CollatzResearch.WordTrace]
  refine ⟨18799878327127230464951303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50133008872339281239870141 18799878327127230464951303)
  ·
    refine ⟨28199817490690845697426955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18799878327127230464951303 28199817490690845697426955)
    ·
      refine ⟨42299726236036268546140433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28199817490690845697426955 42299726236036268546140433)
      ·
        refine ⟨31724794677027201409605325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42299726236036268546140433 31724794677027201409605325)
        ·
          refine ⟨11896798003885200528601997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31724794677027201409605325 11896798003885200528601997)
          ·
            refine ⟨4461299251456950198225749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11896798003885200528601997 4461299251456950198225749)
            ·
              refine ⟨26140425301505567567729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4461299251456950198225749 26140425301505567567729)
              ·
                rfl

theorem cell22_2061786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 9].length) (baseStart_2061786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061786 prefixEnd_2061786 := by exact prefixLift 2061786
  have htrace : WordTrace (prefixWord ++ tailWord_2061786) baseStart_2061786 baseEnd_2061786 := by
    simpa [prefixWord, tailWord_2061786, baseEnd_2061786] using wordTrace_append hprefix tailTrace_2061786
  have hstable : (prefixWord ++ tailWord_2061786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061786).length < 2 ^ (prefixWord ++ tailWord_2061786).sum := by decide
  have hdescent : baseEnd_2061786 < baseStart_2061786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061818 : List Nat := [3, 1, 1, 1, 1, 2, 3, 4, 3, 3]
def baseStart_2061818 : Nat := 118140960795 + 2061818 * 2 ^ 59
def prefixEnd_2061818 : Nat := 4983230072969 + 3 ^ 40 * 2061818 * 2
def baseEnd_2061818 : Nat := 705802437394612907528585

theorem tailTrace_2061818 : CollatzResearch.WordTrace tailWord_2061818 prefixEnd_2061818 705802437394612907528585 := by
  unfold tailWord_2061818
  simp only [CollatzResearch.WordTrace]
  refine ⟨18800170111098247831242527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50133786962928660883313405 18800170111098247831242527)
  ·
    refine ⟨28200255166647371746863791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18800170111098247831242527 28200255166647371746863791)
    ·
      refine ⟨42300382749971057620295687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28200255166647371746863791 42300382749971057620295687)
      ·
        refine ⟨63450574124956586430443531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42300382749971057620295687 63450574124956586430443531)
        ·
          refine ⟨95175861187434879645665297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63450574124956586430443531 95175861187434879645665297)
          ·
            refine ⟨71381895890576159734248973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95175861187434879645665297 71381895890576159734248973)
            ·
              refine ⟨26768210958966059900343365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71381895890576159734248973 26768210958966059900343365)
              ·
                refine ⟨5019039554806136231314381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26768210958966059900343365 5019039554806136231314381)
                ·
                  refine ⟨1882139833052301086742893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5019039554806136231314381 1882139833052301086742893)
                  ·
                    refine ⟨705802437394612907528585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1882139833052301086742893 705802437394612907528585)
                    ·
                      rfl

theorem cell22_2061818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 4, 3, 3].length) (baseStart_2061818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061818 prefixEnd_2061818 := by exact prefixLift 2061818
  have htrace : WordTrace (prefixWord ++ tailWord_2061818) baseStart_2061818 baseEnd_2061818 := by
    simpa [prefixWord, tailWord_2061818, baseEnd_2061818] using wordTrace_append hprefix tailTrace_2061818
  have hstable : (prefixWord ++ tailWord_2061818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061818).length < 2 ^ (prefixWord ++ tailWord_2061818).sum := by decide
  have hdescent : baseEnd_2061818 < baseStart_2061818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061837 : List Nat := [1, 7, 1, 1, 2, 2, 8]
def baseStart_2061837 : Nat := 118140960795 + 2061837 * 2 ^ 59
def prefixEnd_2061837 : Nat := 4983230072969 + 3 ^ 40 * 2061837 * 2
def baseEnd_2061837 : Nat := 26141071906774192270501

theorem tailTrace_2061837 : CollatzResearch.WordTrace tailWord_2061837 prefixEnd_2061837 26141071906774192270501 := by
  unfold tailWord_2061837
  simp only [CollatzResearch.WordTrace]
  refine ⟨75201373431324157569911765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50134248954216105046607843 75201373431324157569911765)
  ·
    refine ⟨1762532189796659943044807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 75201373431324157569911765 1762532189796659943044807)
    ·
      refine ⟨2643798284694989914567211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1762532189796659943044807 2643798284694989914567211)
      ·
        refine ⟨3965697427042484871850817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2643798284694989914567211 3965697427042484871850817)
        ·
          refine ⟨2974273070281863653888113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3965697427042484871850817 2974273070281863653888113)
          ·
            refine ⟨2230704802711397740416085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2974273070281863653888113 2230704802711397740416085)
            ·
              refine ⟨26141071906774192270501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2230704802711397740416085 26141071906774192270501)
              ·
                rfl

theorem cell22_2061837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 8].length) (baseStart_2061837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061837 prefixEnd_2061837 := by exact prefixLift 2061837
  have htrace : WordTrace (prefixWord ++ tailWord_2061837) baseStart_2061837 baseEnd_2061837 := by
    simpa [prefixWord, tailWord_2061837, baseEnd_2061837] using wordTrace_append hprefix tailTrace_2061837
  have hstable : (prefixWord ++ tailWord_2061837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061837).length < 2 ^ (prefixWord ++ tailWord_2061837).sum := by decide
  have hdescent : baseEnd_2061837 < baseStart_2061837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061854 : List Nat := [4, 3, 3, 1, 1, 1, 2, 7]
def baseStart_2061854 : Nat := 118140960795 + 2061854 * 2 ^ 59
def prefixEnd_2061854 : Nat := 4983230072969 + 3 ^ 40 * 2061854 * 2
def baseEnd_2061854 : Nat := 78423862325591201514275

theorem tailTrace_2061854 : CollatzResearch.WordTrace tailWord_2061854 prefixEnd_2061854 78423862325591201514275 := by
  unfold tailWord_2061854
  simp only [CollatzResearch.WordTrace]
  refine ⟨9400249184032821184160077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50134662314841712982187077 9400249184032821184160077)
  ·
    refine ⟨3525093444012307944060029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9400249184032821184160077 3525093444012307944060029)
    ·
      refine ⟨1321910041504615479022511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3525093444012307944060029 1321910041504615479022511)
      ·
        refine ⟨1982865062256923218533767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1321910041504615479022511 1982865062256923218533767)
        ·
          refine ⟨2974297593385384827800651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1982865062256923218533767 2974297593385384827800651)
          ·
            refine ⟨4461446390078077241700977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2974297593385384827800651 4461446390078077241700977)
            ·
              refine ⟨3346084792558557931275733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4461446390078077241700977 3346084792558557931275733)
              ·
                refine ⟨78423862325591201514275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3346084792558557931275733 78423862325591201514275)
                ·
                  rfl

theorem cell22_2061854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 7].length) (baseStart_2061854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061854 prefixEnd_2061854 := by exact prefixLift 2061854
  have htrace : WordTrace (prefixWord ++ tailWord_2061854) baseStart_2061854 baseEnd_2061854 := by
    simpa [prefixWord, tailWord_2061854, baseEnd_2061854] using wordTrace_append hprefix tailTrace_2061854
  have hstable : (prefixWord ++ tailWord_2061854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061854).length < 2 ^ (prefixWord ++ tailWord_2061854).sum := by decide
  have hdescent : baseEnd_2061854 < baseStart_2061854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061861 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 2, 8]
def baseStart_2061861 : Nat := 118140960795 + 2061861 * 2 ^ 59
def prefixEnd_2061861 : Nat := 4983230072969 + 3 ^ 40 * 2061861 * 2
def baseEnd_2061861 : Nat := 705817157173375128703453

theorem tailTrace_2061861 : CollatzResearch.WordTrace tailWord_2061861 prefixEnd_2061861 705817157173375128703453 := by
  unfold tailWord_2061861
  simp only [CollatzResearch.WordTrace]
  refine ⟨75202248783237209668785437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50134832522158139779190291 75202248783237209668785437)
  ·
    refine ⟨28200843293713953625794539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75202248783237209668785437 28200843293713953625794539)
    ·
      refine ⟨42301264940570930438691809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28200843293713953625794539 42301264940570930438691809)
      ·
        refine ⟨31725948705428197829018857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42301264940570930438691809 31725948705428197829018857)
        ·
          refine ⟨23794461529071148371764143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31725948705428197829018857 23794461529071148371764143)
          ·
            refine ⟨35691692293606722557646215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23794461529071148371764143 35691692293606722557646215)
            ·
              refine ⟨53537538440410083836469323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35691692293606722557646215 53537538440410083836469323)
              ·
                refine ⟨80306307660615125754703985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53537538440410083836469323 80306307660615125754703985)
                ·
                  refine ⟨60229730745461344316027989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80306307660615125754703985 60229730745461344316027989)
                  ·
                    refine ⟨705817157173375128703453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60229730745461344316027989 705817157173375128703453)
                    ·
                      rfl

theorem cell22_2061861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_2061861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061861 prefixEnd_2061861 := by exact prefixLift 2061861
  have htrace : WordTrace (prefixWord ++ tailWord_2061861) baseStart_2061861 baseEnd_2061861 := by
    simpa [prefixWord, tailWord_2061861, baseEnd_2061861] using wordTrace_append hprefix tailTrace_2061861
  have hstable : (prefixWord ++ tailWord_2061861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061861).length < 2 ^ (prefixWord ++ tailWord_2061861).sum := by decide
  have hdescent : baseEnd_2061861 < baseStart_2061861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061908 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_2061908 : Nat := 118140960795 + 2061908 * 2 ^ 59
def prefixEnd_2061908 : Nat := 4983230072969 + 3 ^ 40 * 2061908 * 2
def baseEnd_2061908 : Nat := 705833246233882672778309

theorem tailTrace_2061908 : CollatzResearch.WordTrace tailWord_2061908 prefixEnd_2061908 705833246233882672778309 := by
  unfold tailWord_2061908
  simp only [CollatzResearch.WordTrace]
  refine ⟨37601981507033468347873189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50135975342711291130497585 37601981507033468347873189)
  ·
    refine ⟨7050371532568775315226223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37601981507033468347873189 7050371532568775315226223)
    ·
      refine ⟨10575557298853162972839335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7050371532568775315226223 10575557298853162972839335)
      ·
        refine ⟨15863335948279744459259003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10575557298853162972839335 15863335948279744459259003)
        ·
          refine ⟨23795003922419616688888505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15863335948279744459259003 23795003922419616688888505)
          ·
            refine ⟨17846252941814712516666379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23795003922419616688888505 17846252941814712516666379)
            ·
              refine ⟨26769379412722068774999569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17846252941814712516666379 26769379412722068774999569)
              ·
                refine ⟨20077034559541551581249677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26769379412722068774999569 20077034559541551581249677)
                ·
                  refine ⟨7528887959828081842968629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20077034559541551581249677 7528887959828081842968629)
                  ·
                    refine ⟨705833246233882672778309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7528887959828081842968629 705833246233882672778309)
                    ·
                      rfl

theorem cell22_2061908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_2061908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061908 prefixEnd_2061908 := by exact prefixLift 2061908
  have htrace : WordTrace (prefixWord ++ tailWord_2061908) baseStart_2061908 baseEnd_2061908 := by
    simpa [prefixWord, tailWord_2061908, baseEnd_2061908] using wordTrace_append hprefix tailTrace_2061908
  have hstable : (prefixWord ++ tailWord_2061908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061908).length < 2 ^ (prefixWord ++ tailWord_2061908).sum := by decide
  have hdescent : baseEnd_2061908 < baseStart_2061908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061925 : List Nat := [1, 3, 1, 3, 3, 2, 2, 1, 1, 5]
def baseStart_2061925 : Nat := 118140960795 + 2061925 * 2 ^ 59
def prefixEnd_2061925 : Nat := 4983230072969 + 3 ^ 40 * 2061925 * 2
def baseEnd_2061925 : Nat := 705839065681300295103257

theorem tailTrace_2061925 : CollatzResearch.WordTrace tailWord_2061925 prefixEnd_2061925 705839065681300295103257 := by
  unfold tailWord_2061925
  simp only [CollatzResearch.WordTrace]
  refine ⟨75204583055005348599115229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50136388703336899066076819 75204583055005348599115229)
  ·
    refine ⟨28201718645627005724668211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75204583055005348599115229 28201718645627005724668211)
    ·
      refine ⟨42302577968440508587002317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28201718645627005724668211 42302577968440508587002317)
      ·
        refine ⟨15863466738165190720125869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42302577968440508587002317 15863466738165190720125869)
        ·
          refine ⟨5948800026811946520047201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15863466738165190720125869 5948800026811946520047201)
          ·
            refine ⟨4461600020108959890035401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5948800026811946520047201 4461600020108959890035401)
            ·
              refine ⟨3346200015081719917526551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4461600020108959890035401 3346200015081719917526551)
              ·
                refine ⟨5019300022622579876289827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3346200015081719917526551 5019300022622579876289827)
                ·
                  refine ⟨7528950033933869814434741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5019300022622579876289827 7528950033933869814434741)
                  ·
                    refine ⟨705839065681300295103257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7528950033933869814434741 705839065681300295103257)
                    ·
                      rfl

theorem cell22_2061925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_2061925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2061925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2061925 prefixEnd_2061925 := by exact prefixLift 2061925
  have htrace : WordTrace (prefixWord ++ tailWord_2061925) baseStart_2061925 baseEnd_2061925 := by
    simpa [prefixWord, tailWord_2061925, baseEnd_2061925] using wordTrace_append hprefix tailTrace_2061925
  have hstable : (prefixWord ++ tailWord_2061925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061925).length < 2 ^ (prefixWord ++ tailWord_2061925).sum := by decide
  have hdescent : baseEnd_2061925 < baseStart_2061925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062030 : List Nat := [4, 1, 1, 1, 3, 1, 2, 2, 3, 4]
def baseStart_2062030 : Nat := 118140960795 + 2062030 * 2 ^ 59
def prefixEnd_2062030 : Nat := 4983230072969 + 3 ^ 40 * 2062030 * 2
def baseEnd_2062030 : Nat := 705875009327115021227935

theorem tailTrace_2062030 : CollatzResearch.WordTrace tailWord_2062030 prefixEnd_2062030 705875009327115021227935 := by
  unfold tailWord_2062030
  simp only [CollatzResearch.WordTrace]
  refine ⟨9401051589953118941460943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50138941813083301021125029 9401051589953118941460943)
  ·
    refine ⟨14101577384929678412191415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9401051589953118941460943 14101577384929678412191415)
    ·
      refine ⟨21152366077394517618287123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14101577384929678412191415 21152366077394517618287123)
      ·
        refine ⟨31728549116091776427430685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21152366077394517618287123 31728549116091776427430685)
        ·
          refine ⟨11898205918534416160286507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31728549116091776427430685 11898205918534416160286507)
          ·
            refine ⟨17847308877801624240429761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11898205918534416160286507 17847308877801624240429761)
            ·
              refine ⟨13385481658351218180322321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17847308877801624240429761 13385481658351218180322321)
              ·
                refine ⟨10039111243763413635241741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13385481658351218180322321 10039111243763413635241741)
                ·
                  refine ⟨3764666716411280113215653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10039111243763413635241741 3764666716411280113215653)
                  ·
                    refine ⟨705875009327115021227935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3764666716411280113215653 705875009327115021227935)
                    ·
                      rfl

theorem cell22_2062030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_2062030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062030 prefixEnd_2062030 := by exact prefixLift 2062030
  have htrace : WordTrace (prefixWord ++ tailWord_2062030) baseStart_2062030 baseEnd_2062030 := by
    simpa [prefixWord, tailWord_2062030, baseEnd_2062030] using wordTrace_append hprefix tailTrace_2062030
  have hstable : (prefixWord ++ tailWord_2062030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062030).length < 2 ^ (prefixWord ++ tailWord_2062030).sum := by decide
  have hdescent : baseEnd_2062030 < baseStart_2062030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062034 : List Nat := [3, 2, 2, 2, 2, 3, 2, 1, 5]
def baseStart_2062034 : Nat := 118140960795 + 2062034 * 2 ^ 59
def prefixEnd_2062034 : Nat := 4983230072969 + 3 ^ 40 * 2062034 * 2
def baseEnd_2062034 : Nat := 235292126202953448042641

theorem tailTrace_2062034 : CollatzResearch.WordTrace tailWord_2062034 prefixEnd_2062034 235292126202953448042641 := by
  unfold tailWord_2062034
  simp only [CollatzResearch.WordTrace]
  refine ⟨18802139652902615053708289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50139039074406973476555437 18802139652902615053708289)
  ·
    refine ⟨14101604739676961290281217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18802139652902615053708289 14101604739676961290281217)
    ·
      refine ⟨10576203554757720967710913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14101604739676961290281217 10576203554757720967710913)
      ·
        refine ⟨7932152666068290725783185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10576203554757720967710913 7932152666068290725783185)
        ·
          refine ⟨5949114499551218044337389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7932152666068290725783185 5949114499551218044337389)
          ·
            refine ⟨2230917937331706766626521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5949114499551218044337389 2230917937331706766626521)
            ·
              refine ⟨1673188452998780074969891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2230917937331706766626521 1673188452998780074969891)
              ·
                refine ⟨2509782679498170112454837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1673188452998780074969891 2509782679498170112454837)
                ·
                  refine ⟨235292126202953448042641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2509782679498170112454837 235292126202953448042641)
                  ·
                    rfl

theorem cell22_2062034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_2062034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062034 prefixEnd_2062034 := by exact prefixLift 2062034
  have htrace : WordTrace (prefixWord ++ tailWord_2062034) baseStart_2062034 baseEnd_2062034 := by
    simpa [prefixWord, tailWord_2062034, baseEnd_2062034] using wordTrace_append hprefix tailTrace_2062034
  have hstable : (prefixWord ++ tailWord_2062034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062034).length < 2 ^ (prefixWord ++ tailWord_2062034).sum := by decide
  have hdescent : baseEnd_2062034 < baseStart_2062034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062060 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 6, 3]
def baseStart_2062060 : Nat := 118140960795 + 2062060 * 2 ^ 59
def prefixEnd_2062060 : Nat := 4983230072969 + 3 ^ 40 * 2062060 * 2
def baseEnd_2062060 : Nat := 705885278940204942977843

theorem tailTrace_2062060 : CollatzResearch.WordTrace tailWord_2062060 prefixEnd_2062060 705885278940204942977843 := by
  unfold tailWord_2062060
  simp only [CollatzResearch.WordTrace]
  refine ⟨37604753454758133327639817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50139671273010844436853089 37604753454758133327639817)
  ·
    refine ⟨28203565091068599995729863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37604753454758133327639817 28203565091068599995729863)
    ·
      refine ⟨42305347636602899993594795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28203565091068599995729863 42305347636602899993594795)
      ·
        refine ⟨63458021454904349990392193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42305347636602899993594795 63458021454904349990392193)
        ·
          refine ⟨47593516091178262492794145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63458021454904349990392193 47593516091178262492794145)
          ·
            refine ⟨35695137068383696869595609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47593516091178262492794145 35695137068383696869595609)
            ·
              refine ⟨26771352801287772652196707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35695137068383696869595609 26771352801287772652196707)
              ·
                refine ⟨40157029201931658978295061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26771352801287772652196707 40157029201931658978295061)
                ·
                  refine ⟨1882360743840546514607581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40157029201931658978295061 1882360743840546514607581)
                  ·
                    refine ⟨705885278940204942977843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1882360743840546514607581 705885278940204942977843)
                    ·
                      rfl

theorem cell22_2062060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 3].length) (baseStart_2062060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062060 prefixEnd_2062060 := by exact prefixLift 2062060
  have htrace : WordTrace (prefixWord ++ tailWord_2062060) baseStart_2062060 baseEnd_2062060 := by
    simpa [prefixWord, tailWord_2062060, baseEnd_2062060] using wordTrace_append hprefix tailTrace_2062060
  have hstable : (prefixWord ++ tailWord_2062060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062060).length < 2 ^ (prefixWord ++ tailWord_2062060).sum := by decide
  have hdescent : baseEnd_2062060 < baseStart_2062060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062062 : List Nat := [4, 1, 2, 1, 1, 2, 2, 5, 4]
def baseStart_2062062 : Nat := 118140960795 + 2062062 * 2 ^ 59
def prefixEnd_2062062 : Nat := 4983230072969 + 3 ^ 40 * 2062062 * 2
def baseEnd_2062062 : Nat := 235295321193692534809279

theorem tailTrace_2062062 : CollatzResearch.WordTrace tailWord_2062062 prefixEnd_2062062 235295321193692534809279 := by
  unfold tailWord_2062062
  simp only [CollatzResearch.WordTrace]
  refine ⟨9401197481938627624606555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50139719903672680664568293 9401197481938627624606555)
  ·
    refine ⟨14101796222907941436909833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9401197481938627624606555 14101796222907941436909833)
    ·
      refine ⟨10576347167180956077682375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14101796222907941436909833 10576347167180956077682375)
      ·
        refine ⟨15864520750771434116523563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10576347167180956077682375 15864520750771434116523563)
        ·
          refine ⟨23796781126157151174785345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15864520750771434116523563 23796781126157151174785345)
          ·
            refine ⟨17847585844617863381089009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23796781126157151174785345 17847585844617863381089009)
            ·
              refine ⟨13385689383463397535816757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17847585844617863381089009 13385689383463397535816757)
              ·
                refine ⟨1254908379699693518982821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13385689383463397535816757 1254908379699693518982821)
                ·
                  refine ⟨235295321193692534809279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1254908379699693518982821 235295321193692534809279)
                  ·
                    rfl

theorem cell22_2062062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_2062062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062062 prefixEnd_2062062 := by exact prefixLift 2062062
  have htrace : WordTrace (prefixWord ++ tailWord_2062062) baseStart_2062062 baseEnd_2062062 := by
    simpa [prefixWord, tailWord_2062062, baseEnd_2062062] using wordTrace_append hprefix tailTrace_2062062
  have hstable : (prefixWord ++ tailWord_2062062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062062).length < 2 ^ (prefixWord ++ tailWord_2062062).sum := by decide
  have hdescent : baseEnd_2062062 < baseStart_2062062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062090 : List Nat := [3, 1, 2, 2, 1, 3, 3, 7]
def baseStart_2062090 : Nat := 118140960795 + 2062090 * 2 ^ 59
def prefixEnd_2062090 : Nat := 4983230072969 + 3 ^ 40 * 2062090 * 2
def baseEnd_2062090 : Nat := 78432838728143873858639

theorem tailTrace_2062090 : CollatzResearch.WordTrace tailWord_2062090 prefixEnd_2062090 78432838728143873858639 := by
  unfold tailWord_2062090
  simp only [CollatzResearch.WordTrace]
  refine ⟨18802650274851895444717931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50140400732938387852581149 18802650274851895444717931)
  ·
    refine ⟨28203975412277843167076897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18802650274851895444717931 28203975412277843167076897)
    ·
      refine ⟨21152981559208382375307673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28203975412277843167076897 21152981559208382375307673)
      ·
        refine ⟨15864736169406286781480755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21152981559208382375307673 15864736169406286781480755)
        ·
          refine ⟨23797104254109430172221133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15864736169406286781480755 23797104254109430172221133)
          ·
            refine ⟨8923914095291036314582925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23797104254109430172221133 8923914095291036314582925)
            ·
              refine ⟨3346467785734138617968597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8923914095291036314582925 3346467785734138617968597)
              ·
                refine ⟨78432838728143873858639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3346467785734138617968597 78432838728143873858639)
                ·
                  rfl

theorem cell22_2062090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 7].length) (baseStart_2062090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062090 prefixEnd_2062090 := by exact prefixLift 2062090
  have htrace : WordTrace (prefixWord ++ tailWord_2062090) baseStart_2062090 baseEnd_2062090 := by
    simpa [prefixWord, tailWord_2062090, baseEnd_2062090] using wordTrace_append hprefix tailTrace_2062090
  have hstable : (prefixWord ++ tailWord_2062090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062090).length < 2 ^ (prefixWord ++ tailWord_2062090).sum := by decide
  have hdescent : baseEnd_2062090 < baseStart_2062090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062135 : List Nat := [1, 1, 3, 1, 2, 1, 2, 6, 5]
def baseStart_2062135 : Nat := 118140960795 + 2062135 * 2 ^ 59
def prefixEnd_2062135 : Nat := 4983230072969 + 3 ^ 40 * 2062135 * 2
def baseEnd_2062135 : Nat := 235303650990976582450871

theorem tailTrace_2062135 : CollatzResearch.WordTrace tailWord_2062135 prefixEnd_2062135 235303650990976582450871 := by
  unfold tailWord_2062135
  simp only [CollatzResearch.WordTrace]
  refine ⟨75212242384244554464259859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50141494922829702976173239 75212242384244554464259859)
  ·
    refine ⟨112818363576366831696389789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75212242384244554464259859 112818363576366831696389789)
    ·
      refine ⟨42306886341137561886146171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112818363576366831696389789 42306886341137561886146171)
      ·
        refine ⟨63460329511706342829219257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42306886341137561886146171 63460329511706342829219257)
        ·
          refine ⟨47595247133779757121914443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63460329511706342829219257 47595247133779757121914443)
          ·
            refine ⟨71392870700669635682871665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47595247133779757121914443 71392870700669635682871665)
            ·
              refine ⟨53544653025502226762153749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71392870700669635682871665 53544653025502226762153749)
              ·
                refine ⟨2509905610570416879475957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53544653025502226762153749 2509905610570416879475957)
                ·
                  refine ⟨235303650990976582450871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2509905610570416879475957 235303650990976582450871)
                  ·
                    rfl

theorem cell22_2062135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 6, 5].length) (baseStart_2062135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062135 prefixEnd_2062135 := by exact prefixLift 2062135
  have htrace : WordTrace (prefixWord ++ tailWord_2062135) baseStart_2062135 baseEnd_2062135 := by
    simpa [prefixWord, tailWord_2062135, baseEnd_2062135] using wordTrace_append hprefix tailTrace_2062135
  have hstable : (prefixWord ++ tailWord_2062135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062135).length < 2 ^ (prefixWord ++ tailWord_2062135).sum := by decide
  have hdescent : baseEnd_2062135 < baseStart_2062135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062216 : List Nat := [2, 1, 3, 3, 3, 2, 1, 2, 1, 4]
def baseStart_2062216 : Nat := 118140960795 + 2062216 * 2 ^ 59
def prefixEnd_2062216 : Nat := 4983230072969 + 3 ^ 40 * 2062216 * 2
def baseEnd_2062216 : Nat := 705938680928272536077365

theorem tailTrace_2062216 : CollatzResearch.WordTrace tailWord_2062216 prefixEnd_2062216 705938680928272536077365 := by
  unfold tailWord_2062216
  simp only [CollatzResearch.WordTrace]
  refine ⟨37607598348475552648979251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50143464464634070198639001 37607598348475552648979251)
  ·
    refine ⟨56411397522713328973468877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37607598348475552648979251 56411397522713328973468877)
    ·
      refine ⟨21154274071017498365050829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56411397522713328973468877 21154274071017498365050829)
      ·
        refine ⟨7932852776631561886894061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21154274071017498365050829 7932852776631561886894061)
        ·
          refine ⟨2974819791236835707585273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7932852776631561886894061 2974819791236835707585273)
          ·
            refine ⟨2231114843427626780688955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2974819791236835707585273 2231114843427626780688955)
            ·
              refine ⟨3346672265141440171033433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2231114843427626780688955 3346672265141440171033433)
              ·
                refine ⟨2510004198856080128275075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3346672265141440171033433 2510004198856080128275075)
                ·
                  refine ⟨3765006298284120192412613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2510004198856080128275075 3765006298284120192412613)
                  ·
                    refine ⟨705938680928272536077365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3765006298284120192412613 705938680928272536077365)
                    ·
                      rfl

theorem cell22_2062216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_2062216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062216 prefixEnd_2062216 := by exact prefixLift 2062216
  have htrace : WordTrace (prefixWord ++ tailWord_2062216) baseStart_2062216 baseEnd_2062216 := by
    simpa [prefixWord, tailWord_2062216, baseEnd_2062216] using wordTrace_append hprefix tailTrace_2062216
  have hstable : (prefixWord ++ tailWord_2062216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062216).length < 2 ^ (prefixWord ++ tailWord_2062216).sum := by decide
  have hdescent : baseEnd_2062216 < baseStart_2062216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062225 : List Nat := [1, 2, 2, 1, 1, 1, 6, 8]
def baseStart_2062225 : Nat := 118140960795 + 2062225 * 2 ^ 59
def prefixEnd_2062225 : Nat := 4983230072969 + 3 ^ 40 * 2062225 * 2
def baseEnd_2062225 : Nat := 78437973534688834733593

theorem tailTrace_2062225 : CollatzResearch.WordTrace tailWord_2062225 prefixEnd_2062225 78437973534688834733593 := by
  unfold tailWord_2062225
  simp only [CollatzResearch.WordTrace]
  refine ⟨75215524953918499835036129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50143683302612333223357419 75215524953918499835036129)
  ·
    refine ⟨56411643715438874876277097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75215524953918499835036129 56411643715438874876277097)
    ·
      refine ⟨42308732786579156157207823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56411643715438874876277097 42308732786579156157207823)
      ·
        refine ⟨63463099179868734235811735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42308732786579156157207823 63463099179868734235811735)
        ·
          refine ⟨95194648769803101353717603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63463099179868734235811735 95194648769803101353717603)
          ·
            refine ⟨142791973154704652030576405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95194648769803101353717603 142791973154704652030576405)
            ·
              refine ⟨6693373741626780563933269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142791973154704652030576405 6693373741626780563933269)
              ·
                refine ⟨78437973534688834733593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6693373741626780563933269 78437973534688834733593)
                ·
                  rfl

theorem cell22_2062225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 8].length) (baseStart_2062225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062225 prefixEnd_2062225 := by exact prefixLift 2062225
  have htrace : WordTrace (prefixWord ++ tailWord_2062225) baseStart_2062225 baseEnd_2062225 := by
    simpa [prefixWord, tailWord_2062225, baseEnd_2062225] using wordTrace_append hprefix tailTrace_2062225
  have hstable : (prefixWord ++ tailWord_2062225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062225).length < 2 ^ (prefixWord ++ tailWord_2062225).sum := by decide
  have hdescent : baseEnd_2062225 < baseStart_2062225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062242 : List Nat := [3, 3, 1, 2, 3, 10]
def baseStart_2062242 : Nat := 118140960795 + 2062242 * 2 ^ 59
def prefixEnd_2062242 : Nat := 4983230072969 + 3 ^ 40 * 2062242 * 2
def baseEnd_2062242 : Nat := 8715402237773051048485

theorem tailTrace_2062242 : CollatzResearch.WordTrace tailWord_2062242 prefixEnd_2062242 8715402237773051048485 := by
  unfold tailWord_2062242
  simp only [CollatzResearch.WordTrace]
  refine ⟨18804036248714227934601245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50144096663237941158936653 18804036248714227934601245)
  ·
    refine ⟨7051513593267835475475467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18804036248714227934601245 7051513593267835475475467)
    ·
      refine ⟨10577270389901753213213201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7051513593267835475475467 10577270389901753213213201)
      ·
        refine ⟨7932952792426314909909901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10577270389901753213213201 7932952792426314909909901)
        ·
          refine ⟨2974857297159868091216213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7932952792426314909909901 2974857297159868091216213)
          ·
            refine ⟨8715402237773051048485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2974857297159868091216213 8715402237773051048485)
            ·
              rfl

theorem cell22_2062242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 10].length) (baseStart_2062242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062242 prefixEnd_2062242 := by exact prefixLift 2062242
  have htrace : WordTrace (prefixWord ++ tailWord_2062242) baseStart_2062242 baseEnd_2062242 := by
    simpa [prefixWord, tailWord_2062242, baseEnd_2062242] using wordTrace_append hprefix tailTrace_2062242
  have hstable : (prefixWord ++ tailWord_2062242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062242).length < 2 ^ (prefixWord ++ tailWord_2062242).sum := by decide
  have hdescent : baseEnd_2062242 < baseStart_2062242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062248 : List Nat := [2, 1, 6, 2, 1, 1, 1, 4, 4]
def baseStart_2062248 : Nat := 118140960795 + 2062248 * 2 ^ 59
def prefixEnd_2062248 : Nat := 4983230072969 + 3 ^ 40 * 2062248 * 2
def baseEnd_2062248 : Nat := 235316545060745039759089

theorem tailTrace_2062248 : CollatzResearch.WordTrace tailWord_2062248 prefixEnd_2062248 235316545060745039759089 := by
  unfold tailWord_2062248
  simp only [CollatzResearch.WordTrace]
  refine ⟨37608181916417587381561699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50144242555223449842082265 37608181916417587381561699)
  ·
    refine ⟨56412272874626381072342549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37608181916417587381561699 56412272874626381072342549)
    ·
      refine ⟨2644325290998111612766057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56412272874626381072342549 2644325290998111612766057)
      ·
        refine ⟨1983243968248583709574543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2644325290998111612766057 1983243968248583709574543)
        ·
          refine ⟨2974865952372875564361815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1983243968248583709574543 2974865952372875564361815)
          ·
            refine ⟨4462298928559313346542723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2974865952372875564361815 4462298928559313346542723)
            ·
              refine ⟨6693448392838970019814085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4462298928559313346542723 6693448392838970019814085)
              ·
                refine ⟨1255021573657306878715141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6693448392838970019814085 1255021573657306878715141)
                ·
                  refine ⟨235316545060745039759089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1255021573657306878715141 235316545060745039759089)
                  ·
                    rfl

theorem cell22_2062248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 4, 4].length) (baseStart_2062248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062248 prefixEnd_2062248 := by exact prefixLift 2062248
  have htrace : WordTrace (prefixWord ++ tailWord_2062248) baseStart_2062248 baseEnd_2062248 := by
    simpa [prefixWord, tailWord_2062248, baseEnd_2062248] using wordTrace_append hprefix tailTrace_2062248
  have hstable : (prefixWord ++ tailWord_2062248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062248).length < 2 ^ (prefixWord ++ tailWord_2062248).sum := by decide
  have hdescent : baseEnd_2062248 < baseStart_2062248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062255 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 1, 8]
def baseStart_2062255 : Nat := 118140960795 + 2062255 * 2 ^ 59
def prefixEnd_2062255 : Nat := 4983230072969 + 3 ^ 40 * 2062255 * 2
def baseEnd_2062255 : Nat := 705952031425289434352245

theorem tailTrace_2062255 : CollatzResearch.WordTrace tailWord_2062255 prefixEnd_2062255 705952031425289434352245 := by
  unfold tailWord_2062255
  simp only [CollatzResearch.WordTrace]
  refine ⟨75216619143809814958628219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50144412762539876639085479 75216619143809814958628219)
  ·
    refine ⟨112824928715714722437942329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75216619143809814958628219 112824928715714722437942329)
    ·
      refine ⟨84618696536786041828456747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112824928715714722437942329 84618696536786041828456747)
      ·
        refine ⟨126928044805179062742685121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84618696536786041828456747 126928044805179062742685121)
        ·
          refine ⟨95196033603884297057013841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126928044805179062742685121 95196033603884297057013841)
          ·
            refine ⟨71397025202913222792760381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95196033603884297057013841 71397025202913222792760381)
            ·
              refine ⟨26773884451092458547285143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71397025202913222792760381 26773884451092458547285143)
              ·
                refine ⟨40160826676638687820927715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26773884451092458547285143 40160826676638687820927715)
                ·
                  refine ⟨60241240014958031731391573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40160826676638687820927715 60241240014958031731391573)
                  ·
                    refine ⟨705952031425289434352245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60241240014958031731391573 705952031425289434352245)
                    ·
                      rfl

theorem cell22_2062255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_2062255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062255 prefixEnd_2062255 := by exact prefixLift 2062255
  have htrace : WordTrace (prefixWord ++ tailWord_2062255) baseStart_2062255 baseEnd_2062255 := by
    simpa [prefixWord, tailWord_2062255, baseEnd_2062255] using wordTrace_append hprefix tailTrace_2062255
  have hstable : (prefixWord ++ tailWord_2062255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062255).length < 2 ^ (prefixWord ++ tailWord_2062255).sum := by decide
  have hdescent : baseEnd_2062255 < baseStart_2062255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062321 : List Nat := [1, 2, 2, 2, 5, 1, 3, 1, 5]
def baseStart_2062321 : Nat := 118140960795 + 2062321 * 2 ^ 59
def prefixEnd_2062321 : Nat := 4983230072969 + 3 ^ 40 * 2062321 * 2
def baseEnd_2062321 : Nat := 235324874858029087400681

theorem tailTrace_2062321 : CollatzResearch.WordTrace tailWord_2062321 prefixEnd_2062321 235324874858029087400681 := by
  unfold tailWord_2062321
  simp only [CollatzResearch.WordTrace]
  refine ⟨75219026361570708230530817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50146017574380472153687211 75219026361570708230530817)
  ·
    refine ⟨56414269771178031172898113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75219026361570708230530817 56414269771178031172898113)
    ·
      refine ⟨42310702328383523379673585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56414269771178031172898113 42310702328383523379673585)
      ·
        refine ⟨31733026746287642534755189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42310702328383523379673585 31733026746287642534755189)
        ·
          refine ⟨2974971257464466487633299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31733026746287642534755189 2974971257464466487633299)
          ·
            refine ⟨4462456886196699731449949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2974971257464466487633299 4462456886196699731449949)
            ·
              refine ⟨1673421332323762399293731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4462456886196699731449949 1673421332323762399293731)
              ·
                refine ⟨2510131998485643598940597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1673421332323762399293731 2510131998485643598940597)
                ·
                  refine ⟨235324874858029087400681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2510131998485643598940597 235324874858029087400681)
                  ·
                    rfl

theorem cell22_2062321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 5].length) (baseStart_2062321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062321 prefixEnd_2062321 := by exact prefixLift 2062321
  have htrace : WordTrace (prefixWord ++ tailWord_2062321) baseStart_2062321 baseEnd_2062321 := by
    simpa [prefixWord, tailWord_2062321, baseEnd_2062321] using wordTrace_append hprefix tailTrace_2062321
  have hstable : (prefixWord ++ tailWord_2062321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062321).length < 2 ^ (prefixWord ++ tailWord_2062321).sum := by decide
  have hdescent : baseEnd_2062321 < baseStart_2062321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062332 : List Nat := [2, 2, 2, 1, 2, 2, 1, 4, 6]
def baseStart_2062332 : Nat := 118140960795 + 2062332 * 2 ^ 59
def prefixEnd_2062332 : Nat := 4983230072969 + 3 ^ 40 * 2062332 * 2
def baseEnd_2062332 : Nat := 235326130032962300059003

theorem tailTrace_2062332 : CollatzResearch.WordTrace tailWord_2062332 prefixEnd_2062332 235326130032962300059003 := by
  unfold tailWord_2062332
  simp only [CollatzResearch.WordTrace]
  refine ⟨37609713782265428554590625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50146285043020571406120833 37609713782265428554590625)
  ·
    refine ⟨28207285336699071415942969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37609713782265428554590625 28207285336699071415942969)
    ·
      refine ⟨21155464002524303561957227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28207285336699071415942969 21155464002524303561957227)
      ·
        refine ⟨31733196003786455342935841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21155464002524303561957227 31733196003786455342935841)
        ·
          refine ⟨23799897002839841507201881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31733196003786455342935841 23799897002839841507201881)
          ·
            refine ⟨17849922752129881130401411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23799897002839841507201881 17849922752129881130401411)
            ·
              refine ⟨26774884128194821695602117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17849922752129881130401411 26774884128194821695602117)
              ·
                refine ⟨5020290774036529067925397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26774884128194821695602117 5020290774036529067925397)
                ·
                  refine ⟨235326130032962300059003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5020290774036529067925397 235326130032962300059003)
                  ·
                    rfl

theorem cell22_2062332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 6].length) (baseStart_2062332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062332 prefixEnd_2062332 := by exact prefixLift 2062332
  have htrace : WordTrace (prefixWord ++ tailWord_2062332) baseStart_2062332 baseEnd_2062332 := by
    simpa [prefixWord, tailWord_2062332, baseEnd_2062332] using wordTrace_append hprefix tailTrace_2062332
  have hstable : (prefixWord ++ tailWord_2062332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062332).length < 2 ^ (prefixWord ++ tailWord_2062332).sum := by decide
  have hdescent : baseEnd_2062332 < baseStart_2062332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062347 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 3, 5]
def baseStart_2062347 : Nat := 118140960795 + 2062347 * 2 ^ 59
def prefixEnd_2062347 : Nat := 4983230072969 + 3 ^ 40 * 2062347 * 2
def baseEnd_2062347 : Nat := 705983524905431861051963

theorem tailTrace_2062347 : CollatzResearch.WordTrace tailWord_2062347 prefixEnd_2062347 705983524905431861051963 := by
  unfold tailWord_2062347
  simp only [CollatzResearch.WordTrace]
  refine ⟨75219974659476514670977295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50146649772984343113984863 75219974659476514670977295)
  ·
    refine ⟨112829961989214772006465943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75219974659476514670977295 112829961989214772006465943)
    ·
      refine ⟨169244942983822158009698915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112829961989214772006465943 169244942983822158009698915)
      ·
        refine ⟨253867414475733237014548373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169244942983822158009698915 253867414475733237014548373)
        ·
          refine ⟨11900035053549995485056955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 253867414475733237014548373 11900035053549995485056955)
          ·
            refine ⟨17850052580324993227585433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11900035053549995485056955 17850052580324993227585433)
            ·
              refine ⟨13387539435243744920689075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17850052580324993227585433 13387539435243744920689075)
              ·
                refine ⟨20081309152865617381033613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13387539435243744920689075 20081309152865617381033613)
                ·
                  refine ⟨7530490932324606517887605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20081309152865617381033613 7530490932324606517887605)
                  ·
                    refine ⟨705983524905431861051963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7530490932324606517887605 705983524905431861051963)
                    ·
                      rfl

theorem cell22_2062347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 5].length) (baseStart_2062347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062347 prefixEnd_2062347 := by exact prefixLift 2062347
  have htrace : WordTrace (prefixWord ++ tailWord_2062347) baseStart_2062347 baseEnd_2062347 := by
    simpa [prefixWord, tailWord_2062347, baseEnd_2062347] using wordTrace_append hprefix tailTrace_2062347
  have hstable : (prefixWord ++ tailWord_2062347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062347).length < 2 ^ (prefixWord ++ tailWord_2062347).sum := by decide
  have hdescent : baseEnd_2062347 < baseStart_2062347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062439 : List Nat := [1, 1, 5, 1, 1, 2, 1, 5, 5]
def baseStart_2062439 : Nat := 118140960795 + 2062439 * 2 ^ 59
def prefixEnd_2062439 : Nat := 4983230072969 + 3 ^ 40 * 2062439 * 2
def baseEnd_2062439 : Nat := 235338339461858095917227

theorem tailTrace_2062439 : CollatzResearch.WordTrace tailWord_2062439 prefixEnd_2062439 235338339461858095917227 := by
  unfold tailWord_2062439
  simp only [CollatzResearch.WordTrace]
  refine ⟨75223330175143214383326371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50148886783428809588884247 75223330175143214383326371)
  ·
    refine ⟨112834995262714821574989557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75223330175143214383326371 112834995262714821574989557)
    ·
      refine ⟨10578280805879514522655271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112834995262714821574989557 10578280805879514522655271)
      ·
        refine ⟨15867421208819271783982907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10578280805879514522655271 15867421208819271783982907)
        ·
          refine ⟨23801131813228907675974361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15867421208819271783982907 23801131813228907675974361)
          ·
            refine ⟨17850848859921680756980771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23801131813228907675974361 17850848859921680756980771)
            ·
              refine ⟨26776273289882521135471157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17850848859921680756980771 26776273289882521135471157)
              ·
                refine ⟨2510275620926486356450421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26776273289882521135471157 2510275620926486356450421)
                ·
                  refine ⟨235338339461858095917227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2510275620926486356450421 235338339461858095917227)
                  ·
                    rfl

theorem cell22_2062439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 5].length) (baseStart_2062439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062439 prefixEnd_2062439 := by exact prefixLift 2062439
  have htrace : WordTrace (prefixWord ++ tailWord_2062439) baseStart_2062439 baseEnd_2062439 := by
    simpa [prefixWord, tailWord_2062439, baseEnd_2062439] using wordTrace_append hprefix tailTrace_2062439
  have hstable : (prefixWord ++ tailWord_2062439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062439).length < 2 ^ (prefixWord ++ tailWord_2062439).sum := by decide
  have hdescent : baseEnd_2062439 < baseStart_2062439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062514 : List Nat := [3, 2, 1, 1, 1, 3, 1, 3, 1, 6]
def baseStart_2062514 : Nat := 118140960795 + 2062514 * 2 ^ 59
def prefixEnd_2062514 : Nat := 4983230072969 + 3 ^ 40 * 2062514 * 2
def baseEnd_2062514 : Nat := 706040692418299092126451

theorem tailTrace_2062514 : CollatzResearch.WordTrace tailWord_2062514 prefixEnd_2062514 706040692418299092126451 := by
  unfold tailWord_2062514
  simp only [CollatzResearch.WordTrace]
  refine ⟨18806516412467875548076649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50150710433247668128204397 18806516412467875548076649)
  ·
    refine ⟨14104887309350906661057487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18806516412467875548076649 14104887309350906661057487)
    ·
      refine ⟨21157330964026359991586231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14104887309350906661057487 21157330964026359991586231)
      ·
        refine ⟨31735996446039539987379347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21157330964026359991586231 31735996446039539987379347)
        ·
          refine ⟨47603994669059309981069021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31735996446039539987379347 47603994669059309981069021)
          ·
            refine ⟨17851498000897241242900883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47603994669059309981069021 17851498000897241242900883)
            ·
              refine ⟨26777247001345861864351325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17851498000897241242900883 26777247001345861864351325)
              ·
                refine ⟨10041467625504698199131747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26777247001345861864351325 10041467625504698199131747)
                ·
                  refine ⟨15062201438257047298697621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10041467625504698199131747 15062201438257047298697621)
                  ·
                    refine ⟨706040692418299092126451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15062201438257047298697621 706040692418299092126451)
                    ·
                      rfl

theorem cell22_2062514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_2062514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062514 prefixEnd_2062514 := by exact prefixLift 2062514
  have htrace : WordTrace (prefixWord ++ tailWord_2062514) baseStart_2062514 baseEnd_2062514 := by
    simpa [prefixWord, tailWord_2062514, baseEnd_2062514] using wordTrace_append hprefix tailTrace_2062514
  have hstable : (prefixWord ++ tailWord_2062514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062514).length < 2 ^ (prefixWord ++ tailWord_2062514).sum := by decide
  have hdescent : baseEnd_2062514 < baseStart_2062514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062546 : List Nat := [3, 2, 2, 2, 1, 3, 2, 7]
def baseStart_2062546 : Nat := 118140960795 + 2062546 * 2 ^ 59
def prefixEnd_2062546 : Nat := 4983230072969 + 3 ^ 40 * 2062546 * 2
def baseEnd_2062546 : Nat := 78450182963584630591817

theorem tailTrace_2062546 : CollatzResearch.WordTrace tailWord_2062546 prefixEnd_2062546 78450182963584630591817 := by
  unfold tailWord_2062546
  simp only [CollatzResearch.WordTrace]
  refine ⟨18806808196438892914367873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50151488523837047771647661 18806808196438892914367873)
  ·
    refine ⟨14105106147329169685775905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18806808196438892914367873 14105106147329169685775905)
    ·
      refine ⟨10578829610496877264331929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14105106147329169685775905 10578829610496877264331929)
      ·
        refine ⟨7934122207872657948248947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10578829610496877264331929 7934122207872657948248947)
        ·
          refine ⟨11901183311808986922373421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7934122207872657948248947 11901183311808986922373421)
          ·
            refine ⟨4462943741928370095890033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11901183311808986922373421 4462943741928370095890033)
            ·
              refine ⟨3347207806446277571917525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4462943741928370095890033 3347207806446277571917525)
              ·
                refine ⟨78450182963584630591817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3347207806446277571917525 78450182963584630591817)
                ·
                  rfl

theorem cell22_2062546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 7].length) (baseStart_2062546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062546 prefixEnd_2062546 := by exact prefixLift 2062546
  have htrace : WordTrace (prefixWord ++ tailWord_2062546) baseStart_2062546 baseEnd_2062546 := by
    simpa [prefixWord, tailWord_2062546, baseEnd_2062546] using wordTrace_append hprefix tailTrace_2062546
  have hstable : (prefixWord ++ tailWord_2062546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062546).length < 2 ^ (prefixWord ++ tailWord_2062546).sum := by decide
  have hdescent : baseEnd_2062546 < baseStart_2062546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062561 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 5, 3]
def baseStart_2062561 : Nat := 118140960795 + 2062561 * 2 ^ 59
def prefixEnd_2062561 : Nat := 4983230072969 + 3 ^ 40 * 2062561 * 2
def baseEnd_2062561 : Nat := 706056781478806636201307

theorem tailTrace_2062561 : CollatzResearch.WordTrace tailWord_2062561 prefixEnd_2062561 706056781478806636201307 := by
  unfold tailWord_2062561
  simp only [CollatzResearch.WordTrace]
  refine ⟨75227779880701229219267537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50151853253800819479511691 75227779880701229219267537)
  ·
    refine ⟨56420834910525921914450653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75227779880701229219267537 56420834910525921914450653)
    ·
      refine ⟨21157813091447220717918995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56420834910525921914450653 21157813091447220717918995)
      ·
        refine ⟨31736719637170831076878493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21157813091447220717918995 31736719637170831076878493)
        ·
          refine ⟨11901269863939061653829435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31736719637170831076878493 11901269863939061653829435)
          ·
            refine ⟨17851904795908592480744153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11901269863939061653829435 17851904795908592480744153)
            ·
              refine ⟨13388928596931444360558115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17851904795908592480744153 13388928596931444360558115)
              ·
                refine ⟨20083392895397166540837173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13388928596931444360558115 20083392895397166540837173)
                ·
                  refine ⟨1882818083943484363203485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20083392895397166540837173 1882818083943484363203485)
                  ·
                    refine ⟨706056781478806636201307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1882818083943484363203485 706056781478806636201307)
                    ·
                      rfl

theorem cell22_2062561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_2062561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062561 prefixEnd_2062561 := by exact prefixLift 2062561
  have htrace : WordTrace (prefixWord ++ tailWord_2062561) baseStart_2062561 baseEnd_2062561 := by
    simpa [prefixWord, tailWord_2062561, baseEnd_2062561] using wordTrace_append hprefix tailTrace_2062561
  have hstable : (prefixWord ++ tailWord_2062561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062561).length < 2 ^ (prefixWord ++ tailWord_2062561).sum := by decide
  have hdescent : baseEnd_2062561 < baseStart_2062561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062589 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 3, 7]
def baseStart_2062589 : Nat := 118140960795 + 2062589 * 2 ^ 59
def prefixEnd_2062589 : Nat := 4983230072969 + 3 ^ 40 * 2062589 * 2
def baseEnd_2062589 : Nat := 706066366451023896501221

theorem tailTrace_2062589 : CollatzResearch.WordTrace tailWord_2062589 prefixEnd_2062589 706066366451023896501221 := by
  unfold tailWord_2062589
  simp only [CollatzResearch.WordTrace]
  refine ⟨75228801124599790001286821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50152534083066526667524547 75228801124599790001286821)
  ·
    refine ⟨14105400210862460625241279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75228801124599790001286821 14105400210862460625241279)
    ·
      refine ⟨21158100316293690937861919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14105400210862460625241279 21158100316293690937861919)
      ·
        refine ⟨31737150474440536406792879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21158100316293690937861919 31737150474440536406792879)
        ·
          refine ⟨47605725711660804610189319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31737150474440536406792879 47605725711660804610189319)
          ·
            refine ⟨71408588567491206915283979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47605725711660804610189319 71408588567491206915283979)
            ·
              refine ⟨107112882851236810372925969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71408588567491206915283979 107112882851236810372925969)
              ·
                refine ⟨80334662138427607779694477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107112882851236810372925969 80334662138427607779694477)
                ·
                  refine ⟨30125498301910352917385429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80334662138427607779694477 30125498301910352917385429)
                  ·
                    refine ⟨706066366451023896501221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30125498301910352917385429 706066366451023896501221)
                    ·
                      rfl

theorem cell22_2062589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_2062589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062589 prefixEnd_2062589 := by exact prefixLift 2062589
  have htrace : WordTrace (prefixWord ++ tailWord_2062589) baseStart_2062589 baseEnd_2062589 := by
    simpa [prefixWord, tailWord_2062589, baseEnd_2062589] using wordTrace_append hprefix tailTrace_2062589
  have hstable : (prefixWord ++ tailWord_2062589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062589).length < 2 ^ (prefixWord ++ tailWord_2062589).sum := by decide
  have hdescent : baseEnd_2062589 < baseStart_2062589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062591 : List Nat := [1, 1, 2, 2, 1, 4, 4, 2, 5]
def baseStart_2062591 : Nat := 118140960795 + 2062591 * 2 ^ 59
def prefixEnd_2062591 : Nat := 4983230072969 + 3 ^ 40 * 2062591 * 2
def baseEnd_2062591 : Nat := 235355683697298852650405

theorem tailTrace_2062591 : CollatzResearch.WordTrace tailWord_2062591 prefixEnd_2062591 235355683697298852650405 := by
  unfold tailWord_2062591
  simp only [CollatzResearch.WordTrace]
  refine ⟨75228874070592544342859627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50152582713728362895239751 75228874070592544342859627)
  ·
    refine ⟨112843311105888816514289441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75228874070592544342859627 112843311105888816514289441)
    ·
      refine ⟨84632483329416612385717081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112843311105888816514289441 84632483329416612385717081)
      ·
        refine ⟨63474362497062459289287811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84632483329416612385717081 63474362497062459289287811)
        ·
          refine ⟨95211543745593688933931717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63474362497062459289287811 95211543745593688933931717)
          ·
            refine ⟨17852164452298816675112197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95211543745593688933931717 17852164452298816675112197)
            ·
              refine ⟨3347280834806028126583537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17852164452298816675112197 3347280834806028126583537)
              ·
                refine ⟨2510460626104521094937653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3347280834806028126583537 2510460626104521094937653)
                ·
                  refine ⟨235355683697298852650405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2510460626104521094937653 235355683697298852650405)
                  ·
                    rfl

theorem cell22_2062591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 5].length) (baseStart_2062591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062591 prefixEnd_2062591 := by exact prefixLift 2062591
  have htrace : WordTrace (prefixWord ++ tailWord_2062591) baseStart_2062591 baseEnd_2062591 := by
    simpa [prefixWord, tailWord_2062591, baseEnd_2062591] using wordTrace_append hprefix tailTrace_2062591
  have hstable : (prefixWord ++ tailWord_2062591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062591).length < 2 ^ (prefixWord ++ tailWord_2062591).sum := by decide
  have hdescent : baseEnd_2062591 < baseStart_2062591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062606 : List Nat := [4, 1, 1, 2, 1, 2, 3, 1, 2, 5]
def baseStart_2062606 : Nat := 118140960795 + 2062606 * 2 ^ 59
def prefixEnd_2062606 : Nat := 4983230072969 + 3 ^ 40 * 2062606 * 2
def baseEnd_2062606 : Nat := 706072185898441518826169

theorem tailTrace_2062606 : CollatzResearch.WordTrace tailWord_2062606 prefixEnd_2062606 706072185898441518826169 := by
  unfold tailWord_2062606
  simp only [CollatzResearch.WordTrace]
  refine ⟨9403677645692275238081959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50152947443692134603103781 9403677645692275238081959)
  ·
    refine ⟨14105516468538412857122939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9403677645692275238081959 14105516468538412857122939)
    ·
      refine ⟨21158274702807619285684409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14105516468538412857122939 21158274702807619285684409)
      ·
        refine ⟨15868706027105714464263307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21158274702807619285684409 15868706027105714464263307)
        ·
          refine ⟨23803059040658571696394961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15868706027105714464263307 23803059040658571696394961)
          ·
            refine ⟨17852294280493928772296221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23803059040658571696394961 17852294280493928772296221)
            ·
              refine ⟨6694610355185223289611083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17852294280493928772296221 6694610355185223289611083)
              ·
                refine ⟨10041915532777834934416625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6694610355185223289611083 10041915532777834934416625)
                ·
                  refine ⟨7531436649583376200812469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10041915532777834934416625 7531436649583376200812469)
                  ·
                    refine ⟨706072185898441518826169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7531436649583376200812469 706072185898441518826169)
                    ·
                      rfl

theorem cell22_2062606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_2062606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062606 prefixEnd_2062606 := by exact prefixLift 2062606
  have htrace : WordTrace (prefixWord ++ tailWord_2062606) baseStart_2062606 baseEnd_2062606 := by
    simpa [prefixWord, tailWord_2062606, baseEnd_2062606] using wordTrace_append hprefix tailTrace_2062606
  have hstable : (prefixWord ++ tailWord_2062606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062606).length < 2 ^ (prefixWord ++ tailWord_2062606).sum := by decide
  have hdescent : baseEnd_2062606 < baseStart_2062606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062619 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 8]
def baseStart_2062619 : Nat := 118140960795 + 2062619 * 2 ^ 59
def prefixEnd_2062619 : Nat := 4983230072969 + 3 ^ 40 * 2062619 * 2
def baseEnd_2062619 : Nat := 235358878688037939417043

theorem tailTrace_2062619 : CollatzResearch.WordTrace tailWord_2062619 prefixEnd_2062619 235358878688037939417043 := by
  unfold tailWord_2062619
  simp only [CollatzResearch.WordTrace]
  refine ⟨75229895314491105124878911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50153263542994070083252607 75229895314491105124878911)
  ·
    refine ⟨112844842971736657687318367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75229895314491105124878911 112844842971736657687318367)
    ·
      refine ⟨169267264457604986530977551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112844842971736657687318367 169267264457604986530977551)
      ·
        refine ⟨253900896686407479796466327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169267264457604986530977551 253900896686407479796466327)
        ·
          refine ⟨380851345029611219694699491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253900896686407479796466327 380851345029611219694699491)
          ·
            refine ⟨571277017544416829542049237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380851345029611219694699491 571277017544416829542049237)
            ·
              refine ⟨13389305098697269442391779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 571277017544416829542049237 13389305098697269442391779)
              ·
                refine ⟨20083957648045904163587669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13389305098697269442391779 20083957648045904163587669)
                ·
                  refine ⟨235358878688037939417043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20083957648045904163587669 235358878688037939417043)
                  ·
                    rfl

theorem cell22_2062619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 8].length) (baseStart_2062619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062619 prefixEnd_2062619 := by exact prefixLift 2062619
  have htrace : WordTrace (prefixWord ++ tailWord_2062619) baseStart_2062619 baseEnd_2062619 := by
    simpa [prefixWord, tailWord_2062619, baseEnd_2062619] using wordTrace_append hprefix tailTrace_2062619
  have hstable : (prefixWord ++ tailWord_2062619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062619).length < 2 ^ (prefixWord ++ tailWord_2062619).sum := by decide
  have hdescent : baseEnd_2062619 < baseStart_2062619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062698 : List Nat := [3, 1, 3, 3, 1, 3, 8]
def baseStart_2062698 : Nat := 118140960795 + 2062698 * 2 ^ 59
def prefixEnd_2062698 : Nat := 4983230072969 + 3 ^ 40 * 2062698 * 2
def baseEnd_2062698 : Nat := 26151988125132738723181

theorem tailTrace_2062698 : CollatzResearch.WordTrace tailWord_2062698 prefixEnd_2062698 26151988125132738723181 := by
  unfold tailWord_2062698
  simp only [CollatzResearch.WordTrace]
  refine ⟨18808194170301225404251187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50155184454136601078003165 18808194170301225404251187)
  ·
    refine ⟨28212291255451838106376781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18808194170301225404251187 28212291255451838106376781)
    ·
      refine ⟨10579609220794439289891293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28212291255451838106376781 10579609220794439289891293)
      ·
        refine ⟨3967353457797914733709235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10579609220794439289891293 3967353457797914733709235)
        ·
          refine ⟨5951030186696872100563853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3967353457797914733709235 5951030186696872100563853)
          ·
            refine ⟨2231636320011327037711445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5951030186696872100563853 2231636320011327037711445)
            ·
              refine ⟨26151988125132738723181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2231636320011327037711445 26151988125132738723181)
              ·
                rfl

theorem cell22_2062698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 8].length) (baseStart_2062698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062698 prefixEnd_2062698 := by exact prefixLift 2062698
  have htrace : WordTrace (prefixWord ++ tailWord_2062698) baseStart_2062698 baseEnd_2062698 := by
    simpa [prefixWord, tailWord_2062698, baseEnd_2062698] using wordTrace_append hprefix tailTrace_2062698
  have hstable : (prefixWord ++ tailWord_2062698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062698).length < 2 ^ (prefixWord ++ tailWord_2062698).sum := by decide
  have hdescent : baseEnd_2062698 < baseStart_2062698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062741 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 4, 5]
def baseStart_2062741 : Nat := 118140960795 + 2062741 * 2 ^ 59
def prefixEnd_2062741 : Nat := 4983230072969 + 3 ^ 40 * 2062741 * 2
def baseEnd_2062741 : Nat := 706118399157346166700755

theorem tailTrace_2062741 : CollatzResearch.WordTrace tailWord_2062741 prefixEnd_2062741 706118399157346166700755 := by
  unfold tailWord_2062741
  simp only [CollatzResearch.WordTrace]
  refine ⟨75234345020049119960820077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50156230013366079973880051 75234345020049119960820077)
  ·
    refine ⟨28212879382518419985307529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75234345020049119960820077 28212879382518419985307529)
    ·
      refine ⟨21159659536888814988980647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28212879382518419985307529 21159659536888814988980647)
      ·
        refine ⟨31739489305333222483470971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21159659536888814988980647 31739489305333222483470971)
        ·
          refine ⟨47609233957999833725206457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31739489305333222483470971 47609233957999833725206457)
          ·
            refine ⟨35706925468499875293904843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47609233957999833725206457 35706925468499875293904843)
            ·
              refine ⟨53560388202749812940857265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35706925468499875293904843 53560388202749812940857265)
              ·
                refine ⟨40170291152062359705642949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53560388202749812940857265 40170291152062359705642949)
                ·
                  refine ⟨7531929591011692444808053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40170291152062359705642949 7531929591011692444808053)
                  ·
                    refine ⟨706118399157346166700755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7531929591011692444808053 706118399157346166700755)
                    ·
                      rfl

theorem cell22_2062741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_2062741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062741 prefixEnd_2062741 := by exact prefixLift 2062741
  have htrace : WordTrace (prefixWord ++ tailWord_2062741) baseStart_2062741 baseEnd_2062741 := by
    simpa [prefixWord, tailWord_2062741, baseEnd_2062741] using wordTrace_append hprefix tailTrace_2062741
  have hstable : (prefixWord ++ tailWord_2062741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062741).length < 2 ^ (prefixWord ++ tailWord_2062741).sum := by decide
  have hdescent : baseEnd_2062741 < baseStart_2062741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062760 : List Nat := [2, 1, 6, 1, 1, 1, 1, 4, 5]
def baseStart_2062760 : Nat := 118140960795 + 2062760 * 2 ^ 59
def prefixEnd_2062760 : Nat := 4983230072969 + 3 ^ 40 * 2062760 * 2
def baseEnd_2062760 : Nat := 235374967748545483491899

theorem tailTrace_2062760 : CollatzResearch.WordTrace tailWord_2062760 prefixEnd_2062760 235374967748545483491899 := by
  unfold tailWord_2062760
  simp only [CollatzResearch.WordTrace]
  refine ⟨37617519003490143102880867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50156692004653524137174489 37617519003490143102880867)
  ·
    refine ⟨56426278505235214654321301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37617519003490143102880867 56426278505235214654321301)
    ·
      refine ⟨2644981804932900686921311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56426278505235214654321301 2644981804932900686921311)
      ·
        refine ⟨3967472707399351030381967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2644981804932900686921311 3967472707399351030381967)
        ·
          refine ⟨5951209061099026545572951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3967472707399351030381967 5951209061099026545572951)
          ·
            refine ⟨8926813591648539818359427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5951209061099026545572951 8926813591648539818359427)
            ·
              refine ⟨13390220387472809727539141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8926813591648539818359427 13390220387472809727539141)
              ·
                refine ⟨2510666322651151823913589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13390220387472809727539141 2510666322651151823913589)
                ·
                  refine ⟨235374967748545483491899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2510666322651151823913589 235374967748545483491899)
                  ·
                    rfl

theorem cell22_2062760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 5].length) (baseStart_2062760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062760 prefixEnd_2062760 := by exact prefixLift 2062760
  have htrace : WordTrace (prefixWord ++ tailWord_2062760) baseStart_2062760 baseEnd_2062760 := by
    simpa [prefixWord, tailWord_2062760, baseEnd_2062760] using wordTrace_append hprefix tailTrace_2062760
  have hstable : (prefixWord ++ tailWord_2062760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062760).length < 2 ^ (prefixWord ++ tailWord_2062760).sum := by decide
  have hdescent : baseEnd_2062760 < baseStart_2062760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062805 : List Nat := [1, 3, 2, 3, 1, 2, 1, 5, 4]
def baseStart_2062805 : Nat := 118140960795 + 2062805 * 2 ^ 59
def prefixEnd_2062805 : Nat := 4983230072969 + 3 ^ 40 * 2062805 * 2
def baseEnd_2062805 : Nat := 235380102555090444366853

theorem tailTrace_2062805 : CollatzResearch.WordTrace tailWord_2062805 prefixEnd_2062805 235380102555090444366853 := by
  unfold tailWord_2062805
  simp only [CollatzResearch.WordTrace]
  refine ⟨75236679291817258891149869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50157786194544839260766579 75236679291817258891149869)
  ·
    refine ⟨28213754734431472084181201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75236679291817258891149869 28213754734431472084181201)
    ·
      refine ⟨21160316050823604063135901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28213754734431472084181201 21160316050823604063135901)
      ·
        refine ⟨7935118519058851523675963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21160316050823604063135901 7935118519058851523675963)
        ·
          refine ⟨11902677778588277285513945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7935118519058851523675963 11902677778588277285513945)
          ·
            refine ⟨8927008333941207964135459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11902677778588277285513945 8927008333941207964135459)
            ·
              refine ⟨13390512500911811946203189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8927008333941207964135459 13390512500911811946203189)
              ·
                refine ⟨1255360546960482369956549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13390512500911811946203189 1255360546960482369956549)
                ·
                  refine ⟨235380102555090444366853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1255360546960482369956549 235380102555090444366853)
                  ·
                    rfl

theorem cell22_2062805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5, 4].length) (baseStart_2062805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062805 prefixEnd_2062805 := by exact prefixLift 2062805
  have htrace : WordTrace (prefixWord ++ tailWord_2062805) baseStart_2062805 baseEnd_2062805 := by
    simpa [prefixWord, tailWord_2062805, baseEnd_2062805] using wordTrace_append hprefix tailTrace_2062805
  have hstable : (prefixWord ++ tailWord_2062805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062805).length < 2 ^ (prefixWord ++ tailWord_2062805).sum := by decide
  have hdescent : baseEnd_2062805 < baseStart_2062805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062816 : List Nat := [2, 1, 1, 3, 1, 1, 13]
def baseStart_2062816 : Nat := 118140960795 + 2062816 * 2 ^ 59
def prefixEnd_2062816 : Nat := 4983230072969 + 3 ^ 40 * 2062816 * 2
def baseEnd_2062816 : Nat := 26153484192224850780575

theorem tailTrace_2062816 : CollatzResearch.WordTrace tailWord_2062816 prefixEnd_2062816 26153484192224850780575 := by
  unfold tailWord_2062816
  simp only [CollatzResearch.WordTrace]
  refine ⟨37618540247388703884900151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50158053663184938513200201 37618540247388703884900151)
  ·
    refine ⟨56427810371083055827350227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37618540247388703884900151 56427810371083055827350227)
    ·
      refine ⟨84641715556624583741025341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56427810371083055827350227 84641715556624583741025341)
      ·
        refine ⟨31740643333734218902884503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84641715556624583741025341 31740643333734218902884503)
        ·
          refine ⟨47610965000601328354326755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31740643333734218902884503 47610965000601328354326755)
          ·
            refine ⟨71416447500901992531490133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47610965000601328354326755 71416447500901992531490133)
            ·
              refine ⟨26153484192224850780575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 71416447500901992531490133 26153484192224850780575)
              ·
                rfl

theorem cell22_2062816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 13].length) (baseStart_2062816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062816 prefixEnd_2062816 := by exact prefixLift 2062816
  have htrace : WordTrace (prefixWord ++ tailWord_2062816) baseStart_2062816 baseEnd_2062816 := by
    simpa [prefixWord, tailWord_2062816, baseEnd_2062816] using wordTrace_append hprefix tailTrace_2062816
  have hstable : (prefixWord ++ tailWord_2062816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062816).length < 2 ^ (prefixWord ++ tailWord_2062816).sum := by decide
  have hdescent : baseEnd_2062816 < baseStart_2062816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062953 : List Nat := [1, 2, 1, 1, 1, 4, 1, 4, 1, 6]
def baseStart_2062953 : Nat := 118140960795 + 2062953 * 2 ^ 59
def prefixEnd_2062953 : Nat := 4983230072969 + 3 ^ 40 * 2062953 * 2
def baseEnd_2062953 : Nat := 706190971089848280400105

theorem tailTrace_2062953 : CollatzResearch.WordTrace tailWord_2062953 prefixEnd_2062953 706190971089848280400105 := by
  unfold tailWord_2062953
  simp only [CollatzResearch.WordTrace]
  refine ⟨75242077295281080167537513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50161384863520720111691675 75242077295281080167537513)
  ·
    refine ⟨56431557971460810125653135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75242077295281080167537513 56431557971460810125653135)
    ·
      refine ⟨84647336957191215188479703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56431557971460810125653135 84647336957191215188479703)
      ·
        refine ⟨126971005435786822782719555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84647336957191215188479703 126971005435786822782719555)
        ·
          refine ⟨190456508153680234174079333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126971005435786822782719555 190456508153680234174079333)
          ·
            refine ⟨35710595278815043907639875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190456508153680234174079333 35710595278815043907639875)
            ·
              refine ⟨53565892918222565861459813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35710595278815043907639875 53565892918222565861459813)
              ·
                refine ⟨10043604922166731099023715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53565892918222565861459813 10043604922166731099023715)
                ·
                  refine ⟨15065407383250096648535573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10043604922166731099023715 15065407383250096648535573)
                  ·
                    refine ⟨706190971089848280400105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15065407383250096648535573 706190971089848280400105)
                    ·
                      rfl

theorem cell22_2062953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 6].length) (baseStart_2062953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2062953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2062953 prefixEnd_2062953 := by exact prefixLift 2062953
  have htrace : WordTrace (prefixWord ++ tailWord_2062953) baseStart_2062953 baseEnd_2062953 := by
    simpa [prefixWord, tailWord_2062953, baseEnd_2062953] using wordTrace_append hprefix tailTrace_2062953
  have hstable : (prefixWord ++ tailWord_2062953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062953).length < 2 ^ (prefixWord ++ tailWord_2062953).sum := by decide
  have hdescent : baseEnd_2062953 < baseStart_2062953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063006 : List Nat := [4, 3, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_2063006 : Nat := 118140960795 + 2063006 * 2 ^ 59
def prefixEnd_2063006 : Nat := 4983230072969 + 3 ^ 40 * 2063006 * 2
def baseEnd_2063006 : Nat := 706209114072973808824943

theorem tailTrace_2063006 : CollatzResearch.WordTrace tailWord_2063006 prefixEnd_2063006 706209114072973808824943 := by
  unfold tailWord_2063006
  simp only [CollatzResearch.WordTrace]
  refine ⟨9405501295511133777402109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50162673576059380146144581 9405501295511133777402109)
  ·
    refine ⟨3527062985816675166525791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9405501295511133777402109 3527062985816675166525791)
    ·
      refine ⟨5290594478725012749788687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3527062985816675166525791 5290594478725012749788687)
      ·
        refine ⟨7935891718087519124683031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5290594478725012749788687 7935891718087519124683031)
        ·
          refine ⟨11903837577131278687024547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7935891718087519124683031 11903837577131278687024547)
          ·
            refine ⟨17855756365696918030536821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11903837577131278687024547 17855756365696918030536821)
            ·
              refine ⟨1673977159284086065362827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17855756365696918030536821 1673977159284086065362827)
              ·
                refine ⟨2510965738926129098044241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1673977159284086065362827 2510965738926129098044241)
                ·
                  refine ⟨1883224304194596823533181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2510965738926129098044241 1883224304194596823533181)
                  ·
                    refine ⟨706209114072973808824943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1883224304194596823533181 706209114072973808824943)
                    ·
                      rfl

theorem cell22_2063006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_2063006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063006 prefixEnd_2063006 := by exact prefixLift 2063006
  have htrace : WordTrace (prefixWord ++ tailWord_2063006) baseStart_2063006 baseEnd_2063006 := by
    simpa [prefixWord, tailWord_2063006, baseEnd_2063006] using wordTrace_append hprefix tailTrace_2063006
  have hstable : (prefixWord ++ tailWord_2063006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063006).length < 2 ^ (prefixWord ++ tailWord_2063006).sum := by decide
  have hdescent : baseEnd_2063006 < baseStart_2063006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063064 : List Nat := [2, 1, 2, 2, 3, 4, 2, 1, 5]
def baseStart_2063064 : Nat := 118140960795 + 2063064 * 2 ^ 59
def prefixEnd_2063064 : Nat := 4983230072969 + 3 ^ 40 * 2063064 * 2
def baseEnd_2063064 : Nat := 235409656219426996958255

theorem tailTrace_2063064 : CollatzResearch.WordTrace tailWord_2063064 prefixEnd_2063064 235409656219426996958255 := by
  unfold tailWord_2063064
  simp only [CollatzResearch.WordTrace]
  refine ⟨37623062898939473062414123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50164083865252630749885497 37623062898939473062414123)
  ·
    refine ⟨56434594348409209593621185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37623062898939473062414123 56434594348409209593621185)
    ·
      refine ⟨42325945761306907195215889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56434594348409209593621185 42325945761306907195215889)
      ·
        refine ⟨31744459320980180396411917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42325945761306907195215889 31744459320980180396411917)
        ·
          refine ⟨11904172245367567648654469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31744459320980180396411917 11904172245367567648654469)
          ·
            refine ⟨2232032296006418934122713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11904172245367567648654469 2232032296006418934122713)
            ·
              refine ⟨1674024222004814200592035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2232032296006418934122713 1674024222004814200592035)
              ·
                refine ⟨2511036333007221300888053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1674024222004814200592035 2511036333007221300888053)
                ·
                  refine ⟨235409656219426996958255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2511036333007221300888053 235409656219426996958255)
                  ·
                    rfl

theorem cell22_2063064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 1, 5].length) (baseStart_2063064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063064 prefixEnd_2063064 := by exact prefixLift 2063064
  have htrace : WordTrace (prefixWord ++ tailWord_2063064) baseStart_2063064 baseEnd_2063064 := by
    simpa [prefixWord, tailWord_2063064, baseEnd_2063064] using wordTrace_append hprefix tailTrace_2063064
  have hstable : (prefixWord ++ tailWord_2063064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063064).length < 2 ^ (prefixWord ++ tailWord_2063064).sum := by decide
  have hdescent : baseEnd_2063064 < baseStart_2063064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063077 : List Nat := [1, 3, 1, 4, 1, 3, 1, 1, 3, 4]
def baseStart_2063077 : Nat := 118140960795 + 2063077 * 2 ^ 59
def prefixEnd_2063077 : Nat := 4983230072969 + 3 ^ 40 * 2063077 * 2
def baseEnd_2063077 : Nat := 706233418823953290299725

theorem tailTrace_2063077 : CollatzResearch.WordTrace tailWord_2063077 prefixEnd_2063077 706233418823953290299725 := by
  unfold tailWord_2063077
  simp only [CollatzResearch.WordTrace]
  refine ⟨75246599946831849345051485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50164399964554566230034323 75246599946831849345051485)
  ·
    refine ⟨28217474980061943504394307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75246599946831849345051485 28217474980061943504394307)
    ·
      refine ⟨42326212470092915256591461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28217474980061943504394307 42326212470092915256591461)
      ·
        refine ⟨7936164838142421610610899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42326212470092915256591461 7936164838142421610610899)
        ·
          refine ⟨11904247257213632415916349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7936164838142421610610899 11904247257213632415916349)
          ·
            refine ⟨4464092721455112155968631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11904247257213632415916349 4464092721455112155968631)
            ·
              refine ⟨6696139082182668233952947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4464092721455112155968631 6696139082182668233952947)
              ·
                refine ⟨10044208623274002350929421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6696139082182668233952947 10044208623274002350929421)
                ·
                  refine ⟨3766578233727750881598533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10044208623274002350929421 3766578233727750881598533)
                  ·
                    refine ⟨706233418823953290299725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3766578233727750881598533 706233418823953290299725)
                    ·
                      rfl

theorem cell22_2063077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_2063077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063077 prefixEnd_2063077 := by exact prefixLift 2063077
  have htrace : WordTrace (prefixWord ++ tailWord_2063077) baseStart_2063077 baseEnd_2063077 := by
    simpa [prefixWord, tailWord_2063077, baseEnd_2063077] using wordTrace_append hprefix tailTrace_2063077
  have hstable : (prefixWord ++ tailWord_2063077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063077).length < 2 ^ (prefixWord ++ tailWord_2063077).sum := by decide
  have hdescent : baseEnd_2063077 < baseStart_2063077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063105 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 3, 6]
def baseStart_2063105 : Nat := 118140960795 + 2063105 * 2 ^ 59
def prefixEnd_2063105 : Nat := 4983230072969 + 3 ^ 40 * 2063105 * 2
def baseEnd_2063105 : Nat := 706243003796170550599639

theorem tailTrace_2063105 : CollatzResearch.WordTrace tailWord_2063105 prefixEnd_2063105 706243003796170550599639 := by
  unfold tailWord_2063105
  simp only [CollatzResearch.WordTrace]
  refine ⟨75247621190730410127070769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50165080793820273418047179 75247621190730410127070769)
  ·
    refine ⟨56435715893047807595303077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75247621190730410127070769 56435715893047807595303077)
    ·
      refine ⟨10581696729946463924119327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56435715893047807595303077 10581696729946463924119327)
      ·
        refine ⟨15872545094919695886178991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10581696729946463924119327 15872545094919695886178991)
        ·
          refine ⟨23808817642379543829268487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15872545094919695886178991 23808817642379543829268487)
          ·
            refine ⟨35713226463569315743902731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23808817642379543829268487 35713226463569315743902731)
            ·
              refine ⟨53569839695353973615854097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35713226463569315743902731 53569839695353973615854097)
              ·
                refine ⟨40177379771515480211890573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53569839695353973615854097 40177379771515480211890573)
                ·
                  refine ⟨15066517414318305079458965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40177379771515480211890573 15066517414318305079458965)
                  ·
                    refine ⟨706243003796170550599639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15066517414318305079458965 706243003796170550599639)
                    ·
                      rfl

theorem cell22_2063105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_2063105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063105 prefixEnd_2063105 := by exact prefixLift 2063105
  have htrace : WordTrace (prefixWord ++ tailWord_2063105) baseStart_2063105 baseEnd_2063105 := by
    simpa [prefixWord, tailWord_2063105, baseEnd_2063105] using wordTrace_append hprefix tailTrace_2063105
  have hstable : (prefixWord ++ tailWord_2063105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063105).length < 2 ^ (prefixWord ++ tailWord_2063105).sum := by decide
  have hdescent : baseEnd_2063105 < baseStart_2063105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063137 : List Nat := [1, 2, 3, 2, 1, 2, 5, 6]
def baseStart_2063137 : Nat := 118140960795 + 2063137 * 2 ^ 59
def prefixEnd_2063137 : Nat := 4983230072969 + 3 ^ 40 * 2063137 * 2
def baseEnd_2063137 : Nat := 78472662005570348199949

theorem tailTrace_2063137 : CollatzResearch.WordTrace tailWord_2063137 prefixEnd_2063137 78472662005570348199949 := by
  unfold tailWord_2063137
  simp only [CollatzResearch.WordTrace]
  refine ⟨75248788326614479592235665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50165858884409653061490443 75248788326614479592235665)
  ·
    refine ⟨56436591244960859694176749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75248788326614479592235665 56436591244960859694176749)
    ·
      refine ⟨21163721716860322385316281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56436591244960859694176749 21163721716860322385316281)
      ·
        refine ⟨15872791287645241788987211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21163721716860322385316281 15872791287645241788987211)
        ·
          refine ⟨23809186931467862683480817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15872791287645241788987211 23809186931467862683480817)
          ·
            refine ⟨17856890198600897012610613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23809186931467862683480817 17856890198600897012610613)
            ·
              refine ⟨1674083456118834094932245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17856890198600897012610613 1674083456118834094932245)
              ·
                refine ⟨78472662005570348199949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1674083456118834094932245 78472662005570348199949)
                ·
                  rfl

theorem cell22_2063137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 6].length) (baseStart_2063137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063137 prefixEnd_2063137 := by exact prefixLift 2063137
  have htrace : WordTrace (prefixWord ++ tailWord_2063137) baseStart_2063137 baseEnd_2063137 := by
    simpa [prefixWord, tailWord_2063137, baseEnd_2063137] using wordTrace_append hprefix tailTrace_2063137
  have hstable : (prefixWord ++ tailWord_2063137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063137).length < 2 ^ (prefixWord ++ tailWord_2063137).sum := by decide
  have hdescent : baseEnd_2063137 < baseStart_2063137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063182 : List Nat := [4, 1, 1, 1, 1, 1, 1, 7, 5]
def baseStart_2063182 : Nat := 118140960795 + 2063182 * 2 ^ 59
def prefixEnd_2063182 : Nat := 4983230072969 + 3 ^ 40 * 2063182 * 2
def baseEnd_2063182 : Nat := 235423120823256005474801

theorem tailTrace_2063182 : CollatzResearch.WordTrace tailWord_2063182 prefixEnd_2063182 235423120823256005474801 := by
  unfold tailWord_2063182
  simp only [CollatzResearch.WordTrace]
  refine ⟨9406303701431431534702975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50166953074300968185082533 9406303701431431534702975)
  ·
    refine ⟨14109455552147147302054463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9406303701431431534702975 14109455552147147302054463)
    ·
      refine ⟨21164183328220720953081695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14109455552147147302054463 21164183328220720953081695)
      ·
        refine ⟨31746274992331081429622543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21164183328220720953081695 31746274992331081429622543)
        ·
          refine ⟨47619412488496622144433815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31746274992331081429622543 47619412488496622144433815)
          ·
            refine ⟨71429118732744933216650723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47619412488496622144433815 71429118732744933216650723)
            ·
              refine ⟨107143678099117399824976085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71429118732744933216650723 107143678099117399824976085)
              ·
                refine ⟨2511179955448064058397877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 107143678099117399824976085 2511179955448064058397877)
                ·
                  refine ⟨235423120823256005474801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2511179955448064058397877 235423120823256005474801)
                  ·
                    rfl

theorem cell22_2063182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_2063182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063182 prefixEnd_2063182 := by exact prefixLift 2063182
  have htrace : WordTrace (prefixWord ++ tailWord_2063182) baseStart_2063182 baseEnd_2063182 := by
    simpa [prefixWord, tailWord_2063182, baseEnd_2063182] using wordTrace_append hprefix tailTrace_2063182
  have hstable : (prefixWord ++ tailWord_2063182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063182).length < 2 ^ (prefixWord ++ tailWord_2063182).sum := by decide
  have hdescent : baseEnd_2063182 < baseStart_2063182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063203 : List Nat := [1, 1, 1, 5, 3, 3, 1, 3, 1, 3]
def baseStart_2063203 : Nat := 118140960795 + 2063203 * 2 ^ 59
def prefixEnd_2063203 : Nat := 4983230072969 + 3 ^ 40 * 2063203 * 2
def baseEnd_2063203 : Nat := 706276551198930961649339

theorem tailTrace_2063203 : CollatzResearch.WordTrace tailWord_2063203 prefixEnd_2063203 706276551198930961649339 := by
  unfold tailWord_2063203
  simp only [CollatzResearch.WordTrace]
  refine ⟨75251195544375372864138263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50167463696250248576092175 75251195544375372864138263)
  ·
    refine ⟨112876793316563059296207395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75251195544375372864138263 112876793316563059296207395)
    ·
      refine ⟨169315189974844588944311093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112876793316563059296207395 169315189974844588944311093)
      ·
        refine ⟨15873299060141680213529165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169315189974844588944311093 15873299060141680213529165)
        ·
          refine ⟨5952487147553130080073437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15873299060141680213529165 5952487147553130080073437)
          ·
            refine ⟨2232182680332423780027539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5952487147553130080073437 2232182680332423780027539)
            ·
              refine ⟨3348274020498635670041309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2232182680332423780027539 3348274020498635670041309)
              ·
                refine ⟨1255602757686988376265491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3348274020498635670041309 1255602757686988376265491)
                ·
                  refine ⟨1883404136530482564398237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1255602757686988376265491 1883404136530482564398237)
                  ·
                    refine ⟨706276551198930961649339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1883404136530482564398237 706276551198930961649339)
                    ·
                      rfl

theorem cell22_2063203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3, 1, 3].length) (baseStart_2063203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063203 prefixEnd_2063203 := by exact prefixLift 2063203
  have htrace : WordTrace (prefixWord ++ tailWord_2063203) baseStart_2063203 baseEnd_2063203 := by
    simpa [prefixWord, tailWord_2063203, baseEnd_2063203] using wordTrace_append hprefix tailTrace_2063203
  have hstable : (prefixWord ++ tailWord_2063203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063203).length < 2 ^ (prefixWord ++ tailWord_2063203).sum := by decide
  have hdescent : baseEnd_2063203 < baseStart_2063203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063227 : List Nat := [1, 1, 1, 1, 1, 5, 5, 1, 6]
def baseStart_2063227 : Nat := 118140960795 + 2063227 * 2 ^ 59
def prefixEnd_2063227 : Nat := 4983230072969 + 3 ^ 40 * 2063227 * 2
def baseEnd_2063227 : Nat := 235428255629800966349755

theorem tailTrace_2063227 : CollatzResearch.WordTrace tailWord_2063227 prefixEnd_2063227 235428255629800966349755 := by
  unfold tailWord_2063227
  simp only [CollatzResearch.WordTrace]
  refine ⟨75252070896288424963011935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50168047264192283308674623 75252070896288424963011935)
  ·
    refine ⟨112878106344432637444517903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75252070896288424963011935 112878106344432637444517903)
    ·
      refine ⟨169317159516648956166776855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112878106344432637444517903 169317159516648956166776855)
      ·
        refine ⟨253975739274973434250165283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169317159516648956166776855 253975739274973434250165283)
        ·
          refine ⟨380963608912460151375247925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253975739274973434250165283 380963608912460151375247925)
          ·
            refine ⟨35715338335543139191429493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 380963608912460151375247925 35715338335543139191429493)
            ·
              refine ⟨3348312968957169299196515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35715338335543139191429493 3348312968957169299196515)
              ·
                refine ⟨5022469453435753948794773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3348312968957169299196515 5022469453435753948794773)
                ·
                  refine ⟨235428255629800966349755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5022469453435753948794773 235428255629800966349755)
                  ·
                    rfl

theorem cell22_2063227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 6].length) (baseStart_2063227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063227 prefixEnd_2063227 := by exact prefixLift 2063227
  have htrace : WordTrace (prefixWord ++ tailWord_2063227) baseStart_2063227 baseEnd_2063227 := by
    simpa [prefixWord, tailWord_2063227, baseEnd_2063227] using wordTrace_append hprefix tailTrace_2063227
  have hstable : (prefixWord ++ tailWord_2063227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063227).length < 2 ^ (prefixWord ++ tailWord_2063227).sum := by decide
  have hdescent : baseEnd_2063227 < baseStart_2063227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063272 : List Nat := [2, 1, 6, 13]
def baseStart_2063272 : Nat := 118140960795 + 2063272 * 2 ^ 59
def prefixEnd_2063272 : Nat := 4983230072969 + 3 ^ 40 * 2063272 * 2
def baseEnd_2063272 : Nat := 968861689038460605863

theorem tailTrace_2063272 : CollatzResearch.WordTrace tailWord_2063272 prefixEnd_2063272 968861689038460605863 := by
  unfold tailWord_2063272
  simp only [CollatzResearch.WordTrace]
  refine ⟨37626856090562698824200035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50169141454083598432266713 37626856090562698824200035)
  ·
    refine ⟨56440284135844048236300053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37626856090562698824200035 56440284135844048236300053)
    ·
      refine ⟨2645638318867689761076565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56440284135844048236300053 2645638318867689761076565)
      ·
        refine ⟨968861689038460605863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 2645638318867689761076565 968861689038460605863)
        ·
          rfl

theorem cell22_2063272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 13].length) (baseStart_2063272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063272 prefixEnd_2063272 := by exact prefixLift 2063272
  have htrace : WordTrace (prefixWord ++ tailWord_2063272) baseStart_2063272 baseEnd_2063272 := by
    simpa [prefixWord, tailWord_2063272, baseEnd_2063272] using wordTrace_append hprefix tailTrace_2063272
  have hstable : (prefixWord ++ tailWord_2063272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063272).length < 2 ^ (prefixWord ++ tailWord_2063272).sum := by decide
  have hdescent : baseEnd_2063272 < baseStart_2063272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063289 : List Nat := [1, 2, 1, 4, 2, 4, 1, 7]
def baseStart_2063289 : Nat := 118140960795 + 2063289 * 2 ^ 59
def prefixEnd_2063289 : Nat := 4983230072969 + 3 ^ 40 * 2063289 * 2
def baseEnd_2063289 : Nat := 78478443417383933777675

theorem tailTrace_2063289 : CollatzResearch.WordTrace tailWord_2063289 prefixEnd_2063289 78478443417383933777675 := by
  unfold tailWord_2063289
  simp only [CollatzResearch.WordTrace]
  refine ⟨75254332222063809551768921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50169554814709206367845947 75254332222063809551768921)
  ·
    refine ⟨56440749166547857163826691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75254332222063809551768921 56440749166547857163826691)
    ·
      refine ⟨84661123749821785745740037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56440749166547857163826691 84661123749821785745740037)
      ·
        refine ⟨15873960703091584827326257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84661123749821785745740037 15873960703091584827326257)
        ·
          refine ⟨11905470527318688620494693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15873960703091584827326257 11905470527318688620494693)
          ·
            refine ⟨2232275723872254116342755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11905470527318688620494693 2232275723872254116342755)
            ·
              refine ⟨3348413585808381174514133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2232275723872254116342755 3348413585808381174514133)
              ·
                refine ⟨78478443417383933777675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3348413585808381174514133 78478443417383933777675)
                ·
                  rfl

theorem cell22_2063289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 7].length) (baseStart_2063289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063289 prefixEnd_2063289 := by exact prefixLift 2063289
  have htrace : WordTrace (prefixWord ++ tailWord_2063289) baseStart_2063289 baseEnd_2063289 := by
    simpa [prefixWord, tailWord_2063289, baseEnd_2063289] using wordTrace_append hprefix tailTrace_2063289
  have hstable : (prefixWord ++ tailWord_2063289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063289).length < 2 ^ (prefixWord ++ tailWord_2063289).sum := by decide
  have hdescent : baseEnd_2063289 < baseStart_2063289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063338 : List Nat := [3, 1, 3, 1, 2, 2, 2, 4, 1, 3]
def baseStart_2063338 : Nat := 118140960795 + 2063338 * 2 ^ 59
def prefixEnd_2063338 : Nat := 4983230072969 + 3 ^ 40 * 2063338 * 2
def baseEnd_2063338 : Nat := 706322764457835609523925

theorem tailTrace_2063338 : CollatzResearch.WordTrace tailWord_2063338 prefixEnd_2063338 706322764457835609523925 := by
  unfold tailWord_2063338
  simp only [CollatzResearch.WordTrace]
  refine ⟨18814029849721572730075667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50170746265924193946868445 18814029849721572730075667)
  ·
    refine ⟨28221044774582359095113501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18814029849721572730075667 28221044774582359095113501)
    ·
      refine ⟨10582891790468384660667563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28221044774582359095113501 10582891790468384660667563)
      ·
        refine ⟨15874337685702576991001345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10582891790468384660667563 15874337685702576991001345)
        ·
          refine ⟨11905753264276932743251009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15874337685702576991001345 11905753264276932743251009)
          ·
            refine ⟨8929314948207699557438257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11905753264276932743251009 8929314948207699557438257)
            ·
              refine ⟨6696986211155774668078693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8929314948207699557438257 6696986211155774668078693)
              ·
                refine ⟨1255684914591707750264755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6696986211155774668078693 1255684914591707750264755)
                ·
                  refine ⟨1883527371887561625397133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1255684914591707750264755 1883527371887561625397133)
                  ·
                    refine ⟨706322764457835609523925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1883527371887561625397133 706322764457835609523925)
                    ·
                      rfl

theorem cell22_2063338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_2063338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063338 prefixEnd_2063338 := by exact prefixLift 2063338
  have htrace : WordTrace (prefixWord ++ tailWord_2063338) baseStart_2063338 baseEnd_2063338 := by
    simpa [prefixWord, tailWord_2063338, baseEnd_2063338] using wordTrace_append hprefix tailTrace_2063338
  have hstable : (prefixWord ++ tailWord_2063338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063338).length < 2 ^ (prefixWord ++ tailWord_2063338).sum := by decide
  have hdescent : baseEnd_2063338 < baseStart_2063338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063381 : List Nat := [1, 3, 2, 1, 4, 1, 2, 3, 1, 4]
def baseStart_2063381 : Nat := 118140960795 + 2063381 * 2 ^ 59
def prefixEnd_2063381 : Nat := 4983230072969 + 3 ^ 40 * 2063381 * 2
def baseEnd_2063381 : Nat := 706337484236597830698793

theorem tailTrace_2063381 : CollatzResearch.WordTrace tailWord_2063381 prefixEnd_2063381 706337484236597830698793 := by
  unfold tailWord_2063381
  simp only [CollatzResearch.WordTrace]
  refine ⟨75257687737730509264117997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50171791825153672842745331 75257687737730509264117997)
  ·
    refine ⟨28221632901648940974044249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75257687737730509264117997 28221632901648940974044249)
    ·
      refine ⟨21166224676236705730533187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28221632901648940974044249 21166224676236705730533187)
      ·
        refine ⟨31749337014355058595799781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21166224676236705730533187 31749337014355058595799781)
        ·
          refine ⟨5953000690191573486712459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31749337014355058595799781 5953000690191573486712459)
          ·
            refine ⟨8929501035287360230068689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5953000690191573486712459 8929501035287360230068689)
            ·
              refine ⟨6697125776465520172551517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8929501035287360230068689 6697125776465520172551517)
              ·
                refine ⟨2511422166174570064706819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6697125776465520172551517 2511422166174570064706819)
                ·
                  refine ⟨3767133249261855097060229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2511422166174570064706819 3767133249261855097060229)
                  ·
                    refine ⟨706337484236597830698793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3767133249261855097060229 706337484236597830698793)
                    ·
                      rfl

theorem cell22_2063381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_2063381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063381 prefixEnd_2063381 := by exact prefixLift 2063381
  have htrace : WordTrace (prefixWord ++ tailWord_2063381) baseStart_2063381 baseEnd_2063381 := by
    simpa [prefixWord, tailWord_2063381, baseEnd_2063381] using wordTrace_append hprefix tailTrace_2063381
  have hstable : (prefixWord ++ tailWord_2063381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063381).length < 2 ^ (prefixWord ++ tailWord_2063381).sum := by decide
  have hdescent : baseEnd_2063381 < baseStart_2063381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063396 : List Nat := [2, 3, 1, 4, 1, 1, 3, 1, 6]
def baseStart_2063396 : Nat := 118140960795 + 2063396 * 2 ^ 59
def prefixEnd_2063396 : Nat := 4983230072969 + 3 ^ 40 * 2063396 * 2
def baseEnd_2063396 : Nat := 235447539681047597191249

theorem tailTrace_2063396 : CollatzResearch.WordTrace tailWord_2063396 prefixEnd_2063396 235447539681047597191249 := by
  unfold tailWord_2063396
  simp only [CollatzResearch.WordTrace]
  refine ⟨37629117416338083412957021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50172156555117444550609361 37629117416338083412957021)
  ·
    refine ⟨14110919031126781279858883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37629117416338083412957021 14110919031126781279858883)
    ·
      refine ⟨21166378546690171919788325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14110919031126781279858883 21166378546690171919788325)
      ·
        refine ⟨3968695977504407234960311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21166378546690171919788325 3968695977504407234960311)
        ·
          refine ⟨5953043966256610852440467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3968695977504407234960311 5953043966256610852440467)
          ·
            refine ⟨8929565949384916278660701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5953043966256610852440467 8929565949384916278660701)
            ·
              refine ⟨3348587231019343604497763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8929565949384916278660701 3348587231019343604497763)
              ·
                refine ⟨5022880846529015406746645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3348587231019343604497763 5022880846529015406746645)
                ·
                  refine ⟨235447539681047597191249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5022880846529015406746645 235447539681047597191249)
                  ·
                    rfl

theorem cell22_2063396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_2063396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063396 prefixEnd_2063396 := by exact prefixLift 2063396
  have htrace : WordTrace (prefixWord ++ tailWord_2063396) baseStart_2063396 baseEnd_2063396 := by
    simpa [prefixWord, tailWord_2063396, baseEnd_2063396] using wordTrace_append hprefix tailTrace_2063396
  have hstable : (prefixWord ++ tailWord_2063396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063396).length < 2 ^ (prefixWord ++ tailWord_2063396).sum := by decide
  have hdescent : baseEnd_2063396 < baseStart_2063396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063409 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 4, 4]
def baseStart_2063409 : Nat := 118140960795 + 2063409 * 2 ^ 59
def prefixEnd_2063409 : Nat := 4983230072969 + 3 ^ 40 * 2063409 * 2
def baseEnd_2063409 : Nat := 706347069208815090998707

theorem tailTrace_2063409 : CollatzResearch.WordTrace tailWord_2063409 prefixEnd_2063409 706347069208815090998707 := by
  unfold tailWord_2063409
  simp only [CollatzResearch.WordTrace]
  refine ⟨75258708981629070046137281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50172472654419380030758187 75258708981629070046137281)
  ·
    refine ⟨56444031736221802534602961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75258708981629070046137281 56444031736221802534602961)
    ·
      refine ⟨42333023802166351900952221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56444031736221802534602961 42333023802166351900952221)
      ·
        refine ⟨15874883925812381962857083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42333023802166351900952221 15874883925812381962857083)
        ·
          refine ⟨23812325888718572944285625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15874883925812381962857083 23812325888718572944285625)
          ·
            refine ⟨17859244416538929708214219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23812325888718572944285625 17859244416538929708214219)
            ·
              refine ⟨26788866624808394562321329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17859244416538929708214219 26788866624808394562321329)
              ·
                refine ⟨20091649968606295921740997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26788866624808394562321329 20091649968606295921740997)
                ·
                  refine ⟨3767184369113680485326437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20091649968606295921740997 3767184369113680485326437)
                  ·
                    refine ⟨706347069208815090998707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3767184369113680485326437 706347069208815090998707)
                    ·
                      rfl

theorem cell22_2063409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_2063409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063409 prefixEnd_2063409 := by exact prefixLift 2063409
  have htrace : WordTrace (prefixWord ++ tailWord_2063409) baseStart_2063409 baseEnd_2063409 := by
    simpa [prefixWord, tailWord_2063409, baseEnd_2063409] using wordTrace_append hprefix tailTrace_2063409
  have hstable : (prefixWord ++ tailWord_2063409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063409).length < 2 ^ (prefixWord ++ tailWord_2063409).sum := by decide
  have hdescent : baseEnd_2063409 < baseStart_2063409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063456 : List Nat := [2, 1, 1, 3, 2, 2, 2, 3, 3, 3]
def baseStart_2063456 : Nat := 118140960795 + 2063456 * 2 ^ 59
def prefixEnd_2063456 : Nat := 4983230072969 + 3 ^ 40 * 2063456 * 2
def baseEnd_2063456 : Nat := 706363158269322635073563

theorem tailTrace_2063456 : CollatzResearch.WordTrace tailWord_2063456 prefixEnd_2063456 706363158269322635073563 := by
  unfold tailWord_2063456
  simp only [CollatzResearch.WordTrace]
  refine ⟨37630211606229398536549111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50173615474972531382065481 37630211606229398536549111)
  ·
    refine ⟨56445317409344097804823667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37630211606229398536549111 56445317409344097804823667)
    ·
      refine ⟨84667976114016146707235501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56445317409344097804823667 84667976114016146707235501)
      ·
        refine ⟨31750491042756055015213313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84667976114016146707235501 31750491042756055015213313)
        ·
          refine ⟨23812868282067041261409985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31750491042756055015213313 23812868282067041261409985)
          ·
            refine ⟨17859651211550280946057489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23812868282067041261409985 17859651211550280946057489)
            ·
              refine ⟨13394738408662710709543117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17859651211550280946057489 13394738408662710709543117)
              ·
                refine ⟨5023026903248516516078669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13394738408662710709543117 5023026903248516516078669)
                ·
                  refine ⟨1883635088718193693529501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5023026903248516516078669 1883635088718193693529501)
                  ·
                    refine ⟨706363158269322635073563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1883635088718193693529501 706363158269322635073563)
                    ·
                      rfl

theorem cell22_2063456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 3, 3].length) (baseStart_2063456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063456 prefixEnd_2063456 := by exact prefixLift 2063456
  have htrace : WordTrace (prefixWord ++ tailWord_2063456) baseStart_2063456 baseEnd_2063456 := by
    simpa [prefixWord, tailWord_2063456, baseEnd_2063456] using wordTrace_append hprefix tailTrace_2063456
  have hstable : (prefixWord ++ tailWord_2063456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063456).length < 2 ^ (prefixWord ++ tailWord_2063456).sum := by decide
  have hdescent : baseEnd_2063456 < baseStart_2063456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063458 : List Nat := [3, 3, 2, 2, 1, 3, 1, 7]
def baseStart_2063458 : Nat := 118140960795 + 2063458 * 2 ^ 59
def prefixEnd_2063458 : Nat := 4983230072969 + 3 ^ 40 * 2063458 * 2
def baseEnd_2063458 : Nat := 78484871434466144058173

theorem tailTrace_2063458 : CollatzResearch.WordTrace tailWord_2063458 prefixEnd_2063458 78484871434466144058173 := by
  unfold tailWord_2063458
  simp only [CollatzResearch.WordTrace]
  refine ⟨18815124039612887853667757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50173664105634367609780685 18815124039612887853667757)
  ·
    refine ⟨7055671514854832945125409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18815124039612887853667757 7055671514854832945125409)
    ·
      refine ⟨5291753636141124708844057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7055671514854832945125409 5291753636141124708844057)
      ·
        refine ⟨3968815227105843531633043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5291753636141124708844057 3968815227105843531633043)
        ·
          refine ⟨5953222840658765297449565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3968815227105843531633043 5953222840658765297449565)
          ·
            refine ⟨2232458565247036986543587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5953222840658765297449565 2232458565247036986543587)
            ·
              refine ⟨3348687847870555479815381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2232458565247036986543587 3348687847870555479815381)
              ·
                refine ⟨78484871434466144058173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3348687847870555479815381 78484871434466144058173)
                ·
                  rfl

theorem cell22_2063458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 7].length) (baseStart_2063458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063458 prefixEnd_2063458 := by exact prefixLift 2063458
  have htrace : WordTrace (prefixWord ++ tailWord_2063458) baseStart_2063458 baseEnd_2063458 := by
    simpa [prefixWord, tailWord_2063458, baseEnd_2063458] using wordTrace_append hprefix tailTrace_2063458
  have hstable : (prefixWord ++ tailWord_2063458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063458).length < 2 ^ (prefixWord ++ tailWord_2063458).sum := by decide
  have hdescent : baseEnd_2063458 < baseStart_2063458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063477 : List Nat := [1, 3, 4, 3, 2, 1, 1, 1, 2, 4]
def baseStart_2063477 : Nat := 118140960795 + 2063477 * 2 ^ 59
def prefixEnd_2063477 : Nat := 4983230072969 + 3 ^ 40 * 2063477 * 2
def baseEnd_2063477 : Nat := 706370346998485580298499

theorem tailTrace_2063477 : CollatzResearch.WordTrace tailWord_2063477 prefixEnd_2063477 706370346998485580298499 := by
  unfold tailWord_2063477
  simp only [CollatzResearch.WordTrace]
  refine ⟨75261189145382717659612685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50174126096921811773075123 75261189145382717659612685)
  ·
    refine ⟨28222945929518519122354757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75261189145382717659612685 28222945929518519122354757)
    ·
      refine ⟨5291802361784722335441517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28222945929518519122354757 5291802361784722335441517)
      ·
        refine ⟨1984425885669270875790569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5291802361784722335441517 1984425885669270875790569)
        ·
          refine ⟨1488319414251953156842927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1984425885669270875790569 1488319414251953156842927)
          ·
            refine ⟨2232479121377929735264391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488319414251953156842927 2232479121377929735264391)
            ·
              refine ⟨3348718682066894602896587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2232479121377929735264391 3348718682066894602896587)
              ·
                refine ⟨5023078023100341904344881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3348718682066894602896587 5023078023100341904344881)
                ·
                  refine ⟨3767308517325256428258661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5023078023100341904344881 3767308517325256428258661)
                  ·
                    refine ⟨706370346998485580298499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3767308517325256428258661 706370346998485580298499)
                    ·
                      rfl

theorem cell22_2063477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_2063477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063477 prefixEnd_2063477 := by exact prefixLift 2063477
  have htrace : WordTrace (prefixWord ++ tailWord_2063477) baseStart_2063477 baseEnd_2063477 := by
    simpa [prefixWord, tailWord_2063477, baseEnd_2063477] using wordTrace_append hprefix tailTrace_2063477
  have hstable : (prefixWord ++ tailWord_2063477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063477).length < 2 ^ (prefixWord ++ tailWord_2063477).sum := by decide
  have hdescent : baseEnd_2063477 < baseStart_2063477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063484 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 1, 7]
def baseStart_2063484 : Nat := 118140960795 + 2063484 * 2 ^ 59
def prefixEnd_2063484 : Nat := 4983230072969 + 3 ^ 40 * 2063484 * 2
def baseEnd_2063484 : Nat := 706372743241539895373477

theorem tailTrace_2063484 : CollatzResearch.WordTrace tailWord_2063484 prefixEnd_2063484 706372743241539895373477 := by
  unfold tailWord_2063484
  simp only [CollatzResearch.WordTrace]
  refine ⟨37630722228178678927558753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50174296304238238570078337 37630722228178678927558753)
  ·
    refine ⟨28223041671134009195669065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37630722228178678927558753 28223041671134009195669065)
    ·
      refine ⟨21167281253350506896751799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28223041671134009195669065 21167281253350506896751799)
      ·
        refine ⟨31750921880025760345127699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21167281253350506896751799 31750921880025760345127699)
        ·
          refine ⟨47626382820038640517691549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31750921880025760345127699 47626382820038640517691549)
          ·
            refine ⟨17859893557514490194134331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47626382820038640517691549 17859893557514490194134331)
            ·
              refine ⟨26789840336271735291201497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17859893557514490194134331 26789840336271735291201497)
              ·
                refine ⟨20092380252203801468401123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26789840336271735291201497 20092380252203801468401123)
                ·
                  refine ⟨30138570378305702202601685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20092380252203801468401123 30138570378305702202601685)
                  ·
                    refine ⟨706372743241539895373477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30138570378305702202601685 706372743241539895373477)
                    ·
                      rfl

theorem cell22_2063484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_2063484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063484 prefixEnd_2063484 := by exact prefixLift 2063484
  have htrace : WordTrace (prefixWord ++ tailWord_2063484) baseStart_2063484 baseEnd_2063484 := by
    simpa [prefixWord, tailWord_2063484, baseEnd_2063484] using wordTrace_append hprefix tailTrace_2063484
  have hstable : (prefixWord ++ tailWord_2063484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063484).length < 2 ^ (prefixWord ++ tailWord_2063484).sum := by decide
  have hdescent : baseEnd_2063484 < baseStart_2063484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063518 : List Nat := [4, 3, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_2063518 : Nat := 118140960795 + 2063518 * 2 ^ 59
def prefixEnd_2063518 : Nat := 4983230072969 + 3 ^ 40 * 2063518 * 2
def baseEnd_2063518 : Nat := 706384382136375140023373

theorem tailTrace_2063518 : CollatzResearch.WordTrace tailWord_2063518 prefixEnd_2063518 706384382136375140023373 := by
  unfold tailWord_2063518
  simp only [CollatzResearch.WordTrace]
  refine ⟨9407835567279272707731901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50175123025489454441236805 9407835567279272707731901)
  ·
    refine ⟨3527938337729727265399463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9407835567279272707731901 3527938337729727265399463)
    ·
      refine ⟨5291907506594590898099195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3527938337729727265399463 5291907506594590898099195)
      ·
        refine ⟨7937861259891886347148793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5291907506594590898099195 7937861259891886347148793)
        ·
          refine ⟨5953395944918914760361595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7937861259891886347148793 5953395944918914760361595)
          ·
            refine ⟨8930093917378372140542393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5953395944918914760361595 8930093917378372140542393)
            ·
              refine ⟨6697570438033779105406795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8930093917378372140542393 6697570438033779105406795)
              ·
                refine ⟨10046355657050668658110193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6697570438033779105406795 10046355657050668658110193)
                ·
                  refine ⟨7534766742788001493582645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10046355657050668658110193 7534766742788001493582645)
                  ·
                    refine ⟨706384382136375140023373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7534766742788001493582645 706384382136375140023373)
                    ·
                      rfl

theorem cell22_2063518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_2063518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063518 prefixEnd_2063518 := by exact prefixLift 2063518
  have htrace : WordTrace (prefixWord ++ tailWord_2063518) baseStart_2063518 baseEnd_2063518 := by
    simpa [prefixWord, tailWord_2063518, baseEnd_2063518] using wordTrace_append hprefix tailTrace_2063518
  have hstable : (prefixWord ++ tailWord_2063518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063518).length < 2 ^ (prefixWord ++ tailWord_2063518).sum := by decide
  have hdescent : baseEnd_2063518 < baseStart_2063518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063529 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 7, 5]
def baseStart_2063529 : Nat := 118140960795 + 2063529 * 2 ^ 59
def prefixEnd_2063529 : Nat := 4983230072969 + 3 ^ 40 * 2063529 * 2
def baseEnd_2063529 : Nat := 706388147661174777998339

theorem tailTrace_2063529 : CollatzResearch.WordTrace tailWord_2063529 prefixEnd_2063529 706388147661174777998339 := by
  unfold tailWord_2063529
  simp only [CollatzResearch.WordTrace]
  refine ⟨75263085741194330540505641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50175390494129553693670427 75263085741194330540505641)
  ·
    refine ⟨56447314305895747905379231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75263085741194330540505641 56447314305895747905379231)
    ·
      refine ⟨84670971458843621858068847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56447314305895747905379231 84670971458843621858068847)
      ·
        refine ⟨127006457188265432787103271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84670971458843621858068847 127006457188265432787103271)
        ·
          refine ⟨190509685782398149180654907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127006457188265432787103271 190509685782398149180654907)
          ·
            refine ⟨285764528673597223770982361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190509685782398149180654907 285764528673597223770982361)
            ·
              refine ⟨214323396505197917828236771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285764528673597223770982361 214323396505197917828236771)
              ·
                refine ⟨321485094757796876742355157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214323396505197917828236771 321485094757796876742355157)
                ·
                  refine ⟨7534806908385864298648949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 321485094757796876742355157 7534806908385864298648949)
                  ·
                    refine ⟨706388147661174777998339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7534806908385864298648949 706388147661174777998339)
                    ·
                      rfl

theorem cell22_2063529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 5].length) (baseStart_2063529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063529 prefixEnd_2063529 := by exact prefixLift 2063529
  have htrace : WordTrace (prefixWord ++ tailWord_2063529) baseStart_2063529 baseEnd_2063529 := by
    simpa [prefixWord, tailWord_2063529, baseEnd_2063529] using wordTrace_append hprefix tailTrace_2063529
  have hstable : (prefixWord ++ tailWord_2063529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063529).length < 2 ^ (prefixWord ++ tailWord_2063529).sum := by decide
  have hdescent : baseEnd_2063529 < baseStart_2063529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063558 : List Nat := [6, 1, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_2063558 : Nat := 118140960795 + 2063558 * 2 ^ 59
def prefixEnd_2063558 : Nat := 4983230072969 + 3 ^ 40 * 2063558 * 2
def baseEnd_2063558 : Nat := 706398074953828369023251

theorem tailTrace_2063558 : CollatzResearch.WordTrace tailWord_2063558 prefixEnd_2063558 706398074953828369023251 := by
  unfold tailWord_2063558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2352004483065289640415979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50176095638726178995540885 2352004483065289640415979)
  ·
    refine ⟨3528006724597934460623969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2352004483065289640415979 3528006724597934460623969)
    ·
      refine ⟨2646005043448450845467977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3528006724597934460623969 2646005043448450845467977)
      ·
        refine ⟨1984503782586338134100983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2646005043448450845467977 1984503782586338134100983)
        ·
          refine ⟨2976755673879507201151475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1984503782586338134100983 2976755673879507201151475)
          ·
            refine ⟨4465133510819260801727213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2976755673879507201151475 4465133510819260801727213)
            ·
              refine ⟨1674425066557222800647705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4465133510819260801727213 1674425066557222800647705)
              ·
                refine ⟨1255818799917917100485779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1674425066557222800647705 1255818799917917100485779)
                ·
                  refine ⟨1883728199876875650728669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1255818799917917100485779 1883728199876875650728669)
                  ·
                    refine ⟨706398074953828369023251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1883728199876875650728669 706398074953828369023251)
                    ·
                      rfl

theorem cell22_2063558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_2063558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063558 prefixEnd_2063558 := by exact prefixLift 2063558
  have htrace : WordTrace (prefixWord ++ tailWord_2063558) baseStart_2063558 baseEnd_2063558 := by
    simpa [prefixWord, tailWord_2063558, baseEnd_2063558] using wordTrace_append hprefix tailTrace_2063558
  have hstable : (prefixWord ++ tailWord_2063558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063558).length < 2 ^ (prefixWord ++ tailWord_2063558).sum := by decide
  have hdescent : baseEnd_2063558 < baseStart_2063558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063625 : List Nat := [1, 2, 1, 1, 3, 3, 3, 4, 1, 3]
def baseStart_2063625 : Nat := 118140960795 + 2063625 * 2 ^ 59
def prefixEnd_2063625 : Nat := 4983230072969 + 3 ^ 40 * 2063625 * 2
def baseEnd_2063625 : Nat := 706421010423062527598045

theorem tailTrace_2063625 : CollatzResearch.WordTrace tailWord_2063625 prefixEnd_2063625 706421010423062527598045 := by
  unfold tailWord_2063625
  simp only [CollatzResearch.WordTrace]
  refine ⟨75266587148846538936000329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50177724765897692624000219 75266587148846538936000329)
  ·
    refine ⟨56449940361634904202000247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75266587148846538936000329 56449940361634904202000247)
    ·
      refine ⟨84674910542452356303000371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56449940361634904202000247 84674910542452356303000371)
      ·
        refine ⟨127012365813678534454500557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84674910542452356303000371 127012365813678534454500557)
        ·
          refine ⟨47629637180129450420437709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127012365813678534454500557 47629637180129450420437709)
          ·
            refine ⟨17861113942548543907664141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47629637180129450420437709 17861113942548543907664141)
            ·
              refine ⟨6697917728455703965374053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17861113942548543907664141 6697917728455703965374053)
              ·
                refine ⟨1255859574085444493507635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6697917728455703965374053 1255859574085444493507635)
                ·
                  refine ⟨1883789361128166740261453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1255859574085444493507635 1883789361128166740261453)
                  ·
                    refine ⟨706421010423062527598045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1883789361128166740261453 706421010423062527598045)
                    ·
                      rfl

theorem cell22_2063625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 4, 1, 3].length) (baseStart_2063625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063625 prefixEnd_2063625 := by exact prefixLift 2063625
  have htrace : WordTrace (prefixWord ++ tailWord_2063625) baseStart_2063625 baseEnd_2063625 := by
    simpa [prefixWord, tailWord_2063625, baseEnd_2063625] using wordTrace_append hprefix tailTrace_2063625
  have hstable : (prefixWord ++ tailWord_2063625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063625).length < 2 ^ (prefixWord ++ tailWord_2063625).sum := by decide
  have hdescent : baseEnd_2063625 < baseStart_2063625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063696 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 3, 6]
def baseStart_2063696 : Nat := 118140960795 + 2063696 * 2 ^ 59
def prefixEnd_2063696 : Nat := 4983230072969 + 3 ^ 40 * 2063696 * 2
def baseEnd_2063696 : Nat := 706445315174042009072827

theorem tailTrace_2063696 : CollatzResearch.WordTrace tailWord_2063696 prefixEnd_2063696 706445315174042009072827 := by
  unfold tailWord_2063696
  simp only [CollatzResearch.WordTrace]
  refine ⟨37634588365794659030917471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50179451154392878707889961 37634588365794659030917471)
  ·
    refine ⟨56451882548691988546376207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37634588365794659030917471 56451882548691988546376207)
    ·
      refine ⟨84677823823037982819564311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56451882548691988546376207 84677823823037982819564311)
      ·
        refine ⟨127016735734556974229346467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84677823823037982819564311 127016735734556974229346467)
        ·
          refine ⟨190525103601835461344019701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127016735734556974229346467 190525103601835461344019701)
          ·
            refine ⟨17861728462672074501001847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190525103601835461344019701 17861728462672074501001847)
            ·
              refine ⟨26792592694008111751502771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17861728462672074501001847 26792592694008111751502771)
              ·
                refine ⟨40188889041012167627254157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26792592694008111751502771 40188889041012167627254157)
                ·
                  refine ⟨15070833390379562860220309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40188889041012167627254157 15070833390379562860220309)
                  ·
                    refine ⟨706445315174042009072827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15070833390379562860220309 706445315174042009072827)
                    ·
                      rfl

theorem cell22_2063696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 3, 6].length) (baseStart_2063696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063696 prefixEnd_2063696 := by exact prefixLift 2063696
  have htrace : WordTrace (prefixWord ++ tailWord_2063696) baseStart_2063696 baseEnd_2063696 := by
    simpa [prefixWord, tailWord_2063696, baseEnd_2063696] using wordTrace_append hprefix tailTrace_2063696
  have hstable : (prefixWord ++ tailWord_2063696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063696).length < 2 ^ (prefixWord ++ tailWord_2063696).sum := by decide
  have hdescent : baseEnd_2063696 < baseStart_2063696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063745 : List Nat := [1, 2, 4, 3, 2, 1, 2, 7]
def baseStart_2063745 : Nat := 118140960795 + 2063745 * 2 ^ 59
def prefixEnd_2063745 : Nat := 4983230072969 + 3 ^ 40 * 2063745 * 2
def baseEnd_2063745 : Nat := 78495787652824690510853

theorem tailTrace_2063745 : CollatzResearch.WordTrace tailWord_2063745 prefixEnd_2063745 78495787652824690510853 := by
  unfold tailWord_2063745
  simp only [CollatzResearch.WordTrace]
  refine ⟨75270963908411799430368689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50180642605607866286912459 75270963908411799430368689)
  ·
    refine ⟨56453222931308849572776517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75270963908411799430368689 56453222931308849572776517)
    ·
      refine ⟨10584979299620409294895597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56453222931308849572776517 10584979299620409294895597)
      ·
        refine ⟨3969367237357653485585849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10584979299620409294895597 3969367237357653485585849)
        ·
          refine ⟨2977025428018240114189387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3969367237357653485585849 2977025428018240114189387)
          ·
            refine ⟨4465538142027360171284081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2977025428018240114189387 4465538142027360171284081)
            ·
              refine ⟨3349153606520520128463061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4465538142027360171284081 3349153606520520128463061)
              ·
                refine ⟨78495787652824690510853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3349153606520520128463061 78495787652824690510853)
                ·
                  rfl

theorem cell22_2063745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 7].length) (baseStart_2063745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063745 prefixEnd_2063745 := by exact prefixLift 2063745
  have htrace : WordTrace (prefixWord ++ tailWord_2063745) baseStart_2063745 baseEnd_2063745 := by
    simpa [prefixWord, tailWord_2063745, baseEnd_2063745] using wordTrace_append hprefix tailTrace_2063745
  have hstable : (prefixWord ++ tailWord_2063745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063745).length < 2 ^ (prefixWord ++ tailWord_2063745).sum := by decide
  have hdescent : baseEnd_2063745 < baseStart_2063745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063818 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 8]
def baseStart_2063818 : Nat := 118140960795 + 2063818 * 2 ^ 59
def prefixEnd_2063818 : Nat := 4983230072969 + 3 ^ 40 * 2063818 * 2
def baseEnd_2063818 : Nat := 235495692755758119174151

theorem tailTrace_2063818 : CollatzResearch.WordTrace tailWord_2063818 prefixEnd_2063818 235495692755758119174151 := by
  unfold tailWord_2063818
  simp only [CollatzResearch.WordTrace]
  refine ⟨18818406609286833224444027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50182417624764888598517405 18818406609286833224444027)
  ·
    refine ⟨28227609913930249836666041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18818406609286833224444027 28227609913930249836666041)
    ·
      refine ⟨21170707435447687377499531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28227609913930249836666041 21170707435447687377499531)
      ·
        refine ⟨31756061153171531066249297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21170707435447687377499531 31756061153171531066249297)
        ·
          refine ⟨23817045864878648299686973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31756061153171531066249297 23817045864878648299686973)
          ·
            refine ⟨8931392199329493112382615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23817045864878648299686973 8931392199329493112382615)
            ·
              refine ⟨13397088298994239668573923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8931392199329493112382615 13397088298994239668573923)
              ·
                refine ⟨20095632448491359502860885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13397088298994239668573923 20095632448491359502860885)
                ·
                  refine ⟨235495692755758119174151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20095632448491359502860885 235495692755758119174151)
                  ·
                    rfl

theorem cell22_2063818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_2063818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063818 prefixEnd_2063818 := by exact prefixLift 2063818
  have htrace : WordTrace (prefixWord ++ tailWord_2063818) baseStart_2063818 baseEnd_2063818 := by
    simpa [prefixWord, tailWord_2063818, baseEnd_2063818] using wordTrace_append hprefix tailTrace_2063818
  have hstable : (prefixWord ++ tailWord_2063818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063818).length < 2 ^ (prefixWord ++ tailWord_2063818).sum := by decide
  have hdescent : baseEnd_2063818 < baseStart_2063818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063820 : List Nat := [2, 2, 1, 4, 2, 1, 2, 1, 3, 4]
def baseStart_2063820 : Nat := 118140960795 + 2063820 * 2 ^ 59
def prefixEnd_2063820 : Nat := 4983230072969 + 3 ^ 40 * 2063820 * 2
def baseEnd_2063820 : Nat := 706487762908147018972447

theorem tailTrace_2063820 : CollatzResearch.WordTrace tailWord_2063820 prefixEnd_2063820 706487762908147018972447 := by
  unfold tailWord_2063820
  simp only [CollatzResearch.WordTrace]
  refine ⟨37636849691570043619674457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50182466255426724826232609 37636849691570043619674457)
  ·
    refine ⟨28227637268677532714755843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37636849691570043619674457 28227637268677532714755843)
    ·
      refine ⟨42341455903016299072133765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28227637268677532714755843 42341455903016299072133765)
      ·
        refine ⟨7939022981815556076025081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42341455903016299072133765 7939022981815556076025081)
        ·
          refine ⟨5954267236361667057018811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7939022981815556076025081 5954267236361667057018811)
          ·
            refine ⟨8931400854542500585528217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5954267236361667057018811 8931400854542500585528217)
            ·
              refine ⟨6698550640906875439146163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8931400854542500585528217 6698550640906875439146163)
              ·
                refine ⟨10047825961360313158719245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6698550640906875439146163 10047825961360313158719245)
                ·
                  refine ⟨3767934735510117434519717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10047825961360313158719245 3767934735510117434519717)
                  ·
                    refine ⟨706487762908147018972447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3767934735510117434519717 706487762908147018972447)
                    ·
                      rfl

theorem cell22_2063820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_2063820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063820 prefixEnd_2063820 := by exact prefixLift 2063820
  have htrace : WordTrace (prefixWord ++ tailWord_2063820) baseStart_2063820 baseEnd_2063820 := by
    simpa [prefixWord, tailWord_2063820, baseEnd_2063820] using wordTrace_append hprefix tailTrace_2063820
  have hstable : (prefixWord ++ tailWord_2063820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063820).length < 2 ^ (prefixWord ++ tailWord_2063820).sum := by decide
  have hdescent : baseEnd_2063820 < baseStart_2063820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063837 : List Nat := [1, 4, 3, 1, 1, 3, 1, 3, 1, 4]
def baseStart_2063837 : Nat := 118140960795 + 2063837 * 2 ^ 59
def prefixEnd_2063837 : Nat := 4983230072969 + 3 ^ 40 * 2063837 * 2
def baseEnd_2063837 : Nat := 706493582355564641297395

theorem tailTrace_2063837 : CollatzResearch.WordTrace tailWord_2063837 prefixEnd_2063837 706493582355564641297395 := by
  unfold tailWord_2063837
  simp only [CollatzResearch.WordTrace]
  refine ⟨75274319424078499142717765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50182879616052332761811843 75274319424078499142717765)
  ·
    refine ⟨14113934892014718589259581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75274319424078499142717765 14113934892014718589259581)
    ·
      refine ⟨5292725584505519470972343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14113934892014718589259581 5292725584505519470972343)
      ·
        refine ⟨7939088376758279206458515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5292725584505519470972343 7939088376758279206458515)
        ·
          refine ⟨11908632565137418809687773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7939088376758279206458515 11908632565137418809687773)
          ·
            refine ⟨4465737211926532053632915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11908632565137418809687773 4465737211926532053632915)
            ·
              refine ⟨6698605817889798080449373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4465737211926532053632915 6698605817889798080449373)
              ·
                refine ⟨2511977181708674280168515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6698605817889798080449373 2511977181708674280168515)
                ·
                  refine ⟨3767965772563011420252773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2511977181708674280168515 3767965772563011420252773)
                  ·
                    refine ⟨706493582355564641297395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3767965772563011420252773 706493582355564641297395)
                    ·
                      rfl

theorem cell22_2063837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_2063837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063837 prefixEnd_2063837 := by exact prefixLift 2063837
  have htrace : WordTrace (prefixWord ++ tailWord_2063837) baseStart_2063837 baseEnd_2063837 := by
    simpa [prefixWord, tailWord_2063837, baseEnd_2063837] using wordTrace_append hprefix tailTrace_2063837
  have hstable : (prefixWord ++ tailWord_2063837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063837).length < 2 ^ (prefixWord ++ tailWord_2063837).sum := by decide
  have hdescent : baseEnd_2063837 < baseStart_2063837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063880 : List Nat := [2, 1, 3, 2, 1, 1, 6, 6]
def baseStart_2063880 : Nat := 118140960795 + 2063880 * 2 ^ 59
def prefixEnd_2063880 : Nat := 4983230072969 + 3 ^ 40 * 2063880 * 2
def baseEnd_2063880 : Nat := 78500922459369651385807

theorem tailTrace_2063880 : CollatzResearch.WordTrace tailWord_2063880 prefixEnd_2063880 78500922459369651385807 := by
  unfold tailWord_2063880
  simp only [CollatzResearch.WordTrace]
  refine ⟨37637943881461358743266547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50183925175281811657688729 37637943881461358743266547)
  ·
    refine ⟨56456915822192038114899821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37637943881461358743266547 56456915822192038114899821)
    ·
      refine ⟨21171343433322014293087433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56456915822192038114899821 21171343433322014293087433)
      ·
        refine ⟨15878507574991510719815575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21171343433322014293087433 15878507574991510719815575)
        ·
          refine ⟨23817761362487266079723363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15878507574991510719815575 23817761362487266079723363)
          ·
            refine ⟨35726642043730899119585045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23817761362487266079723363 35726642043730899119585045)
            ·
              refine ⟨1674686345799885896230549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35726642043730899119585045 1674686345799885896230549)
              ·
                refine ⟨78500922459369651385807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1674686345799885896230549 78500922459369651385807)
                ·
                  rfl

theorem cell22_2063880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 6].length) (baseStart_2063880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063880 prefixEnd_2063880 := by exact prefixLift 2063880
  have htrace : WordTrace (prefixWord ++ tailWord_2063880) baseStart_2063880 baseEnd_2063880 := by
    simpa [prefixWord, tailWord_2063880, baseEnd_2063880] using wordTrace_append hprefix tailTrace_2063880
  have hstable : (prefixWord ++ tailWord_2063880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063880).length < 2 ^ (prefixWord ++ tailWord_2063880).sum := by decide
  have hdescent : baseEnd_2063880 < baseStart_2063880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063886 : List Nat := [4, 1, 1, 2, 5, 1, 1, 3, 4]
def baseStart_2063886 : Nat := 118140960795 + 2063886 * 2 ^ 59
def prefixEnd_2063886 : Nat := 4983230072969 + 3 ^ 40 * 2063886 * 2
def baseEnd_2063886 : Nat := 235503452018981615607415

theorem tailTrace_2063886 : CollatzResearch.WordTrace tailWord_2063886 prefixEnd_2063886 235503452018981615607415 := by
  unfold tailWord_2063886
  simp only [CollatzResearch.WordTrace]
  refine ⟨9409513325112622563906439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50184071067267320340834341 9409513325112622563906439)
  ·
    refine ⟨14114269987668933845859659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9409513325112622563906439 14114269987668933845859659)
    ·
      refine ⟨21171404981503400768789489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14114269987668933845859659 21171404981503400768789489)
      ·
        refine ⟨15878553736127550576592117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21171404981503400768789489 15878553736127550576592117)
        ·
          refine ⟨1488614412761957866555511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15878553736127550576592117 1488614412761957866555511)
          ·
            refine ⟨2232921619142936799833267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488614412761957866555511 2232921619142936799833267)
            ·
              refine ⟨3349382428714405199749901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2232921619142936799833267 3349382428714405199749901)
              ·
                refine ⟨1256018410767901949906213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3349382428714405199749901 1256018410767901949906213)
                ·
                  refine ⟨235503452018981615607415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1256018410767901949906213 235503452018981615607415)
                  ·
                    rfl

theorem cell22_2063886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_2063886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2063886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2063886 prefixEnd_2063886 := by exact prefixLift 2063886
  have htrace : WordTrace (prefixWord ++ tailWord_2063886) baseStart_2063886 baseEnd_2063886 := by
    simpa [prefixWord, tailWord_2063886, baseEnd_2063886] using wordTrace_append hprefix tailTrace_2063886
  have hstable : (prefixWord ++ tailWord_2063886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063886).length < 2 ^ (prefixWord ++ tailWord_2063886).sum := by decide
  have hdescent : baseEnd_2063886 < baseStart_2063886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064000 : List Nat := [2, 1, 1, 2, 1, 4, 3, 1, 1, 6]
def baseStart_2064000 : Nat := 118140960795 + 2064000 * 2 ^ 59
def prefixEnd_2064000 : Nat := 4983230072969 + 3 ^ 40 * 2064000 * 2
def baseEnd_2064000 : Nat := 706549380586686549471895

theorem tailTrace_2064000 : CollatzResearch.WordTrace tailWord_2064000 prefixEnd_2064000 706549380586686549471895 := by
  unfold tailWord_2064000
  simp only [CollatzResearch.WordTrace]
  refine ⟨37640132261243988990450727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50186843014991985320600969 37640132261243988990450727)
  ·
    refine ⟨56460198391865983485676091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37640132261243988990450727 56460198391865983485676091)
    ·
      refine ⟨84690297587798975228514137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56460198391865983485676091 84690297587798975228514137)
      ·
        refine ⟨63517723190849231421385603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84690297587798975228514137 63517723190849231421385603)
        ·
          refine ⟨95276584786273847132078405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63517723190849231421385603 95276584786273847132078405)
          ·
            refine ⟨17864359647426346337264701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95276584786273847132078405 17864359647426346337264701)
            ·
              refine ⟨6699134867784879876474263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17864359647426346337264701 6699134867784879876474263)
              ·
                refine ⟨10048702301677319814711395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6699134867784879876474263 10048702301677319814711395)
                ·
                  refine ⟨15073053452515979722067093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10048702301677319814711395 15073053452515979722067093)
                  ·
                    refine ⟨706549380586686549471895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15073053452515979722067093 706549380586686549471895)
                    ·
                      rfl

theorem cell22_2064000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 1, 6].length) (baseStart_2064000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2064000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2064000 prefixEnd_2064000 := by exact prefixLift 2064000
  have htrace : WordTrace (prefixWord ++ tailWord_2064000) baseStart_2064000 baseEnd_2064000 := by
    simpa [prefixWord, tailWord_2064000, baseEnd_2064000] using wordTrace_append hprefix tailTrace_2064000
  have hstable : (prefixWord ++ tailWord_2064000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064000).length < 2 ^ (prefixWord ++ tailWord_2064000).sum := by decide
  have hdescent : baseEnd_2064000 < baseStart_2064000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064036 : List Nat := [2, 3, 1, 2, 2, 3, 3, 1, 2, 3]
def baseStart_2064036 : Nat := 118140960795 + 2064036 * 2 ^ 59
def prefixEnd_2064036 : Nat := 4983230072969 + 3 ^ 40 * 2064036 * 2
def baseEnd_2064036 : Nat := 706561704122394455571785

theorem tailTrace_2064036 : CollatzResearch.WordTrace tailWord_2064036 prefixEnd_2064036 706561704122394455571785 := by
  unfold tailWord_2064036
  simp only [CollatzResearch.WordTrace]
  refine ⟨37640788775178778064605981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50187718366905037419474641 37640788775178778064605981)
  ·
    refine ⟨14115295790692041774227243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37640788775178778064605981 14115295790692041774227243)
    ·
      refine ⟨21172943686038062661340865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14115295790692041774227243 21172943686038062661340865)
      ·
        refine ⟨15879707764528546996005649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21172943686038062661340865 15879707764528546996005649)
        ·
          refine ⟨11909780823396410247004237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15879707764528546996005649 11909780823396410247004237)
          ·
            refine ⟨4466167808773653842626589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11909780823396410247004237 4466167808773653842626589)
            ·
              refine ⟨1674812928290120190984971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4466167808773653842626589 1674812928290120190984971)
              ·
                refine ⟨2512219392435180286477457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1674812928290120190984971 2512219392435180286477457)
                ·
                  refine ⟨1884164544326385214858093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2512219392435180286477457 1884164544326385214858093)
                  ·
                    refine ⟨706561704122394455571785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1884164544326385214858093 706561704122394455571785)
                    ·
                      rfl

theorem cell22_2064036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_2064036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2064036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2064036 prefixEnd_2064036 := by exact prefixLift 2064036
  have htrace : WordTrace (prefixWord ++ tailWord_2064036) baseStart_2064036 baseEnd_2064036 := by
    simpa [prefixWord, tailWord_2064036, baseEnd_2064036] using wordTrace_append hprefix tailTrace_2064036
  have hstable : (prefixWord ++ tailWord_2064036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064036).length < 2 ^ (prefixWord ++ tailWord_2064036).sum := by decide
  have hdescent : baseEnd_2064036 < baseStart_2064036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064047 : List Nat := [1, 1, 2, 1, 2, 4, 1, 4, 3, 3]
def baseStart_2064047 : Nat := 118140960795 + 2064047 * 2 ^ 59
def prefixEnd_2064047 : Nat := 4983230072969 + 3 ^ 40 * 2064047 * 2
def baseEnd_2064047 : Nat := 706565469647194093546751

theorem tailTrace_2064047 : CollatzResearch.WordTrace tailWord_2064047 prefixEnd_2064047 706565469647194093546751 := by
  unfold tailWord_2064047
  simp only [CollatzResearch.WordTrace]
  refine ⟨75281978753317705007862395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50187985835545136671908263 75281978753317705007862395)
  ·
    refine ⟨112922968129976557511793593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75281978753317705007862395 112922968129976557511793593)
    ·
      refine ⟨84692226097482418133845195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112922968129976557511793593 84692226097482418133845195)
      ·
        refine ⟨127038339146223627200767793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84692226097482418133845195 127038339146223627200767793)
        ·
          refine ⟨95278754359667720400575845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127038339146223627200767793 95278754359667720400575845)
          ·
            refine ⟨17864766442437697575107971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95278754359667720400575845 17864766442437697575107971)
            ·
              refine ⟨26797149663656546362661957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17864766442437697575107971 26797149663656546362661957)
              ·
                refine ⟨5024465561935602442999117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26797149663656546362661957 5024465561935602442999117)
                ·
                  refine ⟨1884174585725850916124669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5024465561935602442999117 1884174585725850916124669)
                  ·
                    refine ⟨706565469647194093546751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1884174585725850916124669 706565469647194093546751)
                    ·
                      rfl

theorem cell22_2064047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 3, 3].length) (baseStart_2064047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2064047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2064047 prefixEnd_2064047 := by exact prefixLift 2064047
  have htrace : WordTrace (prefixWord ++ tailWord_2064047) baseStart_2064047 baseEnd_2064047 := by
    simpa [prefixWord, tailWord_2064047, baseEnd_2064047] using wordTrace_append hprefix tailTrace_2064047
  have hstable : (prefixWord ++ tailWord_2064047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064047).length < 2 ^ (prefixWord ++ tailWord_2064047).sum := by decide
  have hdescent : baseEnd_2064047 < baseStart_2064047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064075 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 4, 5]
def baseStart_2064075 : Nat := 118140960795 + 2064075 * 2 ^ 59
def prefixEnd_2064075 : Nat := 4983230072969 + 3 ^ 40 * 2064075 * 2
def baseEnd_2064075 : Nat := 706575054619411353846665

theorem tailTrace_2064075 : CollatzResearch.WordTrace tailWord_2064075 prefixEnd_2064075 706575054619411353846665 := by
  unfold tailWord_2064075
  simp only [CollatzResearch.WordTrace]
  refine ⟨75282999997216265789881679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50188666664810843859921119 75282999997216265789881679)
  ·
    refine ⟨112924499995824398684822519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75282999997216265789881679 112924499995824398684822519)
    ·
      refine ⟨169386749993736598027233779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112924499995824398684822519 169386749993736598027233779)
      ·
        refine ⟨254080124990604897040850669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169386749993736598027233779 254080124990604897040850669)
        ·
          refine ⟨95280046871476836390319001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254080124990604897040850669 95280046871476836390319001)
          ·
            refine ⟨71460035153607627292739251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95280046871476836390319001 71460035153607627292739251)
            ·
              refine ⟨107190052730411440939108877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71460035153607627292739251 107190052730411440939108877)
              ·
                refine ⟨40196269773904290352165829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107190052730411440939108877 40196269773904290352165829)
                ·
                  refine ⟨7536800582607054441031093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40196269773904290352165829 7536800582607054441031093)
                  ·
                    refine ⟨706575054619411353846665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7536800582607054441031093 706575054619411353846665)
                    ·
                      rfl

theorem cell22_2064075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 5].length) (baseStart_2064075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2064075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2064075 prefixEnd_2064075 := by exact prefixLift 2064075
  have htrace : WordTrace (prefixWord ++ tailWord_2064075) baseStart_2064075 baseEnd_2064075 := by
    simpa [prefixWord, tailWord_2064075, baseEnd_2064075] using wordTrace_append hprefix tailTrace_2064075
  have hstable : (prefixWord ++ tailWord_2064075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064075).length < 2 ^ (prefixWord ++ tailWord_2064075).sum := by decide
  have hdescent : baseEnd_2064075 < baseStart_2064075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064105 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 8]
def baseStart_2064105 : Nat := 118140960795 + 2064105 * 2 ^ 59
def prefixEnd_2064105 : Nat := 4983230072969 + 3 ^ 40 * 2064105 * 2
def baseEnd_2064105 : Nat := 235528441410833758532191

theorem tailTrace_2064105 : CollatzResearch.WordTrace tailWord_2064105 prefixEnd_2064105 235528441410833758532191 := by
  unfold tailWord_2064105
  simp only [CollatzResearch.WordTrace]
  refine ⟨75284094187107580913473769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50189396124738387275649179 75284094187107580913473769)
  ·
    refine ⟨56463070640330685685105327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75284094187107580913473769 56463070640330685685105327)
    ·
      refine ⟨84694605960496028527657991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56463070640330685685105327 84694605960496028527657991)
      ·
        refine ⟨127041908940744042791486987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84694605960496028527657991 127041908940744042791486987)
        ·
          refine ⟨190562863411116064187230481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127041908940744042791486987 190562863411116064187230481)
          ·
            refine ⟨142922147558337048140422861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190562863411116064187230481 142922147558337048140422861)
            ·
              refine ⟨53595805334376393052658573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 142922147558337048140422861 53595805334376393052658573)
              ·
                refine ⟨20098427000391147394746965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53595805334376393052658573 20098427000391147394746965)
                ·
                  refine ⟨235528441410833758532191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20098427000391147394746965 235528441410833758532191)
                  ·
                    rfl

theorem cell22_2064105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 8].length) (baseStart_2064105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2064105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2064105 prefixEnd_2064105 := by exact prefixLift 2064105
  have htrace : WordTrace (prefixWord ++ tailWord_2064105) baseStart_2064105 baseEnd_2064105 := by
    simpa [prefixWord, tailWord_2064105, baseEnd_2064105] using wordTrace_append hprefix tailTrace_2064105
  have hstable : (prefixWord ++ tailWord_2064105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064105).length < 2 ^ (prefixWord ++ tailWord_2064105).sum := by decide
  have hdescent : baseEnd_2064105 < baseStart_2064105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064152 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 4, 4]
def baseStart_2064152 : Nat := 118140960795 + 2064152 * 2 ^ 59
def prefixEnd_2064152 : Nat := 4983230072969 + 3 ^ 40 * 2064152 * 2
def baseEnd_2064152 : Nat := 706601413293008819671429

theorem tailTrace_2064152 : CollatzResearch.WordTrace tailWord_2064152 prefixEnd_2064152 706601413293008819671429 := by
  unfold tailWord_2064152
  simp only [CollatzResearch.WordTrace]
  refine ⟨37642904208968653970217355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50190538945291538626956473 37642904208968653970217355)
  ·
    refine ⟨56464356313452980955326033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37642904208968653970217355 56464356313452980955326033)
    ·
      refine ⟨42348267235089735716494525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56464356313452980955326033 42348267235089735716494525)
      ·
        refine ⟨15880600213158650893685447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42348267235089735716494525 15880600213158650893685447)
        ·
          refine ⟨23820900319737976340528171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15880600213158650893685447 23820900319737976340528171)
          ·
            refine ⟨35731350479606964510792257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23820900319737976340528171 35731350479606964510792257)
            ·
              refine ⟨26798512859705223383094193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35731350479606964510792257 26798512859705223383094193)
              ·
                refine ⟨20098884644778917537320645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26798512859705223383094193 20098884644778917537320645)
                ·
                  refine ⟨3768540870896047038247621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20098884644778917537320645 3768540870896047038247621)
                  ·
                    refine ⟨706601413293008819671429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3768540870896047038247621 706601413293008819671429)
                    ·
                      rfl

theorem cell22_2064152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_2064152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2064152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2064152 prefixEnd_2064152 := by exact prefixLift 2064152
  have htrace : WordTrace (prefixWord ++ tailWord_2064152) baseStart_2064152 baseEnd_2064152 := by
    simpa [prefixWord, tailWord_2064152, baseEnd_2064152] using wordTrace_append hprefix tailTrace_2064152
  have hstable : (prefixWord ++ tailWord_2064152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064152).length < 2 ^ (prefixWord ++ tailWord_2064152).sum := by decide
  have hdescent : baseEnd_2064152 < baseStart_2064152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064154 : List Nat := [3, 1, 1, 3, 2, 3, 2, 1, 1, 5]
def baseStart_2064154 : Nat := 118140960795 + 2064154 * 2 ^ 59
def prefixEnd_2064154 : Nat := 4983230072969 + 3 ^ 40 * 2064154 * 2
def baseEnd_2064154 : Nat := 706602097933881481121423

theorem tailTrace_2064154 : CollatzResearch.WordTrace tailWord_2064154 prefixEnd_2064154 706602097933881481121423 := by
  unfold tailWord_2064154
  simp only [CollatzResearch.WordTrace]
  refine ⟨18821470340982515570501879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50190587575953374854671677 18821470340982515570501879)
  ·
    refine ⟨28232205511473773355752819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18821470340982515570501879 28232205511473773355752819)
    ·
      refine ⟨42348308267210660033629229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28232205511473773355752819 42348308267210660033629229)
      ·
        refine ⟨15880615600203997512610961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42348308267210660033629229 15880615600203997512610961)
        ·
          refine ⟨11910461700152998134458221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15880615600203997512610961 11910461700152998134458221)
          ·
            refine ⟨4466423137557374300421833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11910461700152998134458221 4466423137557374300421833)
            ·
              refine ⟨3349817353168030725316375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4466423137557374300421833 3349817353168030725316375)
              ·
                refine ⟨5024726029752046087974563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3349817353168030725316375 5024726029752046087974563)
                ·
                  refine ⟨7537089044628069131961845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5024726029752046087974563 7537089044628069131961845)
                  ·
                    refine ⟨706602097933881481121423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7537089044628069131961845 706602097933881481121423)
                    ·
                      rfl

theorem cell22_2064154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_2064154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2064154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2064154 prefixEnd_2064154 := by exact prefixLift 2064154
  have htrace : WordTrace (prefixWord ++ tailWord_2064154) baseStart_2064154 baseEnd_2064154 := by
    simpa [prefixWord, tailWord_2064154, baseEnd_2064154] using wordTrace_append hprefix tailTrace_2064154
  have hstable : (prefixWord ++ tailWord_2064154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064154).length < 2 ^ (prefixWord ++ tailWord_2064154).sum := by decide
  have hdescent : baseEnd_2064154 < baseStart_2064154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064199 : List Nat := [1, 1, 4, 1, 2, 1, 3, 3, 3, 3]
def baseStart_2064199 : Nat := 118140960795 + 2064199 * 2 ^ 59
def prefixEnd_2064199 : Nat := 4983230072969 + 3 ^ 40 * 2064199 * 2
def baseEnd_2064199 : Nat := 706617502353516363746285

theorem tailTrace_2064199 : CollatzResearch.WordTrace tailWord_2064199 prefixEnd_2064199 706617502353516363746285 := by
  unfold tailWord_2064199
  simp only [CollatzResearch.WordTrace]
  refine ⟨75287522648767034967395651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50191681765844689978263767 75287522648767034967395651)
  ·
    refine ⟨112931283973150552451093477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75287522648767034967395651 112931283973150552451093477)
    ·
      refine ⟨21174615744965728584580027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112931283973150552451093477 21174615744965728584580027)
      ·
        refine ⟨31761923617448592876870041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21174615744965728584580027 31761923617448592876870041)
        ·
          refine ⟨23821442713086444657652531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31761923617448592876870041 23821442713086444657652531)
          ·
            refine ⟨35732164069629666986478797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23821442713086444657652531 35732164069629666986478797)
            ·
              refine ⟨13399561526111125119929549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35732164069629666986478797 13399561526111125119929549)
              ·
                refine ⟨5024835572291671919973581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13399561526111125119929549 5024835572291671919973581)
                ·
                  refine ⟨1884313339609376969990093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5024835572291671919973581 1884313339609376969990093)
                  ·
                    refine ⟨706617502353516363746285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1884313339609376969990093 706617502353516363746285)
                    ·
                      rfl

theorem cell22_2064199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_2064199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2064199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2064199 prefixEnd_2064199 := by exact prefixLift 2064199
  have htrace : WordTrace (prefixWord ++ tailWord_2064199) baseStart_2064199 baseEnd_2064199 := by
    simpa [prefixWord, tailWord_2064199, baseEnd_2064199] using wordTrace_append hprefix tailTrace_2064199
  have hstable : (prefixWord ++ tailWord_2064199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064199).length < 2 ^ (prefixWord ++ tailWord_2064199).sum := by decide
  have hdescent : baseEnd_2064199 < baseStart_2064199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064205 : List Nat := [1, 6, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_2064205 : Nat := 118140960795 + 2064205 * 2 ^ 59
def prefixEnd_2064205 : Nat := 4983230072969 + 3 ^ 40 * 2064205 * 2
def baseEnd_2064205 : Nat := 706619556276134348096267

theorem tailTrace_2064205 : CollatzResearch.WordTrace tailWord_2064205 prefixEnd_2064205 706619556276134348096267 := by
  unfold tailWord_2064205
  simp only [CollatzResearch.WordTrace]
  refine ⟨75287741486745297992114069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50191827657830198661409379 75287741486745297992114069)
  ·
    refine ⟨3529112882191185843380347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75287741486745297992114069 3529112882191185843380347)
    ·
      refine ⟨5293669323286778765070521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3529112882191185843380347 5293669323286778765070521)
      ·
        refine ⟨3970251992465084073802891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5293669323286778765070521 3970251992465084073802891)
        ·
          refine ⟨5955377988697626110704337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3970251992465084073802891 5955377988697626110704337)
          ·
            refine ⟨4466533491523219583028253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5955377988697626110704337 4466533491523219583028253)
            ·
              refine ⟨1674950059321207343635595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4466533491523219583028253 1674950059321207343635595)
              ·
                refine ⟨2512425088981811015453393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1674950059321207343635595 2512425088981811015453393)
                ·
                  refine ⟨1884318816736358261590045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2512425088981811015453393 1884318816736358261590045)
                  ·
                    refine ⟨706619556276134348096267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1884318816736358261590045 706619556276134348096267)
                    ·
                      rfl

theorem cell22_2064205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_2064205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2064205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2064205 prefixEnd_2064205 := by exact prefixLift 2064205
  have htrace : WordTrace (prefixWord ++ tailWord_2064205) baseStart_2064205 baseEnd_2064205 := by
    simpa [prefixWord, tailWord_2064205, baseEnd_2064205] using wordTrace_append hprefix tailTrace_2064205
  have hstable : (prefixWord ++ tailWord_2064205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064205).length < 2 ^ (prefixWord ++ tailWord_2064205).sum := by decide
  have hdescent : baseEnd_2064205 < baseStart_2064205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064263 : List Nat := [1, 1, 4, 2, 4, 2, 2, 1, 5]
def baseStart_2064263 : Nat := 118140960795 + 2064263 * 2 ^ 59
def prefixEnd_2064263 : Nat := 4983230072969 + 3 ^ 40 * 2064263 * 2
def baseEnd_2064263 : Nat := 235546470287147176715363

theorem tailTrace_2064263 : CollatzResearch.WordTrace tailWord_2064263 prefixEnd_2064263 235546470287147176715363 := by
  unfold tailWord_2064263
  simp only [CollatzResearch.WordTrace]
  refine ⟨75289856920535173897725443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50193237947023449265150295 75289856920535173897725443)
  ·
    refine ⟨112934785380802760846588165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75289856920535173897725443 112934785380802760846588165)
    ·
      refine ⟨21175272258900517658735281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112934785380802760846588165 21175272258900517658735281)
      ·
        refine ⟨15881454194175388244051461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21175272258900517658735281 15881454194175388244051461)
        ·
          refine ⟨2977772661407885295759649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15881454194175388244051461 2977772661407885295759649)
          ·
            refine ⟨2233329496055913971819737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2977772661407885295759649 2233329496055913971819737)
            ·
              refine ⟨1674997122041935478864803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2233329496055913971819737 1674997122041935478864803)
              ·
                refine ⟨2512495683062903218297205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1674997122041935478864803 2512495683062903218297205)
                ·
                  refine ⟨235546470287147176715363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2512495683062903218297205 235546470287147176715363)
                  ·
                    rfl

theorem cell22_2064263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 5].length) (baseStart_2064263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2064263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2064263 prefixEnd_2064263 := by exact prefixLift 2064263
  have htrace : WordTrace (prefixWord ++ tailWord_2064263) baseStart_2064263 baseEnd_2064263 := by
    simpa [prefixWord, tailWord_2064263, baseEnd_2064263] using wordTrace_append hprefix tailTrace_2064263
  have hstable : (prefixWord ++ tailWord_2064263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064263).length < 2 ^ (prefixWord ++ tailWord_2064263).sum := by decide
  have hdescent : baseEnd_2064263 < baseStart_2064263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064276 : List Nat := [2, 4, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_2064276 : Nat := 118140960795 + 2064276 * 2 ^ 59
def prefixEnd_2064276 : Nat := 4983230072969 + 3 ^ 40 * 2064276 * 2
def baseEnd_2064276 : Nat := 706643861027113829571049

theorem tailTrace_2064276 : CollatzResearch.WordTrace tailWord_2064276 prefixEnd_2064276 706643861027113829571049 := by
  unfold tailWord_2064276
  simp only [CollatzResearch.WordTrace]
  refine ⟨37645165534744038558974341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50193554046325384745299121 37645165534744038558974341)
  ·
    refine ⟨7058468537764507229807689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37645165534744038558974341 7058468537764507229807689)
    ·
      refine ⟨5293851403323380422355767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7058468537764507229807689 5293851403323380422355767)
      ·
        refine ⟨7940777104985070633533651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5293851403323380422355767 7940777104985070633533651)
        ·
          refine ⟨11911165657477605950300477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7940777104985070633533651 11911165657477605950300477)
          ·
            refine ⟨4466687121554102231362679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11911165657477605950300477 4466687121554102231362679)
            ·
              refine ⟨6700030682331153347044019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4466687121554102231362679 6700030682331153347044019)
              ·
                refine ⟨10050046023496730020566029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6700030682331153347044019 10050046023496730020566029)
                ·
                  refine ⟨3768767258811273757712261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10050046023496730020566029 3768767258811273757712261)
                  ·
                    refine ⟨706643861027113829571049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3768767258811273757712261 706643861027113829571049)
                    ·
                      rfl

theorem cell22_2064276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_2064276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2064276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2064276 prefixEnd_2064276 := by exact prefixLift 2064276
  have htrace : WordTrace (prefixWord ++ tailWord_2064276) baseStart_2064276 baseEnd_2064276 := by
    simpa [prefixWord, tailWord_2064276, baseEnd_2064276] using wordTrace_append hprefix tailTrace_2064276
  have hstable : (prefixWord ++ tailWord_2064276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064276).length < 2 ^ (prefixWord ++ tailWord_2064276).sum := by decide
  have hdescent : baseEnd_2064276 < baseStart_2064276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064368 : List Nat := [2, 1, 1, 1, 3, 2, 4, 4, 1, 3]
def baseStart_2064368 : Nat := 118140960795 + 2064368 * 2 ^ 59
def prefixEnd_2064368 : Nat := 4983230072969 + 3 ^ 40 * 2064368 * 2
def baseEnd_2064368 : Nat := 706675354507256256270767

theorem tailTrace_2064368 : CollatzResearch.WordTrace tailWord_2064368 prefixEnd_2064368 706675354507256256270767 := by
  unfold tailWord_2064368
  simp only [CollatzResearch.WordTrace]
  refine ⟨37646843292577388415148879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50195791056769851220198505 37646843292577388415148879)
  ·
    refine ⟨56470264938866082622723319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37646843292577388415148879 56470264938866082622723319)
    ·
      refine ⟨84705397408299123934084979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56470264938866082622723319 84705397408299123934084979)
      ·
        refine ⟨127058096112448685901127469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84705397408299123934084979 127058096112448685901127469)
        ·
          refine ⟨47646786042168257212922801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127058096112448685901127469 47646786042168257212922801)
          ·
            refine ⟨35735089531626192909692101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47646786042168257212922801 35735089531626192909692101)
            ·
              refine ⟨6700329287179911170567269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35735089531626192909692101 6700329287179911170567269)
              ·
                refine ⟨1256311741346233344481363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6700329287179911170567269 1256311741346233344481363)
                ·
                  refine ⟨1884467612019350016722045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1256311741346233344481363 1884467612019350016722045)
                  ·
                    refine ⟨706675354507256256270767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1884467612019350016722045 706675354507256256270767)
                    ·
                      rfl

theorem cell22_2064368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4, 1, 3].length) (baseStart_2064368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2064368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2064368 prefixEnd_2064368 := by exact prefixLift 2064368
  have htrace : WordTrace (prefixWord ++ tailWord_2064368) baseStart_2064368 baseEnd_2064368 := by
    simpa [prefixWord, tailWord_2064368, baseEnd_2064368] using wordTrace_append hprefix tailTrace_2064368
  have hstable : (prefixWord ++ tailWord_2064368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064368).length < 2 ^ (prefixWord ++ tailWord_2064368).sum := by decide
  have hdescent : baseEnd_2064368 < baseStart_2064368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064379 : List Nat := [1, 1, 1, 1, 1, 3, 6, 1, 2, 5]
def baseStart_2064379 : Nat := 118140960795 + 2064379 * 2 ^ 59
def prefixEnd_2064379 : Nat := 4983230072969 + 3 ^ 40 * 2064379 * 2
def baseEnd_2064379 : Nat := 706679120032055894245733

theorem tailTrace_2064379 : CollatzResearch.WordTrace tailWord_2064379 prefixEnd_2064379 706679120032055894245733 := by
  unfold tailWord_2064379
  simp only [CollatzResearch.WordTrace]
  refine ⟨75294087788114925708948191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50196058525409950472632127 75294087788114925708948191)
  ·
    refine ⟨112941131682172388563422287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75294087788114925708948191 112941131682172388563422287)
    ·
      refine ⟨169411697523258582845133431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112941131682172388563422287 169411697523258582845133431)
      ·
        refine ⟨254117546284887874267700147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169411697523258582845133431 254117546284887874267700147)
        ·
          refine ⟨381176319427331811401550221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254117546284887874267700147 381176319427331811401550221)
          ·
            refine ⟨142941119785249429275581333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 381176319427331811401550221 142941119785249429275581333)
            ·
              refine ⟨6700364989933566997292875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142941119785249429275581333 6700364989933566997292875)
              ·
                refine ⟨10050547484900350495939313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6700364989933566997292875 10050547484900350495939313)
                ·
                  refine ⟨7537910613675262871954485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10050547484900350495939313 7537910613675262871954485)
                  ·
                    refine ⟨706679120032055894245733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7537910613675262871954485 706679120032055894245733)
                    ·
                      rfl

theorem cell22_2064379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 5].length) (baseStart_2064379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2064379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2064379 prefixEnd_2064379 := by exact prefixLift 2064379
  have htrace : WordTrace (prefixWord ++ tailWord_2064379) baseStart_2064379 baseEnd_2064379 := by
    simpa [prefixWord, tailWord_2064379, baseEnd_2064379] using wordTrace_append hprefix tailTrace_2064379
  have hstable : (prefixWord ++ tailWord_2064379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064379).length < 2 ^ (prefixWord ++ tailWord_2064379).sum := by decide
  have hdescent : baseEnd_2064379 < baseStart_2064379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064439 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 3, 6]
def baseStart_2064439 : Nat := 118140960795 + 2064439 * 2 ^ 59
def prefixEnd_2064439 : Nat := 4983230072969 + 3 ^ 40 * 2064439 * 2
def baseEnd_2064439 : Nat := 706699659258235737745549

theorem tailTrace_2064439 : CollatzResearch.WordTrace tailWord_2064439 prefixEnd_2064439 706699659258235737745549 := by
  unfold tailWord_2064439
  simp only [CollatzResearch.WordTrace]
  refine ⟨75296276167897555956132371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50197517445265037304088247 75296276167897555956132371)
  ·
    refine ⟨112944414251846333934198557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75296276167897555956132371 112944414251846333934198557)
    ·
      refine ⟨42354155344442375225324459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112944414251846333934198557 42354155344442375225324459)
      ·
        refine ⟨63531233016663562837986689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42354155344442375225324459 63531233016663562837986689)
        ·
          refine ⟨47648424762497672128490017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63531233016663562837986689 47648424762497672128490017)
          ·
            refine ⟨35736318571873254096367513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47648424762497672128490017 35736318571873254096367513)
            ·
              refine ⟨26802238928904940572275635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35736318571873254096367513 26802238928904940572275635)
              ·
                refine ⟨40203358393357410858413453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26802238928904940572275635 40203358393357410858413453)
                ·
                  refine ⟨15076259397509029071905045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40203358393357410858413453 15076259397509029071905045)
                  ·
                    refine ⟨706699659258235737745549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15076259397509029071905045 706699659258235737745549)
                    ·
                      rfl

theorem cell22_2064439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_2064439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2064439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2064439 prefixEnd_2064439 := by exact prefixLift 2064439
  have htrace : WordTrace (prefixWord ++ tailWord_2064439) baseStart_2064439 baseEnd_2064439 := by
    simpa [prefixWord, tailWord_2064439, baseEnd_2064439] using wordTrace_append hprefix tailTrace_2064439
  have hstable : (prefixWord ++ tailWord_2064439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064439).length < 2 ^ (prefixWord ++ tailWord_2064439).sum := by decide
  have hdescent : baseEnd_2064439 < baseStart_2064439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064477 : List Nat := [1, 4, 4, 1, 1, 1, 4, 2, 4]
def baseStart_2064477 : Nat := 118140960795 + 2064477 * 2 ^ 59
def prefixEnd_2064477 : Nat := 4983230072969 + 3 ^ 40 * 2064477 * 2
def baseEnd_2064477 : Nat := 235570889144938768431811

theorem tailTrace_2064477 : CollatzResearch.WordTrace tailWord_2064477 prefixEnd_2064477 235570889144938768431811 := by
  unfold tailWord_2064477
  simp only [CollatzResearch.WordTrace]
  refine ⟨75297662141759888446015685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50198441427839925630677123 75297662141759888446015685)
  ·
    refine ⟨14118311651579979083627941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75297662141759888446015685 14118311651579979083627941)
    ·
      refine ⟨2647183434671246078180239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14118311651579979083627941 2647183434671246078180239)
      ·
        refine ⟨3970775152006869117270359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2647183434671246078180239 3970775152006869117270359)
        ·
          refine ⟨5956162728010303675905539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3970775152006869117270359 5956162728010303675905539)
          ·
            refine ⟨8934244092015455513858309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5956162728010303675905539 8934244092015455513858309)
            ·
              refine ⟨1675170767252897908848433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8934244092015455513858309 1675170767252897908848433)
              ·
                refine ⟨1256378075439673431636325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1675170767252897908848433 1256378075439673431636325)
                ·
                  refine ⟨235570889144938768431811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1256378075439673431636325 235570889144938768431811)
                  ·
                    rfl

theorem cell22_2064477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_2064477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2064477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2064477 prefixEnd_2064477 := by exact prefixLift 2064477
  have htrace : WordTrace (prefixWord ++ tailWord_2064477) baseStart_2064477 baseEnd_2064477 := by
    simpa [prefixWord, tailWord_2064477, baseEnd_2064477] using wordTrace_append hprefix tailTrace_2064477
  have hstable : (prefixWord ++ tailWord_2064477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064477).length < 2 ^ (prefixWord ++ tailWord_2064477).sum := by decide
  have hdescent : baseEnd_2064477 < baseStart_2064477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064503 : List Nat := [1, 1, 3, 1, 1, 6, 1, 2, 3, 3]
def baseStart_2064503 : Nat := 118140960795 + 2064503 * 2 ^ 59
def prefixEnd_2064503 : Nat := 4983230072969 + 3 ^ 40 * 2064503 * 2
def baseEnd_2064503 : Nat := 706721567766160904145353

theorem tailTrace_2064503 : CollatzResearch.WordTrace tailWord_2064503 prefixEnd_2064503 706721567766160904145353 := by
  unfold tailWord_2064503
  simp only [CollatzResearch.WordTrace]
  refine ⟨75298610439665694886462163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50199073626443796590974775 75298610439665694886462163)
  ·
    refine ⟨112947915659498542329693245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75298610439665694886462163 112947915659498542329693245)
    ·
      refine ⟨42355468372311953373634967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112947915659498542329693245 42355468372311953373634967)
      ·
        refine ⟨63533202558467930060452451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42355468372311953373634967 63533202558467930060452451)
        ·
          refine ⟨95299803837701895090678677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63533202558467930060452451 95299803837701895090678677)
          ·
            refine ⟨4467178304892276332375563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 95299803837701895090678677 4467178304892276332375563)
            ·
              refine ⟨6700767457338414498563345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4467178304892276332375563 6700767457338414498563345)
              ·
                refine ⟨5025575593003810873922509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6700767457338414498563345 5025575593003810873922509)
                ·
                  refine ⟨1884590847376429077720941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5025575593003810873922509 1884590847376429077720941)
                  ·
                    refine ⟨706721567766160904145353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1884590847376429077720941 706721567766160904145353)
                    ·
                      rfl

theorem cell22_2064503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 3, 3].length) (baseStart_2064503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2064503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2064503 prefixEnd_2064503 := by exact prefixLift 2064503
  have htrace : WordTrace (prefixWord ++ tailWord_2064503) baseStart_2064503 baseEnd_2064503 := by
    simpa [prefixWord, tailWord_2064503, baseEnd_2064503] using wordTrace_append hprefix tailTrace_2064503
  have hstable : (prefixWord ++ tailWord_2064503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064503).length < 2 ^ (prefixWord ++ tailWord_2064503).sum := by decide
  have hdescent : baseEnd_2064503 < baseStart_2064503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064516 : List Nat := [2, 3, 2, 1, 2, 1, 2, 2, 7]
def baseStart_2064516 : Nat := 118140960795 + 2064516 * 2 ^ 59
def prefixEnd_2064516 : Nat := 4983230072969 + 3 ^ 40 * 2064516 * 2
def baseEnd_2064516 : Nat := 235575339310611067856771

theorem tailTrace_2064516 : CollatzResearch.WordTrace tailWord_2064516 prefixEnd_2064516 235575339310611067856771 := by
  unfold tailWord_2064516
  simp only [CollatzResearch.WordTrace]
  refine ⟨37649542294309299053342701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50199389725745732071123601 37649542294309299053342701)
  ·
    refine ⟨14118578360365987145003513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37649542294309299053342701 14118578360365987145003513)
    ·
      refine ⟨10588933770274490358752635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14118578360365987145003513 10588933770274490358752635)
      ·
        refine ⟨15883400655411735538128953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10588933770274490358752635 15883400655411735538128953)
        ·
          refine ⟨11912550491558801653596715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15883400655411735538128953 11912550491558801653596715)
          ·
            refine ⟨17868825737338202480395073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11912550491558801653596715 17868825737338202480395073)
            ·
              refine ⟨13401619303003651860296305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17868825737338202480395073 13401619303003651860296305)
              ·
                refine ⟨10051214477252738895222229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13401619303003651860296305 10051214477252738895222229)
                ·
                  refine ⟨235575339310611067856771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10051214477252738895222229 235575339310611067856771)
                  ·
                    rfl

theorem cell22_2064516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_2064516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2064516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2064516 prefixEnd_2064516 := by exact prefixLift 2064516
  have htrace : WordTrace (prefixWord ++ tailWord_2064516) baseStart_2064516 baseEnd_2064516 := by
    simpa [prefixWord, tailWord_2064516, baseEnd_2064516] using wordTrace_append hprefix tailTrace_2064516
  have hstable : (prefixWord ++ tailWord_2064516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064516).length < 2 ^ (prefixWord ++ tailWord_2064516).sum := by decide
  have hdescent : baseEnd_2064516 < baseStart_2064516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064580 : List Nat := [2, 3, 3, 1, 2, 1, 2, 3, 1, 4]
def baseStart_2064580 : Nat := 118140960795 + 2064580 * 2 ^ 59
def prefixEnd_2064580 : Nat := 4983230072969 + 3 ^ 40 * 2064580 * 2
def baseEnd_2064580 : Nat := 706747926439758369970117

theorem tailTrace_2064580 : CollatzResearch.WordTrace tailWord_2064580 prefixEnd_2064580 706747926439758369970117 := by
  unfold tailWord_2064580
  simp only [CollatzResearch.WordTrace]
  refine ⟨37650709430193368518507597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50200945906924491358010129 37650709430193368518507597)
  ·
    refine ⟨14119016036322513194440349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37650709430193368518507597 14119016036322513194440349)
    ·
      refine ⟨5294631013620942447915131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14119016036322513194440349 5294631013620942447915131)
      ·
        refine ⟨7941946520431413671872697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5294631013620942447915131 7941946520431413671872697)
        ·
          refine ⟨5956459890323560253904523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7941946520431413671872697 5956459890323560253904523)
          ·
            refine ⟨8934689835485340380856785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5956459890323560253904523 8934689835485340380856785)
            ·
              refine ⟨6701017376614005285642589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8934689835485340380856785 6701017376614005285642589)
              ·
                refine ⟨2512881516230251982115971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6701017376614005285642589 2512881516230251982115971)
                ·
                  refine ⟨3769322274345377973173957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2512881516230251982115971 3769322274345377973173957)
                  ·
                    refine ⟨706747926439758369970117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3769322274345377973173957 706747926439758369970117)
                    ·
                      rfl

theorem cell22_2064580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_2064580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2064580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2064580 prefixEnd_2064580 := by exact prefixLift 2064580
  have htrace : WordTrace (prefixWord ++ tailWord_2064580) baseStart_2064580 baseEnd_2064580 := by
    simpa [prefixWord, tailWord_2064580, baseEnd_2064580] using wordTrace_append hprefix tailTrace_2064580
  have hstable : (prefixWord ++ tailWord_2064580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064580).length < 2 ^ (prefixWord ++ tailWord_2064580).sum := by decide
  have hdescent : baseEnd_2064580 < baseStart_2064580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064593 : List Nat := [1, 2, 2, 1, 2, 2, 4, 1, 4, 3]
def baseStart_2064593 : Nat := 118140960795 + 2064593 * 2 ^ 59
def prefixEnd_2064593 : Nat := 4983230072969 + 3 ^ 40 * 2064593 * 2
def baseEnd_2064593 : Nat := 706752376605430669395077

theorem tailTrace_2064593 : CollatzResearch.WordTrace tailWord_2064593 prefixEnd_2064593 706752376605430669395077 := by
  unfold tailWord_2064593
  simp only [CollatzResearch.WordTrace]
  refine ⟨75301893009339640257238433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50201262006226426838158955 75301893009339640257238433)
  ·
    refine ⟨56476419757004730192928825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75301893009339640257238433 56476419757004730192928825)
    ·
      refine ⟨42357314817753547644696619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56476419757004730192928825 42357314817753547644696619)
      ·
        refine ⟨63535972226630321467044929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42357314817753547644696619 63535972226630321467044929)
        ·
          refine ⟨47651979169972741100283697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63535972226630321467044929 47651979169972741100283697)
          ·
            refine ⟨35738984377479555825212773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47651979169972741100283697 35738984377479555825212773)
            ·
              refine ⟨6701059570777416717227395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35738984377479555825212773 6701059570777416717227395)
              ·
                refine ⟨10051589356166125075841093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6701059570777416717227395 10051589356166125075841093)
                ·
                  refine ⟨1884673004281148451720205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10051589356166125075841093 1884673004281148451720205)
                  ·
                    refine ⟨706752376605430669395077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1884673004281148451720205 706752376605430669395077)
                    ·
                      rfl

theorem cell22_2064593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4, 3].length) (baseStart_2064593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2064593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2064593 prefixEnd_2064593 := by exact prefixLift 2064593
  have htrace : WordTrace (prefixWord ++ tailWord_2064593) baseStart_2064593 baseEnd_2064593 := by
    simpa [prefixWord, tailWord_2064593, baseEnd_2064593] using wordTrace_append hprefix tailTrace_2064593
  have hstable : (prefixWord ++ tailWord_2064593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064593).length < 2 ^ (prefixWord ++ tailWord_2064593).sum := by decide
  have hdescent : baseEnd_2064593 < baseStart_2064593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064689 : List Nat := [1, 2, 2, 3, 4, 1, 2, 3, 1, 3]
def baseStart_2064689 : Nat := 118140960795 + 2064689 * 2 ^ 59
def prefixEnd_2064689 : Nat := 4983230072969 + 3 ^ 40 * 2064689 * 2
def baseEnd_2064689 : Nat := 706785239367318418994783

theorem tailTrace_2064689 : CollatzResearch.WordTrace tailWord_2064689 prefixEnd_2064689 706785239367318418994783 := by
  unfold tailWord_2064689
  simp only [CollatzResearch.WordTrace]
  refine ⟨75305394416991848652733121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50203596277994565768488747 75305394416991848652733121)
  ·
    refine ⟨56479045812743886489549841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75305394416991848652733121 56479045812743886489549841)
    ·
      refine ⟨42359284359557914867162381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56479045812743886489549841 42359284359557914867162381)
      ·
        refine ⟨15884731634834218075185893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42359284359557914867162381 15884731634834218075185893)
        ·
          refine ⟨2978387181531415889097355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15884731634834218075185893 2978387181531415889097355)
          ·
            refine ⟨4467580772297123833646033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2978387181531415889097355 4467580772297123833646033)
            ·
              refine ⟨3350685579222842875234525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4467580772297123833646033 3350685579222842875234525)
              ·
                refine ⟨1256507092208566078212947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3350685579222842875234525 1256507092208566078212947)
                ·
                  refine ⟨1884760638312849117319421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1256507092208566078212947 1884760638312849117319421)
                  ·
                    refine ⟨706785239367318418994783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1884760638312849117319421 706785239367318418994783)
                    ·
                      rfl

theorem cell22_2064689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 3, 1, 3].length) (baseStart_2064689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2064689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2064689 prefixEnd_2064689 := by exact prefixLift 2064689
  have htrace : WordTrace (prefixWord ++ tailWord_2064689) baseStart_2064689 baseEnd_2064689 := by
    simpa [prefixWord, tailWord_2064689, baseEnd_2064689] using wordTrace_append hprefix tailTrace_2064689
  have hstable : (prefixWord ++ tailWord_2064689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064689).length < 2 ^ (prefixWord ++ tailWord_2064689).sum := by decide
  have hdescent : baseEnd_2064689 < baseStart_2064689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064702 : List Nat := [4, 2, 1, 2, 1, 4, 1, 2, 5]
def baseStart_2064702 : Nat := 118140960795 + 2064702 * 2 ^ 59
def prefixEnd_2064702 : Nat := 4983230072969 + 3 ^ 40 * 2064702 * 2
def baseEnd_2064702 : Nat := 235596563177663572806581

theorem tailTrace_2064702 : CollatzResearch.WordTrace tailWord_2064702 prefixEnd_2064702 235596563177663572806581 := by
  unfold tailWord_2064702
  simp only [CollatzResearch.WordTrace]
  refine ⟨9413233570743093984119545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50203912377296501248637573 9413233570743093984119545)
  ·
    refine ⟨7059925178057320488089659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9413233570743093984119545 7059925178057320488089659)
    ·
      refine ⟨10589887767085980732134489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7059925178057320488089659 10589887767085980732134489)
      ·
        refine ⟨7942415825314485549100867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10589887767085980732134489 7942415825314485549100867)
        ·
          refine ⟨11913623737971728323651301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7942415825314485549100867 11913623737971728323651301)
          ·
            refine ⟨2233804450869699060684619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11913623737971728323651301 2233804450869699060684619)
            ·
              refine ⟨3350706676304548591026929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2233804450869699060684619 3350706676304548591026929)
              ·
                refine ⟨2513030007228411443270197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3350706676304548591026929 2513030007228411443270197)
                ·
                  refine ⟨235596563177663572806581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2513030007228411443270197 235596563177663572806581)
                  ·
                    rfl

theorem cell22_2064702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_2064702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2064702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2064702 prefixEnd_2064702 := by exact prefixLift 2064702
  have htrace : WordTrace (prefixWord ++ tailWord_2064702) baseStart_2064702 baseEnd_2064702 := by
    simpa [prefixWord, tailWord_2064702, baseEnd_2064702] using wordTrace_append hprefix tailTrace_2064702
  have hstable : (prefixWord ++ tailWord_2064702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064702).length < 2 ^ (prefixWord ++ tailWord_2064702).sum := by decide
  have hdescent : baseEnd_2064702 < baseStart_2064702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064728 : List Nat := [2, 1, 2, 2, 1, 1, 2, 5, 1, 5]
def baseStart_2064728 : Nat := 118140960795 + 2064728 * 2 ^ 59
def prefixEnd_2064728 : Nat := 4983230072969 + 3 ^ 40 * 2064728 * 2
def baseEnd_2064728 : Nat := 706798589864335317269663

theorem tailTrace_2064728 : CollatzResearch.WordTrace tailWord_2064728 prefixEnd_2064728 706798589864335317269663 := by
  unfold tailWord_2064728
  simp only [CollatzResearch.WordTrace]
  refine ⟨37653408431925279156701419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50204544575900372208935225 37653408431925279156701419)
  ·
    refine ⟨56480112647887918735052129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37653408431925279156701419 56480112647887918735052129)
    ·
      refine ⟨42360084485915939051289097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56480112647887918735052129 42360084485915939051289097)
      ·
        refine ⟨31770063364436954288466823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42360084485915939051289097 31770063364436954288466823)
        ·
          refine ⟨47655095046655431432700235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31770063364436954288466823 47655095046655431432700235)
          ·
            refine ⟨71482642569983147149050353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47655095046655431432700235 71482642569983147149050353)
            ·
              refine ⟨53611981927487360361787765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71482642569983147149050353 53611981927487360361787765)
              ·
                refine ⟨5026123305701940033917603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53611981927487360361787765 5026123305701940033917603)
                ·
                  refine ⟨7539184958552910050876405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5026123305701940033917603 7539184958552910050876405)
                  ·
                    refine ⟨706798589864335317269663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7539184958552910050876405 706798589864335317269663)
                    ·
                      rfl

theorem cell22_2064728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_2064728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2064728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2064728 prefixEnd_2064728 := by exact prefixLift 2064728
  have htrace : WordTrace (prefixWord ++ tailWord_2064728) baseStart_2064728 baseEnd_2064728 := by
    simpa [prefixWord, tailWord_2064728, baseEnd_2064728] using wordTrace_append hprefix tailTrace_2064728
  have hstable : (prefixWord ++ tailWord_2064728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064728).length < 2 ^ (prefixWord ++ tailWord_2064728).sum := by decide
  have hdescent : baseEnd_2064728 < baseStart_2064728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064779 : List Nat := [1, 1, 1, 1, 4, 6, 2, 1, 2, 3]
def baseStart_2064779 : Nat := 118140960795 + 2064779 * 2 ^ 59
def prefixEnd_2064779 : Nat := 4983230072969 + 3 ^ 40 * 2064779 * 2
def baseEnd_2064779 : Nat := 706816048206588184244507

theorem tailTrace_2064779 : CollatzResearch.WordTrace tailWord_2064779 prefixEnd_2064779 706816048206588184244507 := by
  unfold tailWord_2064779
  simp only [CollatzResearch.WordTrace]
  refine ⟨75308676986665794023509391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50205784657777196015672927 75308676986665794023509391)
  ·
    refine ⟨112963015479998691035264087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75308676986665794023509391 112963015479998691035264087)
    ·
      refine ⟨169444523219998036552896131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112963015479998691035264087 169444523219998036552896131)
      ·
        refine ⟨254166784829997054829344197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169444523219998036552896131 254166784829997054829344197)
        ·
          refine ⟨47656272155624447780502037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 254166784829997054829344197 47656272155624447780502037)
          ·
            refine ⟨2233887757294895989711033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47656272155624447780502037 2233887757294895989711033)
            ·
              refine ⟨1675415817971171992283275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2233887757294895989711033 1675415817971171992283275)
              ·
                refine ⟨2513123726956757988424913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1675415817971171992283275 2513123726956757988424913)
                ·
                  refine ⟨1884842795217568491318685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2513123726956757988424913 1884842795217568491318685)
                  ·
                    refine ⟨706816048206588184244507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1884842795217568491318685 706816048206588184244507)
                    ·
                      rfl

theorem cell22_2064779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 2, 3].length) (baseStart_2064779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2064779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2064779 prefixEnd_2064779 := by exact prefixLift 2064779
  have htrace : WordTrace (prefixWord ++ tailWord_2064779) baseStart_2064779 baseEnd_2064779 := by
    simpa [prefixWord, tailWord_2064779, baseEnd_2064779] using wordTrace_append hprefix tailTrace_2064779
  have hstable : (prefixWord ++ tailWord_2064779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064779).length < 2 ^ (prefixWord ++ tailWord_2064779).sum := by decide
  have hdescent : baseEnd_2064779 < baseStart_2064779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064897 : List Nat := [1, 2, 4, 1, 3, 1, 3, 1, 1, 5]
def baseStart_2064897 : Nat := 118140960795 + 2064897 * 2 ^ 59
def prefixEnd_2064897 : Nat := 4983230072969 + 3 ^ 40 * 2064897 * 2
def baseEnd_2064897 : Nat := 706856442018075209794145

theorem tailTrace_2064897 : CollatzResearch.WordTrace tailWord_2064897 prefixEnd_2064897 706856442018075209794145 := by
  unfold tailWord_2064897
  simp only [CollatzResearch.WordTrace]
  refine ⟨75312980800238300176304945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50208653866825533450869963 75312980800238300176304945)
  ·
    refine ⟨56484735600178725132228709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75312980800238300176304945 56484735600178725132228709)
    ·
      refine ⟨10590887925033510962292883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56484735600178725132228709 10590887925033510962292883)
      ·
        refine ⟨15886331887550266443439325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10590887925033510962292883 15886331887550266443439325)
        ·
          refine ⟨5957374457831349916289747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15886331887550266443439325 5957374457831349916289747)
          ·
            refine ⟨8936061686747024874434621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5957374457831349916289747 8936061686747024874434621)
            ·
              refine ⟨3351023132530134327912983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8936061686747024874434621 3351023132530134327912983)
              ·
                refine ⟨5026534698795201491869475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3351023132530134327912983 5026534698795201491869475)
                ·
                  refine ⟨7539802048192802237804213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5026534698795201491869475 7539802048192802237804213)
                  ·
                    refine ⟨706856442018075209794145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7539802048192802237804213 706856442018075209794145)
                    ·
                      rfl

theorem cell22_2064897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_2064897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2064897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2064897 prefixEnd_2064897 := by exact prefixLift 2064897
  have htrace : WordTrace (prefixWord ++ tailWord_2064897) baseStart_2064897 baseEnd_2064897 := by
    simpa [prefixWord, tailWord_2064897, baseEnd_2064897] using wordTrace_append hprefix tailTrace_2064897
  have hstable : (prefixWord ++ tailWord_2064897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064897).length < 2 ^ (prefixWord ++ tailWord_2064897).sum := by decide
  have hdescent : baseEnd_2064897 < baseStart_2064897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064916 : List Nat := [2, 4, 3, 1, 1, 1, 3, 3, 4]
def baseStart_2064916 : Nat := 118140960795 + 2064916 * 2 ^ 59
def prefixEnd_2064916 : Nat := 4983230072969 + 3 ^ 40 * 2064916 * 2
def baseEnd_2064916 : Nat := 235620982035455164523029

theorem tailTrace_2064916 : CollatzResearch.WordTrace tailWord_2064916 prefixEnd_2064916 235620982035455164523029 := by
  unfold tailWord_2064916
  simp only [CollatzResearch.WordTrace]
  refine ⟨37656836893584733210623301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50209115858112977614164401 37656836893584733210623301)
  ·
    refine ⟨7060656917547137476991869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37656836893584733210623301 7060656917547137476991869)
    ·
      refine ⟨2647746344080176553871951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7060656917547137476991869 2647746344080176553871951)
      ·
        refine ⟨3971619516120264830807927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2647746344080176553871951 3971619516120264830807927)
        ·
          refine ⟨5957429274180397246211891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3971619516120264830807927 5957429274180397246211891)
          ·
            refine ⟨8936143911270595869317837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5957429274180397246211891 8936143911270595869317837)
            ·
              refine ⟨3351053966726473450994189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8936143911270595869317837 3351053966726473450994189)
              ·
                refine ⟨1256645237522427544122821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3351053966726473450994189 1256645237522427544122821)
                ·
                  refine ⟨235620982035455164523029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1256645237522427544122821 235620982035455164523029)
                  ·
                    rfl

theorem cell22_2064916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_2064916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2064916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2064916 prefixEnd_2064916 := by exact prefixLift 2064916
  have htrace : WordTrace (prefixWord ++ tailWord_2064916) baseStart_2064916 baseEnd_2064916 := by
    simpa [prefixWord, tailWord_2064916, baseEnd_2064916] using wordTrace_append hprefix tailTrace_2064916
  have hstable : (prefixWord ++ tailWord_2064916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064916).length < 2 ^ (prefixWord ++ tailWord_2064916).sum := by decide
  have hdescent : baseEnd_2064916 < baseStart_2064916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064948 : List Nat := [2, 5, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_2064948 : Nat := 118140960795 + 2064948 * 2 ^ 59
def prefixEnd_2064948 : Nat := 4983230072969 + 3 ^ 40 * 2064948 * 2
def baseEnd_2064948 : Nat := 706873900360328076768989

theorem tailTrace_2064948 : CollatzResearch.WordTrace tailWord_2064948 prefixEnd_2064948 706873900360328076768989 := by
  unfold tailWord_2064948
  simp only [CollatzResearch.WordTrace]
  refine ⟨37657420461526767943205749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50209893948702357257607665 37657420461526767943205749)
  ·
    refine ⟨3530383168268134494675539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37657420461526767943205749 3530383168268134494675539)
    ·
      refine ⟨5295574752402201742013309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3530383168268134494675539 5295574752402201742013309)
      ·
        refine ⟨1985840532150825653254991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5295574752402201742013309 1985840532150825653254991)
        ·
          refine ⟨2978760798226238479882487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1985840532150825653254991 2978760798226238479882487)
          ·
            refine ⟨4468141197339357719823731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2978760798226238479882487 4468141197339357719823731)
            ·
              refine ⟨6702211796009036579735597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4468141197339357719823731 6702211796009036579735597)
              ·
                refine ⟨2513329423503388717400849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6702211796009036579735597 2513329423503388717400849)
                ·
                  refine ⟨1884997067627541538050637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2513329423503388717400849 1884997067627541538050637)
                  ·
                    refine ⟨706873900360328076768989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1884997067627541538050637 706873900360328076768989)
                    ·
                      rfl

theorem cell22_2064948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_2064948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2064948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2064948 prefixEnd_2064948 := by exact prefixLift 2064948
  have htrace : WordTrace (prefixWord ++ tailWord_2064948) baseStart_2064948 baseEnd_2064948 := by
    simpa [prefixWord, tailWord_2064948, baseEnd_2064948] using wordTrace_append hprefix tailTrace_2064948
  have hstable : (prefixWord ++ tailWord_2064948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064948).length < 2 ^ (prefixWord ++ tailWord_2064948).sum := by decide
  have hdescent : baseEnd_2064948 < baseStart_2064948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064993 : List Nat := [1, 2, 3, 1, 1, 6, 2, 2, 1, 3]
def baseStart_2064993 : Nat := 118140960795 + 2064993 * 2 ^ 59
def prefixEnd_2064993 : Nat := 4983230072969 + 3 ^ 40 * 2064993 * 2
def baseEnd_2064993 : Nat := 706889304779962959393851

theorem tailTrace_2064993 : CollatzResearch.WordTrace tailWord_2064993 prefixEnd_2064993 706889304779962959393851 := by
  unfold tailWord_2064993
  simp only [CollatzResearch.WordTrace]
  refine ⟨75316482207890508571799633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50210988138593672381199755 75316482207890508571799633)
  ·
    refine ⟨56487361655917881428849725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75316482207890508571799633 56487361655917881428849725)
    ·
      refine ⟨21182760620969205535818647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56487361655917881428849725 21182760620969205535818647)
      ·
        refine ⟨31774140931453808303727971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21182760620969205535818647 31774140931453808303727971)
        ·
          refine ⟨47661211397180712455591957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31774140931453808303727971 47661211397180712455591957)
          ·
            refine ⟨2234119284242845896355873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47661211397180712455591957 2234119284242845896355873)
            ·
              refine ⟨1675589463182134422266905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2234119284242845896355873 1675589463182134422266905)
              ·
                refine ⟨1256692097386600816700179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1675589463182134422266905 1256692097386600816700179)
                ·
                  refine ⟨1885038146079901225050269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1256692097386600816700179 1885038146079901225050269)
                  ·
                    refine ⟨706889304779962959393851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1885038146079901225050269 706889304779962959393851)
                    ·
                      rfl

theorem cell22_2064993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_2064993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2064993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2064993 prefixEnd_2064993 := by exact prefixLift 2064993
  have htrace : WordTrace (prefixWord ++ tailWord_2064993) baseStart_2064993 baseEnd_2064993 := by
    simpa [prefixWord, tailWord_2064993, baseEnd_2064993] using wordTrace_append hprefix tailTrace_2064993
  have hstable : (prefixWord ++ tailWord_2064993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064993).length < 2 ^ (prefixWord ++ tailWord_2064993).sum := by decide
  have hdescent : baseEnd_2064993 < baseStart_2064993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065002 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 5, 4]
def baseStart_2065002 : Nat := 118140960795 + 2065002 * 2 ^ 59
def prefixEnd_2065002 : Nat := 4983230072969 + 3 ^ 40 * 2065002 * 2
def baseEnd_2065002 : Nat := 706892385663889935918823

theorem tailTrace_2065002 : CollatzResearch.WordTrace tailWord_2065002 prefixEnd_2065002 706892385663889935918823 := by
  unfold tailWord_2065002
  simp only [CollatzResearch.WordTrace]
  refine ⟨18829202616214475777219315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50211206976571935405918173 18829202616214475777219315)
  ·
    refine ⟨28243803924321713665828973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18829202616214475777219315 28243803924321713665828973)
    ·
      refine ⟨10591426471620642624685865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28243803924321713665828973 10591426471620642624685865)
      ·
        refine ⟨7943569853715481968514399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10591426471620642624685865 7943569853715481968514399)
        ·
          refine ⟨11915354780573222952771599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7943569853715481968514399 11915354780573222952771599)
          ·
            refine ⟨17873032170859834429157399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11915354780573222952771599 17873032170859834429157399)
            ·
              refine ⟨26809548256289751643736099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17873032170859834429157399 26809548256289751643736099)
              ·
                refine ⟨40214322384434627465604149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26809548256289751643736099 40214322384434627465604149)
                ·
                  refine ⟨3770092723540746324900389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40214322384434627465604149 3770092723540746324900389)
                  ·
                    refine ⟨706892385663889935918823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3770092723540746324900389 706892385663889935918823)
                    ·
                      rfl

theorem cell22_2065002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_2065002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2065002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2065002 prefixEnd_2065002 := by exact prefixLift 2065002
  have htrace : WordTrace (prefixWord ++ tailWord_2065002) baseStart_2065002 baseEnd_2065002 := by
    simpa [prefixWord, tailWord_2065002, baseEnd_2065002] using wordTrace_append hprefix tailTrace_2065002
  have hstable : (prefixWord ++ tailWord_2065002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065002).length < 2 ^ (prefixWord ++ tailWord_2065002).sum := by decide
  have hdescent : baseEnd_2065002 < baseStart_2065002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065017 : List Nat := [1, 2, 1, 3, 3, 3, 1, 2, 6]
def baseStart_2065017 : Nat := 118140960795 + 2065017 * 2 ^ 59
def prefixEnd_2065017 : Nat := 4983230072969 + 3 ^ 40 * 2065017 * 2
def baseEnd_2065017 : Nat := 235632506823478298931259

theorem tailTrace_2065017 : CollatzResearch.WordTrace tailWord_2065017 prefixEnd_2065017 235632506823478298931259 := by
  unfold tailWord_2065017
  simp only [CollatzResearch.WordTrace]
  refine ⟨75317357559803560670673305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50211571706535707113782203 75317357559803560670673305)
  ·
    refine ⟨56488018169852670503004979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75317357559803560670673305 56488018169852670503004979)
    ·
      refine ⟨84732027254779005754507469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56488018169852670503004979 84732027254779005754507469)
      ·
        refine ⟨31774510220542127157940301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84732027254779005754507469 31774510220542127157940301)
        ·
          refine ⟨11915441332703297684227613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31774510220542127157940301 11915441332703297684227613)
          ·
            refine ⟨4468290499763736631585355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11915441332703297684227613 4468290499763736631585355)
            ·
              refine ⟨6702435749645604947378033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4468290499763736631585355 6702435749645604947378033)
              ·
                refine ⟨5026826812234203710533525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6702435749645604947378033 5026826812234203710533525)
                ·
                  refine ⟨235632506823478298931259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5026826812234203710533525 235632506823478298931259)
                  ·
                    rfl

theorem cell22_2065017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 6].length) (baseStart_2065017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2065017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2065017 prefixEnd_2065017 := by exact prefixLift 2065017
  have htrace : WordTrace (prefixWord ++ tailWord_2065017) baseStart_2065017 baseEnd_2065017 := by
    simpa [prefixWord, tailWord_2065017, baseEnd_2065017] using wordTrace_append hprefix tailTrace_2065017
  have hstable : (prefixWord ++ tailWord_2065017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065017).length < 2 ^ (prefixWord ++ tailWord_2065017).sum := by decide
  have hdescent : baseEnd_2065017 < baseStart_2065017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065047 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 4, 4]
def baseStart_2065047 : Nat := 118140960795 + 2065047 * 2 ^ 59
def prefixEnd_2065047 : Nat := 4983230072969 + 3 ^ 40 * 2065047 * 2
def baseEnd_2065047 : Nat := 706907790083524818543685

theorem tailTrace_2065047 : CollatzResearch.WordTrace tailWord_2065047 prefixEnd_2065047 706907790083524818543685 := by
  unfold tailWord_2065047
  simp only [CollatzResearch.WordTrace]
  refine ⟨75318451749694875794265395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50212301166463250529510263 75318451749694875794265395)
  ·
    refine ⟨112977677624542313691398093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75318451749694875794265395 112977677624542313691398093)
    ·
      refine ⟨42366629109203367634274285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112977677624542313691398093 42366629109203367634274285)
      ·
        refine ⟨15887485915951262862852857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42366629109203367634274285 15887485915951262862852857)
        ·
          refine ⟨11915614436963447147139643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15887485915951262862852857 11915614436963447147139643)
          ·
            refine ⟨17873421655445170720709465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11915614436963447147139643 17873421655445170720709465)
            ·
              refine ⟨13405066241583878040532099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17873421655445170720709465 13405066241583878040532099)
              ·
                refine ⟨20107599362375817060798149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13405066241583878040532099 20107599362375817060798149)
                ·
                  refine ⟨3770174880445465698899653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20107599362375817060798149 3770174880445465698899653)
                  ·
                    refine ⟨706907790083524818543685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3770174880445465698899653 706907790083524818543685)
                    ·
                      rfl

theorem cell22_2065047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_2065047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2065047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2065047 prefixEnd_2065047 := by exact prefixLift 2065047
  have htrace : WordTrace (prefixWord ++ tailWord_2065047) baseStart_2065047 baseEnd_2065047 := by
    simpa [prefixWord, tailWord_2065047, baseEnd_2065047] using wordTrace_append hprefix tailTrace_2065047
  have hstable : (prefixWord ++ tailWord_2065047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065047).length < 2 ^ (prefixWord ++ tailWord_2065047).sum := by decide
  have hdescent : baseEnd_2065047 < baseStart_2065047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065111 : List Nat := [1, 1, 3, 2, 1, 6, 1, 1, 3, 3]
def baseStart_2065111 : Nat := 118140960795 + 2065111 * 2 ^ 59
def prefixEnd_2065111 : Nat := 4983230072969 + 3 ^ 40 * 2065111 * 2
def baseEnd_2065111 : Nat := 706929698591449984943489

theorem tailTrace_2065111 : CollatzResearch.WordTrace tailWord_2065111 prefixEnd_2065111 706929698591449984943489 := by
  unfold tailWord_2065111
  simp only [CollatzResearch.WordTrace]
  refine ⟨75320786021463014724595187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50213857347642009816396791 75320786021463014724595187)
  ·
    refine ⟨112981179032194522086892781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75320786021463014724595187 112981179032194522086892781)
    ·
      refine ⟨42367942137072945782584793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112981179032194522086892781 42367942137072945782584793)
      ·
        refine ⟨31775956602804709336938595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42367942137072945782584793 31775956602804709336938595)
        ·
          refine ⟨47663934904207064005407893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31775956602804709336938595 47663934904207064005407893)
          ·
            refine ⟨2234246948634706125253495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47663934904207064005407893 2234246948634706125253495)
            ·
              refine ⟨3351370422952059187880243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2234246948634706125253495 3351370422952059187880243)
              ·
                refine ⟨5027055634428088781820365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3351370422952059187880243 5027055634428088781820365)
                ·
                  refine ⟨1885145862910533293182637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5027055634428088781820365 1885145862910533293182637)
                  ·
                    refine ⟨706929698591449984943489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1885145862910533293182637 706929698591449984943489)
                    ·
                      rfl

theorem cell22_2065111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 3, 3].length) (baseStart_2065111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2065111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2065111 prefixEnd_2065111 := by exact prefixLift 2065111
  have htrace : WordTrace (prefixWord ++ tailWord_2065111) baseStart_2065111 baseEnd_2065111 := by
    simpa [prefixWord, tailWord_2065111, baseEnd_2065111] using wordTrace_append hprefix tailTrace_2065111
  have hstable : (prefixWord ++ tailWord_2065111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065111).length < 2 ^ (prefixWord ++ tailWord_2065111).sum := by decide
  have hdescent : baseEnd_2065111 < baseStart_2065111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065124 : List Nat := [2, 3, 1, 1, 1, 5, 1, 3, 5]
def baseStart_2065124 : Nat := 118140960795 + 2065124 * 2 ^ 59
def prefixEnd_2065124 : Nat := 4983230072969 + 3 ^ 40 * 2065124 * 2
def baseEnd_2065124 : Nat := 235644716252374094789483

theorem tailTrace_2065124 : CollatzResearch.WordTrace tailWord_2065124 prefixEnd_2065124 235644716252374094789483 := by
  unfold tailWord_2065124
  simp only [CollatzResearch.WordTrace]
  refine ⟨37660630085207958972409213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50214173446943945296545617 37660630085207958972409213)
  ·
    refine ⟨14122736281952984614653455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37660630085207958972409213 14122736281952984614653455)
    ·
      refine ⟨21184104422929476921980183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14122736281952984614653455 21184104422929476921980183)
      ·
        refine ⟨31776156634394215382970275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21184104422929476921980183 31776156634394215382970275)
        ·
          refine ⟨47664234951591323074455413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31776156634394215382970275 47664234951591323074455413)
          ·
            refine ⟨4468522026711686538230195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47664234951591323074455413 4468522026711686538230195)
            ·
              refine ⟨6702783040067529807345293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4468522026711686538230195 6702783040067529807345293)
              ·
                refine ⟨2513543640025323677754485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6702783040067529807345293 2513543640025323677754485)
                ·
                  refine ⟨235644716252374094789483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2513543640025323677754485 235644716252374094789483)
                  ·
                    rfl

theorem cell22_2065124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_2065124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2065124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2065124 prefixEnd_2065124 := by exact prefixLift 2065124
  have htrace : WordTrace (prefixWord ++ tailWord_2065124) baseStart_2065124 baseEnd_2065124 := by
    simpa [prefixWord, tailWord_2065124, baseEnd_2065124] using wordTrace_append hprefix tailTrace_2065124
  have hstable : (prefixWord ++ tailWord_2065124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065124).length < 2 ^ (prefixWord ++ tailWord_2065124).sum := by decide
  have hdescent : baseEnd_2065124 < baseStart_2065124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065167 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 3, 5]
def baseStart_2065167 : Nat := 118140960795 + 2065167 * 2 ^ 59
def prefixEnd_2065167 : Nat := 4983230072969 + 3 ^ 40 * 2065167 * 2
def baseEnd_2065167 : Nat := 706948868535884505543317

theorem tailTrace_2065167 : CollatzResearch.WordTrace tailWord_2065167 prefixEnd_2065167 706948868535884505543317 := by
  unfold tailWord_2065167
  simp only [CollatzResearch.WordTrace]
  refine ⟨75322828509260136288633755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50215219006173424192422503 75322828509260136288633755)
  ·
    refine ⟨112984242763890204432950633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75322828509260136288633755 112984242763890204432950633)
    ·
      refine ⟨84738182072917653324712975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112984242763890204432950633 84738182072917653324712975)
      ·
        refine ⟨127107273109376479987069463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84738182072917653324712975 127107273109376479987069463)
        ·
          refine ⟨190660909664064719980604195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127107273109376479987069463 190660909664064719980604195)
          ·
            refine ⟨285991364496097079970906293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190660909664064719980604195 285991364496097079970906293)
            ·
              refine ⟨26811690421509101247272465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 285991364496097079970906293 26811690421509101247272465)
              ·
                refine ⟨20108767816131825935454349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26811690421509101247272465 20108767816131825935454349)
                ·
                  refine ⟨7540787931049434725795381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20108767816131825935454349 7540787931049434725795381)
                  ·
                    refine ⟨706948868535884505543317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7540787931049434725795381 706948868535884505543317)
                    ·
                      rfl

theorem cell22_2065167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 5].length) (baseStart_2065167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2065167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2065167 prefixEnd_2065167 := by exact prefixLift 2065167
  have htrace : WordTrace (prefixWord ++ tailWord_2065167) baseStart_2065167 baseEnd_2065167 := by
    simpa [prefixWord, tailWord_2065167, baseEnd_2065167] using wordTrace_append hprefix tailTrace_2065167
  have hstable : (prefixWord ++ tailWord_2065167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065167).length < 2 ^ (prefixWord ++ tailWord_2065167).sum := by decide
  have hdescent : baseEnd_2065167 < baseStart_2065167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065184 : List Nat := [2, 1, 1, 5, 1, 2, 1, 3, 1, 5]
def baseStart_2065184 : Nat := 118140960795 + 2065184 * 2 ^ 59
def prefixEnd_2065184 : Nat := 4983230072969 + 3 ^ 40 * 2065184 * 2
def baseEnd_2065184 : Nat := 706954687983302127868265

theorem tailTrace_2065184 : CollatzResearch.WordTrace tailWord_2065184 prefixEnd_2065184 706954687983302127868265 := by
  unfold tailWord_2065184
  simp only [CollatzResearch.WordTrace]
  refine ⟨37661724275099274096001303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50215632366799032128001737 37661724275099274096001303)
  ·
    refine ⟨56492586412648911144001955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37661724275099274096001303 56492586412648911144001955)
    ·
      refine ⟨84738879618973366716002933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56492586412648911144001955 84738879618973366716002933)
      ·
        refine ⟨7944269964278753129625275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84738879618973366716002933 7944269964278753129625275)
        ·
          refine ⟨11916404946418129694437913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7944269964278753129625275 11916404946418129694437913)
          ·
            refine ⟨8937303709813597270828435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11916404946418129694437913 8937303709813597270828435)
            ·
              refine ⟨13405955564720395906242653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8937303709813597270828435 13405955564720395906242653)
              ·
                refine ⟨5027233336770148464840995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13405955564720395906242653 5027233336770148464840995)
                ·
                  refine ⟨7540850005155222697261493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5027233336770148464840995 7540850005155222697261493)
                  ·
                    refine ⟨706954687983302127868265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7540850005155222697261493 706954687983302127868265)
                    ·
                      rfl

theorem cell22_2065184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 1, 5].length) (baseStart_2065184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2065184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2065184 prefixEnd_2065184 := by exact prefixLift 2065184
  have htrace : WordTrace (prefixWord ++ tailWord_2065184) baseStart_2065184 baseEnd_2065184 := by
    simpa [prefixWord, tailWord_2065184, baseEnd_2065184] using wordTrace_append hprefix tailTrace_2065184
  have hstable : (prefixWord ++ tailWord_2065184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065184).length < 2 ^ (prefixWord ++ tailWord_2065184).sum := by decide
  have hdescent : baseEnd_2065184 < baseStart_2065184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065321 : List Nat := [1, 2, 1, 1, 1, 1, 6, 5, 4]
def baseStart_2065321 : Nat := 118140960795 + 2065321 * 2 ^ 59
def prefixEnd_2065321 : Nat := 4983230072969 + 3 ^ 40 * 2065321 * 2
def baseEnd_2065321 : Nat := 235667195294359812397615

theorem tailTrace_2065321 : CollatzResearch.WordTrace tailWord_2065321 prefixEnd_2065321 235667195294359812397615 := by
  unfold tailWord_2065321
  simp only [CollatzResearch.WordTrace]
  refine ⟨75328445350702220589739817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50218963567134813726493211 75328445350702220589739817)
  ·
    refine ⟨56496334013026665442304863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75328445350702220589739817 56496334013026665442304863)
    ·
      refine ⟨84744501019539998163457295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56496334013026665442304863 84744501019539998163457295)
      ·
        refine ⟨127116751529309997245185943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84744501019539998163457295 127116751529309997245185943)
        ·
          refine ⟨190675127293964995867778915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127116751529309997245185943 190675127293964995867778915)
          ·
            refine ⟨286012690940947493801668373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190675127293964995867778915 286012690940947493801668373)
            ·
              refine ⟨13406844887856913771953205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 286012690940947493801668373 13406844887856913771953205)
              ·
                refine ⟨1256891708236585666120613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13406844887856913771953205 1256891708236585666120613)
                ·
                  refine ⟨235667195294359812397615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1256891708236585666120613 235667195294359812397615)
                  ·
                    rfl

theorem cell22_2065321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5, 4].length) (baseStart_2065321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2065321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2065321 prefixEnd_2065321 := by exact prefixLift 2065321
  have htrace : WordTrace (prefixWord ++ tailWord_2065321) baseStart_2065321 baseEnd_2065321 := by
    simpa [prefixWord, tailWord_2065321, baseEnd_2065321] using wordTrace_append hprefix tailTrace_2065321
  have hstable : (prefixWord ++ tailWord_2065321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065321).length < 2 ^ (prefixWord ++ tailWord_2065321).sum := by decide
  have hdescent : baseEnd_2065321 < baseStart_2065321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065368 : List Nat := [2, 1, 2, 2, 2, 5, 1, 1, 2, 4]
def baseStart_2065368 : Nat := 118140960795 + 2065368 * 2 ^ 59
def prefixEnd_2065368 : Nat := 4983230072969 + 3 ^ 40 * 2065368 * 2
def baseEnd_2065368 : Nat := 707017674943586981267701

theorem tailTrace_2065368 : CollatzResearch.WordTrace tailWord_2065368 prefixEnd_2065368 707017674943586981267701 := by
  unfold tailWord_2065368
  simp only [CollatzResearch.WordTrace]
  refine ⟨37665079790765973808350379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50220106387687965077800505 37665079790765973808350379)
  ·
    refine ⟨56497619686148960712525569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37665079790765973808350379 56497619686148960712525569)
    ·
      refine ⟨42373214764611720534394177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56497619686148960712525569 42373214764611720534394177)
      ·
        refine ⟨31779911073458790400795633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42373214764611720534394177 31779911073458790400795633)
        ·
          refine ⟨23834933305094092800596725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31779911073458790400795633 23834933305094092800596725)
          ·
            refine ⟨2234524997352571200055943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23834933305094092800596725 2234524997352571200055943)
            ·
              refine ⟨3351787496028856800083915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2234524997352571200055943 3351787496028856800083915)
              ·
                refine ⟨5027681244043285200125873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3351787496028856800083915 5027681244043285200125873)
                ·
                  refine ⟨3770760933032463900094405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5027681244043285200125873 3770760933032463900094405)
                  ·
                    refine ⟨707017674943586981267701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3770760933032463900094405 707017674943586981267701)
                    ·
                      rfl

theorem cell22_2065368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 2, 4].length) (baseStart_2065368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2065368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2065368 prefixEnd_2065368 := by exact prefixLift 2065368
  have htrace : WordTrace (prefixWord ++ tailWord_2065368) baseStart_2065368 baseEnd_2065368 := by
    simpa [prefixWord, tailWord_2065368, baseEnd_2065368] using wordTrace_append hprefix tailTrace_2065368
  have hstable : (prefixWord ++ tailWord_2065368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065368).length < 2 ^ (prefixWord ++ tailWord_2065368).sum := by decide
  have hdescent : baseEnd_2065368 < baseStart_2065368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065432 : List Nat := [2, 1, 2, 3, 2, 4, 1, 3, 1, 3]
def baseStart_2065432 : Nat := 118140960795 + 2065432 * 2 ^ 59
def prefixEnd_2065432 : Nat := 4983230072969 + 3 ^ 40 * 2065432 * 2
def baseEnd_2065432 : Nat := 707039583451512147667505

theorem tailTrace_2065432 : CollatzResearch.WordTrace tailWord_2065432 prefixEnd_2065432 707039583451512147667505 := by
  unfold tailWord_2065432
  simp only [CollatzResearch.WordTrace]
  refine ⟨37666246926650043273515275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50221662568866724364687033 37666246926650043273515275)
  ·
    refine ⟨56499370389975064910272913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37666246926650043273515275 56499370389975064910272913)
    ·
      refine ⟨42374527792481298682704685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56499370389975064910272913 42374527792481298682704685)
      ·
        refine ⟨15890447922180487006014257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42374527792481298682704685 15890447922180487006014257)
        ·
          refine ⟨11917835941635365254510693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15890447922180487006014257 11917835941635365254510693)
          ·
            refine ⟨2234594239056630985220755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11917835941635365254510693 2234594239056630985220755)
            ·
              refine ⟨3351891358584946477831133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2234594239056630985220755 3351891358584946477831133)
              ·
                refine ⟨1256959259469354929186675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3351891358584946477831133 1256959259469354929186675)
                ·
                  refine ⟨1885438889204032393780013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1256959259469354929186675 1885438889204032393780013)
                  ·
                    refine ⟨707039583451512147667505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1885438889204032393780013 707039583451512147667505)
                    ·
                      rfl

theorem cell22_2065432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3, 1, 3].length) (baseStart_2065432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2065432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2065432 prefixEnd_2065432 := by exact prefixLift 2065432
  have htrace : WordTrace (prefixWord ++ tailWord_2065432) baseStart_2065432 baseEnd_2065432 := by
    simpa [prefixWord, tailWord_2065432, baseEnd_2065432] using wordTrace_append hprefix tailTrace_2065432
  have hstable : (prefixWord ++ tailWord_2065432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065432).length < 2 ^ (prefixWord ++ tailWord_2065432).sum := by decide
  have hdescent : baseEnd_2065432 < baseStart_2065432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065462 : List Nat := [5, 1, 2, 1, 1, 4, 2, 1, 5]
def baseStart_2065462 : Nat := 118140960795 + 2065462 * 2 ^ 59
def prefixEnd_2065462 : Nat := 4983230072969 + 3 ^ 40 * 2065462 * 2
def baseEnd_2065462 : Nat := 235683284354867356472471

theorem tailTrace_2065462 : CollatzResearch.WordTrace tailWord_2065462 prefixEnd_2065462 235683284354867356472471 := by
  unfold tailWord_2065462
  simp only [CollatzResearch.WordTrace]
  refine ⟨4708349252699462604413915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50222392028794267780415093 4708349252699462604413915)
  ·
    refine ⟨7062523879049193906620873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4708349252699462604413915 7062523879049193906620873)
    ·
      refine ⟨5296892909286895429965655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7062523879049193906620873 5296892909286895429965655)
      ·
        refine ⟨7945339363930343144948483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5296892909286895429965655 7945339363930343144948483)
        ·
          refine ⟨11918009045895514717422725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7945339363930343144948483 11918009045895514717422725)
          ·
            refine ⟨2234626696105409009516761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11918009045895514717422725 2234626696105409009516761)
            ·
              refine ⟨1675970022079056757137571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2234626696105409009516761 1675970022079056757137571)
              ·
                refine ⟨2513955033118585135706357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1675970022079056757137571 2513955033118585135706357)
                ·
                  refine ⟨235683284354867356472471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2513955033118585135706357 235683284354867356472471)
                  ·
                    rfl

theorem cell22_2065462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_2065462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2065462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2065462 prefixEnd_2065462 := by exact prefixLift 2065462
  have htrace : WordTrace (prefixWord ++ tailWord_2065462) baseStart_2065462 baseEnd_2065462 := by
    simpa [prefixWord, tailWord_2065462, baseEnd_2065462] using wordTrace_append hprefix tailTrace_2065462
  have hstable : (prefixWord ++ tailWord_2065462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065462).length < 2 ^ (prefixWord ++ tailWord_2065462).sum := by decide
  have hdescent : baseEnd_2065462 < baseStart_2065462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065471 : List Nat := [1, 1, 2, 2, 3, 1, 1, 5, 1, 5]
def baseStart_2065471 : Nat := 118140960795 + 2065471 * 2 ^ 59
def prefixEnd_2065471 : Nat := 4983230072969 + 3 ^ 40 * 2065471 * 2
def baseEnd_2065471 : Nat := 707052933948529045942385

theorem tailTrace_2065471 : CollatzResearch.WordTrace tailWord_2065471 prefixEnd_2065471 707052933948529045942385 := by
  unfold tailWord_2065471
  simp only [CollatzResearch.WordTrace]
  refine ⟨75333916300158796207700267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50222610866772530805133511 75333916300158796207700267)
  ·
    refine ⟨113000874450238194311550401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75333916300158796207700267 113000874450238194311550401)
    ·
      refine ⟨84750655837678645733662801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113000874450238194311550401 84750655837678645733662801)
      ·
        refine ⟨63562991878258984300247101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84750655837678645733662801 63562991878258984300247101)
        ·
          refine ⟨23836121954347119112592663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63562991878258984300247101 23836121954347119112592663)
          ·
            refine ⟨35754182931520678668888995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23836121954347119112592663 35754182931520678668888995)
            ·
              refine ⟨53631274397281018003333493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35754182931520678668888995 53631274397281018003333493)
              ·
                refine ⟨5027931974745095437812515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53631274397281018003333493 5027931974745095437812515)
                ·
                  refine ⟨7541897962117643156718773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5027931974745095437812515 7541897962117643156718773)
                  ·
                    refine ⟨707052933948529045942385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7541897962117643156718773 707052933948529045942385)
                    ·
                      rfl

theorem cell22_2065471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 5].length) (baseStart_2065471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2065471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2065471 prefixEnd_2065471 := by exact prefixLift 2065471
  have htrace : WordTrace (prefixWord ++ tailWord_2065471) baseStart_2065471 baseEnd_2065471 := by
    simpa [prefixWord, tailWord_2065471, baseEnd_2065471] using wordTrace_append hprefix tailTrace_2065471
  have hstable : (prefixWord ++ tailWord_2065471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065471).length < 2 ^ (prefixWord ++ tailWord_2065471).sum := by decide
  have hdescent : baseEnd_2065471 < baseStart_2065471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065518 : List Nat := [4, 1, 2, 2, 1, 2, 3, 7]
def baseStart_2065518 : Nat := 118140960795 + 2065518 * 2 ^ 59
def prefixEnd_2065518 : Nat := 4983230072969 + 3 ^ 40 * 2065518 * 2
def baseEnd_2065518 : Nat := 78563224778781843335249

theorem tailTrace_2065518 : CollatzResearch.WordTrace tailWord_2065518 prefixEnd_2065518 78563224778781843335249 := by
  unfold tailWord_2065518
  simp only [CollatzResearch.WordTrace]
  refine ⟨9416953816373565404332651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50223753687325682156440805 9416953816373565404332651)
  ·
    refine ⟨14125430724560348106498977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9416953816373565404332651 14125430724560348106498977)
    ·
      refine ⟨10594073043420261079874233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14125430724560348106498977 10594073043420261079874233)
      ·
        refine ⟨7945554782565195809905675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10594073043420261079874233 7945554782565195809905675)
        ·
          refine ⟨11918332173847793714858513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7945554782565195809905675 11918332173847793714858513)
          ·
            refine ⟨8938749130385845286143885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11918332173847793714858513 8938749130385845286143885)
            ·
              refine ⟨3352030923894691982303957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8938749130385845286143885 3352030923894691982303957)
              ·
                refine ⟨78563224778781843335249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3352030923894691982303957 78563224778781843335249)
                ·
                  rfl

theorem cell22_2065518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_2065518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2065518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2065518 prefixEnd_2065518 := by exact prefixLift 2065518
  have htrace : WordTrace (prefixWord ++ tailWord_2065518) baseStart_2065518 baseEnd_2065518 := by
    simpa [prefixWord, tailWord_2065518, baseEnd_2065518] using wordTrace_append hprefix tailTrace_2065518
  have hstable : (prefixWord ++ tailWord_2065518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065518).length < 2 ^ (prefixWord ++ tailWord_2065518).sum := by decide
  have hdescent : baseEnd_2065518 < baseStart_2065518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065567 : List Nat := [1, 1, 2, 6, 2, 1, 2, 1, 3, 3]
def baseStart_2065567 : Nat := 118140960795 + 2065567 * 2 ^ 59
def prefixEnd_2065567 : Nat := 4983230072969 + 3 ^ 40 * 2065567 * 2
def baseEnd_2065567 : Nat := 707085796710416795542091

theorem tailTrace_2065567 : CollatzResearch.WordTrace tailWord_2065567 prefixEnd_2065567 707085796710416795542091 := by
  unfold tailWord_2065567
  simp only [CollatzResearch.WordTrace]
  refine ⟨75337417707811004603194955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50224945138540669735463303 75337417707811004603194955)
  ·
    refine ⟨113006126561716506904792433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75337417707811004603194955 113006126561716506904792433)
    ·
      refine ⟨84754594921287380178594325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113006126561716506904792433 84754594921287380178594325)
      ·
        refine ⟨3972871636935345945871609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 84754594921287380178594325 3972871636935345945871609)
        ·
          refine ⟨2979653727701509459403707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3972871636935345945871609 2979653727701509459403707)
          ·
            refine ⟨4469480591552264189105561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2979653727701509459403707 4469480591552264189105561)
            ·
              refine ⟨3352110443664198141829171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4469480591552264189105561 3352110443664198141829171)
              ·
                refine ⟨5028165665496297212743757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3352110443664198141829171 5028165665496297212743757)
                ·
                  refine ⟨1885562124561111454778909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5028165665496297212743757 1885562124561111454778909)
                  ·
                    refine ⟨707085796710416795542091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1885562124561111454778909 707085796710416795542091)
                    ·
                      rfl

theorem cell22_2065567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3, 3].length) (baseStart_2065567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2065567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2065567 prefixEnd_2065567 := by exact prefixLift 2065567
  have htrace : WordTrace (prefixWord ++ tailWord_2065567) baseStart_2065567 baseEnd_2065567 := by
    simpa [prefixWord, tailWord_2065567, baseEnd_2065567] using wordTrace_append hprefix tailTrace_2065567
  have hstable : (prefixWord ++ tailWord_2065567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065567).length < 2 ^ (prefixWord ++ tailWord_2065567).sum := by decide
  have hdescent : baseEnd_2065567 < baseStart_2065567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065601 : List Nat := [1, 2, 6, 1, 1, 3, 1, 3, 1, 3]
def baseStart_2065601 : Nat := 118140960795 + 2065601 * 2 ^ 59
def prefixEnd_2065601 : Nat := 4983230072969 + 3 ^ 40 * 2065601 * 2
def baseEnd_2065601 : Nat := 707097435605252040191987

theorem tailTrace_2065601 : CollatzResearch.WordTrace tailWord_2065601 prefixEnd_2065601 707097435605252040191987 := by
  unfold tailWord_2065601
  simp only [CollatzResearch.WordTrace]
  refine ⟨75338657789687828409932657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50225771859791885606621771 75338657789687828409932657)
  ·
    refine ⟨56503993342265871307449493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75338657789687828409932657 56503993342265871307449493)
    ·
      refine ⟨2648624687918712717536695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56503993342265871307449493 2648624687918712717536695)
      ·
        refine ⟨3972937031878069076305043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2648624687918712717536695 3972937031878069076305043)
        ·
          refine ⟨5959405547817103614457565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3972937031878069076305043 5959405547817103614457565)
          ·
            refine ⟨2234777080431413855421587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5959405547817103614457565 2234777080431413855421587)
            ·
              refine ⟨3352165620647120783132381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2234777080431413855421587 3352165620647120783132381)
              ·
                refine ⟨1257062107742670293674643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3352165620647120783132381 1257062107742670293674643)
                ·
                  refine ⟨1885593161614005440511965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1257062107742670293674643 1885593161614005440511965)
                  ·
                    refine ⟨707097435605252040191987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1885593161614005440511965 707097435605252040191987)
                    ·
                      rfl

theorem cell22_2065601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_2065601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2065601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2065601 prefixEnd_2065601 := by exact prefixLift 2065601
  have htrace : WordTrace (prefixWord ++ tailWord_2065601) baseStart_2065601 baseEnd_2065601 := by
    simpa [prefixWord, tailWord_2065601, baseEnd_2065601] using wordTrace_append hprefix tailTrace_2065601
  have hstable : (prefixWord ++ tailWord_2065601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065601).length < 2 ^ (prefixWord ++ tailWord_2065601).sum := by decide
  have hdescent : baseEnd_2065601 < baseStart_2065601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065610 : List Nat := [3, 1, 2, 1, 3, 2, 2, 3, 1, 4]
def baseStart_2065610 : Nat := 118140960795 + 2065610 * 2 ^ 59
def prefixEnd_2065610 : Nat := 4983230072969 + 3 ^ 40 * 2065610 * 2
def baseEnd_2065610 : Nat := 707100516489179016716959

theorem tailTrace_2065610 : CollatzResearch.WordTrace tailWord_2065610 prefixEnd_2065610 707100516489179016716959 := by
  unfold tailWord_2065610
  simp only [CollatzResearch.WordTrace]
  refine ⟨18834746511663805736752571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50225990697770148631340189 18834746511663805736752571)
  ·
    refine ⟨28252119767495708605128857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18834746511663805736752571 28252119767495708605128857)
    ·
      refine ⟨21189089825621781453846643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28252119767495708605128857 21189089825621781453846643)
      ·
        refine ⟨31783634738432672180769965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21189089825621781453846643 31783634738432672180769965)
        ·
          refine ⟨11918863026912252067788737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31783634738432672180769965 11918863026912252067788737)
          ·
            refine ⟨8939147270184189050841553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11918863026912252067788737 8939147270184189050841553)
            ·
              refine ⟨6704360452638141788131165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8939147270184189050841553 6704360452638141788131165)
              ·
                refine ⟨2514135169739303170549187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6704360452638141788131165 2514135169739303170549187)
                ·
                  refine ⟨3771202754608954755823781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2514135169739303170549187 3771202754608954755823781)
                  ·
                    refine ⟨707100516489179016716959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3771202754608954755823781 707100516489179016716959)
                    ·
                      rfl

theorem cell22_2065610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_2065610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2065610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2065610 prefixEnd_2065610 := by exact prefixLift 2065610
  have htrace : WordTrace (prefixWord ++ tailWord_2065610) baseStart_2065610 baseEnd_2065610 := by
    simpa [prefixWord, tailWord_2065610, baseEnd_2065610] using wordTrace_append hprefix tailTrace_2065610
  have hstable : (prefixWord ++ tailWord_2065610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065610).length < 2 ^ (prefixWord ++ tailWord_2065610).sum := by decide
  have hdescent : baseEnd_2065610 < baseStart_2065610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065670 : List Nat := [6, 2, 14]
def baseStart_2065670 : Nat := 118140960795 + 2065670 * 2 ^ 59
def prefixEnd_2065670 : Nat := 4983230072969 + 3 ^ 40 * 2065670 * 2
def baseEnd_2065670 : Nat := 323329243582697238325

theorem tailTrace_2065670 : CollatzResearch.WordTrace tailWord_2065670 prefixEnd_2065670 323329243582697238325 := by
  unfold tailWord_2065670
  simp only [CollatzResearch.WordTrace]
  refine ⟨2354411700826182912318577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50227449617625235462796309 2354411700826182912318577)
  ·
    refine ⟨1765808775619637184238933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2354411700826182912318577 1765808775619637184238933)
    ·
      refine ⟨323329243582697238325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 14 1765808775619637184238933 323329243582697238325)
      ·
        rfl

theorem cell22_2065670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 14].length) (baseStart_2065670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2065670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2065670 prefixEnd_2065670 := by exact prefixLift 2065670
  have htrace : WordTrace (prefixWord ++ tailWord_2065670) baseStart_2065670 baseEnd_2065670 := by
    simpa [prefixWord, tailWord_2065670, baseEnd_2065670] using wordTrace_append hprefix tailTrace_2065670
  have hstable : (prefixWord ++ tailWord_2065670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065670).length < 2 ^ (prefixWord ++ tailWord_2065670).sum := by decide
  have hdescent : baseEnd_2065670 < baseStart_2065670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065685 : List Nat := [1, 3, 2, 1, 2, 1, 1, 5, 3, 3]
def baseStart_2065685 : Nat := 118140960795 + 2065685 * 2 ^ 59
def prefixEnd_2065685 : Nat := 4983230072969 + 3 ^ 40 * 2065685 * 2
def baseEnd_2065685 : Nat := 707126190521903821091729

theorem tailTrace_2065685 : CollatzResearch.WordTrace tailWord_2065685 prefixEnd_2065685 707126190521903821091729 := by
  unfold tailWord_2065685
  simp only [CollatzResearch.WordTrace]
  refine ⟨75341721521383510755990509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50227814347589007170660339 75341721521383510755990509)
  ·
    refine ⟨28253145570518816533496441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75341721521383510755990509 28253145570518816533496441)
    ·
      refine ⟨21189859177889112400122331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28253145570518816533496441 21189859177889112400122331)
      ·
        refine ⟨31784788766833668600183497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21189859177889112400122331 31784788766833668600183497)
        ·
          refine ⟨23838591575125251450137623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31784788766833668600183497 23838591575125251450137623)
          ·
            refine ⟨35757887362687877175206435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23838591575125251450137623 35757887362687877175206435)
            ·
              refine ⟨53636831044031815762809653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35757887362687877175206435 53636831044031815762809653)
              ·
                refine ⟨5028452910377982727763405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53636831044031815762809653 5028452910377982727763405)
                ·
                  refine ⟨1885669841391743522911277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5028452910377982727763405 1885669841391743522911277)
                  ·
                    refine ⟨707126190521903821091729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1885669841391743522911277 707126190521903821091729)
                    ·
                      rfl

theorem cell22_2065685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_2065685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2065685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2065685 prefixEnd_2065685 := by exact prefixLift 2065685
  have htrace : WordTrace (prefixWord ++ tailWord_2065685) baseStart_2065685 baseEnd_2065685 := by
    simpa [prefixWord, tailWord_2065685, baseEnd_2065685] using wordTrace_append hprefix tailTrace_2065685
  have hstable : (prefixWord ++ tailWord_2065685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065685).length < 2 ^ (prefixWord ++ tailWord_2065685).sum := by decide
  have hdescent : baseEnd_2065685 < baseStart_2065685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065732 : List Nat := [2, 3, 4, 1, 1, 2, 1, 1, 7]
def baseStart_2065732 : Nat := 118140960795 + 2065732 * 2 ^ 59
def prefixEnd_2065732 : Nat := 4983230072969 + 3 ^ 40 * 2065732 * 2
def baseEnd_2065732 : Nat := 235714093194137121722195

theorem tailTrace_2065732 : CollatzResearch.WordTrace tailWord_2065732 prefixEnd_2065732 235714093194137121722195 := by
  unfold tailWord_2065732
  simp only [CollatzResearch.WordTrace]
  refine ⟨37671717876106618891475725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50228957168142158521967633 37671717876106618891475725)
  ·
    refine ⟨14126894203539982084303397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37671717876106618891475725 14126894203539982084303397)
    ·
      refine ⟨2648792663163746640806887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14126894203539982084303397 2648792663163746640806887)
      ·
        refine ⟨3973188994745619961210331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2648792663163746640806887 3973188994745619961210331)
        ·
          refine ⟨5959783492118429941815497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3973188994745619961210331 5959783492118429941815497)
          ·
            refine ⟨4469837619088822456361623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5959783492118429941815497 4469837619088822456361623)
            ·
              refine ⟨6704756428633233684542435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4469837619088822456361623 6704756428633233684542435)
              ·
                refine ⟨10057134642949850526813653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6704756428633233684542435 10057134642949850526813653)
                ·
                  refine ⟨235714093194137121722195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10057134642949850526813653 235714093194137121722195)
                  ·
                    rfl

theorem cell22_2065732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_2065732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2065732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2065732 prefixEnd_2065732 := by exact prefixLift 2065732
  have htrace : WordTrace (prefixWord ++ tailWord_2065732) baseStart_2065732 baseEnd_2065732 := by
    simpa [prefixWord, tailWord_2065732, baseEnd_2065732] using wordTrace_append hprefix tailTrace_2065732
  have hstable : (prefixWord ++ tailWord_2065732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065732).length < 2 ^ (prefixWord ++ tailWord_2065732).sum := by decide
  have hdescent : baseEnd_2065732 < baseStart_2065732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065760 : List Nat := [2, 1, 1, 3, 4, 1, 2, 2, 6]
def baseStart_2065760 : Nat := 118140960795 + 2065760 * 2 ^ 59
def prefixEnd_2065760 : Nat := 4983230072969 + 3 ^ 40 * 2065760 * 2
def baseEnd_2065760 : Nat := 235717288184876208488833

theorem tailTrace_2065760 : CollatzResearch.WordTrace tailWord_2065760 prefixEnd_2065760 235717288184876208488833 := by
  unfold tailWord_2065760
  simp only [CollatzResearch.WordTrace]
  refine ⟨37672228498055899282485367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50229637997407865709980489 37672228498055899282485367)
  ·
    refine ⟨56508342747083848923728051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37672228498055899282485367 56508342747083848923728051)
    ·
      refine ⟨84762514120625773385592077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56508342747083848923728051 84762514120625773385592077)
      ·
        refine ⟨31785942795234665019597029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84762514120625773385592077 31785942795234665019597029)
        ·
          refine ⟨5959864274106499691174443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31785942795234665019597029 5959864274106499691174443)
          ·
            refine ⟨8939796411159749536761665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5959864274106499691174443 8939796411159749536761665)
            ·
              refine ⟨6704847308369812152571249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8939796411159749536761665 6704847308369812152571249)
              ·
                refine ⟨5028635481277359114428437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6704847308369812152571249 5028635481277359114428437)
                ·
                  refine ⟨235717288184876208488833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5028635481277359114428437 235717288184876208488833)
                  ·
                    rfl

theorem cell22_2065760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 6].length) (baseStart_2065760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2065760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2065760 prefixEnd_2065760 := by exact prefixLift 2065760
  have htrace : WordTrace (prefixWord ++ tailWord_2065760) baseStart_2065760 baseEnd_2065760 := by
    simpa [prefixWord, tailWord_2065760, baseEnd_2065760] using wordTrace_append hprefix tailTrace_2065760
  have hstable : (prefixWord ++ tailWord_2065760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065760).length < 2 ^ (prefixWord ++ tailWord_2065760).sum := by decide
  have hdescent : baseEnd_2065760 < baseStart_2065760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065775 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 6, 3]
def baseStart_2065775 : Nat := 118140960795 + 2065775 * 2 ^ 59
def prefixEnd_2065775 : Nat := 4983230072969 + 3 ^ 40 * 2065775 * 2
def baseEnd_2065775 : Nat := 707156999361173586341453

theorem tailTrace_2065775 : CollatzResearch.WordTrace tailWord_2065775 prefixEnd_2065775 707156999361173586341453 := by
  unfold tailWord_2065775
  simp only [CollatzResearch.WordTrace]
  refine ⟨75345004091057456126766779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50230002727371637417844519 75345004091057456126766779)
  ·
    refine ⟨113017506136586184190150169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75345004091057456126766779 113017506136586184190150169)
    ·
      refine ⟨84763129602439638142612627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113017506136586184190150169 84763129602439638142612627)
      ·
        refine ⟨127144694403659457213918941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84763129602439638142612627 127144694403659457213918941)
        ·
          refine ⟨47679260401372296455219603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127144694403659457213918941 47679260401372296455219603)
          ·
            refine ⟨71518890602058444682829405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47679260401372296455219603 71518890602058444682829405)
            ·
              refine ⟨26819583975771916756061027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71518890602058444682829405 26819583975771916756061027)
              ·
                refine ⟨40229375963657875134091541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26819583975771916756061027 40229375963657875134091541)
                ·
                  refine ⟨1885751998296462896910541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 40229375963657875134091541 1885751998296462896910541)
                  ·
                    refine ⟨707156999361173586341453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1885751998296462896910541 707156999361173586341453)
                    ·
                      rfl

theorem cell22_2065775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6, 3].length) (baseStart_2065775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2065775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2065775 prefixEnd_2065775 := by exact prefixLift 2065775
  have htrace : WordTrace (prefixWord ++ tailWord_2065775) baseStart_2065775 baseEnd_2065775 := by
    simpa [prefixWord, tailWord_2065775, baseEnd_2065775] using wordTrace_append hprefix tailTrace_2065775
  have hstable : (prefixWord ++ tailWord_2065775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065775).length < 2 ^ (prefixWord ++ tailWord_2065775).sum := by decide
  have hdescent : baseEnd_2065775 < baseStart_2065775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065777 : List Nat := [1, 2, 2, 2, 1, 2, 5, 3, 4]
def baseStart_2065777 : Nat := 118140960795 + 2065777 * 2 ^ 59
def prefixEnd_2065777 : Nat := 4983230072969 + 3 ^ 40 * 2065777 * 2
def baseEnd_2065777 : Nat := 235719228000682082597149

theorem tailTrace_2065777 : CollatzResearch.WordTrace tailWord_2065777 prefixEnd_2065777 235719228000682082597149 := by
  unfold tailWord_2065777
  simp only [CollatzResearch.WordTrace]
  refine ⟨75345077037050210468339585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50230051358033473645559723 75345077037050210468339585)
  ·
    refine ⟨56508807777787657851254689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75345077037050210468339585 56508807777787657851254689)
    ·
      refine ⟨42381605833340743388441017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56508807777787657851254689 42381605833340743388441017)
      ·
        refine ⟨31786204375005557541330763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42381605833340743388441017 31786204375005557541330763)
        ·
          refine ⟨47679306562508336311996145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31786204375005557541330763 47679306562508336311996145)
          ·
            refine ⟨35759479921881252233997109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47679306562508336311996145 35759479921881252233997109)
            ·
              refine ⟨3352451242676367396937229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35759479921881252233997109 3352451242676367396937229)
              ·
                refine ⟨1257169216003637773851461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3352451242676367396937229 1257169216003637773851461)
                ·
                  refine ⟨235719228000682082597149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1257169216003637773851461 235719228000682082597149)
                  ·
                    rfl

theorem cell22_2065777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 3, 4].length) (baseStart_2065777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2065777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2065777 prefixEnd_2065777 := by exact prefixLift 2065777
  have htrace : WordTrace (prefixWord ++ tailWord_2065777) baseStart_2065777 baseEnd_2065777 := by
    simpa [prefixWord, tailWord_2065777, baseEnd_2065777] using wordTrace_append hprefix tailTrace_2065777
  have hstable : (prefixWord ++ tailWord_2065777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065777).length < 2 ^ (prefixWord ++ tailWord_2065777).sum := by decide
  have hdescent : baseEnd_2065777 < baseStart_2065777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065794 : List Nat := [3, 4, 2, 1, 1, 1, 3, 1, 6]
def baseStart_2065794 : Nat := 118140960795 + 2065794 * 2 ^ 59
def prefixEnd_2065794 : Nat := 4983230072969 + 3 ^ 40 * 2065794 * 2
def baseEnd_2065794 : Nat := 235721167816487956705465

theorem tailTrace_2065794 : CollatzResearch.WordTrace tailWord_2065794 prefixEnd_2065794 235721167816487956705465 := by
  unfold tailWord_2065794
  simp only [CollatzResearch.WordTrace]
  refine ⟨18836424269497155592927109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50230464718659081581138957 18836424269497155592927109)
  ·
    refine ⟨3531829550530716673673833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18836424269497155592927109 3531829550530716673673833)
    ·
      refine ⟨2648872162898037505255375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3531829550530716673673833 2648872162898037505255375)
      ·
        refine ⟨3973308244347056257883063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2648872162898037505255375 3973308244347056257883063)
        ·
          refine ⟨5959962366520584386824595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3973308244347056257883063 5959962366520584386824595)
          ·
            refine ⟨8939943549780876580236893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5959962366520584386824595 8939943549780876580236893)
            ·
              refine ⟨3352478831167828717588835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8939943549780876580236893 3352478831167828717588835)
              ·
                refine ⟨5028718246751743076383253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3352478831167828717588835 5028718246751743076383253)
                ·
                  refine ⟨235721167816487956705465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5028718246751743076383253 235721167816487956705465)
                  ·
                    rfl

theorem cell22_2065794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_2065794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2065794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2065794 prefixEnd_2065794 := by exact prefixLift 2065794
  have htrace : WordTrace (prefixWord ++ tailWord_2065794) baseStart_2065794 baseEnd_2065794 := by
    simpa [prefixWord, tailWord_2065794, baseEnd_2065794] using wordTrace_append hprefix tailTrace_2065794
  have hstable : (prefixWord ++ tailWord_2065794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065794).length < 2 ^ (prefixWord ++ tailWord_2065794).sum := by decide
  have hdescent : baseEnd_2065794 < baseStart_2065794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065901 : List Nat := [1, 5, 1, 3, 2, 2, 1, 2, 5]
def baseStart_2065901 : Nat := 118140960795 + 2065901 * 2 ^ 59
def prefixEnd_2065901 : Nat := 4983230072969 + 3 ^ 40 * 2065901 * 2
def baseEnd_2065901 : Nat := 235733377245383752563689

theorem tailTrace_2065901 : CollatzResearch.WordTrace tailWord_2065901 prefixEnd_2065901 235733377245383752563689 := by
  unfold tailWord_2065901
  simp only [CollatzResearch.WordTrace]
  refine ⟨75349599688600979645853557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50233066459067319763902371 75349599688600979645853557)
  ·
    refine ⟨7064024970806341841798771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75349599688600979645853557 7064024970806341841798771)
    ·
      refine ⟨10596037456209512762698157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7064024970806341841798771 10596037456209512762698157)
      ·
        refine ⟨3973514046078567286011809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10596037456209512762698157 3973514046078567286011809)
        ·
          refine ⟨2980135534558925464508857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3973514046078567286011809 2980135534558925464508857)
          ·
            refine ⟨2235101650919194098381643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2980135534558925464508857 2235101650919194098381643)
            ·
              refine ⟨3352652476378791147572465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2235101650919194098381643 3352652476378791147572465)
              ·
                refine ⟨2514489357284093360679349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3352652476378791147572465 2514489357284093360679349)
                ·
                  refine ⟨235733377245383752563689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2514489357284093360679349 235733377245383752563689)
                  ·
                    rfl

theorem cell22_2065901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_2065901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2065901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2065901 prefixEnd_2065901 := by exact prefixLift 2065901
  have htrace : WordTrace (prefixWord ++ tailWord_2065901) baseStart_2065901 baseEnd_2065901 := by
    simpa [prefixWord, tailWord_2065901, baseEnd_2065901] using wordTrace_append hprefix tailTrace_2065901
  have hstable : (prefixWord ++ tailWord_2065901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065901).length < 2 ^ (prefixWord ++ tailWord_2065901).sum := by decide
  have hdescent : baseEnd_2065901 < baseStart_2065901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065912 : List Nat := [2, 1, 2, 1, 1, 6, 2, 1, 6]
def baseStart_2065912 : Nat := 118140960795 + 2065912 * 2 ^ 59
def prefixEnd_2065912 : Nat := 4983230072969 + 3 ^ 40 * 2065912 * 2
def baseEnd_2065912 : Nat := 235734632420316965222011

theorem tailTrace_2065912 : CollatzResearch.WordTrace tailWord_2065912 prefixEnd_2065912 235734632420316965222011 := by
  unfold tailWord_2065912
  simp only [CollatzResearch.WordTrace]
  refine ⟨37675000445780564262251995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50233333927707419016335993 37675000445780564262251995)
  ·
    refine ⟨56512500668670846393377993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37675000445780564262251995 56512500668670846393377993)
    ·
      refine ⟨42384375501503134795033495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56512500668670846393377993 42384375501503134795033495)
      ·
        refine ⟨63576563252254702192550243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42384375501503134795033495 63576563252254702192550243)
        ·
          refine ⟨95364844878382053288825365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63576563252254702192550243 95364844878382053288825365)
          ·
            refine ⟨4470227103674158747913689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 95364844878382053288825365 4470227103674158747913689)
            ·
              refine ⟨3352670327755619060935267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4470227103674158747913689 3352670327755619060935267)
              ·
                refine ⟨5029005491633428591402901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3352670327755619060935267 5029005491633428591402901)
                ·
                  refine ⟨235734632420316965222011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5029005491633428591402901 235734632420316965222011)
                  ·
                    rfl

theorem cell22_2065912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 6].length) (baseStart_2065912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2065912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2065912 prefixEnd_2065912 := by exact prefixLift 2065912
  have htrace : WordTrace (prefixWord ++ tailWord_2065912) baseStart_2065912 baseEnd_2065912 := by
    simpa [prefixWord, tailWord_2065912, baseEnd_2065912] using wordTrace_append hprefix tailTrace_2065912
  have hstable : (prefixWord ++ tailWord_2065912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065912).length < 2 ^ (prefixWord ++ tailWord_2065912).sum := by decide
  have hdescent : baseEnd_2065912 < baseStart_2065912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065918 : List Nat := [4, 2, 2, 3, 1, 1, 3, 1, 5]
def baseStart_2065918 : Nat := 118140960795 + 2065918 * 2 ^ 59
def prefixEnd_2065918 : Nat := 4983230072969 + 3 ^ 40 * 2065918 * 2
def baseEnd_2065918 : Nat := 235735317061189626672005

theorem tailTrace_2065918 : CollatzResearch.WordTrace tailWord_2065918 prefixEnd_2065918 235735317061189626672005 := by
  unfold tailWord_2065918
  simp only [CollatzResearch.WordTrace]
  refine ⟨9418777466192423943652801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50233479819692927699481605 9418777466192423943652801)
  ·
    refine ⟨7064083099644317957739601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9418777466192423943652801 7064083099644317957739601)
    ·
      refine ⟨5298062324733238468304701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7064083099644317957739601 5298062324733238468304701)
      ·
        refine ⟨1986773371774964425614263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5298062324733238468304701 1986773371774964425614263)
        ·
          refine ⟨2980160057662446638421395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1986773371774964425614263 2980160057662446638421395)
          ·
            refine ⟨4470240086493669957632093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2980160057662446638421395 4470240086493669957632093)
            ·
              refine ⟨1676340032435126234112035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4470240086493669957632093 1676340032435126234112035)
              ·
                refine ⟨2514510048652689351168053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1676340032435126234112035 2514510048652689351168053)
                ·
                  refine ⟨235735317061189626672005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2514510048652689351168053 235735317061189626672005)
                  ·
                    rfl

theorem cell22_2065918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_2065918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2065918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2065918 prefixEnd_2065918 := by exact prefixLift 2065918
  have htrace : WordTrace (prefixWord ++ tailWord_2065918) baseStart_2065918 baseEnd_2065918 := by
    simpa [prefixWord, tailWord_2065918, baseEnd_2065918] using wordTrace_append hprefix tailTrace_2065918
  have hstable : (prefixWord ++ tailWord_2065918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065918).length < 2 ^ (prefixWord ++ tailWord_2065918).sum := by decide
  have hdescent : baseEnd_2065918 < baseStart_2065918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066017 : List Nat := [1, 2, 3, 1, 1, 3, 2, 2, 2, 5]
def baseStart_2066017 : Nat := 118140960795 + 2066017 * 2 ^ 59
def prefixEnd_2066017 : Nat := 4983230072969 + 3 ^ 40 * 2066017 * 2
def baseEnd_2066017 : Nat := 707239840906765621790711

theorem tailTrace_2066017 : CollatzResearch.WordTrace tailWord_2066017 prefixEnd_2066017 707239840906765621790711 := by
  unfold tailWord_2066017
  simp only [CollatzResearch.WordTrace]
  refine ⟨75353830556180731457076305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50235887037453820971384203 75353830556180731457076305)
  ·
    refine ⟨56515372917135548592807229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75353830556180731457076305 56515372917135548592807229)
    ·
      refine ⟨21193264843925830722302711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56515372917135548592807229 21193264843925830722302711)
      ·
        refine ⟨31789897265888746083454067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21193264843925830722302711 31789897265888746083454067)
        ·
          refine ⟨47684845898833119125181101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31789897265888746083454067 47684845898833119125181101)
          ·
            refine ⟨17881817212062419671942913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47684845898833119125181101 17881817212062419671942913)
            ·
              refine ⟨13411362909046814753957185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17881817212062419671942913 13411362909046814753957185)
              ·
                refine ⟨10058522181785111065467889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13411362909046814753957185 10058522181785111065467889)
                ·
                  refine ⟨7543891636338833299100917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10058522181785111065467889 7543891636338833299100917)
                  ·
                    refine ⟨707239840906765621790711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7543891636338833299100917 707239840906765621790711)
                    ·
                      rfl

theorem cell22_2066017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_2066017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2066017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2066017 prefixEnd_2066017 := by exact prefixLift 2066017
  have htrace : WordTrace (prefixWord ++ tailWord_2066017) baseStart_2066017 baseEnd_2066017 := by
    simpa [prefixWord, tailWord_2066017, baseEnd_2066017] using wordTrace_append hprefix tailTrace_2066017
  have hstable : (prefixWord ++ tailWord_2066017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066017).length < 2 ^ (prefixWord ++ tailWord_2066017).sum := by decide
  have hdescent : baseEnd_2066017 < baseStart_2066017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066019 : List Nat := [1, 1, 1, 5, 1, 4, 2, 2, 5]
def baseStart_2066019 : Nat := 118140960795 + 2066019 * 2 ^ 59
def prefixEnd_2066019 : Nat := 4983230072969 + 3 ^ 40 * 2066019 * 2
def baseEnd_2066019 : Nat := 235746841849212761080235

theorem tailTrace_2066019 : CollatzResearch.WordTrace tailWord_2066019 prefixEnd_2066019 235746841849212761080235 := by
  unfold tailWord_2066019
  simp only [CollatzResearch.WordTrace]
  refine ⟨75353903502173485798649111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50235935668115657199099407 75353903502173485798649111)
  ·
    refine ⟨113030855253260228697973667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75353903502173485798649111 113030855253260228697973667)
    ·
      refine ⟨169546282879890343046960501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113030855253260228697973667 169546282879890343046960501)
      ·
        refine ⟨15894964019989719660652547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 169546282879890343046960501 15894964019989719660652547)
        ·
          refine ⟨23842446029984579490978821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15894964019989719660652547 23842446029984579490978821)
          ·
            refine ⟨4470458630622108654558529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23842446029984579490978821 4470458630622108654558529)
            ·
              refine ⟨3352843972966581490918897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4470458630622108654558529 3352843972966581490918897)
              ·
                refine ⟨2514632979724936118189173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3352843972966581490918897 2514632979724936118189173)
                ·
                  refine ⟨235746841849212761080235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2514632979724936118189173 235746841849212761080235)
                  ·
                    rfl

theorem cell22_2066019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 5].length) (baseStart_2066019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2066019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2066019 prefixEnd_2066019 := by exact prefixLift 2066019
  have htrace : WordTrace (prefixWord ++ tailWord_2066019) baseStart_2066019 baseEnd_2066019 := by
    simpa [prefixWord, tailWord_2066019, baseEnd_2066019] using wordTrace_append hprefix tailTrace_2066019
  have hstable : (prefixWord ++ tailWord_2066019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066019).length < 2 ^ (prefixWord ++ tailWord_2066019).sum := by decide
  have hdescent : baseEnd_2066019 < baseStart_2066019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066023 : List Nat := [1, 1, 5, 1, 1, 1, 6, 2, 1, 3]
def baseStart_2066023 : Nat := 118140960795 + 2066023 * 2 ^ 59
def prefixEnd_2066023 : Nat := 4983230072969 + 3 ^ 40 * 2066023 * 2
def baseEnd_2066023 : Nat := 707241894829383606140693

theorem tailTrace_2066023 : CollatzResearch.WordTrace tailWord_2066023 prefixEnd_2066023 707241894829383606140693 := by
  unfold tailWord_2066023
  simp only [CollatzResearch.WordTrace]
  refine ⟨75354049394158994481794723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50236032929439329654529815 75354049394158994481794723)
  ·
    refine ⟨113031074091238491722692085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75354049394158994481794723 113031074091238491722692085)
    ·
      refine ⟨10596663196053608599002383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113031074091238491722692085 10596663196053608599002383)
      ·
        refine ⟨15894994794080412898503575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10596663196053608599002383 15894994794080412898503575)
        ·
          refine ⟨23842492191120619347755363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15894994794080412898503575 23842492191120619347755363)
          ·
            refine ⟨35763738286680929021633045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23842492191120619347755363 35763738286680929021633045)
            ·
              refine ⟨1676425232188168547889049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35763738286680929021633045 1676425232188168547889049)
              ·
                refine ⟨1257318924141126410916787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1676425232188168547889049 1257318924141126410916787)
                ·
                  refine ⟨1885978386211689616375181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1257318924141126410916787 1885978386211689616375181)
                  ·
                    refine ⟨707241894829383606140693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1885978386211689616375181 707241894829383606140693)
                    ·
                      rfl

theorem cell22_2066023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_2066023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2066023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2066023 prefixEnd_2066023 := by exact prefixLift 2066023
  have htrace : WordTrace (prefixWord ++ tailWord_2066023) baseStart_2066023 baseEnd_2066023 := by
    simpa [prefixWord, tailWord_2066023, baseEnd_2066023] using wordTrace_append hprefix tailTrace_2066023
  have hstable : (prefixWord ++ tailWord_2066023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066023).length < 2 ^ (prefixWord ++ tailWord_2066023).sum := by decide
  have hdescent : baseEnd_2066023 < baseStart_2066023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066034 : List Nat := [3, 2, 1, 2, 3, 2, 1, 1, 2, 5]
def baseStart_2066034 : Nat := 118140960795 + 2066034 * 2 ^ 59
def prefixEnd_2066034 : Nat := 4983230072969 + 3 ^ 40 * 2066034 * 2
def baseEnd_2066034 : Nat := 707245660354183244115659

theorem tailTrace_2066034 : CollatzResearch.WordTrace tailWord_2066034 prefixEnd_2066034 707245660354183244115659 := by
  unfold tailWord_2066034
  simp only [CollatzResearch.WordTrace]
  refine ⟨18838612649279785840111289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50236300398079428906963437 18838612649279785840111289)
  ·
    refine ⟨14128959486959839380083467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18838612649279785840111289 14128959486959839380083467)
    ·
      refine ⟨21193439230439759070125201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14128959486959839380083467 21193439230439759070125201)
      ·
        refine ⟨15895079422829819302593901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21193439230439759070125201 15895079422829819302593901)
        ·
          refine ⟨5960654783561182238472713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15895079422829819302593901 5960654783561182238472713)
          ·
            refine ⟨4470491087670886678854535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5960654783561182238472713 4470491087670886678854535)
            ·
              refine ⟨6705736631506330018281803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4470491087670886678854535 6705736631506330018281803)
              ·
                refine ⟨10058604947259495027422705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6705736631506330018281803 10058604947259495027422705)
                ·
                  refine ⟨7543953710444621270567029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10058604947259495027422705 7543953710444621270567029)
                  ·
                    refine ⟨707245660354183244115659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7543953710444621270567029 707245660354183244115659)
                    ·
                      rfl

theorem cell22_2066034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_2066034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2066034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2066034 prefixEnd_2066034 := by exact prefixLift 2066034
  have htrace : WordTrace (prefixWord ++ tailWord_2066034) baseStart_2066034 baseEnd_2066034 := by
    simpa [prefixWord, tailWord_2066034, baseEnd_2066034] using wordTrace_append hprefix tailTrace_2066034
  have hstable : (prefixWord ++ tailWord_2066034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066034).length < 2 ^ (prefixWord ++ tailWord_2066034).sum := by decide
  have hdescent : baseEnd_2066034 < baseStart_2066034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066049 : List Nat := [1, 2, 4, 2, 1, 2, 2, 1, 3, 4]
def baseStart_2066049 : Nat := 118140960795 + 2066049 * 2 ^ 59
def prefixEnd_2066049 : Nat := 4983230072969 + 3 ^ 40 * 2066049 * 2
def baseEnd_2066049 : Nat := 707250795160728204990613

theorem tailTrace_2066049 : CollatzResearch.WordTrace tailWord_2066049 prefixEnd_2066049 707250795160728204990613 := by
  unfold tailWord_2066049
  simp only [CollatzResearch.WordTrace]
  refine ⟨75354997692064800922241201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50236665128043200614827467 75354997692064800922241201)
  ·
    refine ⟨56516248269048600691680901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75354997692064800922241201 56516248269048600691680901)
    ·
      refine ⟨10596796550446612629690169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56516248269048600691680901 10596796550446612629690169)
      ·
        refine ⟨7947597412834959472267627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10596796550446612629690169 7947597412834959472267627)
        ·
          refine ⟨11921396119252439208401441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7947597412834959472267627 11921396119252439208401441)
          ·
            refine ⟨8941047089439329406301081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11921396119252439208401441 8941047089439329406301081)
            ·
              refine ⟨6705785317079497054725811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8941047089439329406301081 6705785317079497054725811)
              ·
                refine ⟨10058677975619245582088717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6705785317079497054725811 10058677975619245582088717)
                ·
                  refine ⟨3772004240857217093283269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10058677975619245582088717 3772004240857217093283269)
                  ·
                    refine ⟨707250795160728204990613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3772004240857217093283269 707250795160728204990613)
                    ·
                      rfl

theorem cell22_2066049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_2066049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2066049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2066049 prefixEnd_2066049 := by exact prefixLift 2066049
  have htrace : WordTrace (prefixWord ++ tailWord_2066049) baseStart_2066049 baseEnd_2066049 := by
    simpa [prefixWord, tailWord_2066049, baseEnd_2066049] using wordTrace_append hprefix tailTrace_2066049
  have hstable : (prefixWord ++ tailWord_2066049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066049).length < 2 ^ (prefixWord ++ tailWord_2066049).sum := by decide
  have hdescent : baseEnd_2066049 < baseStart_2066049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066081 : List Nat := [1, 2, 3, 3, 2, 1, 2, 4, 4]
def baseStart_2066081 : Nat := 118140960795 + 2066081 * 2 ^ 59
def prefixEnd_2066081 : Nat := 4983230072969 + 3 ^ 40 * 2066081 * 2
def baseEnd_2066081 : Nat := 235753916471563596063505

theorem tailTrace_2066081 : CollatzResearch.WordTrace tailWord_2066081 prefixEnd_2066081 235753916471563596063505 := by
  unfold tailWord_2066081
  simp only [CollatzResearch.WordTrace]
  refine ⟨75356164827948870387406097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50237443218632580258270731 75356164827948870387406097)
  ·
    refine ⟨56517123620961652790554573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75356164827948870387406097 56517123620961652790554573)
    ·
      refine ⟨21193921357860619796457965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56517123620961652790554573 21193921357860619796457965)
      ·
        refine ⟨7947720509197732423671737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21193921357860619796457965 7947720509197732423671737)
        ·
          refine ⟨5960790381898299317753803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7947720509197732423671737 5960790381898299317753803)
          ·
            refine ⟨8941185572847448976630705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5960790381898299317753803 8941185572847448976630705)
            ·
              refine ⟨6705889179635586732473029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8941185572847448976630705 6705889179635586732473029)
              ·
                refine ⟨1257354221181672512338693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6705889179635586732473029 1257354221181672512338693)
                ·
                  refine ⟨235753916471563596063505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1257354221181672512338693 235753916471563596063505)
                  ·
                    rfl

theorem cell22_2066081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4, 4].length) (baseStart_2066081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2066081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2066081 prefixEnd_2066081 := by exact prefixLift 2066081
  have htrace : WordTrace (prefixWord ++ tailWord_2066081) baseStart_2066081 baseEnd_2066081 := by
    simpa [prefixWord, tailWord_2066081, baseEnd_2066081] using wordTrace_append hprefix tailTrace_2066081
  have hstable : (prefixWord ++ tailWord_2066081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066081).length < 2 ^ (prefixWord ++ tailWord_2066081).sum := by decide
  have hdescent : baseEnd_2066081 < baseStart_2066081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066147 : List Nat := [1, 1, 1, 7, 3, 1, 2, 1, 2, 3]
def baseStart_2066147 : Nat := 118140960795 + 2066147 * 2 ^ 59
def prefixEnd_2066147 : Nat := 4983230072969 + 3 ^ 40 * 2066147 * 2
def baseEnd_2066147 : Nat := 707284342563488616040313

theorem tailTrace_2066147 : CollatzResearch.WordTrace tailWord_2066147 prefixEnd_2066147 707284342563488616040313 := by
  unfold tailWord_2066147
  simp only [CollatzResearch.WordTrace]
  refine ⟨75358572045709763659308695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50239048030473175772872463 75358572045709763659308695)
  ·
    refine ⟨113037858068564645488963043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75358572045709763659308695 113037858068564645488963043)
    ·
      refine ⟨169556787102846968233444565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113037858068564645488963043 169556787102846968233444565)
      ·
        refine ⟨3973987197722975817971357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 169556787102846968233444565 3973987197722975817971357)
        ·
          refine ⟨1490245199146115931739259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3973987197722975817971357 1490245199146115931739259)
          ·
            refine ⟨2235367798719173897608889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1490245199146115931739259 2235367798719173897608889)
            ·
              refine ⟨1676525849039380423206667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2235367798719173897608889 1676525849039380423206667)
              ·
                refine ⟨2514788773559070634810001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1676525849039380423206667 2514788773559070634810001)
                ·
                  refine ⟨1886091580169302976107501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2514788773559070634810001 1886091580169302976107501)
                  ·
                    refine ⟨707284342563488616040313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1886091580169302976107501 707284342563488616040313)
                    ·
                      rfl

theorem cell22_2066147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 2, 3].length) (baseStart_2066147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2066147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2066147 prefixEnd_2066147 := by exact prefixLift 2066147
  have htrace : WordTrace (prefixWord ++ tailWord_2066147) baseStart_2066147 baseEnd_2066147 := by
    simpa [prefixWord, tailWord_2066147, baseEnd_2066147] using wordTrace_append hprefix tailTrace_2066147
  have hstable : (prefixWord ++ tailWord_2066147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066147).length < 2 ^ (prefixWord ++ tailWord_2066147).sum := by decide
  have hdescent : baseEnd_2066147 < baseStart_2066147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066216 : List Nat := [2, 1, 5, 1, 1, 3, 1, 2, 6]
def baseStart_2066216 : Nat := 118140960795 + 2066216 * 2 ^ 59
def prefixEnd_2066216 : Nat := 4983230072969 + 3 ^ 40 * 2066216 * 2
def baseEnd_2066216 : Nat := 235769320891198478688367

theorem tailTrace_2066216 : CollatzResearch.WordTrace tailWord_2066216 prefixEnd_2066216 235769320891198478688367 := by
  unfold tailWord_2066216
  simp only [CollatzResearch.WordTrace]
  refine ⟨37680544341229894221785251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50240725788306525629047001 37680544341229894221785251)
  ·
    refine ⟨56520816511844841332677877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37680544341229894221785251 56520816511844841332677877)
    ·
      refine ⟨5298826547985453874938551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56520816511844841332677877 5298826547985453874938551)
      ·
        refine ⟨7948239821978180812407827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5298826547985453874938551 7948239821978180812407827)
        ·
          refine ⟨11922359732967271218611741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7948239821978180812407827 11922359732967271218611741)
          ·
            refine ⟨4470884899862726706979403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11922359732967271218611741 4470884899862726706979403)
            ·
              refine ⟨6706327349794090060469105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4470884899862726706979403 6706327349794090060469105)
              ·
                refine ⟨5029745512345567545351829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6706327349794090060469105 5029745512345567545351829)
                ·
                  refine ⟨235769320891198478688367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5029745512345567545351829 235769320891198478688367)
                  ·
                    rfl

theorem cell22_2066216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 6].length) (baseStart_2066216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2066216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2066216 prefixEnd_2066216 := by exact prefixLift 2066216
  have htrace : WordTrace (prefixWord ++ tailWord_2066216) baseStart_2066216 baseEnd_2066216 := by
    simpa [prefixWord, tailWord_2066216, baseEnd_2066216] using wordTrace_append hprefix tailTrace_2066216
  have hstable : (prefixWord ++ tailWord_2066216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066216).length < 2 ^ (prefixWord ++ tailWord_2066216).sum := by decide
  have hdescent : baseEnd_2066216 < baseStart_2066216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066248 : List Nat := [2, 1, 3, 1, 1, 4, 3, 2, 2, 3]
def baseStart_2066248 : Nat := 118140960795 + 2066248 * 2 ^ 59
def prefixEnd_2066248 : Nat := 4983230072969 + 3 ^ 40 * 2066248 * 2
def baseEnd_2066248 : Nat := 707318916927558019265003

theorem tailTrace_2066248 : CollatzResearch.WordTrace tailWord_2066248 prefixEnd_2066248 707318916927558019265003 := by
  unfold tailWord_2066248
  simp only [CollatzResearch.WordTrace]
  refine ⟨37681127909171928954367699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50241503878895905272490265 37681127909171928954367699)
  ·
    refine ⟨56521691863757893431551549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37681127909171928954367699 56521691863757893431551549)
    ·
      refine ⟨21195634448909210036831831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56521691863757893431551549 21195634448909210036831831)
      ·
        refine ⟨31793451673363815055247747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21195634448909210036831831 31793451673363815055247747)
        ·
          refine ⟨47690177510045722582871621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31793451673363815055247747 47690177510045722582871621)
          ·
            refine ⟨8941908283133572984288429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47690177510045722582871621 8941908283133572984288429)
            ·
              refine ⟨3353215606175089869108161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8941908283133572984288429 3353215606175089869108161)
              ·
                refine ⟨2514911704631317401831121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3353215606175089869108161 2514911704631317401831121)
                ·
                  refine ⟨1886183778473488051373341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2514911704631317401831121 1886183778473488051373341)
                  ·
                    refine ⟨707318916927558019265003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1886183778473488051373341 707318916927558019265003)
                    ·
                      rfl

theorem cell22_2066248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_2066248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2066248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2066248 prefixEnd_2066248 := by exact prefixLift 2066248
  have htrace : WordTrace (prefixWord ++ tailWord_2066248) baseStart_2066248 baseEnd_2066248 := by
    simpa [prefixWord, tailWord_2066248, baseEnd_2066248] using wordTrace_append hprefix tailTrace_2066248
  have hstable : (prefixWord ++ tailWord_2066248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066248).length < 2 ^ (prefixWord ++ tailWord_2066248).sum := by decide
  have hdescent : baseEnd_2066248 < baseStart_2066248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066289 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 9]
def baseStart_2066289 : Nat := 118140960795 + 2066289 * 2 ^ 59
def prefixEnd_2066289 : Nat := 4983230072969 + 3 ^ 40 * 2066289 * 2
def baseEnd_2066289 : Nat := 235777650688482526329959

theorem tailTrace_2066289 : CollatzResearch.WordTrace tailWord_2066289 prefixEnd_2066289 235777650688482526329959 := by
  unfold tailWord_2066289
  simp only [CollatzResearch.WordTrace]
  refine ⟨75363751211195321910977921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50242500807463547940651947 75363751211195321910977921)
  ·
    refine ⟨56522813408396491433233441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75363751211195321910977921 56522813408396491433233441)
    ·
      refine ⟨42392110056297368574925081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56522813408396491433233441 42392110056297368574925081)
      ·
        refine ⟨31794082542223026431193811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42392110056297368574925081 31794082542223026431193811)
        ·
          refine ⟨47691123813334539646790717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31794082542223026431193811 47691123813334539646790717)
          ·
            refine ⟨17884171430000452367546519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47691123813334539646790717 17884171430000452367546519)
            ·
              refine ⟨26826257145000678551319779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17884171430000452367546519 26826257145000678551319779)
              ·
                refine ⟨40239385717501017826979669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26826257145000678551319779 40239385717501017826979669)
                ·
                  refine ⟨235777650688482526329959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40239385717501017826979669 235777650688482526329959)
                  ·
                    rfl

theorem cell22_2066289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 9].length) (baseStart_2066289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2066289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2066289 prefixEnd_2066289 := by exact prefixLift 2066289
  have htrace : WordTrace (prefixWord ++ tailWord_2066289) baseStart_2066289 baseEnd_2066289 := by
    simpa [prefixWord, tailWord_2066289, baseEnd_2066289] using wordTrace_append hprefix tailTrace_2066289
  have hstable : (prefixWord ++ tailWord_2066289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066289).length < 2 ^ (prefixWord ++ tailWord_2066289).sum := by decide
  have hdescent : baseEnd_2066289 < baseStart_2066289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066368 : List Nat := [2, 1, 1, 2, 3, 2, 3, 4, 4]
def baseStart_2066368 : Nat := 118140960795 + 2066368 * 2 ^ 59
def prefixEnd_2066368 : Nat := 4983230072969 + 3 ^ 40 * 2066368 * 2
def baseEnd_2066368 : Nat := 235786665126639235421545

theorem tailTrace_2066368 : CollatzResearch.WordTrace tailWord_2066368 prefixEnd_2066368 235786665126639235421545 := by
  unfold tailWord_2066368
  simp only [CollatzResearch.WordTrace]
  refine ⟨37683316288954559201551879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50244421718606078935402505 37683316288954559201551879)
  ·
    refine ⟨56524974433431838802327819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37683316288954559201551879 56524974433431838802327819)
    ·
      refine ⟨84787461650147758203491729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56524974433431838802327819 84787461650147758203491729)
      ·
        refine ⟨63590596237610818652618797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84787461650147758203491729 63590596237610818652618797)
        ·
          refine ⟨23846473589104056994732049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63590596237610818652618797 23846473589104056994732049)
          ·
            refine ⟨17884855191828042746049037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23846473589104056994732049 17884855191828042746049037)
            ·
              refine ⟨6706820696935516029768389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17884855191828042746049037 6706820696935516029768389)
              ·
                refine ⟨1257528880675409255581573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6706820696935516029768389 1257528880675409255581573)
                ·
                  refine ⟨235786665126639235421545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1257528880675409255581573 235786665126639235421545)
                  ·
                    rfl

theorem cell22_2066368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4, 4].length) (baseStart_2066368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2066368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2066368 prefixEnd_2066368 := by exact prefixLift 2066368
  have htrace : WordTrace (prefixWord ++ tailWord_2066368) baseStart_2066368 baseEnd_2066368 := by
    simpa [prefixWord, tailWord_2066368, baseEnd_2066368] using wordTrace_append hprefix tailTrace_2066368
  have hstable : (prefixWord ++ tailWord_2066368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066368).length < 2 ^ (prefixWord ++ tailWord_2066368).sum := by decide
  have hdescent : baseEnd_2066368 < baseStart_2066368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066383 : List Nat := [1, 1, 2, 1, 1, 5, 1, 5, 2, 3]
def baseStart_2066383 : Nat := 118140960795 + 2066383 * 2 ^ 59
def prefixEnd_2066383 : Nat := 4983230072969 + 3 ^ 40 * 2066383 * 2
def baseEnd_2066383 : Nat := 707365130186462667139589

theorem tailTrace_2066383 : CollatzResearch.WordTrace tailWord_2066383 prefixEnd_2066383 707365130186462667139589 := by
  unfold tailWord_2066383
  simp only [CollatzResearch.WordTrace]
  refine ⟨75367179672854775964899803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50244786448569850643266535 75367179672854775964899803)
  ·
    refine ⟨113050769509282163947349705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75367179672854775964899803 113050769509282163947349705)
    ·
      refine ⟨84788077131961622960512279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113050769509282163947349705 84788077131961622960512279)
      ·
        refine ⟨127182115697942434440768419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84788077131961622960512279 127182115697942434440768419)
        ·
          refine ⟨190773173546913651661152629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127182115697942434440768419 190773173546913651661152629)
          ·
            refine ⟨17884985020023154843233059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 190773173546913651661152629 17884985020023154843233059)
            ·
              refine ⟨26827477530034732264849589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17884985020023154843233059 26827477530034732264849589)
              ·
                refine ⟨2515076018440756149829649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26827477530034732264849589 2515076018440756149829649)
                ·
                  refine ⟨1886307013830567112372237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2515076018440756149829649 1886307013830567112372237)
                  ·
                    refine ⟨707365130186462667139589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1886307013830567112372237 707365130186462667139589)
                    ·
                      rfl

theorem cell22_2066383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 2, 3].length) (baseStart_2066383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2066383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2066383 prefixEnd_2066383 := by exact prefixLift 2066383
  have htrace : WordTrace (prefixWord ++ tailWord_2066383) baseStart_2066383 baseEnd_2066383 := by
    simpa [prefixWord, tailWord_2066383, baseEnd_2066383] using wordTrace_append hprefix tailTrace_2066383
  have hstable : (prefixWord ++ tailWord_2066383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066383).length < 2 ^ (prefixWord ++ tailWord_2066383).sum := by decide
  have hdescent : baseEnd_2066383 < baseStart_2066383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066417 : List Nat := [1, 2, 2, 2, 5, 2, 1, 2, 2, 3]
def baseStart_2066417 : Nat := 118140960795 + 2066417 * 2 ^ 59
def prefixEnd_2066417 : Nat := 4983230072969 + 3 ^ 40 * 2066417 * 2
def baseEnd_2066417 : Nat := 707376769081297911789485

theorem tailTrace_2066417 : CollatzResearch.WordTrace tailWord_2066417 prefixEnd_2066417 707376769081297911789485 := by
  unfold tailWord_2066417
  simp only [CollatzResearch.WordTrace]
  refine ⟨75368419754731599771637505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50245613169821066514425003 75368419754731599771637505)
  ·
    refine ⟨56526314816048699828728129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75368419754731599771637505 56526314816048699828728129)
    ·
      refine ⟨42394736112036524871546097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56526314816048699828728129 42394736112036524871546097)
      ·
        refine ⟨31796052084027393653659573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42394736112036524871546097 31796052084027393653659573)
        ·
          refine ⟨2980879882877568155030585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31796052084027393653659573 2980879882877568155030585)
          ·
            refine ⟨2235659912158176116272939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2980879882877568155030585 2235659912158176116272939)
            ·
              refine ⟨3353489868237264174409409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2235659912158176116272939 3353489868237264174409409)
              ·
                refine ⟨2515117401177948130807057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3353489868237264174409409 2515117401177948130807057)
                ·
                  refine ⟨1886338050883461098105293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2515117401177948130807057 1886338050883461098105293)
                  ·
                    refine ⟨707376769081297911789485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1886338050883461098105293 707376769081297911789485)
                    ·
                      rfl

theorem cell22_2066417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 2, 3].length) (baseStart_2066417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2066417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2066417 prefixEnd_2066417 := by exact prefixLift 2066417
  have htrace : WordTrace (prefixWord ++ tailWord_2066417) baseStart_2066417 baseEnd_2066417 := by
    simpa [prefixWord, tailWord_2066417, baseEnd_2066417] using wordTrace_append hprefix tailTrace_2066417
  have hstable : (prefixWord ++ tailWord_2066417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066417).length < 2 ^ (prefixWord ++ tailWord_2066417).sum := by decide
  have hdescent : baseEnd_2066417 < baseStart_2066417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066565 : List Nat := [1, 3, 1, 1, 5, 2, 3, 6]
def baseStart_2066565 : Nat := 118140960795 + 2066565 * 2 ^ 59
def prefixEnd_2066565 : Nat := 4983230072969 + 3 ^ 40 * 2066565 * 2
def baseEnd_2066565 : Nat := 78603048056208317676559

theorem tailTrace_2066565 : CollatzResearch.WordTrace tailWord_2066565 prefixEnd_2066565 78603048056208317676559 := by
  unfold tailWord_2066565
  simp only [CollatzResearch.WordTrace]
  refine ⟨75373817758195421048025149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50249211838796947365350099 75373817758195421048025149)
  ·
    refine ⟨28265181659323282893009431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75373817758195421048025149 28265181659323282893009431)
    ·
      refine ⟨42397772488984924339514147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28265181659323282893009431 42397772488984924339514147)
      ·
        refine ⟨63596658733477386509271221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42397772488984924339514147 63596658733477386509271221)
        ·
          refine ⟨5962186756263504985244177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63596658733477386509271221 5962186756263504985244177)
          ·
            refine ⟨4471640067197628738933133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5962186756263504985244177 4471640067197628738933133)
            ·
              refine ⟨1676865025199110777099925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4471640067197628738933133 1676865025199110777099925)
              ·
                refine ⟨78603048056208317676559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1676865025199110777099925 78603048056208317676559)
                ·
                  rfl

theorem cell22_2066565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 6].length) (baseStart_2066565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2066565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2066565 prefixEnd_2066565 := by exact prefixLift 2066565
  have htrace : WordTrace (prefixWord ++ tailWord_2066565) baseStart_2066565 baseEnd_2066565 := by
    simpa [prefixWord, tailWord_2066565, baseEnd_2066565] using wordTrace_append hprefix tailTrace_2066565
  have hstable : (prefixWord ++ tailWord_2066565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066565).length < 2 ^ (prefixWord ++ tailWord_2066565).sum := by decide
  have hdescent : baseEnd_2066565 < baseStart_2066565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066586 : List Nat := [3, 1, 1, 5, 3, 1, 1, 2, 2, 3]
def baseStart_2066586 : Nat := 118140960795 + 2066586 * 2 ^ 59
def prefixEnd_2066586 : Nat := 4983230072969 + 3 ^ 40 * 2066586 * 2
def baseEnd_2066586 : Nat := 707434621235037804313967

theorem tailTrace_2066586 : CollatzResearch.WordTrace tailWord_2066586 prefixEnd_2066586 707434621235037804313967 := by
  unfold tailWord_2066586
  simp only [CollatzResearch.WordTrace]
  refine ⟨18843645922779835408634903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50249722460746227756359741 18843645922779835408634903)
  ·
    refine ⟨28265468884169753112952355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18843645922779835408634903 28265468884169753112952355)
    ·
      refine ⟨42398203326254629669428533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28265468884169753112952355 42398203326254629669428533)
      ·
        refine ⟨3974831561836371531508925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42398203326254629669428533 3974831561836371531508925)
        ·
          refine ⟨1490561835688639324315847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3974831561836371531508925 1490561835688639324315847)
          ·
            refine ⟨2235842753532958986473771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1490561835688639324315847 2235842753532958986473771)
            ·
              refine ⟨3353764130299438479710657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2235842753532958986473771 3353764130299438479710657)
              ·
                refine ⟨2515323097724578859782993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3353764130299438479710657 2515323097724578859782993)
                ·
                  refine ⟨1886492323293434144837245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2515323097724578859782993 1886492323293434144837245)
                  ·
                    refine ⟨707434621235037804313967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1886492323293434144837245 707434621235037804313967)
                    ·
                      rfl

theorem cell22_2066586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 2, 3].length) (baseStart_2066586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2066586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2066586 prefixEnd_2066586 := by exact prefixLift 2066586
  have htrace : WordTrace (prefixWord ++ tailWord_2066586) baseStart_2066586 baseEnd_2066586 := by
    simpa [prefixWord, tailWord_2066586, baseEnd_2066586] using wordTrace_append hprefix tailTrace_2066586
  have hstable : (prefixWord ++ tailWord_2066586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066586).length < 2 ^ (prefixWord ++ tailWord_2066586).sum := by decide
  have hdescent : baseEnd_2066586 < baseStart_2066586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066597 : List Nat := [1, 3, 1, 2, 1, 3, 1, 6, 1, 3]
def baseStart_2066597 : Nat := 118140960795 + 2066597 * 2 ^ 59
def prefixEnd_2066597 : Nat := 4983230072969 + 3 ^ 40 * 2066597 * 2
def baseEnd_2066597 : Nat := 707438386759837442288933

theorem tailTrace_2066597 : CollatzResearch.WordTrace tailWord_2066597 prefixEnd_2066597 707438386759837442288933 := by
  unfold tailWord_2066597
  simp only [CollatzResearch.WordTrace]
  refine ⟨75374984894079490513190045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50249989929386327008793363 75374984894079490513190045)
  ·
    refine ⟨28265619335279808942446267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75374984894079490513190045 28265619335279808942446267)
    ·
      refine ⟨42398429002919713413669401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28265619335279808942446267 42398429002919713413669401)
      ·
        refine ⟨31798821752189785060252051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42398429002919713413669401 31798821752189785060252051)
        ·
          refine ⟨47698232628284677590378077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31798821752189785060252051 47698232628284677590378077)
          ·
            refine ⟨17886837235606754096391779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47698232628284677590378077 17886837235606754096391779)
            ·
              refine ⟨26830255853410131144587669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17886837235606754096391779 26830255853410131144587669)
              ·
                refine ⟨1257668243128599897402547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26830255853410131144587669 1257668243128599897402547)
                ·
                  refine ⟨1886502364692899846103821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1257668243128599897402547 1886502364692899846103821)
                  ·
                    refine ⟨707438386759837442288933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1886502364692899846103821 707438386759837442288933)
                    ·
                      rfl

theorem cell22_2066597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6, 1, 3].length) (baseStart_2066597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2066597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2066597 prefixEnd_2066597 := by exact prefixLift 2066597
  have htrace : WordTrace (prefixWord ++ tailWord_2066597) baseStart_2066597 baseEnd_2066597 := by
    simpa [prefixWord, tailWord_2066597, baseEnd_2066597] using wordTrace_append hprefix tailTrace_2066597
  have hstable : (prefixWord ++ tailWord_2066597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066597).length < 2 ^ (prefixWord ++ tailWord_2066597).sum := by decide
  have hdescent : baseEnd_2066597 < baseStart_2066597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066670 : List Nat := [4, 1, 2, 1, 1, 1, 1, 5, 1, 5]
def baseStart_2066670 : Nat := 118140960795 + 2066670 * 2 ^ 59
def prefixEnd_2066670 : Nat := 4983230072969 + 3 ^ 40 * 2066670 * 2
def baseEnd_2066670 : Nat := 707463376151689585213709

theorem tailTrace_2066670 : CollatzResearch.WordTrace tailWord_2066670 prefixEnd_2066670 707463376151689585213709 := by
  unfold tailWord_2066670
  simp only [CollatzResearch.WordTrace]
  refine ⟨9422205927851877997574683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50251764948543349320398309 9422205927851877997574683)
  ·
    refine ⟨14133308891777816996362025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9422205927851877997574683 14133308891777816996362025)
    ·
      refine ⟨10599981668833362747271519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14133308891777816996362025 10599981668833362747271519)
      ·
        refine ⟨15899972503250044120907279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10599981668833362747271519 15899972503250044120907279)
        ·
          refine ⟨23849958754875066181360919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15899972503250044120907279 23849958754875066181360919)
          ·
            refine ⟨35774938132312599272041379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23849958754875066181360919 35774938132312599272041379)
            ·
              refine ⟨53662407198468898908062069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35774938132312599272041379 53662407198468898908062069)
              ·
                refine ⟨5030850674856459272630819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53662407198468898908062069 5030850674856459272630819)
                ·
                  refine ⟨7546276012284688908946229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5030850674856459272630819 7546276012284688908946229)
                  ·
                    refine ⟨707463376151689585213709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7546276012284688908946229 707463376151689585213709)
                    ·
                      rfl

theorem cell22_2066670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_2066670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2066670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2066670 prefixEnd_2066670 := by exact prefixLift 2066670
  have htrace : WordTrace (prefixWord ++ tailWord_2066670) baseStart_2066670 baseEnd_2066670 := by
    simpa [prefixWord, tailWord_2066670, baseEnd_2066670] using wordTrace_append hprefix tailTrace_2066670
  have hstable : (prefixWord ++ tailWord_2066670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066670).length < 2 ^ (prefixWord ++ tailWord_2066670).sum := by decide
  have hdescent : baseEnd_2066670 < baseStart_2066670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066674 : List Nat := [3, 2, 1, 3, 2, 3, 1, 2, 1, 4]
def baseStart_2066674 : Nat := 118140960795 + 2066674 * 2 ^ 59
def prefixEnd_2066674 : Nat := 4983230072969 + 3 ^ 40 * 2066674 * 2
def baseEnd_2066674 : Nat := 707464745433434908113697

theorem tailTrace_2066674 : CollatzResearch.WordTrace tailWord_2066674 prefixEnd_2066674 707464745433434908113697 := by
  unfold tailWord_2066674
  simp only [CollatzResearch.WordTrace]
  refine ⟨18844448328700133165935769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50251862209867021775828717 18844448328700133165935769)
  ·
    refine ⟨14133336246525099874451827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18844448328700133165935769 14133336246525099874451827)
    ·
      refine ⟨21200004369787649811677741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14133336246525099874451827 21200004369787649811677741)
      ·
        refine ⟨7950001638670368679379153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21200004369787649811677741 7950001638670368679379153)
        ·
          refine ⟨5962501229002776509534365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7950001638670368679379153 5962501229002776509534365)
          ·
            refine ⟨2235937960876041191075387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5962501229002776509534365 2235937960876041191075387)
            ·
              refine ⟨3353906941314061786613081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2235937960876041191075387 3353906941314061786613081)
              ·
                refine ⟨2515430205985546339959811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3353906941314061786613081 2515430205985546339959811)
                ·
                  refine ⟨3773145308978319509939717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2515430205985546339959811 3773145308978319509939717)
                  ·
                    refine ⟨707464745433434908113697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3773145308978319509939717 707464745433434908113697)
                    ·
                      rfl

theorem cell22_2066674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_2066674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2066674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2066674 prefixEnd_2066674 := by exact prefixLift 2066674
  have htrace : WordTrace (prefixWord ++ tailWord_2066674) baseStart_2066674 baseEnd_2066674 := by
    simpa [prefixWord, tailWord_2066674, baseEnd_2066674] using wordTrace_append hprefix tailTrace_2066674
  have hstable : (prefixWord ++ tailWord_2066674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066674).length < 2 ^ (prefixWord ++ tailWord_2066674).sum := by decide
  have hdescent : baseEnd_2066674 < baseStart_2066674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066760 : List Nat := [2, 1, 3, 1, 1, 2, 3, 2, 2, 5]
def baseStart_2066760 : Nat := 118140960795 + 2066760 * 2 ^ 59
def prefixEnd_2066760 : Nat := 4983230072969 + 3 ^ 40 * 2066760 * 2
def baseEnd_2066760 : Nat := 707494184990959350463433

theorem tailTrace_2066760 : CollatzResearch.WordTrace tailWord_2066760 prefixEnd_2066760 707494184990959350463433 := by
  unfold tailWord_2066760
  simp only [CollatzResearch.WordTrace]
  refine ⟨37690464996244484675686867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50253953328325979567582489 37690464996244484675686867)
  ·
    refine ⟨56535697494366727013530301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37690464996244484675686867 56535697494366727013530301)
    ·
      refine ⟨21200886560387522630073863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56535697494366727013530301 21200886560387522630073863)
      ·
        refine ⟨31801329840581283945110795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21200886560387522630073863 31801329840581283945110795)
        ·
          refine ⟨47701994760871925917666193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31801329840581283945110795 47701994760871925917666193)
          ·
            refine ⟨35776496070653944438249645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47701994760871925917666193 35776496070653944438249645)
            ·
              refine ⟨13416186026495229164343617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35776496070653944438249645 13416186026495229164343617)
              ·
                refine ⟨10062139519871421873257713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13416186026495229164343617 10062139519871421873257713)
                ·
                  refine ⟨7546604639903566404943285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10062139519871421873257713 7546604639903566404943285)
                  ·
                    refine ⟨707494184990959350463433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7546604639903566404943285 707494184990959350463433)
                    ·
                      rfl

theorem cell22_2066760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_2066760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2066760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2066760 prefixEnd_2066760 := by exact prefixLift 2066760
  have htrace : WordTrace (prefixWord ++ tailWord_2066760) baseStart_2066760 baseEnd_2066760 := by
    simpa [prefixWord, tailWord_2066760, baseEnd_2066760] using wordTrace_append hprefix tailTrace_2066760
  have hstable : (prefixWord ++ tailWord_2066760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066760).length < 2 ^ (prefixWord ++ tailWord_2066760).sum := by decide
  have hdescent : baseEnd_2066760 < baseStart_2066760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066807 : List Nat := [1, 1, 3, 1, 1, 2, 2, 7, 4]
def baseStart_2066807 : Nat := 118140960795 + 2066807 * 2 ^ 59
def prefixEnd_2066807 : Nat := 4983230072969 + 3 ^ 40 * 2066807 * 2
def baseEnd_2066807 : Nat := 235836758017155631512763

theorem tailTrace_2066807 : CollatzResearch.WordTrace tailWord_2066807 prefixEnd_2066807 235836758017155631512763 := by
  unfold tailWord_2066807
  simp only [CollatzResearch.WordTrace]
  refine ⟨75382644223318696378334675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50255096148879130918889783 75382644223318696378334675)
  ·
    refine ⟨113073966334978044567502013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75382644223318696378334675 113073966334978044567502013)
    ·
      refine ⟨42402737375616766712813255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113073966334978044567502013 42402737375616766712813255)
      ·
        refine ⟨63604106063425150069219883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42402737375616766712813255 63604106063425150069219883)
        ·
          refine ⟨95406159095137725103829825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63604106063425150069219883 95406159095137725103829825)
          ·
            refine ⟨71554619321353293827872369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95406159095137725103829825 71554619321353293827872369)
            ·
              refine ⟨53665964491014970370904277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71554619321353293827872369 53665964491014970370904277)
              ·
                refine ⟨1257796042758163368068069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 53665964491014970370904277 1257796042758163368068069)
                ·
                  refine ⟨235836758017155631512763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1257796042758163368068069 235836758017155631512763)
                  ·
                    rfl

theorem cell22_2066807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7, 4].length) (baseStart_2066807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2066807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2066807 prefixEnd_2066807 := by exact prefixLift 2066807
  have htrace : WordTrace (prefixWord ++ tailWord_2066807) baseStart_2066807 baseEnd_2066807 := by
    simpa [prefixWord, tailWord_2066807, baseEnd_2066807] using wordTrace_append hprefix tailTrace_2066807
  have hstable : (prefixWord ++ tailWord_2066807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066807).length < 2 ^ (prefixWord ++ tailWord_2066807).sum := by decide
  have hdescent : baseEnd_2066807 < baseStart_2066807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067004 : List Nat := [2, 2, 2, 2, 3, 2, 2, 7]
def baseStart_2067004 : Nat := 118140960795 + 2067004 * 2 ^ 59
def prefixEnd_2067004 : Nat := 4983230072969 + 3 ^ 40 * 2067004 * 2
def baseEnd_2067004 : Nat := 78619745686380449706965

theorem tailTrace_2067004 : CollatzResearch.WordTrace tailWord_2067004 prefixEnd_2067004 78619745686380449706965 := by
  unfold tailWord_2067004
  simp only [CollatzResearch.WordTrace]
  refine ⟨37694914701802499511628033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50259886269069999348837377 37694914701802499511628033)
  ·
    refine ⟨28271186026351874633721025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37694914701802499511628033 28271186026351874633721025)
    ·
      refine ⟨21203389519763905975290769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28271186026351874633721025 21203389519763905975290769)
      ·
        refine ⟨15902542139822929481468077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21203389519763905975290769 15902542139822929481468077)
        ·
          refine ⟨5963453302433598555550529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15902542139822929481468077 5963453302433598555550529)
          ·
            refine ⟨4472589976825198916662897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5963453302433598555550529 4472589976825198916662897)
            ·
              refine ⟨3354442482618899187497173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4472589976825198916662897 3354442482618899187497173)
              ·
                refine ⟨78619745686380449706965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3354442482618899187497173 78619745686380449706965)
                ·
                  rfl

theorem cell22_2067004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 7].length) (baseStart_2067004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067004 prefixEnd_2067004 := by exact prefixLift 2067004
  have htrace : WordTrace (prefixWord ++ tailWord_2067004) baseStart_2067004 baseEnd_2067004 := by
    simpa [prefixWord, tailWord_2067004, baseEnd_2067004] using wordTrace_append hprefix tailTrace_2067004
  have hstable : (prefixWord ++ tailWord_2067004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067004).length < 2 ^ (prefixWord ++ tailWord_2067004).sum := by decide
  have hdescent : baseEnd_2067004 < baseStart_2067004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067012 : List Nat := [2, 3, 5, 1, 1, 2, 1, 2, 1, 4]
def baseStart_2067012 : Nat := 118140960795 + 2067012 * 2 ^ 59
def prefixEnd_2067012 : Nat := 4983230072969 + 3 ^ 40 * 2067012 * 2
def baseEnd_2067012 : Nat := 707580449740914693162661

theorem tailTrace_2067012 : CollatzResearch.WordTrace tailWord_2067012 prefixEnd_2067012 707580449740914693162661 := by
  unfold tailWord_2067012
  simp only [CollatzResearch.WordTrace]
  refine ⟨37695060593788008194773645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50260080791717344259698193 37695060593788008194773645)
  ·
    refine ⟨14135647722670503073040117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37695060593788008194773645 14135647722670503073040117)
    ·
      refine ⟨1325216974000359663097511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14135647722670503073040117 1325216974000359663097511)
      ·
        refine ⟨1987825461000539494646267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1325216974000359663097511 1987825461000539494646267)
        ·
          refine ⟨2981738191500809241969401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1987825461000539494646267 2981738191500809241969401)
          ·
            refine ⟨2236303643625606931477051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2981738191500809241969401 2236303643625606931477051)
            ·
              refine ⟨3354455465438410397215577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2236303643625606931477051 3354455465438410397215577)
              ·
                refine ⟨2515841599078807797911683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3354455465438410397215577 2515841599078807797911683)
                ·
                  refine ⟨3773762398618211696867525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2515841599078807797911683 3773762398618211696867525)
                  ·
                    refine ⟨707580449740914693162661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3773762398618211696867525 707580449740914693162661)
                    ·
                      rfl

theorem cell22_2067012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_2067012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067012 prefixEnd_2067012 := by exact prefixLift 2067012
  have htrace : WordTrace (prefixWord ++ tailWord_2067012) baseStart_2067012 baseEnd_2067012 := by
    simpa [prefixWord, tailWord_2067012, baseEnd_2067012] using wordTrace_append hprefix tailTrace_2067012
  have hstable : (prefixWord ++ tailWord_2067012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067012).length < 2 ^ (prefixWord ++ tailWord_2067012).sum := by decide
  have hdescent : baseEnd_2067012 < baseStart_2067012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067019 : List Nat := [1, 1, 1, 1, 3, 1, 4, 4, 3, 3]
def baseStart_2067019 : Nat := 118140960795 + 2067019 * 2 ^ 59
def prefixEnd_2067019 : Nat := 4983230072969 + 3 ^ 40 * 2067019 * 2
def baseEnd_2067019 : Nat := 707582845983969008237639

theorem tailTrace_2067019 : CollatzResearch.WordTrace tailWord_2067019 prefixEnd_2067019 707582845983969008237639 := by
  unfold tailWord_2067019
  simp only [CollatzResearch.WordTrace]
  refine ⟨75390376498550656585052111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50260250999033771056701407 75390376498550656585052111)
  ·
    refine ⟨113085564747825984877578167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75390376498550656585052111 113085564747825984877578167)
    ·
      refine ⟨169628347121738977316367251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113085564747825984877578167 169628347121738977316367251)
      ·
        refine ⟨254442520682608465974550877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169628347121738977316367251 254442520682608465974550877)
        ·
          refine ⟨95415945255978174740456579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254442520682608465974550877 95415945255978174740456579)
          ·
            refine ⟨143123917883967262110684869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95415945255978174740456579 143123917883967262110684869)
            ·
              refine ⟨26835734603243861645753413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143123917883967262110684869 26835734603243861645753413)
              ·
                refine ⟨5031700238108224058578765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26835734603243861645753413 5031700238108224058578765)
                ·
                  refine ⟨1886887589290584021967037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5031700238108224058578765 1886887589290584021967037)
                  ·
                    refine ⟨707582845983969008237639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1886887589290584021967037 707582845983969008237639)
                    ·
                      rfl

theorem cell22_2067019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 3, 3].length) (baseStart_2067019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067019 prefixEnd_2067019 := by exact prefixLift 2067019
  have htrace : WordTrace (prefixWord ++ tailWord_2067019) baseStart_2067019 baseEnd_2067019 := by
    simpa [prefixWord, tailWord_2067019, baseEnd_2067019] using wordTrace_append hprefix tailTrace_2067019
  have hstable : (prefixWord ++ tailWord_2067019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067019).length < 2 ^ (prefixWord ++ tailWord_2067019).sum := by decide
  have hdescent : baseEnd_2067019 < baseStart_2067019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067032 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 9]
def baseStart_2067032 : Nat := 118140960795 + 2067032 * 2 ^ 59
def prefixEnd_2067032 : Nat := 4983230072969 + 3 ^ 40 * 2067032 * 2
def baseEnd_2067032 : Nat := 235862432049880435887533

theorem tailTrace_2067032 : CollatzResearch.WordTrace tailWord_2067032 prefixEnd_2067032 235862432049880435887533 := by
  unfold tailWord_2067032
  simp only [CollatzResearch.WordTrace]
  refine ⟨37695425323751779902637675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50260567098335706536850233 37695425323751779902637675)
  ·
    refine ⟨56543137985627669853956513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37695425323751779902637675 56543137985627669853956513)
    ·
      refine ⟨42407353489220752390467385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56543137985627669853956513 42407353489220752390467385)
      ·
        refine ⟨31805515116915564292850539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42407353489220752390467385 31805515116915564292850539)
        ·
          refine ⟨47708272675373346439275809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31805515116915564292850539 47708272675373346439275809)
          ·
            refine ⟨35781204506530009829456857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47708272675373346439275809 35781204506530009829456857)
            ·
              refine ⟨26835903379897507372092643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35781204506530009829456857 26835903379897507372092643)
              ·
                refine ⟨40253855069846261058138965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26835903379897507372092643 40253855069846261058138965)
                ·
                  refine ⟨235862432049880435887533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40253855069846261058138965 235862432049880435887533)
                  ·
                    rfl

theorem cell22_2067032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 9].length) (baseStart_2067032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067032 prefixEnd_2067032 := by exact prefixLift 2067032
  have htrace : WordTrace (prefixWord ++ tailWord_2067032) baseStart_2067032 baseEnd_2067032 := by
    simpa [prefixWord, tailWord_2067032, baseEnd_2067032] using wordTrace_append hprefix tailTrace_2067032
  have hstable : (prefixWord ++ tailWord_2067032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067032).length < 2 ^ (prefixWord ++ tailWord_2067032).sum := by decide
  have hdescent : baseEnd_2067032 < baseStart_2067032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067038 : List Nat := [4, 4, 1, 2, 1, 10]
def baseStart_2067038 : Nat := 118140960795 + 2067038 * 2 ^ 59
def prefixEnd_2067038 : Nat := 4983230072969 + 3 ^ 40 * 2067038 * 2
def baseEnd_2067038 : Nat := 8735670988546411012501

theorem tailTrace_2067038 : CollatzResearch.WordTrace tailWord_2067038 prefixEnd_2067038 8735670988546411012501 := by
  unfold tailWord_2067038
  simp only [CollatzResearch.WordTrace]
  refine ⟨9423883685685227853749221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50260712990321215219995845 9423883685685227853749221)
  ·
    refine ⟨1766978191065980222577979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9423883685685227853749221 1766978191065980222577979)
    ·
      refine ⟨2650467286598970333866969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1766978191065980222577979 2650467286598970333866969)
      ·
        refine ⟨1987850464949227750400227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2650467286598970333866969 1987850464949227750400227)
        ·
          refine ⟨2981775697423841625600341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1987850464949227750400227 2981775697423841625600341)
          ·
            refine ⟨8735670988546411012501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2981775697423841625600341 8735670988546411012501)
            ·
              rfl

theorem cell22_2067038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 10].length) (baseStart_2067038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067038 prefixEnd_2067038 := by exact prefixLift 2067038
  have htrace : WordTrace (prefixWord ++ tailWord_2067038) baseStart_2067038 baseEnd_2067038 := by
    simpa [prefixWord, tailWord_2067038, baseEnd_2067038] using wordTrace_append hprefix tailTrace_2067038
  have hstable : (prefixWord ++ tailWord_2067038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067038).length < 2 ^ (prefixWord ++ tailWord_2067038).sum := by decide
  have hdescent : baseEnd_2067038 < baseStart_2067038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067074 : List Nat := [3, 4, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_2067074 : Nat := 118140960795 + 2067074 * 2 ^ 59
def prefixEnd_2067074 : Nat := 4983230072969 + 3 ^ 40 * 2067074 * 2
def baseEnd_2067074 : Nat := 707601673607967198112471

theorem tailTrace_2067074 : CollatzResearch.WordTrace tailWord_2067074 prefixEnd_2067074 707601673607967198112471 := by
  unfold tailWord_2067074
  simp only [CollatzResearch.WordTrace]
  refine ⟨18848095628337850244576069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50261588342234267318869517 18848095628337850244576069)
  ·
    refine ⟨3534017930313346920858013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18848095628337850244576069 3534017930313346920858013)
    ·
      refine ⟨1325256723867505095321755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3534017930313346920858013 1325256723867505095321755)
      ·
        refine ⟨1987885085801257642982633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1325256723867505095321755 1987885085801257642982633)
        ·
          refine ⟨1490913814350943232236975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1987885085801257642982633 1490913814350943232236975)
          ·
            refine ⟨2236370721526414848355463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1490913814350943232236975 2236370721526414848355463)
            ·
              refine ⟨3354556082289622272533195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2236370721526414848355463 3354556082289622272533195)
              ·
                refine ⟨5031834123434433408799793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3354556082289622272533195 5031834123434433408799793)
                ·
                  refine ⟨3773875592575825056599845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5031834123434433408799793 3773875592575825056599845)
                  ·
                    refine ⟨707601673607967198112471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3773875592575825056599845 707601673607967198112471)
                    ·
                      rfl

theorem cell22_2067074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_2067074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067074 prefixEnd_2067074 := by exact prefixLift 2067074
  have htrace : WordTrace (prefixWord ++ tailWord_2067074) baseStart_2067074 baseEnd_2067074 := by
    simpa [prefixWord, tailWord_2067074, baseEnd_2067074] using wordTrace_append hprefix tailTrace_2067074
  have hstable : (prefixWord ++ tailWord_2067074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067074).length < 2 ^ (prefixWord ++ tailWord_2067074).sum := by decide
  have hdescent : baseEnd_2067074 < baseStart_2067074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067079 : List Nat := [1, 1, 4, 2, 1, 2, 1, 3, 3, 4]
def baseStart_2067079 : Nat := 118140960795 + 2067079 * 2 ^ 59
def prefixEnd_2067079 : Nat := 4983230072969 + 3 ^ 40 * 2067079 * 2
def baseEnd_2067079 : Nat := 707603385210148851737455

theorem tailTrace_2067079 : CollatzResearch.WordTrace tailWord_2067079 prefixEnd_2067079 707603385210148851737455 := by
  unfold tailWord_2067079
  simp only [CollatzResearch.WordTrace]
  refine ⟨75392564878333286832236291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50261709918888857888157527 75392564878333286832236291)
  ·
    refine ⟨113088847317499930248354437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75392564878333286832236291 113088847317499930248354437)
    ·
      refine ⟨21204158872031236921566457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113088847317499930248354437 21204158872031236921566457)
      ·
        refine ⟨15903119154023427691174843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21204158872031236921566457 15903119154023427691174843)
        ·
          refine ⟨23854678731035141536762265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15903119154023427691174843 23854678731035141536762265)
          ·
            refine ⟨17891009048276356152571699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23854678731035141536762265 17891009048276356152571699)
            ·
              refine ⟨26836513572414534228857549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17891009048276356152571699 26836513572414534228857549)
              ·
                refine ⟨10063692589655450335821581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26836513572414534228857549 10063692589655450335821581)
                ·
                  refine ⟨3773884721120793875933093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10063692589655450335821581 3773884721120793875933093)
                  ·
                    refine ⟨707603385210148851737455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3773884721120793875933093 707603385210148851737455)
                    ·
                      rfl

theorem cell22_2067079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_2067079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067079 prefixEnd_2067079 := by exact prefixLift 2067079
  have htrace : WordTrace (prefixWord ++ tailWord_2067079) baseStart_2067079 baseEnd_2067079 := by
    simpa [prefixWord, tailWord_2067079, baseEnd_2067079] using wordTrace_append hprefix tailTrace_2067079
  have hstable : (prefixWord ++ tailWord_2067079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067079).length < 2 ^ (prefixWord ++ tailWord_2067079).sum := by decide
  have hdescent : baseEnd_2067079 < baseStart_2067079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067096 : List Nat := [2, 1, 2, 4, 1, 1, 3, 3, 1, 4]
def baseStart_2067096 : Nat := 118140960795 + 2067096 * 2 ^ 59
def prefixEnd_2067096 : Nat := 4983230072969 + 3 ^ 40 * 2067096 * 2
def baseEnd_2067096 : Nat := 707609204657566474062403

theorem tailTrace_2067096 : CollatzResearch.WordTrace tailWord_2067096 prefixEnd_2067096 707609204657566474062403 := by
  unfold tailWord_2067096
  simp only [CollatzResearch.WordTrace]
  refine ⟨37696592459635849367802571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50262123279514465823736761 37696592459635849367802571)
  ·
    refine ⟨56544888689453774051703857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37696592459635849367802571 56544888689453774051703857)
    ·
      refine ⟨42408666517090330538777893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56544888689453774051703857 42408666517090330538777893)
      ·
        refine ⟨7951624971954436976020855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42408666517090330538777893 7951624971954436976020855)
        ·
          refine ⟨11927437457931655464031283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7951624971954436976020855 11927437457931655464031283)
          ·
            refine ⟨17891156186897483196046925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11927437457931655464031283 17891156186897483196046925)
            ·
              refine ⟨6709183570086556198517597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17891156186897483196046925 6709183570086556198517597)
              ·
                refine ⟨2515943838782458574444099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6709183570086556198517597 2515943838782458574444099)
                ·
                  refine ⟨3773915758173687861666149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2515943838782458574444099 3773915758173687861666149)
                  ·
                    refine ⟨707609204657566474062403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3773915758173687861666149 707609204657566474062403)
                    ·
                      rfl

theorem cell22_2067096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_2067096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067096 prefixEnd_2067096 := by exact prefixLift 2067096
  have htrace : WordTrace (prefixWord ++ tailWord_2067096) baseStart_2067096 baseEnd_2067096 := by
    simpa [prefixWord, tailWord_2067096, baseEnd_2067096] using wordTrace_append hprefix tailTrace_2067096
  have hstable : (prefixWord ++ tailWord_2067096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067096).length < 2 ^ (prefixWord ++ tailWord_2067096).sum := by decide
  have hdescent : baseEnd_2067096 < baseStart_2067096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067199 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 4, 5]
def baseStart_2067199 : Nat := 118140960795 + 2067199 * 2 ^ 59
def prefixEnd_2067199 : Nat := 4983230072969 + 3 ^ 40 * 2067199 * 2
def baseEnd_2067199 : Nat := 707644463662508538737087

theorem tailTrace_2067199 : CollatzResearch.WordTrace tailWord_2067199 prefixEnd_2067199 707644463662508538737087 := by
  unfold tailWord_2067199
  simp only [CollatzResearch.WordTrace]
  refine ⟨75396941637898547326604651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50264627758599031551069767 75396941637898547326604651)
  ·
    refine ⟨113095412456847820989906977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75396941637898547326604651 113095412456847820989906977)
    ·
      refine ⟨84821559342635865742430233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113095412456847820989906977 84821559342635865742430233)
      ·
        refine ⟨63616169506976899306822675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84821559342635865742430233 63616169506976899306822675)
        ·
          refine ⟨95424254260465348960234013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63616169506976899306822675 95424254260465348960234013)
          ·
            refine ⟨35784095347674505860087755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95424254260465348960234013 35784095347674505860087755)
            ·
              refine ⟨53676143021511758790131633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35784095347674505860087755 53676143021511758790131633)
              ·
                refine ⟨40257107266133819092598725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53676143021511758790131633 40257107266133819092598725)
                ·
                  refine ⟨7548207612400091079862261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40257107266133819092598725 7548207612400091079862261)
                  ·
                    refine ⟨707644463662508538737087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7548207612400091079862261 707644463662508538737087)
                    ·
                      rfl

theorem cell22_2067199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 5].length) (baseStart_2067199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067199 prefixEnd_2067199 := by exact prefixLift 2067199
  have htrace : WordTrace (prefixWord ++ tailWord_2067199) baseStart_2067199 baseEnd_2067199 := by
    simpa [prefixWord, tailWord_2067199, baseEnd_2067199] using wordTrace_append hprefix tailTrace_2067199
  have hstable : (prefixWord ++ tailWord_2067199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067199).length < 2 ^ (prefixWord ++ tailWord_2067199).sum := by decide
  have hdescent : baseEnd_2067199 < baseStart_2067199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067231 : List Nat := [1, 1, 2, 4, 2, 2, 1, 2, 3, 4]
def baseStart_2067231 : Nat := 118140960795 + 2067231 * 2 ^ 59
def prefixEnd_2067231 : Nat := 4983230072969 + 3 ^ 40 * 2067231 * 2
def baseEnd_2067231 : Nat := 707655417916471121936989

theorem tailTrace_2067231 : CollatzResearch.WordTrace tailWord_2067231 prefixEnd_2067231 707655417916471121936989 := by
  unfold tailWord_2067231
  simp only [CollatzResearch.WordTrace]
  refine ⟨75398108773782616791769547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50265405849188411194513031 75398108773782616791769547)
  ·
    refine ⟨113097163160673925187654321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75398108773782616791769547 113097163160673925187654321)
    ·
      refine ⟨84822872370505443890740741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113097163160673925187654321 84822872370505443890740741)
      ·
        refine ⟨15904288569469770729513889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84822872370505443890740741 15904288569469770729513889)
        ·
          refine ⟨11928216427102328047135417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15904288569469770729513889 11928216427102328047135417)
          ·
            refine ⟨8946162320326746035351563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11928216427102328047135417 8946162320326746035351563)
            ·
              refine ⟨13419243480490119053027345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8946162320326746035351563 13419243480490119053027345)
              ·
                refine ⟨10064432610367589289770509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13419243480490119053027345 10064432610367589289770509)
                ·
                  refine ⟨3774162228887845983663941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10064432610367589289770509 3774162228887845983663941)
                  ·
                    refine ⟨707655417916471121936989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3774162228887845983663941 707655417916471121936989)
                    ·
                      rfl

theorem cell22_2067231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 4].length) (baseStart_2067231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067231 prefixEnd_2067231 := by exact prefixLift 2067231
  have htrace : WordTrace (prefixWord ++ tailWord_2067231) baseStart_2067231 baseEnd_2067231 := by
    simpa [prefixWord, tailWord_2067231, baseEnd_2067231] using wordTrace_append hprefix tailTrace_2067231
  have hstable : (prefixWord ++ tailWord_2067231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067231).length < 2 ^ (prefixWord ++ tailWord_2067231).sum := by decide
  have hdescent : baseEnd_2067231 < baseStart_2067231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067263 : List Nat := [1, 1, 2, 2, 5, 1, 1, 5, 4]
def baseStart_2067263 : Nat := 118140960795 + 2067263 * 2 ^ 59
def prefixEnd_2067263 : Nat := 4983230072969 + 3 ^ 40 * 2067263 * 2
def baseEnd_2067263 : Nat := 235888790723477901712297

theorem tailTrace_2067263 : CollatzResearch.WordTrace tailWord_2067263 prefixEnd_2067263 235888790723477901712297 := by
  unfold tailWord_2067263
  simp only [CollatzResearch.WordTrace]
  refine ⟨75399275909666686256934443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50266183939777790837956295 75399275909666686256934443)
  ·
    refine ⟨113098913864500029385401665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75399275909666686256934443 113098913864500029385401665)
    ·
      refine ⟨84824185398375022039051249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113098913864500029385401665 84824185398375022039051249)
      ·
        refine ⟨63618139048781266529288437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84824185398375022039051249 63618139048781266529288437)
        ·
          refine ⟨5964200535823243737120791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63618139048781266529288437 5964200535823243737120791)
          ·
            refine ⟨8946300803734865605681187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5964200535823243737120791 8946300803734865605681187)
            ·
              refine ⟨13419451205602298408521781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8946300803734865605681187 13419451205602298408521781)
              ·
                refine ⟨1258073550525215475798917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13419451205602298408521781 1258073550525215475798917)
                ·
                  refine ⟨235888790723477901712297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1258073550525215475798917 235888790723477901712297)
                  ·
                    rfl

theorem cell22_2067263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5, 4].length) (baseStart_2067263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067263 prefixEnd_2067263 := by exact prefixLift 2067263
  have htrace : WordTrace (prefixWord ++ tailWord_2067263) baseStart_2067263 baseEnd_2067263 := by
    simpa [prefixWord, tailWord_2067263, baseEnd_2067263] using wordTrace_append hprefix tailTrace_2067263
  have hstable : (prefixWord ++ tailWord_2067263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067263).length < 2 ^ (prefixWord ++ tailWord_2067263).sum := by decide
  have hdescent : baseEnd_2067263 < baseStart_2067263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067295 : List Nat := [1, 1, 2, 3, 1, 3, 5, 1, 2, 3]
def baseStart_2067295 : Nat := 118140960795 + 2067295 * 2 ^ 59
def prefixEnd_2067295 : Nat := 4983230072969 + 3 ^ 40 * 2067295 * 2
def baseEnd_2067295 : Nat := 707677326424396288336793

theorem tailTrace_2067295 : CollatzResearch.WordTrace tailWord_2067295 prefixEnd_2067295 707677326424396288336793 := by
  unfold tailWord_2067295
  simp only [CollatzResearch.WordTrace]
  refine ⟨75400443045550755722099339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50266962030367170481399559 75400443045550755722099339)
  ·
    refine ⟨113100664568326133583149009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75400443045550755722099339 113100664568326133583149009)
    ·
      refine ⟨84825498426244600187361757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113100664568326133583149009 84825498426244600187361757)
      ·
        refine ⟨31809561909841725070260659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84825498426244600187361757 31809561909841725070260659)
        ·
          refine ⟨47714342864762587605390989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31809561909841725070260659 47714342864762587605390989)
          ·
            refine ⟨17892878574285970352021621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47714342864762587605390989 17892878574285970352021621)
            ·
              refine ⟨1677457366339309720502027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17892878574285970352021621 1677457366339309720502027)
              ·
                refine ⟨2516186049508964580753041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1677457366339309720502027 2516186049508964580753041)
                ·
                  refine ⟨1887139537131723435564781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2516186049508964580753041 1887139537131723435564781)
                  ·
                    refine ⟨707677326424396288336793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1887139537131723435564781 707677326424396288336793)
                    ·
                      rfl

theorem cell22_2067295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 2, 3].length) (baseStart_2067295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067295 prefixEnd_2067295 := by exact prefixLift 2067295
  have htrace : WordTrace (prefixWord ++ tailWord_2067295) baseStart_2067295 baseEnd_2067295 := by
    simpa [prefixWord, tailWord_2067295, baseEnd_2067295] using wordTrace_append hprefix tailTrace_2067295
  have hstable : (prefixWord ++ tailWord_2067295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067295).length < 2 ^ (prefixWord ++ tailWord_2067295).sum := by decide
  have hdescent : baseEnd_2067295 < baseStart_2067295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067340 : List Nat := [2, 2, 1, 2, 1, 2, 2, 6, 1, 3]
def baseStart_2067340 : Nat := 118140960795 + 2067340 * 2 ^ 59
def prefixEnd_2067340 : Nat := 4983230072969 + 3 ^ 40 * 2067340 * 2
def baseEnd_2067340 : Nat := 707692730844031170961655

theorem tailTrace_2067340 : CollatzResearch.WordTrace tailWord_2067340 prefixEnd_2067340 707692730844031170961655 := by
  unfold tailWord_2067340
  simp only [CollatzResearch.WordTrace]
  refine ⟨37701042165193864203743737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50268056220258485604991649 37701042165193864203743737)
  ·
    refine ⟨28275781623895398152807803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37701042165193864203743737 28275781623895398152807803)
    ·
      refine ⟨42413672435843097229211705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28275781623895398152807803 42413672435843097229211705)
      ·
        refine ⟨31810254326882322921908779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42413672435843097229211705 31810254326882322921908779)
        ·
          refine ⟨47715381490323484382863169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31810254326882322921908779 47715381490323484382863169)
          ·
            refine ⟨35786536117742613287147377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47715381490323484382863169 35786536117742613287147377)
            ·
              refine ⟨26839902088306959965360533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35786536117742613287147377 26839902088306959965360533)
              ·
                refine ⟨1258120410389388748376275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26839902088306959965360533 1258120410389388748376275)
                ·
                  refine ⟨1887180615584083122564413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1258120410389388748376275 1887180615584083122564413)
                  ·
                    refine ⟨707692730844031170961655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1887180615584083122564413 707692730844031170961655)
                    ·
                      rfl

theorem cell22_2067340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6, 1, 3].length) (baseStart_2067340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067340 prefixEnd_2067340 := by exact prefixLift 2067340
  have htrace : WordTrace (prefixWord ++ tailWord_2067340) baseStart_2067340 baseEnd_2067340 := by
    simpa [prefixWord, tailWord_2067340, baseEnd_2067340] using wordTrace_append hprefix tailTrace_2067340
  have hstable : (prefixWord ++ tailWord_2067340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067340).length < 2 ^ (prefixWord ++ tailWord_2067340).sum := by decide
  have hdescent : baseEnd_2067340 < baseStart_2067340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067346 : List Nat := [3, 2, 3, 2, 3, 1, 2, 1, 2, 3]
def baseStart_2067346 : Nat := 118140960795 + 2067346 * 2 ^ 59
def prefixEnd_2067346 : Nat := 4983230072969 + 3 ^ 40 * 2067346 * 2
def baseEnd_2067346 : Nat := 707694784766649155311637

theorem tailTrace_2067346 : CollatzResearch.WordTrace tailWord_2067346 prefixEnd_2067346 707694784766649155311637 := by
  unfold tailWord_2067346
  simp only [CollatzResearch.WordTrace]
  refine ⟨18850575792091497858051473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50268202112243994288137261 18850575792091497858051473)
  ·
    refine ⟨14137931844068623393538605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18850575792091497858051473 14137931844068623393538605)
    ·
      refine ⟨5301724441525733772576977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14137931844068623393538605 5301724441525733772576977)
      ·
        refine ⟨3976293331144300329432733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5301724441525733772576977 3976293331144300329432733)
        ·
          refine ⟨1491109999179112623537275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3976293331144300329432733 1491109999179112623537275)
          ·
            refine ⟨2236664998768668935305913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491109999179112623537275 2236664998768668935305913)
            ·
              refine ⟨1677498749076501701479435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2236664998768668935305913 1677498749076501701479435)
              ·
                refine ⟨2516248123614752552219153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1677498749076501701479435 2516248123614752552219153)
                ·
                  refine ⟨1887186092711064414164365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2516248123614752552219153 1887186092711064414164365)
                  ·
                    refine ⟨707694784766649155311637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1887186092711064414164365 707694784766649155311637)
                    ·
                      rfl

theorem cell22_2067346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_2067346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067346 prefixEnd_2067346 := by exact prefixLift 2067346
  have htrace : WordTrace (prefixWord ++ tailWord_2067346) baseStart_2067346 baseEnd_2067346 := by
    simpa [prefixWord, tailWord_2067346, baseEnd_2067346] using wordTrace_append hprefix tailTrace_2067346
  have hstable : (prefixWord ++ tailWord_2067346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067346).length < 2 ^ (prefixWord ++ tailWord_2067346).sum := by decide
  have hdescent : baseEnd_2067346 < baseStart_2067346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067351 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 1, 7]
def baseStart_2067351 : Nat := 118140960795 + 2067351 * 2 ^ 59
def prefixEnd_2067351 : Nat := 4983230072969 + 3 ^ 40 * 2067351 * 2
def baseEnd_2067351 : Nat := 707696496368830808936621

theorem tailTrace_2067351 : CollatzResearch.WordTrace tailWord_2067351 prefixEnd_2067351 707696496368830808936621 := by
  unfold tailWord_2067351
  simp only [CollatzResearch.WordTrace]
  refine ⟨75402485533347877286137907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50268323688898584857425271 75402485533347877286137907)
  ·
    refine ⟨113103728300021815929206861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75402485533347877286137907 113103728300021815929206861)
    ·
      refine ⟨42413898112508180973452573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113103728300021815929206861 42413898112508180973452573)
      ·
        refine ⟨15905211792190567865044715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42413898112508180973452573 15905211792190567865044715)
        ·
          refine ⟨23857817688285851797567073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15905211792190567865044715 23857817688285851797567073)
          ·
            refine ⟨17893363266214388848175305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23857817688285851797567073 17893363266214388848175305)
            ·
              refine ⟨13420022449660791636131479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17893363266214388848175305 13420022449660791636131479)
              ·
                refine ⟨20130033674491187454197219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13420022449660791636131479 20130033674491187454197219)
                ·
                  refine ⟨30195050511736781181295829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20130033674491187454197219 30195050511736781181295829)
                  ·
                    refine ⟨707696496368830808936621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30195050511736781181295829 707696496368830808936621)
                    ·
                      rfl

theorem cell22_2067351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_2067351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067351 prefixEnd_2067351 := by exact prefixLift 2067351
  have htrace : WordTrace (prefixWord ++ tailWord_2067351) baseStart_2067351 baseEnd_2067351 := by
    simpa [prefixWord, tailWord_2067351, baseEnd_2067351] using wordTrace_append hprefix tailTrace_2067351
  have hstable : (prefixWord ++ tailWord_2067351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067351).length < 2 ^ (prefixWord ++ tailWord_2067351).sum := by decide
  have hdescent : baseEnd_2067351 < baseStart_2067351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067383 : List Nat := [1, 1, 3, 1, 3, 1, 2, 5, 1, 4]
def baseStart_2067383 : Nat := 118140960795 + 2067383 * 2 ^ 59
def prefixEnd_2067383 : Nat := 4983230072969 + 3 ^ 40 * 2067383 * 2
def baseEnd_2067383 : Nat := 707707450622793392136523

theorem tailTrace_2067383 : CollatzResearch.WordTrace tailWord_2067383 prefixEnd_2067383 707707450622793392136523 := by
  unfold tailWord_2067383
  simp only [CollatzResearch.WordTrace]
  refine ⟨75403652669231946751302803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50269101779487964500868535 75403652669231946751302803)
  ·
    refine ⟨113105479003847920126954205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75403652669231946751302803 113105479003847920126954205)
    ·
      refine ⟨42414554626442970047607827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113105479003847920126954205 42414554626442970047607827)
      ·
        refine ⟨63621831939664455071411741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42414554626442970047607827 63621831939664455071411741)
        ·
          refine ⟨23858186977374170651779403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63621831939664455071411741 23858186977374170651779403)
          ·
            refine ⟨35787280466061255977669105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23858186977374170651779403 35787280466061255977669105)
            ·
              refine ⟨26840460349545941983251829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35787280466061255977669105 26840460349545941983251829)
              ·
                refine ⟨2516293157769932060929859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26840460349545941983251829 2516293157769932060929859)
                ·
                  refine ⟨3774439736654898091394789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2516293157769932060929859 3774439736654898091394789)
                  ·
                    refine ⟨707707450622793392136523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3774439736654898091394789 707707450622793392136523)
                    ·
                      rfl

theorem cell22_2067383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 4].length) (baseStart_2067383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067383 prefixEnd_2067383 := by exact prefixLift 2067383
  have htrace : WordTrace (prefixWord ++ tailWord_2067383) baseStart_2067383 baseEnd_2067383 := by
    simpa [prefixWord, tailWord_2067383, baseEnd_2067383] using wordTrace_append hprefix tailTrace_2067383
  have hstable : (prefixWord ++ tailWord_2067383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067383).length < 2 ^ (prefixWord ++ tailWord_2067383).sum := by decide
  have hdescent : baseEnd_2067383 < baseStart_2067383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067428 : List Nat := [2, 3, 1, 1, 1, 1, 2, 5, 2, 4]
def baseStart_2067428 : Nat := 118140960795 + 2067428 * 2 ^ 59
def prefixEnd_2067428 : Nat := 4983230072969 + 3 ^ 40 * 2067428 * 2
def baseEnd_2067428 : Nat := 707722855042428274761385

theorem tailTrace_2067428 : CollatzResearch.WordTrace tailWord_2067428 prefixEnd_2067428 707722855042428274761385 := by
  unfold tailWord_2067428
  simp only [CollatzResearch.WordTrace]
  refine ⟨37702646977034459718345469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50270195969379279624460625 37702646977034459718345469)
  ·
    refine ⟨14138492616387922394379551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37702646977034459718345469 14138492616387922394379551)
    ·
      refine ⟨21207738924581883591569327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14138492616387922394379551 21207738924581883591569327)
      ·
        refine ⟨31811608386872825387353991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21207738924581883591569327 31811608386872825387353991)
        ·
          refine ⟨47717412580309238081030987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31811608386872825387353991 47717412580309238081030987)
          ·
            refine ⟨71576118870463857121546481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47717412580309238081030987 71576118870463857121546481)
            ·
              refine ⟨53682089152847892841159861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71576118870463857121546481 53682089152847892841159861)
              ·
                refine ⟨5032695858079489953858737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53682089152847892841159861 5032695858079489953858737)
                ·
                  refine ⟨3774521893559617465394053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5032695858079489953858737 3774521893559617465394053)
                  ·
                    refine ⟨707722855042428274761385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3774521893559617465394053 707722855042428274761385)
                    ·
                      rfl

theorem cell22_2067428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_2067428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067428 prefixEnd_2067428 := by exact prefixLift 2067428
  have htrace : WordTrace (prefixWord ++ tailWord_2067428) baseStart_2067428 baseEnd_2067428 := by
    simpa [prefixWord, tailWord_2067428, baseEnd_2067428] using wordTrace_append hprefix tailTrace_2067428
  have hstable : (prefixWord ++ tailWord_2067428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067428).length < 2 ^ (prefixWord ++ tailWord_2067428).sum := by decide
  have hdescent : baseEnd_2067428 < baseStart_2067428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067552 : List Nat := [2, 1, 1, 3, 2, 2, 5, 1, 1, 4]
def baseStart_2067552 : Nat := 118140960795 + 2067552 * 2 ^ 59
def prefixEnd_2067552 : Nat := 4983230072969 + 3 ^ 40 * 2067552 * 2
def baseEnd_2067552 : Nat := 707765302776533284661005

theorem tailTrace_2067552 : CollatzResearch.WordTrace tailWord_2067552 prefixEnd_2067552 707765302776533284661005 := by
  unfold tailWord_2067552
  simp only [CollatzResearch.WordTrace]
  refine ⟨37704908302809844307102455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50273211070413125742803273 37704908302809844307102455)
  ·
    refine ⟨56557362454214766460653683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37704908302809844307102455 56557362454214766460653683)
    ·
      refine ⟨84836043681322149690980525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56557362454214766460653683 84836043681322149690980525)
      ·
        refine ⟨31813516380495806134117697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84836043681322149690980525 31813516380495806134117697)
        ·
          refine ⟨23860137285371854600588273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31813516380495806134117697 23860137285371854600588273)
          ·
            refine ⟨17895102964028890950441205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23860137285371854600588273 17895102964028890950441205)
            ·
              refine ⟨1677665902877708526603863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17895102964028890950441205 1677665902877708526603863)
              ·
                refine ⟨2516498854316562789905795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1677665902877708526603863 2516498854316562789905795)
                ·
                  refine ⟨3774748281474844184858693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2516498854316562789905795 3774748281474844184858693)
                  ·
                    refine ⟨707765302776533284661005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3774748281474844184858693 707765302776533284661005)
                    ·
                      rfl

theorem cell22_2067552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 1, 4].length) (baseStart_2067552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067552 prefixEnd_2067552 := by exact prefixLift 2067552
  have htrace : WordTrace (prefixWord ++ tailWord_2067552) baseStart_2067552 baseEnd_2067552 := by
    simpa [prefixWord, tailWord_2067552, baseEnd_2067552] using wordTrace_append hprefix tailTrace_2067552
  have hstable : (prefixWord ++ tailWord_2067552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067552).length < 2 ^ (prefixWord ++ tailWord_2067552).sum := by decide
  have hdescent : baseEnd_2067552 < baseStart_2067552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067560 : List Nat := [2, 1, 4, 4, 2, 1, 2, 2, 1, 3]
def baseStart_2067560 : Nat := 118140960795 + 2067560 * 2 ^ 59
def prefixEnd_2067560 : Nat := 4983230072969 + 3 ^ 40 * 2067560 * 2
def baseEnd_2067560 : Nat := 707768041340023930460981

theorem tailTrace_2067560 : CollatzResearch.WordTrace tailWord_2067560 prefixEnd_2067560 707768041340023930460981 := by
  unfold tailWord_2067560
  simp only [CollatzResearch.WordTrace]
  refine ⟨37705054194795352990248067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50273405593060470653664089 37705054194795352990248067)
  ·
    refine ⟨56557581292193029485372101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37705054194795352990248067 56557581292193029485372101)
    ·
      refine ⟨10604546492286193028507269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56557581292193029485372101 10604546492286193028507269)
      ·
        refine ⟨1988352467303661192845113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10604546492286193028507269 1988352467303661192845113)
        ·
          refine ⟨1491264350477745894633835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1988352467303661192845113 1491264350477745894633835)
          ·
            refine ⟨2236896525716618841950753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491264350477745894633835 2236896525716618841950753)
            ·
              refine ⟨1677672394287464131463065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2236896525716618841950753 1677672394287464131463065)
              ·
                refine ⟨1258254295715598098597299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1677672394287464131463065 1258254295715598098597299)
                ·
                  refine ⟨1887381443573397147895949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1258254295715598098597299 1887381443573397147895949)
                  ·
                    refine ⟨707768041340023930460981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1887381443573397147895949 707768041340023930460981)
                    ·
                      rfl

theorem cell22_2067560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_2067560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067560 prefixEnd_2067560 := by exact prefixLift 2067560
  have htrace : WordTrace (prefixWord ++ tailWord_2067560) baseStart_2067560 baseEnd_2067560 := by
    simpa [prefixWord, tailWord_2067560, baseEnd_2067560] using wordTrace_append hprefix tailTrace_2067560
  have hstable : (prefixWord ++ tailWord_2067560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067560).length < 2 ^ (prefixWord ++ tailWord_2067560).sum := by decide
  have hdescent : baseEnd_2067560 < baseStart_2067560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067736 : List Nat := [2, 1, 2, 3, 1, 5, 2, 2, 4]
def baseStart_2067736 : Nat := 118140960795 + 2067736 * 2 ^ 59
def prefixEnd_2067736 : Nat := 4983230072969 + 3 ^ 40 * 2067736 * 2
def baseEnd_2067736 : Nat := 235942763245606046020147

theorem tailTrace_2067736 : CollatzResearch.WordTrace tailWord_2067736 prefixEnd_2067736 235942763245606046020147 := by
  unfold tailWord_2067736
  simp only [CollatzResearch.WordTrace]
  refine ⟨37708263818476544019451531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50277685091302058692602041 37708263818476544019451531)
  ·
    refine ⟨56562395727714816029177297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37708263818476544019451531 56562395727714816029177297)
    ·
      refine ⟨42421796795786112021882973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56562395727714816029177297 42421796795786112021882973)
      ·
        refine ⟨15908173798419792008206115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42421796795786112021882973 15908173798419792008206115)
        ·
          refine ⟨23862260697629688012309173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15908173798419792008206115 23862260697629688012309173)
          ·
            refine ⟨2237086940402783251153985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23862260697629688012309173 2237086940402783251153985)
            ·
              refine ⟨1677815205302087438365489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2237086940402783251153985 1677815205302087438365489)
              ·
                refine ⟨1258361403976565578774117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1677815205302087438365489 1258361403976565578774117)
                ·
                  refine ⟨235942763245606046020147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1258361403976565578774117 235942763245606046020147)
                  ·
                    rfl

theorem cell22_2067736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2, 4].length) (baseStart_2067736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067736 prefixEnd_2067736 := by exact prefixLift 2067736
  have htrace : WordTrace (prefixWord ++ tailWord_2067736) baseStart_2067736 baseEnd_2067736 := by
    simpa [prefixWord, tailWord_2067736, baseEnd_2067736] using wordTrace_append hprefix tailTrace_2067736
  have hstable : (prefixWord ++ tailWord_2067736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067736).length < 2 ^ (prefixWord ++ tailWord_2067736).sum := by decide
  have hdescent : baseEnd_2067736 < baseStart_2067736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067745 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 2, 7]
def baseStart_2067745 : Nat := 118140960795 + 2067745 * 2 ^ 59
def prefixEnd_2067745 : Nat := 4983230072969 + 3 ^ 40 * 2067745 * 2
def baseEnd_2067745 : Nat := 707831370620745114585413

theorem tailTrace_2067745 : CollatzResearch.WordTrace tailWord_2067745 prefixEnd_2067745 707831370620745114585413 := by
  unfold tailWord_2067745
  simp only [CollatzResearch.WordTrace]
  refine ⟨75416855893920482575980689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50277903929280321717320459 75416855893920482575980689)
  ·
    refine ⟨56562641920440361931985517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75416855893920482575980689 56562641920440361931985517)
    ·
      refine ⟨21210990720165135724494569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56562641920440361931985517 21210990720165135724494569)
      ·
        refine ⟨15908243040123851793370927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21210990720165135724494569 15908243040123851793370927)
        ·
          refine ⟨23862364560185777690056391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15908243040123851793370927 23862364560185777690056391)
          ·
            refine ⟨35793546840278666535084587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23862364560185777690056391 35793546840278666535084587)
            ·
              refine ⟨53690320260417999802626881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35793546840278666535084587 53690320260417999802626881)
              ·
                refine ⟨40267740195313499851970161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53690320260417999802626881 40267740195313499851970161)
                ·
                  refine ⟨30200805146485124888977621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40267740195313499851970161 30200805146485124888977621)
                  ·
                    refine ⟨707831370620745114585413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30200805146485124888977621 707831370620745114585413)
                    ·
                      rfl

theorem cell22_2067745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_2067745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067745 prefixEnd_2067745 := by exact prefixLift 2067745
  have htrace : WordTrace (prefixWord ++ tailWord_2067745) baseStart_2067745 baseEnd_2067745 := by
    simpa [prefixWord, tailWord_2067745, baseEnd_2067745] using wordTrace_append hprefix tailTrace_2067745
  have hstable : (prefixWord ++ tailWord_2067745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067745).length < 2 ^ (prefixWord ++ tailWord_2067745).sum := by decide
  have hdescent : baseEnd_2067745 < baseStart_2067745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067747 : List Nat := [1, 1, 1, 4, 2, 5, 1, 7]
def baseStart_2067747 : Nat := 118140960795 + 2067747 * 2 ^ 59
def prefixEnd_2067747 : Nat := 4983230072969 + 3 ^ 40 * 2067747 * 2
def baseEnd_2067747 : Nat := 78648006140179752892823

theorem tailTrace_2067747 : CollatzResearch.WordTrace tailWord_2067747 prefixEnd_2067747 78648006140179752892823 := by
  unfold tailWord_2067747
  simp only [CollatzResearch.WordTrace]
  refine ⟨75416928839913236917553495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50277952559942157945035663 75416928839913236917553495)
  ·
    refine ⟨113125393259869855376330243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75416928839913236917553495 113125393259869855376330243)
    ·
      refine ⟨169688089889804783064495365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113125393259869855376330243 169688089889804783064495365)
      ·
        refine ⟨31816516854338396824592881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169688089889804783064495365 31816516854338396824592881)
        ·
          refine ⟨23862387640753797618444661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31816516854338396824592881 23862387640753797618444661)
          ·
            refine ⟨2237098841320668526729187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23862387640753797618444661 2237098841320668526729187)
            ·
              refine ⟨3355648261981002790093781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2237098841320668526729187 3355648261981002790093781)
              ·
                refine ⟨78648006140179752892823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3355648261981002790093781 78648006140179752892823)
                ·
                  rfl

theorem cell22_2067747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 7].length) (baseStart_2067747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067747 prefixEnd_2067747 := by exact prefixLift 2067747
  have htrace : WordTrace (prefixWord ++ tailWord_2067747) baseStart_2067747 baseEnd_2067747 := by
    simpa [prefixWord, tailWord_2067747, baseEnd_2067747] using wordTrace_append hprefix tailTrace_2067747
  have hstable : (prefixWord ++ tailWord_2067747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067747).length < 2 ^ (prefixWord ++ tailWord_2067747).sum := by decide
  have hdescent : baseEnd_2067747 < baseStart_2067747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067760 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 2, 6]
def baseStart_2067760 : Nat := 118140960795 + 2067760 * 2 ^ 59
def prefixEnd_2067760 : Nat := 4983230072969 + 3 ^ 40 * 2067760 * 2
def baseEnd_2067760 : Nat := 707836505427290075460367

theorem tailTrace_2067760 : CollatzResearch.WordTrace tailWord_2067760 prefixEnd_2067760 707836505427290075460367 := by
  unfold tailWord_2067760
  simp only [CollatzResearch.WordTrace]
  refine ⟨37708701494433070068888367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50278268659244093425184489 37708701494433070068888367)
  ·
    refine ⟨56563052241649605103332551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37708701494433070068888367 56563052241649605103332551)
    ·
      refine ⟨84844578362474407654998827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56563052241649605103332551 84844578362474407654998827)
      ·
        refine ⟨127266867543711611482498241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84844578362474407654998827 127266867543711611482498241)
        ·
          refine ⟨95450150657783708611873681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127266867543711611482498241 95450150657783708611873681)
          ·
            refine ⟨71587612993337781458905261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95450150657783708611873681 71587612993337781458905261)
            ·
              refine ⟨26845354872501668047089473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71587612993337781458905261 26845354872501668047089473)
              ·
                refine ⟨20134016154376251035317105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26845354872501668047089473 20134016154376251035317105)
                ·
                  refine ⟨15100512115782188276487829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20134016154376251035317105 15100512115782188276487829)
                  ·
                    refine ⟨707836505427290075460367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15100512115782188276487829 707836505427290075460367)
                    ·
                      rfl

theorem cell22_2067760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 2, 6].length) (baseStart_2067760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067760 prefixEnd_2067760 := by exact prefixLift 2067760
  have htrace : WordTrace (prefixWord ++ tailWord_2067760) baseStart_2067760 baseEnd_2067760 := by
    simpa [prefixWord, tailWord_2067760, baseEnd_2067760] using wordTrace_append hprefix tailTrace_2067760
  have hstable : (prefixWord ++ tailWord_2067760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067760).length < 2 ^ (prefixWord ++ tailWord_2067760).sum := by decide
  have hdescent : baseEnd_2067760 < baseStart_2067760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067764 : List Nat := [2, 5, 1, 1, 1, 1, 5, 6]
def baseStart_2067764 : Nat := 118140960795 + 2067764 * 2 ^ 59
def prefixEnd_2067764 : Nat := 4983230072969 + 3 ^ 40 * 2067764 * 2
def baseEnd_2067764 : Nat := 78648652745448377595595

theorem tailTrace_2067764 : CollatzResearch.WordTrace tailWord_2067764 prefixEnd_2067764 78648652745448377595595 := by
  unfold tailWord_2067764
  simp only [CollatzResearch.WordTrace]
  refine ⟨37708774440425824410461173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50278365920567765880614897 37708774440425824410461173)
  ·
    refine ⟨3535197603789921038480735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37708774440425824410461173 3535197603789921038480735)
    ·
      refine ⟨5302796405684881557721103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3535197603789921038480735 5302796405684881557721103)
      ·
        refine ⟨7954194608527322336581655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5302796405684881557721103 7954194608527322336581655)
        ·
          refine ⟨11931291912790983504872483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7954194608527322336581655 11931291912790983504872483)
          ·
            refine ⟨17896937869186475257308725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11931291912790983504872483 17896937869186475257308725)
            ·
              refine ⟨1677837925236232055372693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17896937869186475257308725 1677837925236232055372693)
              ·
                refine ⟨78648652745448377595595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1677837925236232055372693 78648652745448377595595)
                ·
                  rfl

theorem cell22_2067764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 6].length) (baseStart_2067764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067764 prefixEnd_2067764 := by exact prefixLift 2067764
  have htrace : WordTrace (prefixWord ++ tailWord_2067764) baseStart_2067764 baseEnd_2067764 := by
    simpa [prefixWord, tailWord_2067764, baseEnd_2067764] using wordTrace_append hprefix tailTrace_2067764
  have hstable : (prefixWord ++ tailWord_2067764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067764).length < 2 ^ (prefixWord ++ tailWord_2067764).sum := by decide
  have hdescent : baseEnd_2067764 < baseStart_2067764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067766 : List Nat := [5, 1, 2, 3, 1, 1, 1, 1, 1, 6]
def baseStart_2067766 : Nat := 118140960795 + 2067766 * 2 ^ 59
def prefixEnd_2067766 : Nat := 4983230072969 + 3 ^ 40 * 2067766 * 2
def baseEnd_2067766 : Nat := 707838559349908059810349

theorem tailTrace_2067766 : CollatzResearch.WordTrace tailWord_2067766 prefixEnd_2067766 707838559349908059810349 := by
  unfold tailWord_2067766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4713601364177775197655947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50278414551229602108330101 4713601364177775197655947)
  ·
    refine ⟨7070402046266662796483921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4713601364177775197655947 7070402046266662796483921)
    ·
      refine ⟨5302801534699997097362941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7070402046266662796483921 5302801534699997097362941)
      ·
        refine ⟨1988550575512498911511103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5302801534699997097362941 1988550575512498911511103)
        ·
          refine ⟨2982825863268748367266655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1988550575512498911511103 2982825863268748367266655)
          ·
            refine ⟨4474238794903122550899983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2982825863268748367266655 4474238794903122550899983)
            ·
              refine ⟨6711358192354683826349975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4474238794903122550899983 6711358192354683826349975)
              ·
                refine ⟨10067037288532025739524963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6711358192354683826349975 10067037288532025739524963)
                ·
                  refine ⟨15100555932798038609287445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10067037288532025739524963 15100555932798038609287445)
                  ·
                    refine ⟨707838559349908059810349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15100555932798038609287445 707838559349908059810349)
                    ·
                      rfl

theorem cell22_2067766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_2067766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067766 prefixEnd_2067766 := by exact prefixLift 2067766
  have htrace : WordTrace (prefixWord ++ tailWord_2067766) baseStart_2067766 baseEnd_2067766 := by
    simpa [prefixWord, tailWord_2067766, baseEnd_2067766] using wordTrace_append hprefix tailTrace_2067766
  have hstable : (prefixWord ++ tailWord_2067766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067766).length < 2 ^ (prefixWord ++ tailWord_2067766).sum := by decide
  have hdescent : baseEnd_2067766 < baseStart_2067766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067796 : List Nat := [2, 4, 1, 1, 2, 1, 1, 6, 1, 3]
def baseStart_2067796 : Nat := 118140960795 + 2067796 * 2 ^ 59
def prefixEnd_2067796 : Nat := 4983230072969 + 3 ^ 40 * 2067796 * 2
def baseEnd_2067796 : Nat := 707848828962997981560257

theorem tailTrace_2067796 : CollatzResearch.WordTrace tailWord_2067796 prefixEnd_2067796 707848828962997981560257 := by
  unfold tailWord_2067796
  simp only [CollatzResearch.WordTrace]
  refine ⟨37709358008367859143043621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50279144011157145524058161 37709358008367859143043621)
  ·
    refine ⟨7070504626568973589320679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37709358008367859143043621 7070504626568973589320679)
    ·
      refine ⟨10605756939853460383981019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7070504626568973589320679 10605756939853460383981019)
      ·
        refine ⟨15908635409780190575971529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10605756939853460383981019 15908635409780190575971529)
        ·
          refine ⟨11931476557335142931978647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15908635409780190575971529 11931476557335142931978647)
          ·
            refine ⟨17897214836002714397967971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11931476557335142931978647 17897214836002714397967971)
            ·
              refine ⟨26845822254004071596951957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17897214836002714397967971 26845822254004071596951957)
              ·
                refine ⟨1258397918156440856107123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26845822254004071596951957 1258397918156440856107123)
                ·
                  refine ⟨1887596877234661284160685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1258397918156440856107123 1887596877234661284160685)
                  ·
                    refine ⟨707848828962997981560257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1887596877234661284160685 707848828962997981560257)
                    ·
                      rfl

theorem cell22_2067796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_2067796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067796 prefixEnd_2067796 := by exact prefixLift 2067796
  have htrace : WordTrace (prefixWord ++ tailWord_2067796) baseStart_2067796 baseEnd_2067796 := by
    simpa [prefixWord, tailWord_2067796, baseEnd_2067796] using wordTrace_append hprefix tailTrace_2067796
  have hstable : (prefixWord ++ tailWord_2067796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067796).length < 2 ^ (prefixWord ++ tailWord_2067796).sum := by decide
  have hdescent : baseEnd_2067796 < baseStart_2067796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067912 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 1, 8]
def baseStart_2067912 : Nat := 118140960795 + 2067912 * 2 ^ 59
def prefixEnd_2067912 : Nat := 4983230072969 + 3 ^ 40 * 2067912 * 2
def baseEnd_2067912 : Nat := 707888538133612345659901

theorem tailTrace_2067912 : CollatzResearch.WordTrace tailWord_2067912 prefixEnd_2067912 707888538133612345659901 := by
  unfold tailWord_2067912
  simp only [CollatzResearch.WordTrace]
  refine ⟨37711473442157735048654995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50281964589543646731539993 37711473442157735048654995)
  ·
    refine ⟨56567210163236602572982493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37711473442157735048654995 56567210163236602572982493)
    ·
      refine ⟨21212703811213725964868435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56567210163236602572982493 21212703811213725964868435)
      ·
        refine ⟨31819055716820588947302653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21212703811213725964868435 31819055716820588947302653)
        ·
          refine ⟨11932145893807720855238495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31819055716820588947302653 11932145893807720855238495)
          ·
            refine ⟨17898218840711581282857743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11932145893807720855238495 17898218840711581282857743)
            ·
              refine ⟨26847328261067371924286615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17898218840711581282857743 26847328261067371924286615)
              ·
                refine ⟨40270992391601057886429923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26847328261067371924286615 40270992391601057886429923)
                ·
                  refine ⟨60406488587401586829644885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40270992391601057886429923 60406488587401586829644885)
                  ·
                    refine ⟨707888538133612345659901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60406488587401586829644885 707888538133612345659901)
                    ·
                      rfl

theorem cell22_2067912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_2067912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067912 prefixEnd_2067912 := by exact prefixLift 2067912
  have htrace : WordTrace (prefixWord ++ tailWord_2067912) baseStart_2067912 baseEnd_2067912 := by
    simpa [prefixWord, tailWord_2067912, baseEnd_2067912] using wordTrace_append hprefix tailTrace_2067912
  have hstable : (prefixWord ++ tailWord_2067912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067912).length < 2 ^ (prefixWord ++ tailWord_2067912).sum := by decide
  have hdescent : baseEnd_2067912 < baseStart_2067912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067989 : List Nat := [1, 3, 2, 1, 3, 2, 2, 2, 6]
def baseStart_2067989 : Nat := 118140960795 + 2067989 * 2 ^ 59
def prefixEnd_2067989 : Nat := 4983230072969 + 3 ^ 40 * 2067989 * 2
def baseEnd_2067989 : Nat := 235971632269069937161555

theorem tailTrace_2067989 : CollatzResearch.WordTrace tailWord_2067989 prefixEnd_2067989 235971632269069937161555 := by
  unfold tailWord_2067989
  simp only [CollatzResearch.WordTrace]
  refine ⟨75425755305036512247863021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50283836870024341498575347 75425755305036512247863021)
  ·
    refine ⟨28284658239388692092948633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75425755305036512247863021 28284658239388692092948633)
    ·
      refine ⟨21213493679541519069711475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28284658239388692092948633 21213493679541519069711475)
      ·
        refine ⟨31820240519312278604567213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21213493679541519069711475 31820240519312278604567213)
        ·
          refine ⟨11932590194742104476712705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31820240519312278604567213 11932590194742104476712705)
          ·
            refine ⟨8949442646056578357534529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11932590194742104476712705 8949442646056578357534529)
            ·
              refine ⟨6712081984542433768150897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8949442646056578357534529 6712081984542433768150897)
              ·
                refine ⟨5034061488406825326113173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6712081984542433768150897 5034061488406825326113173)
                ·
                  refine ⟨235971632269069937161555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5034061488406825326113173 235971632269069937161555)
                  ·
                    rfl

theorem cell22_2067989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 6].length) (baseStart_2067989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2067989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2067989 prefixEnd_2067989 := by exact prefixLift 2067989
  have htrace : WordTrace (prefixWord ++ tailWord_2067989) baseStart_2067989 baseEnd_2067989 := by
    simpa [prefixWord, tailWord_2067989, baseEnd_2067989] using wordTrace_append hprefix tailTrace_2067989
  have hstable : (prefixWord ++ tailWord_2067989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067989).length < 2 ^ (prefixWord ++ tailWord_2067989).sum := by decide
  have hdescent : baseEnd_2067989 < baseStart_2067989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068019 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 4, 4]
def baseStart_2068019 : Nat := 118140960795 + 2068019 * 2 ^ 59
def prefixEnd_2068019 : Nat := 4983230072969 + 3 ^ 40 * 2068019 * 2
def baseEnd_2068019 : Nat := 707925166420299733234573

theorem tailTrace_2068019 : CollatzResearch.WordTrace tailWord_2068019 prefixEnd_2068019 707925166420299733234573 := by
  unfold tailWord_2068019
  simp only [CollatzResearch.WordTrace]
  refine ⟨75426849494927827371455111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50284566329951884914303407 75426849494927827371455111)
  ·
    refine ⟨113140274242391741057182667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75426849494927827371455111 113140274242391741057182667)
    ·
      refine ⟨169710411363587611585774001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113140274242391741057182667 169710411363587611585774001)
      ·
        refine ⟨127282808522690708689330501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169710411363587611585774001 127282808522690708689330501)
        ·
          refine ⟨23865526598004507879249469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127282808522690708689330501 23865526598004507879249469)
          ·
            refine ⟨8949572474251690454718551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23865526598004507879249469 8949572474251690454718551)
            ·
              refine ⟨13424358711377535682077827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8949572474251690454718551 13424358711377535682077827)
              ·
                refine ⟨20136538067066303523116741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13424358711377535682077827 20136538067066303523116741)
                ·
                  refine ⟨3775600887574931910584389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20136538067066303523116741 3775600887574931910584389)
                  ·
                    refine ⟨707925166420299733234573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3775600887574931910584389 707925166420299733234573)
                    ·
                      rfl

theorem cell22_2068019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 4].length) (baseStart_2068019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2068019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2068019 prefixEnd_2068019 := by exact prefixLift 2068019
  have htrace : WordTrace (prefixWord ++ tailWord_2068019) baseStart_2068019 baseEnd_2068019 := by
    simpa [prefixWord, tailWord_2068019, baseEnd_2068019] using wordTrace_append hprefix tailTrace_2068019
  have hstable : (prefixWord ++ tailWord_2068019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068019).length < 2 ^ (prefixWord ++ tailWord_2068019).sum := by decide
  have hdescent : baseEnd_2068019 < baseStart_2068019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068021 : List Nat := [1, 3, 3, 1, 1, 3, 2, 1, 4, 3]
def baseStart_2068021 : Nat := 118140960795 + 2068021 * 2 ^ 59
def prefixEnd_2068021 : Nat := 4983230072969 + 3 ^ 40 * 2068021 * 2
def baseEnd_2068021 : Nat := 707925851061172394684567

theorem tailTrace_2068021 : CollatzResearch.WordTrace tailWord_2068021 prefixEnd_2068021 707925851061172394684567 := by
  unfold tailWord_2068021
  simp only [CollatzResearch.WordTrace]
  refine ⟨75426922440920581713027917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50284614960613721142018611 75426922440920581713027917)
  ·
    refine ⟨28285095915345218142385469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75426922440920581713027917 28285095915345218142385469)
    ·
      refine ⟨10606910968254456803394551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28285095915345218142385469 10606910968254456803394551)
      ·
        refine ⟨15910366452381685205091827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10606910968254456803394551 15910366452381685205091827)
        ·
          refine ⟨23865549678572527807637741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15910366452381685205091827 23865549678572527807637741)
          ·
            refine ⟨8949581129464697927864153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23865549678572527807637741 8949581129464697927864153)
            ·
              refine ⟨6712185847098523445898115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8949581129464697927864153 6712185847098523445898115)
              ·
                refine ⟨10068278770647785168847173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6712185847098523445898115 10068278770647785168847173)
                ·
                  refine ⟨1887802269496459719158845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10068278770647785168847173 1887802269496459719158845)
                  ·
                    refine ⟨707925851061172394684567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1887802269496459719158845 707925851061172394684567)
                    ·
                      rfl

theorem cell22_2068021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_2068021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2068021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2068021 prefixEnd_2068021 := by exact prefixLift 2068021
  have htrace : WordTrace (prefixWord ++ tailWord_2068021) baseStart_2068021 baseEnd_2068021 := by
    simpa [prefixWord, tailWord_2068021, baseEnd_2068021] using wordTrace_append hprefix tailTrace_2068021
  have hstable : (prefixWord ++ tailWord_2068021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068021).length < 2 ^ (prefixWord ++ tailWord_2068021).sum := by decide
  have hdescent : baseEnd_2068021 < baseStart_2068021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068023 : List Nat := [1, 1, 3, 1, 2, 5, 3, 2, 4]
def baseStart_2068023 : Nat := 118140960795 + 2068023 * 2 ^ 59
def prefixEnd_2068023 : Nat := 4983230072969 + 3 ^ 40 * 2068023 * 2
def baseEnd_2068023 : Nat := 235975511900681685378187

theorem tailTrace_2068023 : CollatzResearch.WordTrace tailWord_2068023 prefixEnd_2068023 235975511900681685378187 := by
  unfold tailWord_2068023
  simp only [CollatzResearch.WordTrace]
  refine ⟨75426995386913336054600723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50284663591275557369733815 75426995386913336054600723)
  ·
    refine ⟨113140493080370004081901085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75426995386913336054600723 113140493080370004081901085)
    ·
      refine ⟨42427684905138751530712907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113140493080370004081901085 42427684905138751530712907)
      ·
        refine ⟨63641527357708127296069361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42427684905138751530712907 63641527357708127296069361)
        ·
          refine ⟨47731145518281095472052021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63641527357708127296069361 47731145518281095472052021)
          ·
            refine ⟨4474794892338852700504877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47731145518281095472052021 4474794892338852700504877)
            ·
              refine ⟨1678048084627069762689329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4474794892338852700504877 1678048084627069762689329)
              ·
                refine ⟨1258536063470302322016997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1678048084627069762689329 1258536063470302322016997)
                ·
                  refine ⟨235975511900681685378187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1258536063470302322016997 235975511900681685378187)
                  ·
                    rfl

theorem cell22_2068023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2, 4].length) (baseStart_2068023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2068023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2068023 prefixEnd_2068023 := by exact prefixLift 2068023
  have htrace : WordTrace (prefixWord ++ tailWord_2068023) baseStart_2068023 baseEnd_2068023 := by
    simpa [prefixWord, tailWord_2068023, baseEnd_2068023] using wordTrace_append hprefix tailTrace_2068023
  have hstable : (prefixWord ++ tailWord_2068023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068023).length < 2 ^ (prefixWord ++ tailWord_2068023).sum := by decide
  have hdescent : baseEnd_2068023 < baseStart_2068023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068186 : List Nat := [3, 1, 1, 2, 2, 5, 8]
def baseStart_2068186 : Nat := 118140960795 + 2068186 * 2 ^ 59
def prefixEnd_2068186 : Nat := 4983230072969 + 3 ^ 40 * 2068186 * 2
def baseEnd_2068186 : Nat := 26221567923450628307743

theorem tailTrace_2068186 : CollatzResearch.WordTrace tailWord_2068186 prefixEnd_2068186 26221567923450628307743 := by
  unfold tailWord_2068186
  simp only [CollatzResearch.WordTrace]
  refine ⟨18858235121330703723196103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50288626990215209928522941 18858235121330703723196103)
  ·
    refine ⟨28287352681996055584794155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18858235121330703723196103 28287352681996055584794155)
    ·
      refine ⟨42431029022994083377191233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28287352681996055584794155 42431029022994083377191233)
      ·
        refine ⟨31823271767245562532893425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42431029022994083377191233 31823271767245562532893425)
        ·
          refine ⟨23867453825434171899670069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31823271767245562532893425 23867453825434171899670069)
          ·
            refine ⟨2237573796134453615594069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23867453825434171899670069 2237573796134453615594069)
            ·
              refine ⟨26221567923450628307743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2237573796134453615594069 26221567923450628307743)
              ·
                rfl

theorem cell22_2068186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 8].length) (baseStart_2068186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2068186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2068186 prefixEnd_2068186 := by exact prefixLift 2068186
  have htrace : WordTrace (prefixWord ++ tailWord_2068186) baseStart_2068186 baseEnd_2068186 := by
    simpa [prefixWord, tailWord_2068186, baseEnd_2068186] using wordTrace_append hprefix tailTrace_2068186
  have hstable : (prefixWord ++ tailWord_2068186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068186).length < 2 ^ (prefixWord ++ tailWord_2068186).sum := by decide
  have hdescent : baseEnd_2068186 < baseStart_2068186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068237 : List Nat := [1, 7, 2, 1, 1, 10]
def baseStart_2068237 : Nat := 118140960795 + 2068237 * 2 ^ 59
def prefixEnd_2068237 : Nat := 4983230072969 + 3 ^ 40 * 2068237 * 2
def baseEnd_2068237 : Nat := 8740738176239751003505

theorem tailTrace_2068237 : CollatzResearch.WordTrace tailWord_2068237 prefixEnd_2068237 8740738176239751003505 := by
  unfold tailWord_2068237
  simp only [CollatzResearch.WordTrace]
  refine ⟨75434800608138050602890965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50289867072092033735260643 75434800608138050602890965)
  ·
    refine ⟨1768003139253235561005257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 75434800608138050602890965 1768003139253235561005257)
    ·
      refine ⟨1326002354439926670753943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1768003139253235561005257 1326002354439926670753943)
      ·
        refine ⟨1989003531659890006130915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1326002354439926670753943 1989003531659890006130915)
        ·
          refine ⟨2983505297489835009196373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1989003531659890006130915 2983505297489835009196373)
          ·
            refine ⟨8740738176239751003505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2983505297489835009196373 8740738176239751003505)
            ·
              rfl

theorem cell22_2068237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 10].length) (baseStart_2068237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2068237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2068237 prefixEnd_2068237 := by exact prefixLift 2068237
  have htrace : WordTrace (prefixWord ++ tailWord_2068237) baseStart_2068237 baseEnd_2068237 := by
    simpa [prefixWord, tailWord_2068237, baseEnd_2068237] using wordTrace_append hprefix tailTrace_2068237
  have hstable : (prefixWord ++ tailWord_2068237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068237).length < 2 ^ (prefixWord ++ tailWord_2068237).sum := by decide
  have hdescent : baseEnd_2068237 < baseStart_2068237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068254 : List Nat := [4, 3, 2, 2, 2, 1, 1, 7]
def baseStart_2068254 : Nat := 118140960795 + 2068254 * 2 ^ 59
def prefixEnd_2068254 : Nat := 4983230072969 + 3 ^ 40 * 2068254 * 2
def baseEnd_2068254 : Nat := 78667290191426383734317

theorem tailTrace_2068254 : CollatzResearch.WordTrace tailWord_2068254 prefixEnd_2068254 78667290191426383734317 := by
  unfold tailWord_2068254
  simp only [CollatzResearch.WordTrace]
  refine ⟨9429427581134557813282477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50290280432717641670839877 9429427581134557813282477)
  ·
    refine ⟨3536035342925459179980929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9429427581134557813282477 3536035342925459179980929)
    ·
      refine ⟨2652026507194094384985697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3536035342925459179980929 2652026507194094384985697)
      ·
        refine ⟨1989019880395570788739273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2652026507194094384985697 1989019880395570788739273)
        ·
          refine ⟨1491764910296678091554455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1989019880395570788739273 1491764910296678091554455)
          ·
            refine ⟨2237647365445017137331683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491764910296678091554455 2237647365445017137331683)
            ·
              refine ⟨3356471048167525705997525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2237647365445017137331683 3356471048167525705997525)
              ·
                refine ⟨78667290191426383734317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3356471048167525705997525 78667290191426383734317)
                ·
                  rfl

theorem cell22_2068254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 7].length) (baseStart_2068254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2068254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2068254 prefixEnd_2068254 := by exact prefixLift 2068254
  have htrace : WordTrace (prefixWord ++ tailWord_2068254) baseStart_2068254 baseEnd_2068254 := by
    simpa [prefixWord, tailWord_2068254, baseEnd_2068254] using wordTrace_append hprefix tailTrace_2068254
  have hstable : (prefixWord ++ tailWord_2068254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068254).length < 2 ^ (prefixWord ++ tailWord_2068254).sum := by decide
  have hdescent : baseEnd_2068254 < baseStart_2068254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068295 : List Nat := [1, 1, 4, 1, 2, 1, 6, 1, 1, 4]
def baseStart_2068295 : Nat := 118140960795 + 2068295 * 2 ^ 59
def prefixEnd_2068295 : Nat := 4983230072969 + 3 ^ 40 * 2068295 * 2
def baseEnd_2068295 : Nat := 708019646860727013333727

theorem tailTrace_2068295 : CollatzResearch.WordTrace tailWord_2068295 prefixEnd_2068295 708019646860727013333727 := by
  unfold tailWord_2068295
  simp only [CollatzResearch.WordTrace]
  refine ⟨75436916041927926508502339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50291277361285284339001559 75436916041927926508502339)
  ·
    refine ⟨113155374062891889762753509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75436916041927926508502339 113155374062891889762753509)
    ·
      refine ⟨21216632636792229330516283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113155374062891889762753509 21216632636792229330516283)
      ·
        refine ⟨31824948955188343995774425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21216632636792229330516283 31824948955188343995774425)
        ·
          refine ⟨23868711716391257996830819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31824948955188343995774425 23868711716391257996830819)
          ·
            refine ⟨35803067574586886995246229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23868711716391257996830819 35803067574586886995246229)
            ·
              refine ⟨1678268792558760327902167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35803067574586886995246229 1678268792558760327902167)
              ·
                refine ⟨2517403188838140491853251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1678268792558760327902167 2517403188838140491853251)
                ·
                  refine ⟨3776104783257210737779877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2517403188838140491853251 3776104783257210737779877)
                  ·
                    refine ⟨708019646860727013333727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3776104783257210737779877 708019646860727013333727)
                    ·
                      rfl

theorem cell22_2068295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_2068295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2068295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2068295 prefixEnd_2068295 := by exact prefixLift 2068295
  have htrace : WordTrace (prefixWord ++ tailWord_2068295) baseStart_2068295 baseEnd_2068295 := by
    simpa [prefixWord, tailWord_2068295, baseEnd_2068295] using wordTrace_append hprefix tailTrace_2068295
  have hstable : (prefixWord ++ tailWord_2068295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068295).length < 2 ^ (prefixWord ++ tailWord_2068295).sum := by decide
  have hdescent : baseEnd_2068295 < baseStart_2068295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068321 : List Nat := [1, 2, 3, 1, 1, 1, 4, 9]
def baseStart_2068321 : Nat := 118140960795 + 2068321 * 2 ^ 59
def prefixEnd_2068321 : Nat := 4983230072969 + 3 ^ 40 * 2068321 * 2
def baseEnd_2068321 : Nat := 78669838576896845798183

theorem tailTrace_2068321 : CollatzResearch.WordTrace tailWord_2068321 prefixEnd_2068321 78669838576896845798183 := by
  unfold tailWord_2068321
  simp only [CollatzResearch.WordTrace]
  refine ⟨75437864339833732948948817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50291909559889155299299211 75437864339833732948948817)
  ·
    refine ⟨56578398254875299711711613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75437864339833732948948817 56578398254875299711711613)
    ·
      refine ⟨21216899345578237391891855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56578398254875299711711613 21216899345578237391891855)
      ·
        refine ⟨31825349018367356087837783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21216899345578237391891855 31825349018367356087837783)
        ·
          refine ⟨47738023527551034131756675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31825349018367356087837783 47738023527551034131756675)
          ·
            refine ⟨71607035291326551197635013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47738023527551034131756675 71607035291326551197635013)
            ·
              refine ⟨13426319117123728349556565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71607035291326551197635013 13426319117123728349556565)
              ·
                refine ⟨78669838576896845798183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13426319117123728349556565 78669838576896845798183)
                ·
                  rfl

theorem cell22_2068321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 9].length) (baseStart_2068321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2068321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2068321 prefixEnd_2068321 := by exact prefixLift 2068321
  have htrace : WordTrace (prefixWord ++ tailWord_2068321) baseStart_2068321 baseEnd_2068321 := by
    simpa [prefixWord, tailWord_2068321, baseEnd_2068321] using wordTrace_append hprefix tailTrace_2068321
  have hstable : (prefixWord ++ tailWord_2068321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068321).length < 2 ^ (prefixWord ++ tailWord_2068321).sum := by decide
  have hdescent : baseEnd_2068321 < baseStart_2068321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068336 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 1, 9]
def baseStart_2068336 : Nat := 118140960795 + 2068336 * 2 ^ 59
def prefixEnd_2068336 : Nat := 4983230072969 + 3 ^ 40 * 2068336 * 2
def baseEnd_2068336 : Nat := 708033681998616573058601

theorem tailTrace_2068336 : CollatzResearch.WordTrace tailWord_2068336 prefixEnd_2068336 708033681998616573058601 := by
  unfold tailWord_2068336
  simp only [CollatzResearch.WordTrace]
  refine ⟨37719205717389695255372431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50292274289852927007163241 37719205717389695255372431)
  ·
    refine ⟨56578808576084542883058647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37719205717389695255372431 56578808576084542883058647)
    ·
      refine ⟨84868212864126814324587971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56578808576084542883058647 84868212864126814324587971)
      ·
        refine ⟨127302319296190221486881957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84868212864126814324587971 127302319296190221486881957)
        ·
          refine ⟨23869184868035666528790367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127302319296190221486881957 23869184868035666528790367)
          ·
            refine ⟨35803777302053499793185551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23869184868035666528790367 35803777302053499793185551)
            ·
              refine ⟨53705665953080249689778327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35803777302053499793185551 53705665953080249689778327)
              ·
                refine ⟨80558498929620374534667491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53705665953080249689778327 80558498929620374534667491)
                ·
                  refine ⟨120837748394430561802001237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80558498929620374534667491 120837748394430561802001237)
                  ·
                    refine ⟨708033681998616573058601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 120837748394430561802001237 708033681998616573058601)
                    ·
                      rfl

theorem cell22_2068336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_2068336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2068336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2068336 prefixEnd_2068336 := by exact prefixLift 2068336
  have htrace : WordTrace (prefixWord ++ tailWord_2068336) baseStart_2068336 baseEnd_2068336 := by
    simpa [prefixWord, tailWord_2068336, baseEnd_2068336] using wordTrace_append hprefix tailTrace_2068336
  have hstable : (prefixWord ++ tailWord_2068336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068336).length < 2 ^ (prefixWord ++ tailWord_2068336).sum := by decide
  have hdescent : baseEnd_2068336 < baseStart_2068336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068351 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 1, 8]
def baseStart_2068351 : Nat := 118140960795 + 2068351 * 2 ^ 59
def prefixEnd_2068351 : Nat := 4983230072969 + 3 ^ 40 * 2068351 * 2
def baseEnd_2068351 : Nat := 708038816805161533933555

theorem tailTrace_2068351 : CollatzResearch.WordTrace tailWord_2068351 prefixEnd_2068351 708038816805161533933555 := by
  unfold tailWord_2068351
  simp only [CollatzResearch.WordTrace]
  refine ⟨75438958529725048072540907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50292639019816698715027271 75438958529725048072540907)
  ·
    refine ⟨113158437794587572108811361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75438958529725048072540907 113158437794587572108811361)
    ·
      refine ⟨84868828345940679081608521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113158437794587572108811361 84868828345940679081608521)
      ·
        refine ⟨63651621259455509311206391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84868828345940679081608521 63651621259455509311206391)
        ·
          refine ⟨95477431889183263966809587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63651621259455509311206391 95477431889183263966809587)
          ·
            refine ⟨143216147833774895950214381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95477431889183263966809587 143216147833774895950214381)
            ·
              refine ⟨53706055437665585981330393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143216147833774895950214381 53706055437665585981330393)
              ·
                refine ⟨40279541578249189485997795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53706055437665585981330393 40279541578249189485997795)
                ·
                  refine ⟨60419312367373784228996693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40279541578249189485997795 60419312367373784228996693)
                  ·
                    refine ⟨708038816805161533933555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60419312367373784228996693 708038816805161533933555)
                    ·
                      rfl

theorem cell22_2068351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_2068351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2068351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2068351 prefixEnd_2068351 := by exact prefixLift 2068351
  have htrace : WordTrace (prefixWord ++ tailWord_2068351) baseStart_2068351 baseEnd_2068351 := by
    simpa [prefixWord, tailWord_2068351, baseEnd_2068351] using wordTrace_append hprefix tailTrace_2068351
  have hstable : (prefixWord ++ tailWord_2068351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068351).length < 2 ^ (prefixWord ++ tailWord_2068351).sum := by decide
  have hdescent : baseEnd_2068351 < baseStart_2068351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068376 : List Nat := [2, 1, 2, 6, 1, 2, 2, 1, 2, 3]
def baseStart_2068376 : Nat := 118140960795 + 2068376 * 2 ^ 59
def prefixEnd_2068376 : Nat := 4983230072969 + 3 ^ 40 * 2068376 * 2
def baseEnd_2068376 : Nat := 708047374816069802058479

theorem tailTrace_2068376 : CollatzResearch.WordTrace tailWord_2068376 prefixEnd_2068376 708047374816069802058479 := by
  unfold tailWord_2068376
  simp only [CollatzResearch.WordTrace]
  refine ⟨37719935177317238671100491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50293246903089651561467321 37719935177317238671100491)
  ·
    refine ⟨56579902765975858006650737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37719935177317238671100491 56579902765975858006650737)
    ·
      refine ⟨42434927074481893504988053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56579902765975858006650737 42434927074481893504988053)
      ·
        refine ⟨1989137206616338758046315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42434927074481893504988053 1989137206616338758046315)
        ·
          refine ⟨2983705809924508137069473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1989137206616338758046315 2983705809924508137069473)
          ·
            refine ⟨2237779357443381102802105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2983705809924508137069473 2237779357443381102802105)
            ·
              refine ⟨1678334518082535827101579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2237779357443381102802105 1678334518082535827101579)
              ·
                refine ⟨2517501777123803740652369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1678334518082535827101579 2517501777123803740652369)
                ·
                  refine ⟨1888126332842852805489277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2517501777123803740652369 1888126332842852805489277)
                  ·
                    refine ⟨708047374816069802058479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1888126332842852805489277 708047374816069802058479)
                    ·
                      rfl

theorem cell22_2068376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 2, 3].length) (baseStart_2068376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2068376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2068376 prefixEnd_2068376 := by exact prefixLift 2068376
  have htrace : WordTrace (prefixWord ++ tailWord_2068376) baseStart_2068376 baseEnd_2068376 := by
    simpa [prefixWord, tailWord_2068376, baseEnd_2068376] using wordTrace_append hprefix tailTrace_2068376
  have hstable : (prefixWord ++ tailWord_2068376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068376).length < 2 ^ (prefixWord ++ tailWord_2068376).sum := by decide
  have hdescent : baseEnd_2068376 < baseStart_2068376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068462 : List Nat := [4, 1, 2, 1, 3, 1, 1, 5, 4]
def baseStart_2068462 : Nat := 118140960795 + 2068462 * 2 ^ 59
def prefixEnd_2068462 : Nat := 4983230072969 + 3 ^ 40 * 2068462 * 2
def baseEnd_2068462 : Nat := 236025604791198081469405

theorem tailTrace_2068462 : CollatzResearch.WordTrace tailWord_2068462 prefixEnd_2068462 236025604791198081469405 := by
  unfold tailWord_2068462
  simp only [CollatzResearch.WordTrace]
  refine ⟨9430375879040364253728955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50295338021548609353221093 9430375879040364253728955)
  ·
    refine ⟨14145563818560546380593433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9430375879040364253728955 14145563818560546380593433)
    ·
      refine ⟨10609172863920409785445075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14145563818560546380593433 10609172863920409785445075)
      ·
        refine ⟨15913759295880614678167613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10609172863920409785445075 15913759295880614678167613)
        ·
          refine ⟨5967659735955230504312855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15913759295880614678167613 5967659735955230504312855)
          ·
            refine ⟨8951489603932845756469283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5967659735955230504312855 8951489603932845756469283)
            ·
              refine ⟨13427234405899268634703925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8951489603932845756469283 13427234405899268634703925)
              ·
                refine ⟨1258803225553056434503493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13427234405899268634703925 1258803225553056434503493)
                ·
                  refine ⟨236025604791198081469405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1258803225553056434503493 236025604791198081469405)
                  ·
                    rfl

theorem cell22_2068462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_2068462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2068462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2068462 prefixEnd_2068462 := by exact prefixLift 2068462
  have htrace : WordTrace (prefixWord ++ tailWord_2068462) baseStart_2068462 baseEnd_2068462 := by
    simpa [prefixWord, tailWord_2068462, baseEnd_2068462] using wordTrace_append hprefix tailTrace_2068462
  have hstable : (prefixWord ++ tailWord_2068462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068462).length < 2 ^ (prefixWord ++ tailWord_2068462).sum := by decide
  have hdescent : baseEnd_2068462 < baseStart_2068462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068473 : List Nat := [1, 2, 1, 3, 1, 5, 9]
def baseStart_2068473 : Nat := 118140960795 + 2068473 * 2 ^ 59
def prefixEnd_2068473 : Nat := 4983230072969 + 3 ^ 40 * 2068473 * 2
def baseEnd_2068473 : Nat := 26225206662903477125303

theorem tailTrace_2068473 : CollatzResearch.WordTrace tailWord_2068473 prefixEnd_2068473 26225206662903477125303 := by
  unfold tailWord_2068473
  simp only [CollatzResearch.WordTrace]
  refine ⟨75443408235283062908482073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50295605490188708605654715 75443408235283062908482073)
  ·
    refine ⟨56582556176462297181361555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75443408235283062908482073 56582556176462297181361555)
    ·
      refine ⟨84873834264693445772042333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56582556176462297181361555 84873834264693445772042333)
      ·
        refine ⟨31827687849260042164515875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84873834264693445772042333 31827687849260042164515875)
        ·
          refine ⟨47741531773890063246773813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31827687849260042164515875 47741531773890063246773813)
          ·
            refine ⟨4475768603802193429385045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47741531773890063246773813 4475768603802193429385045)
            ·
              refine ⟨26225206662903477125303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4475768603802193429385045 26225206662903477125303)
              ·
                rfl

theorem cell22_2068473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 9].length) (baseStart_2068473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2068473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2068473 prefixEnd_2068473 := by exact prefixLift 2068473
  have htrace : WordTrace (prefixWord ++ tailWord_2068473) baseStart_2068473 baseEnd_2068473 := by
    simpa [prefixWord, tailWord_2068473, baseEnd_2068473] using wordTrace_append hprefix tailTrace_2068473
  have hstable : (prefixWord ++ tailWord_2068473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068473).length < 2 ^ (prefixWord ++ tailWord_2068473).sum := by decide
  have hdescent : baseEnd_2068473 < baseStart_2068473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068477 : List Nat := [1, 4, 1, 1, 1, 2, 5, 2, 2, 3]
def baseStart_2068477 : Nat := 118140960795 + 2068477 * 2 ^ 59
def prefixEnd_2068477 : Nat := 4983230072969 + 3 ^ 40 * 2068477 * 2
def baseEnd_2068477 : Nat := 708081949180139205283169

theorem tailTrace_2068477 : CollatzResearch.WordTrace tailWord_2068477 prefixEnd_2068477 708081949180139205283169 := by
  unfold tailWord_2068477
  simp only [CollatzResearch.WordTrace]
  refine ⟨75443554127268571591627685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50295702751512381061085123 75443554127268571591627685)
  ·
    refine ⟨14145666398862857173430191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75443554127268571591627685 14145666398862857173430191)
    ·
      refine ⟨21218499598294285760145287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14145666398862857173430191 21218499598294285760145287)
      ·
        refine ⟨31827749397441428640217931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21218499598294285760145287 31827749397441428640217931)
        ·
          refine ⟨47741624096162142960326897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31827749397441428640217931 47741624096162142960326897)
          ·
            refine ⟨35806218072121607220245173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47741624096162142960326897 35806218072121607220245173)
            ·
              refine ⟨3356832944261400676897985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35806218072121607220245173 3356832944261400676897985)
              ·
                refine ⟨2517624708196050507673489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3356832944261400676897985 2517624708196050507673489)
                ·
                  refine ⟨1888218531147037880755117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2517624708196050507673489 1888218531147037880755117)
                  ·
                    refine ⟨708081949180139205283169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1888218531147037880755117 708081949180139205283169)
                    ·
                      rfl

theorem cell22_2068477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_2068477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2068477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2068477 prefixEnd_2068477 := by exact prefixLift 2068477
  have htrace : WordTrace (prefixWord ++ tailWord_2068477) baseStart_2068477 baseEnd_2068477 := by
    simpa [prefixWord, tailWord_2068477, baseEnd_2068477] using wordTrace_append hprefix tailTrace_2068477
  have hstable : (prefixWord ++ tailWord_2068477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068477).length < 2 ^ (prefixWord ++ tailWord_2068477).sum := by decide
  have hdescent : baseEnd_2068477 < baseStart_2068477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068494 : List Nat := [4, 1, 1, 2, 2, 1, 5, 1, 2, 3]
def baseStart_2068494 : Nat := 118140960795 + 2068494 * 2 ^ 59
def prefixEnd_2068494 : Nat := 4983230072969 + 3 ^ 40 * 2068494 * 2
def baseEnd_2068494 : Nat := 708087768627556827608117

theorem tailTrace_2068494 : CollatzResearch.WordTrace tailWord_2068494 prefixEnd_2068494 708087768627556827608117 := by
  unfold tailWord_2068494
  simp only [CollatzResearch.WordTrace]
  refine ⟨9430521771025872936874567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50296116112137988996664357 9430521771025872936874567)
  ·
    refine ⟨14145782656538809405311851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9430521771025872936874567 14145782656538809405311851)
    ·
      refine ⟨21218673984808214107967777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14145782656538809405311851 21218673984808214107967777)
      ·
        refine ⟨15914005488606160580975833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21218673984808214107967777 15914005488606160580975833)
        ·
          refine ⟨11935504116454620435731875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15914005488606160580975833 11935504116454620435731875)
          ·
            refine ⟨17903256174681930653597813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11935504116454620435731875 17903256174681930653597813)
            ·
              refine ⟨1678430266376430998774795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17903256174681930653597813 1678430266376430998774795)
              ·
                refine ⟨2517645399564646498162193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1678430266376430998774795 2517645399564646498162193)
                ·
                  refine ⟨1888234049673484873621645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2517645399564646498162193 1888234049673484873621645)
                  ·
                    refine ⟨708087768627556827608117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1888234049673484873621645 708087768627556827608117)
                    ·
                      rfl

theorem cell22_2068494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_2068494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2068494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2068494 prefixEnd_2068494 := by exact prefixLift 2068494
  have htrace : WordTrace (prefixWord ++ tailWord_2068494) baseStart_2068494 baseEnd_2068494 := by
    simpa [prefixWord, tailWord_2068494, baseEnd_2068494] using wordTrace_append hprefix tailTrace_2068494
  have hstable : (prefixWord ++ tailWord_2068494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068494).length < 2 ^ (prefixWord ++ tailWord_2068494).sum := by decide
  have hdescent : baseEnd_2068494 < baseStart_2068494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068612 : List Nat := [2, 3, 2, 1, 2, 1, 4, 1, 1, 5]
def baseStart_2068612 : Nat := 118140960795 + 2068612 * 2 ^ 59
def prefixEnd_2068612 : Nat := 4983230072969 + 3 ^ 40 * 2068612 * 2
def baseEnd_2068612 : Nat := 708128162439043853157755

theorem tailTrace_2068612 : CollatzResearch.WordTrace tailWord_2068612 prefixEnd_2068612 708128162439043853157755 := by
  unfold tailWord_2068612
  simp only [CollatzResearch.WordTrace]
  refine ⟨37724238990889744823896045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50298985321186326431861393 37724238990889744823896045)
  ·
    refine ⟨14146589621583654308961017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37724238990889744823896045 14146589621583654308961017)
    ·
      refine ⟨10609942216187740731720763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14146589621583654308961017 10609942216187740731720763)
      ·
        refine ⟨15914913324281611097581145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10609942216187740731720763 15914913324281611097581145)
        ·
          refine ⟨11936184993211208323185859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15914913324281611097581145 11936184993211208323185859)
          ·
            refine ⟨17904277489816812484778789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11936184993211208323185859 17904277489816812484778789)
            ·
              refine ⟨3357052029340652340896023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17904277489816812484778789 3357052029340652340896023)
              ·
                refine ⟨5035578044010978511344035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3357052029340652340896023 5035578044010978511344035)
                ·
                  refine ⟨7553367066016467767016053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5035578044010978511344035 7553367066016467767016053)
                  ·
                    refine ⟨708128162439043853157755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7553367066016467767016053 708128162439043853157755)
                    ·
                      rfl

theorem cell22_2068612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_2068612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2068612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2068612 prefixEnd_2068612 := by exact prefixLift 2068612
  have htrace : WordTrace (prefixWord ++ tailWord_2068612) baseStart_2068612 baseEnd_2068612 := by
    simpa [prefixWord, tailWord_2068612, baseEnd_2068612] using wordTrace_append hprefix tailTrace_2068612
  have hstable : (prefixWord ++ tailWord_2068612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068612).length < 2 ^ (prefixWord ++ tailWord_2068612).sum := by decide
  have hdescent : baseEnd_2068612 < baseStart_2068612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068642 : List Nat := [3, 3, 1, 3, 1, 2, 9]
def baseStart_2068642 : Nat := 118140960795 + 2068642 * 2 ^ 59
def prefixEnd_2068642 : Nat := 4983230072969 + 3 ^ 40 * 2068642 * 2
def baseEnd_2068642 : Nat := 26227349335264213885469

theorem tailTrace_2068642 : CollatzResearch.WordTrace tailWord_2068642 prefixEnd_2068642 26227349335264213885469 := by
  unfold tailWord_2068642
  simp only [CollatzResearch.WordTrace]
  refine ⟨18862393042917701192846045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50299714781113869847589453 18862393042917701192846045)
  ·
    refine ⟨7073397391094137947317267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18862393042917701192846045 7073397391094137947317267)
    ·
      refine ⟨10610096086641206920975901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7073397391094137947317267 10610096086641206920975901)
      ·
        refine ⟨3978786032490452595365963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10610096086641206920975901 3978786032490452595365963)
        ·
          refine ⟨5968179048735678893048945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3978786032490452595365963 5968179048735678893048945)
          ·
            refine ⟨4476134286551759169786709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5968179048735678893048945 4476134286551759169786709)
            ·
              refine ⟨26227349335264213885469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4476134286551759169786709 26227349335264213885469)
              ·
                rfl

theorem cell22_2068642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 9].length) (baseStart_2068642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2068642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2068642 prefixEnd_2068642 := by exact prefixLift 2068642
  have htrace : WordTrace (prefixWord ++ tailWord_2068642) baseStart_2068642 baseEnd_2068642 := by
    simpa [prefixWord, tailWord_2068642, baseEnd_2068642] using wordTrace_append hprefix tailTrace_2068642
  have hstable : (prefixWord ++ tailWord_2068642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068642).length < 2 ^ (prefixWord ++ tailWord_2068642).sum := by decide
  have hdescent : baseEnd_2068642 < baseStart_2068642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068734 : List Nat := [4, 2, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_2068734 : Nat := 118140960795 + 2068734 * 2 ^ 59
def prefixEnd_2068734 : Nat := 4983230072969 + 3 ^ 40 * 2068734 * 2
def baseEnd_2068734 : Nat := 708169925532276201607381

theorem tailTrace_2068734 : CollatzResearch.WordTrace tailWord_2068734 prefixEnd_2068734 708169925532276201607381 := by
  unfold tailWord_2068734
  simp only [CollatzResearch.WordTrace]
  refine ⟨9431615960917188060466657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50301951791558336322488837 9431615960917188060466657)
  ·
    refine ⟨7073711970687891045349993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9431615960917188060466657 7073711970687891045349993)
    ·
      refine ⟨5305283978015918284012495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7073711970687891045349993 5305283978015918284012495)
      ·
        refine ⟨7957925967023877426018743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5305283978015918284012495 7957925967023877426018743)
        ·
          refine ⟨11936888950535816139028115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7957925967023877426018743 11936888950535816139028115)
          ·
            refine ⟨17905333425803724208542173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11936888950535816139028115 17905333425803724208542173)
            ·
              refine ⟨6714500034676396578203315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17905333425803724208542173 6714500034676396578203315)
              ·
                refine ⟨10071750052014594867304973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6714500034676396578203315 10071750052014594867304973)
                ·
                  refine ⟨3776906269505473075239365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10071750052014594867304973 3776906269505473075239365)
                  ·
                    refine ⟨708169925532276201607381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3776906269505473075239365 708169925532276201607381)
                    ·
                      rfl

theorem cell22_2068734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_2068734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2068734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2068734 prefixEnd_2068734 := by exact prefixLift 2068734
  have htrace : WordTrace (prefixWord ++ tailWord_2068734) baseStart_2068734 baseEnd_2068734 := by
    simpa [prefixWord, tailWord_2068734, baseEnd_2068734] using wordTrace_append hprefix tailTrace_2068734
  have hstable : (prefixWord ++ tailWord_2068734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068734).length < 2 ^ (prefixWord ++ tailWord_2068734).sum := by decide
  have hdescent : baseEnd_2068734 < baseStart_2068734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
